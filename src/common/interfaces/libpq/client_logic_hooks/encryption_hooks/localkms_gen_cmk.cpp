/*
 * Copyright (c) 2020 Huawei Technologies Co.,Ltd.
 *
 * openGauss is licensed under Mulan PSL v2.
 * You can use this software according to the terms and conditions of the Mulan PSL v2.
 * You may obtain a copy of Mulan PSL v2 at:
 *
 *          http://license.coscl.org.cn/MulanPSL2
 *
 * THIS SOFTWARE IS PROVIDED ON AN "AS IS" BASIS, WITHOUT WARRANTIES OF ANY KIND,
 * EITHER EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO NON-INFRINGEMENT,
 * MERCHANTABILITY OR FIT FOR A PARTICULAR PURPOSE.
 * See the Mulan PSL v2 for more details.
 * -------------------------------------------------------------------------
 *
 * localkms_gen_cmk.cpp
 *      Use openssl to generate cmk, then encrypt cmk plain and store cmk cipher in file.
 *      At the same time, we need to store/read the iv and salt that are used to derive a key to
 *      encrypt/decrypt cmk plain.
 *
 * IDENTIFICATION
 *	  src\common\interfaces\libpq\client_logic_hooks\encryption_hooks\localkms_gen_cmk.cpp
 *
 * -------------------------------------------------------------------------
 */

#include "localkms_gen_cmk.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <openssl/rand.h>
#include <openssl/rsa.h>
#include <openssl/pem.h>
#include <openssl/err.h>
#include "securec.h"
#include "securec_check.h"
#include "pthread.h"
#include "aead_aes_hamc_enc_key.h"
#include "encrypt_decrypt.h"

static char g_env_value[PATH_MAX] = {0};
static pthread_mutex_t g_env_lock;

static char *get_env_value(const char *name);
static bool is_contain_danger_char(const char *path_value);
static bool is_contain_unsupport_char(const char *key_path_value);
static bool set_global_env_value();
static void rm_one_file(const char *real_path);

#define free_safely(ptr) \
    {                    \
        free(ptr);       \
        ptr = NULL;      \
    }

static char *get_env_value(const char *name)
{
    char *ret = NULL;
    (void)pthread_mutex_lock(&g_env_lock);
    ret = getenv(name);
    (void)pthread_mutex_unlock(&g_env_lock);
    return ret;
}

/* to check environment value */
static bool is_contain_danger_char(const char *path_value)
{
    const char danger_char_list[] = {'|', ';', '&', '$', '<', '>', '`', '\\', '\'', '\"', '{', '}', '(', ')', '[',']',
        '~', '*', '?', '!'};

    for (size_t i = 0; i < strlen(path_value); i++) {
        for (size_t j = 0; j < sizeof(danger_char_list); j++) {
            if (path_value[i] == danger_char_list[j]) {
                printf("ERROR(CLIENT): The path '%s' contain invalid character '%c'.\n", path_value, path_value[i]);
                return true;
            }
        }
    }

    return false;
}

/* to check KEY_PATH value : only support 0-9, a-z, A_Z, '_', '.', '-' */
static bool is_contain_unsupport_char(const char *key_path_value)
{
    char cur_char = 0;
    const char legal_symbol[] = {'_', '.', '-'};

    for (size_t i = 0; i < strlen(key_path_value); i++) {
        cur_char = key_path_value[i];
        if (cur_char >= '0' && cur_char <= '9') {
            continue;
        } else if (cur_char >= 'A' && cur_char <= 'Z') {
            continue;
        } else if (cur_char >= 'a' && cur_char <= 'z') {
            continue;
        } else if (strchr(legal_symbol, cur_char) != NULL) {
                continue;
        } else {
            printf("ERROR(CLIENT): key_path value '%s' contain invalid charachter '%c'.\n", key_path_value, cur_char);
            return true;
        }
    }

    return false;
}

/* 
 * RSA keys generated by LOCALKMS are stored under the path ：$LOCALKMS_FILE_PATH/
 * but, if $LOCALKMS_FILE_PATH cannot be found, we will try to find $GAUSSHOME
 */
static bool set_global_env_value()
{
    char *local_kms_path = NULL;
    char tmp_gausshome_buf[PATH_MAX] = {0};
    errno_t rc = 0;
    bool is_get_localkms_env = false;

    local_kms_path = get_env_value("LOCALKMS_FILE_PATH");
    if (local_kms_path == NULL || realpath(local_kms_path, g_env_value) == NULL) {
        /* fail to get LOCALKMS_FILE_PATH, then try to get GAUSSHOME */
        local_kms_path = get_env_value("GAUSSHOME");
        if (local_kms_path != NULL) {
            rc = sprintf_s(tmp_gausshome_buf, sizeof(tmp_gausshome_buf), "%s/%s", local_kms_path, "/etc/localkms");
            securec_check_ss_c(rc, "", "");

            if (realpath(tmp_gausshome_buf, g_env_value) != NULL) {
                is_get_localkms_env = true;
            }
        }
    } else {
        is_get_localkms_env = true;
    }

    if (!is_get_localkms_env) {
        printf("ERROR(CLIENT): failed to get environment value : %s.\n", "LOCALKMS_FILE_PATH");
        return false;
    }

    if (is_contain_danger_char(g_env_value)) {
        return false;
    }

    return true;
}

bool check_algo_type_kms(CmkAlgorithm algo_type)
{
    if (algo_type == CmkAlgorithm::RSA_2048) {
        return true;
    } else {
        printf("ERROR(CLIENT): Invalid algorithm, keys generated by localkms are only used for RSA_2048.\n");
        return false;
    }
}


KmsErrType check_file_exist(const char *real_file_path, CheckKeyFileType chk_type)
{
    bool is_file_exist = false;
    struct stat statbuf;

    is_file_exist = (lstat(real_file_path, &statbuf) < 0) ? false : true;
    if (chk_type == CREATE_KEY_FILE && is_file_exist) {
        printf("ERROR(CLIENT): cannot create file, the file '%s' already exists.\n", real_file_path);
        return KEY_FILES_EXIST;
    } else if (chk_type == READ_KEY_FILE && !is_file_exist) {
        printf("ERROR(CLIENT): cannot read file, failed to find file '%s'.\n", real_file_path);
        return KEY_FILES_NONEXIST;
    } 

    return SUCCEED;
}

#if ((!defined(ENABLE_MULTIPLE_NODES)) && (!defined(ENABLE_PRIVATEGAUSS)))
void localkms_post_process(CEQueryType qry_type, ExecStatusType backend_exec_ret, const char *query_args)
{
    RealCmkPath real_cmk_path = {0};
    KmsErrType err_type = FAILED;
    
    switch (qry_type) {
        case CE_CREATE_CMK:
            if (backend_exec_ret == PGRES_FATAL_ERROR) {
                err_type = get_and_check_real_key_path(query_args, &real_cmk_path, REMOVE_KEY_FILE);
                if (err_type != SUCCEED) {
                    handle_kms_err(err_type);
                    break;
                }
                rm_cmk_store_file(real_cmk_path);
            }
            break;
        case CE_DROP_CMK:
            if (backend_exec_ret == PGRES_TUPLES_OK || backend_exec_ret == PGRES_COMMAND_OK) {
                err_type = get_and_check_real_key_path(query_args, &real_cmk_path, REMOVE_KEY_FILE);
                if (err_type != SUCCEED) {
                    handle_kms_err(err_type);
                    break;
                }
                rm_cmk_store_file(real_cmk_path);
            }
            break;
        default:
            break;
    }
}
#endif

/* 
 * @function : check the legitimacy of the KEY_PATH and get the real key path of rsa key store file.
 *             for each cmk_path, we will check four file : $LOCALKMS_FILE_PATH/cmk_path.pub, cmk_path.pub.rand,
 *             cmk_path.priv and cmk_path.priv.rand.
 * @param cmk_path : KEY_PATH parsed from user input.
 * @param real_cmk_path : real path of KEY_PATH. real_path = {real_public_cmk_path, real_private_cmk_path}
 * @param chk_type : 
 *         (1) while creating new file (real_path), we should make sure real_path non-exist
 *         (2) while deleting existing file, we will not check weather it exists
 */
KmsErrType get_and_check_real_key_path(const char *cmk_path, RealCmkPath *real_cmk_path, CheckKeyFileType chk_type)
{
    error_t rc = 0;
    KmsErrType chk_file_ret = FAILED;
    char tmp_pub_rand_path[PATH_MAX] = {0};
    char tmp_priv_rand_path[PATH_MAX] = {0}; 

    if (strlen(cmk_path) < MIN_KEY_PATH_LEN) {
        return PATH_TOO_SHORT;
    } else if (strlen(cmk_path) > MAX_KEY_PATH_LEN) {
        return PATH_TOO_LONG;
    }

    if (is_contain_unsupport_char(cmk_path)) {
        return CONTAIN_INVALID_CHAR;
    }

    if (strlen(g_env_value) == 0) {
        if (!set_global_env_value()) {
            return FAILED;
        }
    }

    rc = sprintf_s(real_cmk_path->real_pub_cmk_path, PATH_MAX, "%s/%s.pub", g_env_value, cmk_path);
    securec_check_ss_c(rc, "", "");
    rc = sprintf_s(real_cmk_path->real_priv_cmk_path, PATH_MAX, "%s/%s.priv", g_env_value, cmk_path);
    securec_check_ss_c(rc, "", "");
    rc = sprintf_s(tmp_pub_rand_path, PATH_MAX, "%s.rand", real_cmk_path->real_pub_cmk_path);
    securec_check_ss_c(rc, "", "");
    rc = sprintf_s(tmp_priv_rand_path, PATH_MAX, "%s.rand", real_cmk_path->real_priv_cmk_path);
    securec_check_ss_c(rc, "", "");

    chk_file_ret = check_file_exist(real_cmk_path->real_pub_cmk_path, chk_type);
    if (chk_file_ret != SUCCEED) {
        return chk_file_ret;
    }
    chk_file_ret = check_file_exist(real_cmk_path->real_priv_cmk_path, chk_type);
    if (chk_file_ret != SUCCEED) {
        return chk_file_ret;
    }
    chk_file_ret = check_file_exist(tmp_pub_rand_path, chk_type);
    if (chk_file_ret != SUCCEED) {
        return chk_file_ret;
    }
    chk_file_ret = check_file_exist(tmp_priv_rand_path, chk_type);
    if (chk_file_ret != SUCCEED) {
        return chk_file_ret;
    }

    return SUCCEED;
}

static void rm_one_file(const char *real_path)
{
    if (remove(real_path) != 0) {
        printf("ERROR(CLIENT): failed to remove file '%s'\n", real_path);
    }
}

void rm_cmk_store_file(RealCmkPath real_cmk_path)
{
    errno_t rc = 0;
    
    rm_one_file(real_cmk_path.real_pub_cmk_path);
    rm_one_file(real_cmk_path.real_priv_cmk_path);

    /* having known the length of real_pub_cmk_path, we can reuse it to store the path of .rand file path */
    rc = strcat_s(real_cmk_path.real_pub_cmk_path, sizeof(real_cmk_path.real_pub_cmk_path), ".rand");
    securec_check_ss_c(rc, "", "");
    rc = strcat_s(real_cmk_path.real_priv_cmk_path, sizeof(real_cmk_path.real_priv_cmk_path), ".rand");
    securec_check_ss_c(rc, "", "");
    rm_one_file(real_cmk_path.real_pub_cmk_path);
    rm_one_file(real_cmk_path.real_priv_cmk_path);
}

/* 
 * if para:is_write_header == true, we will create a file header, and write the size of conent to header
 * after that, if trying to read all content from file, we will read header to calcule the size of content 
 * buffer before reading all content
 */
KmsErrType create_file_and_write(const char *real_path, const unsigned char *content, const size_t content_len,
    bool is_write_header)
{
    int fd = 0;
    char head[KEY_FILE_HEADER_LEN] = {0};
    errno_t rc = 0;

    fd = open(real_path, O_CREAT | O_RDWR, S_IRUSR | S_IWUSR);
    if (fd == -1) {
        printf("ERROR(CLIENT): failed to open file '%s'.\n", real_path);
        return OPEN_FILE_ERR;
    }

    if (is_write_header) {
        rc = sprintf_s(head, sizeof(head), "%lu", content_len);
        securec_check_ss_c(rc, "", "");
        write(fd, head, sizeof(head));
    }
    
    write(fd, content, content_len);
    close(fd);

    return SUCCEED;
}

/* the input file must contain a header which store the size value of file content */
KmsErrType read_content_from_file(const char *real_path, unsigned char *buf, const size_t buf_len, size_t *content_len)
{
    int fd = 0;
    char header[KEY_FILE_HEADER_LEN] = {0};

    fd = open(real_path, O_RDONLY, 0);
    if (fd < 0) {
        printf("ERROR(CLIENT): failed to open file '%s'.\n", real_path);
        return OPEN_FILE_ERR;
    }

    if (read(fd, header, sizeof(header)) < 0) {
        printf("ERROR(CLIENT): failed to read from file '%s'.\n", real_path);
        close(fd);
        return READ_FILE_ERR;
    }
    *content_len = atoi(header);

    if (*content_len > buf_len) {
        printf("ERROR(CLIENT): the header of file '%s' is invalid.\n", real_path);
        close(fd);
        return READ_FILE_ERR;
    }

    if (read(fd, buf, *content_len) < 0) {
        printf("ERROR(CLIENT): failed to read from file '%s'.\n", real_path);
        close(fd);
        return READ_FILE_ERR;
    }

    close(fd);
    return SUCCEED;
}

RsaKeyStr *generate_cmk_kms()
{
    BIGNUM *rsa_n_val = NULL;
    RSA *rsa = NULL;
    BIO *pub_key_biobuf = NULL;
    BIO *priv_key_biobuf = NULL;
    RsaKeyStr *rsa_str = NULL;
    unsigned char *pub_key = NULL;
    unsigned char *priv_key = NULL;
    size_t pub_key_len = 0;
    size_t priv_key_len = 0;

    /* generate rsa key */
    rsa_n_val = BN_new();
    if (BN_set_word(rsa_n_val, RSA_F4) != 1) { /* public exponent - 65537 */
        return NULL;
    }

    rsa = RSA_new();
    if (rsa == NULL) {
        BN_free(rsa_n_val);
        return NULL;
    }

    if (RSA_generate_key_ex(rsa, DEFAULT_RSA_KEY_LEN, rsa_n_val, NULL) != 1) {
        BN_free(rsa_n_val);
        RSA_free(rsa);
        return NULL;
    }
    BN_free(rsa_n_val);

    /* convert public key to BIO in PEM format */
    pub_key_biobuf = BIO_new(BIO_s_mem());
    if (pub_key_biobuf == NULL) {
        RSA_free(rsa);
        return NULL;
    }

    if (PEM_write_bio_RSA_PUBKEY(pub_key_biobuf, rsa) != 1) {
        RSA_free(rsa);
        BIO_free(pub_key_biobuf);
        return NULL;
    }

    /* convert private key to BIO in PEM format */
    priv_key_biobuf = BIO_new(BIO_s_mem());
    if (priv_key_biobuf == NULL) {
        RSA_free(rsa);
        BIO_free(pub_key_biobuf);
        return NULL;
    }

    if (PEM_write_bio_RSAPrivateKey(priv_key_biobuf, rsa, NULL, NULL, 0, NULL, NULL) != 1) {
        RSA_free(rsa);
        BIO_free(pub_key_biobuf);
        BIO_free(priv_key_biobuf);
        return NULL;
    }
    RSA_free(rsa);

    /* convert the BIO structures to strings (PEM format) */
    pub_key_len = BIO_pending(pub_key_biobuf);
    priv_key_len = BIO_pending(priv_key_biobuf);

    pub_key = (unsigned char *)malloc(pub_key_len);
    if (pub_key == NULL) {
        BIO_free(pub_key_biobuf);
        BIO_free(priv_key_biobuf);
        return NULL;
    }

    priv_key = (unsigned char *)malloc(priv_key_len);
    if (priv_key == NULL) {
        BIO_free(pub_key_biobuf);
        BIO_free(priv_key_biobuf);
        free_safely(pub_key);
        return NULL;
    }

    rsa_str = (RsaKeyStr *)malloc(sizeof(RsaKeyStr));
    if (rsa_str == NULL) {
        BIO_free(pub_key_biobuf);
        BIO_free(priv_key_biobuf);
        free_safely(pub_key);
        free_safely(priv_key);
        return NULL;
    }

    BIO_read(pub_key_biobuf, pub_key, pub_key_len);
    BIO_read(priv_key_biobuf, priv_key, priv_key_len);
    rsa_str->pub_key = pub_key;
    rsa_str->pub_key_len = pub_key_len;
    rsa_str->priv_key = priv_key;
    rsa_str->priv_key_len = priv_key_len;

    BIO_free(pub_key_biobuf);
    BIO_free(priv_key_biobuf);
    return rsa_str;
}

void free_rsa_str(RsaKeyStr *rsa_key_str)
{
    errno_t rc = 0;
    
    if (rsa_key_str == NULL) {
        return;
    }

    if (rsa_key_str->pub_key != NULL) {
        rc = memset_s(rsa_key_str->pub_key, rsa_key_str->pub_key_len, 0, rsa_key_str->pub_key_len);
        securec_check_c(rc, "", "");
        free_safely(rsa_key_str->pub_key);
    }

    if (rsa_key_str->priv_key != NULL) {
        rc = memset_s(rsa_key_str->priv_key, rsa_key_str->priv_key_len, 0, rsa_key_str->priv_key_len);
        securec_check_c(rc, "", "");
        free_safely(rsa_key_str->priv_key);
    }    
    
    free_safely(rsa_key_str);
}

/* 
 * for each cmk, we will create 2 file, one stores cmk cipher, another stores the key materials that
 * are used to derive a key to encrypt cmk plain.
 */
KmsErrType write_cmk_plain_kms(char *real_cmk_path, const size_t path_len, const unsigned char *cmk_plain,
    const size_t plain_len)
{
    unsigned char iv[KEY_METERIAL_LEN] = {0};
    unsigned char salt[KEY_METERIAL_LEN] = {0};
    unsigned char iv_salt_buf[sizeof(iv) + sizeof(salt)] = {0};
    unsigned char derived_key[DRIVED_KEY_LEN] = {0};
    unsigned char cmk_cipher[DEFAULT_RSA_KEY_LEN] = {0};
    int cipher_len = 0;
    errno_t rc = 0;
    KmsErrType ret = FAILED;

    if (RAND_priv_bytes(iv, sizeof(iv)) != 1) {
        return DERIVE_KEY_ERR;
    }

    if (RAND_priv_bytes(salt, sizeof(salt)) != 1) {
        return DERIVE_KEY_ERR;
    }
    
    if (PKCS5_PBKDF2_HMAC((const char *)iv, sizeof(iv), salt, sizeof(salt), ITERATE_ROUD, EVP_sha256(),
        sizeof(derived_key), derived_key) != 1) {
        return DERIVE_KEY_ERR;
    }

    /* encrypt cek with cmk */
    AeadAesHamcEncKey derived_aead_key = AeadAesHamcEncKey(derived_key, DRIVED_KEY_LEN);
    cipher_len = encrypt_data(cmk_plain, plain_len, derived_aead_key, EncryptionType::DETERMINISTIC_TYPE, cmk_cipher,
        AEAD_AES_256_CBC_HMAC_SHA256);
    if (cipher_len <= 0) {
        return ENC_CMK_ERR;
    }

    ret = create_file_and_write(real_cmk_path, cmk_cipher, (size_t)cipher_len, true);
    if (ret != SUCCEED) {
        return ret;
    }

    /* from now on, the real_cmk_math switchs to real_cmk_math.rand */
    rc = strcat_s(real_cmk_path, path_len, ".rand");
    securec_check_c(rc, "", "");

    for (size_t i = 0; i < sizeof(iv); i++) {
        iv_salt_buf[i] = iv[i];
    }
    for (size_t i = 0; i < sizeof(salt); i++) {
        iv_salt_buf[sizeof(iv) + i] = salt[i];
    }

    return create_file_and_write(real_cmk_path, iv_salt_buf, sizeof(iv_salt_buf), true);
}

KmsErrType read_iv_and_salt(const char *real_cmk_path, unsigned char *iv, const size_t iv_len, unsigned char *salt,
    const size_t salt_len)
{
    errno_t rc = 0;
    unsigned char iv_salt_buf[iv_len + salt_len] = {0};
    char real_rand_path[strlen(real_cmk_path) + strlen(".rand") + 1] = {0};
    size_t iv_salt_len = 0;
    KmsErrType ret = FAILED;

    rc = sprintf_s(real_rand_path, sizeof(real_rand_path), "%s.rand", real_cmk_path);
    securec_check_ss_c(rc, "", "");

    ret = read_content_from_file(real_rand_path, iv_salt_buf, sizeof(iv_salt_buf), &iv_salt_len);
    if (ret != SUCCEED) {
        return ret;
    } else if (iv_salt_len < sizeof(iv_salt_buf)) {
        return DERIVE_KEY_ERR;
    }

    for (size_t i = 0; i < iv_len; i++) {
        iv[i] = iv_salt_buf[i];
    }
    for (size_t i = 0; i < salt_len; i++) {
        salt[i] = iv_salt_buf[iv_len + i];
    }

    return SUCCEED;
}

KmsErrType read_cmk_plain_kms(const char *real_cmk_path, unsigned char *cmk_plain, size_t *plain_len)
{
    unsigned char iv[KEY_METERIAL_LEN] = {0};
    unsigned char salt[KEY_METERIAL_LEN] = {0};
    unsigned char derived_key[DRIVED_KEY_LEN] = {0};
    unsigned char cmk_cipher[DEFAULT_RSA_KEY_LEN] = {0};
    size_t cmk_cipher_len = 0;
    int tmp_plainlen = 0;
    KmsErrType ret = FAILED;

    ret = read_iv_and_salt(real_cmk_path, iv, sizeof(iv), salt, sizeof(salt));
    if (ret != SUCCEED) {
        return ret;
    }

    if (PKCS5_PBKDF2_HMAC((const char *)iv, sizeof(iv), salt, sizeof(salt), ITERATE_ROUD, EVP_sha256(),
        sizeof(derived_key), derived_key) != 1) {
        return DERIVE_KEY_ERR;
    }

    ret = read_content_from_file(real_cmk_path, cmk_cipher, sizeof(cmk_cipher), &cmk_cipher_len);
    if (ret != SUCCEED) {
        return ret;
    }

    /* decrypt cek ciher with cmk */
    AeadAesHamcEncKey derived_aead_key = AeadAesHamcEncKey(derived_key, DRIVED_KEY_LEN);
    tmp_plainlen = decrypt_data(cmk_cipher, cmk_cipher_len, derived_aead_key, cmk_plain, AEAD_AES_256_CBC_HMAC_SHA256);
    if (tmp_plainlen <= 0) {
        return DEC_CMK_ERR;
    }
    *plain_len = (size_t)tmp_plainlen;

    return SUCCEED;
}

KmsErrType encrypt_cek_use_ras2048(const unsigned char *cek_plain, const size_t plain_len, 
    const char *real_pub_cmk_path, const size_t path_len, unsigned char *cek_cipher, size_t &cipher_len)
{
    BIO *cmk_plain_bio = NULL;
    int bio_write_len = 0;
    RSA *pub_cmk = NULL;
    int enc_ret = 0;
    KmsErrType ret = FAILED;
    errno_t rc = 0;
    unsigned char cmk_plain[DEFAULT_RSA_KEY_LEN] = {0};
    size_t cmk_plain_len = 0;

    ret = read_cmk_plain_kms(real_pub_cmk_path, cmk_plain, &cmk_plain_len);
    if (ret != SUCCEED) {
        return ret;
    }
    cmk_plain[cmk_plain_len] = '\0';

    cmk_plain_bio = BIO_new(BIO_s_mem());
    if (cmk_plain_bio == NULL) {
        return HEAP_ERR;
    }

    bio_write_len = BIO_write(cmk_plain_bio, cmk_plain, cmk_plain_len);
    if (bio_write_len < 0) {
        printf("ERROR(CLIENT): failed to write rsa key to from BIO.\n");
        BIO_free(cmk_plain_bio);
        rc = memset_s(cmk_plain, sizeof(cmk_plain), 0, cmk_plain_len);
        securec_check_c(rc, "", "");
        return WRITE_FILE_ERR;
    }
    rc = memset_s(cmk_plain, sizeof(cmk_plain), 0, cmk_plain_len);
    securec_check_c(rc, "", "");

    pub_cmk = PEM_read_bio_RSA_PUBKEY(cmk_plain_bio, NULL, NULL, NULL);
    if (pub_cmk == NULL) {
        printf("ERROR(CLIENT): failed to read rsa key from BIO.\n");
        BIO_free(cmk_plain_bio);
        RSA_free(pub_cmk);
        return READ_FILE_ERR;
    }
    BIO_free(cmk_plain_bio);
    
    enc_ret = RSA_public_encrypt(plain_len, cek_plain, cek_cipher, pub_cmk, RSA_PKCS1_OAEP_PADDING);
    if (enc_ret == -1) {
        printf("ERROR(CLIENT): failed to encrypt column key with RSA 2048.\n");
        RSA_free(pub_cmk);
        return ENC_CEK_ERR;
    }

    RSA_free(pub_cmk);
    cipher_len = enc_ret;
    return SUCCEED;
}

KmsErrType decrypt_cek_use_rsa2048(const unsigned char *cek_cipher, const size_t cipher_len, 
    const char *real_priv_cmk_path, const size_t path_len, unsigned char *cek_plain, size_t *cek_plain_len)
{
    BIO *cmk_plain_bio = NULL;
    int bio_write_len = 0;
    RSA *priv_cmk = NULL;
    int dec_ret = 0;
    KmsErrType ret = FAILED;
    errno_t rc = 0;
    unsigned char cmk_plain[DEFAULT_RSA_KEY_LEN] = {0};
    size_t cmk_plain_len = 0;

    ret = read_cmk_plain_kms(real_priv_cmk_path, cmk_plain, &cmk_plain_len);
    if (ret != SUCCEED) {
        return ret;
    }

    cmk_plain_bio = BIO_new(BIO_s_mem());
    if (cmk_plain_bio == NULL) {
        return HEAP_ERR;
    }

    bio_write_len = BIO_write(cmk_plain_bio, cmk_plain, cmk_plain_len);
    if (bio_write_len < 0) {
        printf("ERROR(CLIENT): failed to write rsa key to BIO.\n");
        BIO_free(cmk_plain_bio);
        rc = memset_s(cmk_plain, sizeof(cmk_plain), 0, cmk_plain_len);
        securec_check_c(rc, "", "");
        return WRITE_FILE_ERR;
    }
    rc = memset_s(cmk_plain, sizeof(cmk_plain), 0, cmk_plain_len);
    securec_check_c(rc, "", "");

    priv_cmk = PEM_read_bio_RSAPrivateKey(cmk_plain_bio, NULL, NULL, NULL);
    if (priv_cmk == NULL) {
        printf("ERROR(CLIENT): failed to read rsa key from BIO.\n");
        BIO_free(cmk_plain_bio);
        RSA_free(priv_cmk);
        return OPEN_FILE_ERR;
    }
    BIO_free(cmk_plain_bio);

    dec_ret = RSA_private_decrypt(cipher_len, cek_cipher, cek_plain, priv_cmk, RSA_PKCS1_OAEP_PADDING);
    if (dec_ret == -1) {
        printf("ERROR(CLIENT): failed to decrypt column key with RSA 2048.\n");
        RSA_free(priv_cmk);
        return DEC_CEK_ERR;
    }

    RSA_free(priv_cmk);
    *cek_plain_len = dec_ret;
    return SUCCEED;
}

void handle_kms_err(KmsErrType err_type)
{
    switch (err_type) {
        case PATH_TOO_LONG:
            printf("ERROR(CLIENT): the key path length is too long.\n");
            break;
        case PATH_TOO_SHORT:
            printf("ERROR(CLIENT): the key path length is too short.\n");
            break;
        case DERIVE_KEY_ERR:
            printf("ERROR(CLIENT): failed to derive key to encrypt/decrypt client master key.\n");
            break;
        case HEAP_ERR:
            printf("ERROR(CLIENT): failed to malloc memory.\n");
        default:
            break;
    }
}