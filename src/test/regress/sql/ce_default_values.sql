\! gs_ktool -d all
\! gs_ktool -g

DROP CLIENT MASTER KEY IF EXISTS defaultcmk CASCADE;
CREATE CLIENT MASTER KEY defaultcmk WITH ( KEY_STORE = gs_ktool , KEY_PATH = "gs_ktool/1" , ALGORITHM = AES_256_CBC);
CREATE COLUMN ENCRYPTION KEY defaultcek WITH VALUES (CLIENT_MASTER_KEY = defaultcmk, ALGORITHM = AEAD_AES_256_CBC_HMAC_SHA256);

CREATE TABLE products (
    product_no integer DEFAULT 1,
    name text ENCRYPTED WITH (COLUMN_ENCRYPTION_KEY = defaultcek, ENCRYPTION_TYPE = DETERMINISTIC) DEFAULT 'Test Product',
    title varchar(35) ENCRYPTED WITH (COLUMN_ENCRYPTION_KEY = defaultcek, ENCRYPTION_TYPE = DETERMINISTIC) NOT NULL DEFAULT ' ',
    value varchar(35) ENCRYPTED WITH (COLUMN_ENCRYPTION_KEY = defaultcek, ENCRYPTION_TYPE = DETERMINISTIC) DEFAULT '',
    price numeric ENCRYPTED WITH (COLUMN_ENCRYPTION_KEY = defaultcek, ENCRYPTION_TYPE = DETERMINISTIC) DEFAULT 9.99,
    max_price decimal(6,0) ENCRYPTED WITH (COLUMN_ENCRYPTION_KEY = defaultcek, ENCRYPTION_TYPE = DETERMINISTIC) DEFAULT NULL
);
INSERT INTO products (name) VALUES ('Test2');
INSERT INTO products (price) VALUES (34);
INSERT INTO products (name) VALUES (DEFAULT);
INSERT INTO products (price) VALUES (DEFAULT);
INSERT INTO products (name, price) VALUES (DEFAULT, DEFAULT);
INSERT INTO products DEFAULT VALUES;

SELECT * FROM products;
ALTER TABLE products ALTER COLUMN price SET DEFAULT 7.77;
INSERT INTO products DEFAULT VALUES;
SELECT * FROM products;

ALTER TABLE products ALTER COLUMN price DROP DEFAULT;
INSERT INTO products DEFAULT VALUES;
SELECT * FROM products;


DROP TABLE products;
DROP CLIENT MASTER KEY defaultcmk CASCADE;

\! gs_ktool -d all