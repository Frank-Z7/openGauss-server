create table fulljoin_test(w_zip text);

create table fulljoin_test2(w_name varchar(20),w_tax int,w_street_2 varchar(50));

create table fulljoin_test3(d_id int);

create table fulljoin_test4(w_id int,w_ytd numeric(6,2));

SELECT
    fulljoin_test3.d_id
FROM
(
    SELECT
        alias2.w_name alias6 ,
        alias2.w_tax alias7,
        MOD(fulljoin_test4.w_id,
        fulljoin_test4.w_ytd + 10) alias8
    FROM
        fulljoin_test alias1
    FULL JOIN fulljoin_test2 alias2 ON
        alias1.w_zip = alias2.w_street_2,
        fulljoin_test4)alias9
FULL JOIN fulljoin_test3 ON
    alias9.alias7 != fulljoin_test3.d_id
WHERE
    alias9.alias8 = 2
    OR alias9.alias7 = 2;

drop table fulljoin_test;

drop table fulljoin_test2;

drop table fulljoin_test3;

drop table fulljoin_test4;
