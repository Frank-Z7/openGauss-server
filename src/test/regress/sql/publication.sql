--
-- PUBLICATION
--
--- prepare
CREATE ROLE regress_publication_user LOGIN SYSADMIN PASSWORD 'Abcdef@123';
SET SESSION AUTHORIZATION 'regress_publication_user' PASSWORD 'Abcdef@123';
CREATE TABLE testpub_tbl1 (id int primary key, data text);
CREATE TABLE testpub_tbl2 (id int primary key, data text);
CREATE TABLE testpub_tbl3 (id int primary key, data text);
--- create publication
CREATE PUBLICATION testpub_default;
------ for all tables
CREATE PUBLICATION testpub_foralltables FOR ALL TABLES;
CREATE TABLE testpub_tbl4 (id int primary key, data text);
select pubname, tablename from pg_publication_tables where pubname='testpub_foralltables' AND tablename like 'testpub_%' order by tablename;
------ for only table testpub_tbl1
CREATE PUBLICATION testpub_only_tbl1 FOR TABLE ONLY testpub_tbl1;
select pubname, tablename from pg_publication_tables where pubname='testpub_only_tbl1';
-- fail - already added
CREATE PUBLICATION testpub_only_tbl1 FOR TABLE testpub_tbl1;
------ publish multi tables
CREATE PUBLICATION testpub_multitbls FOR TABLE testpub_tbl2, testpub_tbl3;
select pubname, tablename from pg_publication_tables where pubname='testpub_multitbls' order by tablename;
------ only insert
CREATE PUBLICATION testpub_only_insert with (publish='insert');
select pubname, puballtables, pubinsert, pubupdate, pubdelete from pg_publication where pubname='testpub_only_insert';
-- fail - view
CREATE VIEW testpub_view AS SELECT 1;
CREATE PUBLICATION testpub_pubview FOR TABLE testpub_view;
------ cascade
------ CREATE PUBLICATION testpub_cascade_tbl1 FOR TABLE testpub_tbl1 *;
------ CREATE TABLE testpub_tbl1cas (num int, id int REFERENCES testpub_tbl1(id));
------ select relname from pg_class where oid in (select pg_get_publication_tables('testpub_cascade_tbl1'));
------ select pubname, tablename from pg_publication_tables where pubname='testpub_cascade_tbl1';
--- alter publication
------ add table
ALTER PUBLICATION testpub_default ADD TABLE testpub_tbl1;
select pubname, tablename from pg_publication_tables where pubname='testpub_default';
-- fail - already added
ALTER PUBLICATION testpub_only_tbl1 ADD TABLE testpub_tbl1;
------ set table
ALTER PUBLICATION testpub_default SET TABLE testpub_tbl2;
select pubname, tablename from pg_publication_tables where pubname='testpub_default';
------ drop table
ALTER PUBLICATION testpub_multitbls DROP TABLE ONLY testpub_tbl2;
select pubname, tablename from pg_publication_tables where pubname='testpub_multitbls';
------ SET (parameter xxx)
ALTER PUBLICATION testpub_default SET (publish='insert, delete');
SELECT pubname, puballtables, pubinsert, pubupdate, pubdelete FROM pg_publication WHERE pubname='testpub_default';
-- fail - can't add to for all tables publication
ALTER PUBLICATION testpub_foralltables ADD TABLE testpub_tbl2;
-- fail - can't drop from all tables publication
ALTER PUBLICATION testpub_foralltables DROP TABLE testpub_tbl2;
-- fail - can't add to for all tables publication
ALTER PUBLICATION testpub_foralltables SET TABLE pub_test.testpub_nopk;
--- drop testpub_tbl1
DROP TABLE testpub_tbl1;
select pubname, tablename from pg_publication_tables where tablename='testpub_tbl1';
--- drop publication
DROP PUBLICATION testpub_foralltables;
select * from pg_publication where pubname='testpub_foralltables';
DROP PUBLICATION IF EXISTS testpub_nonexists;
--- clean
DROP TABLE testpub_tbl2;
DROP TABLE testpub_tbl3;
DROP TABLE testpub_tbl4;
DROP VIEW testpub_view;
DROP PUBLICATION IF EXISTS testpub_default;
DROP PUBLICATION IF EXISTS testpub_only_tbl1;
DROP PUBLICATION IF EXISTS testpub_only_insert;
DROP PUBLICATION IF EXISTS testpub_multitbls;
--- DROP PUBLICATION IF EXISTS testpub_cascade_tbl1;
RESET SESSION AUTHORIZATION;
DROP ROLE regress_publication_user;
--- permission
CREATE ROLE normal_user LOGIN PASSWORD 'Abcdef@123';
SET SESSION AUTHORIZATION 'normal_user' PASSWORD 'Abcdef@123';
--- fail permission denied
create publication p1;
RESET SESSION AUTHORIZATION;
DROP ROLE normal_user;