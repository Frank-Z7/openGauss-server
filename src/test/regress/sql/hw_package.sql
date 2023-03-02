drop schema if exists dams_ci;
drop trigger if exists insert_trigger on test_trigger_src_tbl;
drop table if exists test_trigger_des_tbl;
drop table if exists test_trigger_src_tbl;
drop package if exists trigger_test;
drop table if exists dams_ci.test1;
drop table if exists dams_ci.DB_LOG;
drop table if exists au_pkg;
drop schema test1;
drop schema test2;
drop schema if exists test cascade;
create schema test;
create table au_pkg(id int,name varchar);
create schema dams_ci;
create table test_trigger_src_tbl(id1 int, id2 int, id3 int);
create table test_trigger_des_tbl(id1 int, id2 int, id3 int);
create table test_package1(col1 int);
insert into test_package1 values(50);
create table dams_ci.test1(col1 int);
create schema pkgschema1;
create schema pkgschema2;
set behavior_compat_options='allow_procedure_compile_check';

drop package if exists exp_pkg;
create or replace package aa
is
procedure a(col1 int,col2 in int);
procedure a(col1 int,col2 in int,col3 out int);
end aa;
/
create or replace package exp_pkg as
  user_exp EXCEPTION;
end exp_pkg;
/

create or replace package body exp_pkg as
end exp_pkg;
/

create or replace function func1(param int) return number 
as
declare
a exception;
begin
  if (param = 1) then
    raise exp_pkg.user_exp;
  end if;
  raise info 'number is %', param;
  exception
    when exp_pkg.user_exp then
      raise info 'user_exp raise';
  return 0;
end;
/
select func1(1); --user_exp raise

CREATE TABLE dams_ci.DB_LOG
(ID VARCHAR(20),
PROC_NAME VARCHAR(100),
INFO VARCHAR(4000),
LOG_LEVEL VARCHAR(10),
TIME_STAMP VARCHAR(23),
ERROR_BACKTRACE VARCHAR(4000),
ERR_STACK VARCHAR(4000),
STEP_NO VARCHAR(20),
LOG_DATE VARCHAR(8)
);

CREATE OR REPLACE PACKAGE dams_ci.pack_log AS
  PROCEDURE excption_1(in_desc IN db_log.id%TYPE,
                     in_info IN db_log.info%TYPE);
END pack_log;
/
CREATE OR REPLACE PACKAGE DAMS_CI.UT_P_PCKG_DAMS_DEPT_ISSUE AUTHID CURRENT_USER
IS
PROCEDURE proc_get_appinfo2();
END UT_P_PCKG_DAMS_DEPT_ISSUE ;
/

CREATE OR REPLACE PACKAGE "dams_ci"."ctp_mx_pckg_init" AS
  type ref_cursor IS ref CURSOR;
  PROCEDURE proc_get_appinfo1(appinfo OUT ref_cursor);
END ctp_mx_pckg_init;
/

create or replace package trigger_test as
  function tri_insert_func() return trigger;
end trigger_test;
/

create or replace package body trigger_test as
  function tri_insert_func() return trigger as
    begin
        insert into test_trigger_des_tbl values(new.id1, new.id2, new.id3);
        return new;
    end;
end trigger_test;
/

create trigger insert_trigger
    before insert on test_trigger_src_tbl
    for each row
    execute procedure trigger_test.tri_insert_func(); --不支持触发器调用package函数

insert into test_trigger_src_tbl values(1,1,1);

create or replace package dams_ci as
    procedure proc();
end dams_ci;
/

insert into test_trigger_src_tbl values(1,1,1);

create schema dams_ci;
create or replace package dams_ci.emp_bonus13 is
var5 int:=42;
var6 int:=43;
procedure testpro1();
end emp_bonus13;
/
create or replace package body dams_ci.emp_bonus13 is
var1 int:=46;
var2 int:=47;
procedure testpro1()
is
a int:=48;
b int:=49;
begin
insert into test_package1 values(50);
commit;
end;
procedure testpro2()
is
a int:=48;
b int:=49;
begin
insert into test_package1 values(50);
commit;
end;
begin
testpro1(56);
insert into test_package1 values(var5);
end emp_bonus13;
/

create or replace package dams_ci.emp_bonus13 is
var5 int:=42;
var6 int:=43;
procedure testpro1();
end emp_bonus13;
/
create or replace package body dams_ci.emp_bonus13 is
var1 int:=46;
var2 int:=47;
procedure testpro1()
is
a int:=48;
b int:=49;
begin
insert into test1 values(50);
commit;
end;
begin
testpro1(56);
end emp_bonus13;
/

drop package body dams_ci.emp_bonus13;
select pkgname,pkgspecsrc,pkgbodydeclsrc from gs_package where pkgname='emp_bonus13';

create or replace package feature_cross_test as
--111
   data1 int; --全局变量
   data2 int; --全局变量
   function func3(a int --函数入参注释
)return number; --公有函数
   procedure proc3(a int /*存储过程入参注释*/);
end feature_cross_test;
/
create or replace package body feature_cross_test as
/*********************************
包体头部注释快 end
**********************************/
   function func3(a int --函数入参注释 end
   )return number is
--函数头部注释
   begin
      data1 := 1;
      data2 := 2;
      insert into t1 values(data1);
      insert into t1 values(data2);
      return 0;
   end;
   procedure proc3(a int /*存储过程入参注释 end*/) is
/***********
存储过程头部注释 end
***********/
   begin
     insert into t1 values (1000);
     commit;
     insert into t1 values (2000);
     rollback;
   end;
end feature_cross_test; --包定义结束
/

create or replace package autonomous_pkg_150_1 IS
  count int := 1;
  function autonomous_f_150_1(num1 int) return int;
end autonomous_pkg_150_1;
/

create or replace package body autonomous_pkg_150_1 as
  autonomous_1 int :=10;
  autonomous_count int :=1;
function autonomous_f_150_1(num1 int) return int
  is
  re_int int;
  begin
  re_int:=autonomous_1;
  insert into au_pkg values(count,'autonomous_f_150_1_public_count');
  insert into au_pkg values(autonomous_count,'autonomous_f_150_1_count');
  count:=count+1;
  autonomous_count:=autonomous_count+1;
  return re_int+num1;
  end;
function autonomous_f_150_1_private(pnum1 int) return int
  is
  re_int int;
  begin
  re_int:=autonomous_1;
  insert into au_pkg values(count,'autonomous_f_150_1_private_public_count');
  insert into au_pkg values(autonomous_count,'autonomous_f_150_1_private_private_count');
  count:=count+1;
  autonomous_count:=autonomous_count+1;
  return re_int+pnum1;
  end;
end autonomous_pkg_150_1;
/

begin
    perform autonomous_pkg_150_1.autonomous_f_150_2_out(3);
end;
/
drop function if exists func1;
create or replace package exp_pkg1 as
  user_exp EXCEPTION;
  function func1(param int) return number;
end exp_pkg1;
/

create or replace package body exp_pkg1 as
  function func1(param int) return number as
  begin
    if (param = 1) then
      raise user_exp;
    end if;
    raise info 'number is %', param;
    exception
      when user_exp then
        raise info 'user_exp raise';
    return 0;
  end;
end exp_pkg1;
/
select exp_pkg1.func1(1);

create or replace package transaction_test as
  data1 character(20) := 'global data1';
  data2 character(20) := 'global data2';
  function func(data1 int, data2 int, data1 int) return number;
end transaction_test;
/

create or replace package transaction_test as
  data1 character(20) := 'global data1';
  data2 character(20) := 'global data2';
end transaction_test;
/

create or replace package body transaction_test as
  data1 character(20) := 'global data1';
  data2 character(20) := 'global data2';
end transaction_test;
/

drop package transaction_test;


drop package if exists exp_pkg1;
drop package autonomous_pkg_150_1;
\sf feature_cross_test.func3
\sf func1
select pkgspecsrc,pkgbodydeclsrc from gs_package where pkgname='feature_cross_test';

create or replace package autonomous_pkg_150 IS
  count int:=1;
  PROCEDURE autonomous_p_150(num4 int);
end autonomous_pkg_150;
/


CREATE OR REPLACE PACKAGE BODY autonomous_pkg_150 as
  autonomous_1 int:=10;
  autonomous_count int:=1;
  PROCEDURE autonomous_p_150(num4 int)
IS
PRAGMA AUTONOMOUS_TRANSACTION;
re_int INT;
BEGIN
  re_int:=autonomous_1;
  autonomous_count:=autonomous_count+1;
  select count(*)) into re_int from test_package1; 
  insert into test_package1 values(autonomous_count);
  commit;
END;
END autonomous_pkg_150;
/

CREATE OR REPLACE PACKAGE BODY autonomous_pkg_150 as
  autonomous_1 int:=10;
  autonomous_count int:=1;
  PROCEDURE autonomous_p_150(num4 int)
IS
PRAGMA AUTONOMOUS_TRANSACTION;
re_int INT;
BEGIN
  re_int:=autonomous_1;
  autonomous_count:=autonomous_count+1;
  select count(*) into re_int from test_package1; 
  insert into test_package1 values(autonomous_count);
  commit;
END;
END autonomous_pkg_150;
/



create or replace package autonomous_pkg_150_1 IS
  count int := 1;
  function autonomous_f_150_1(num1 int) return int;
end autonomous_pkg_150_1;
/

create or replace package body autonomous_pkg_150_1 as
  autonomous_1 int :=10;
  autonomous_count int :=1;
procedure autonomous_f_150_1_private(pnum1 int)
  is
  declare PRAGMA AUTONOMOUS_TRANSACTION;
  begin
  end;
function autonomous_f_150_1(num1 int) return int
  is
  declare PRAGMA AUTONOMOUS_TRANSACTION;
  re_int int;
  begin
  autonomous_f_150_1_private(1);
  return 1;
  end;
end autonomous_pkg_150_1;
/

select autonomous_pkg_150_1.autonomous_f_150_1(1);


create or replace package autonomous_pkg_150_2 IS
  count int := 1;
  function autonomous_f_150_2(num1 int) return int;
end autonomous_pkg_150_2;
/


create or replace package body autonomous_pkg_150_2 as
  autonomous_1 int :=10;
  autonomous_count int :=1;
function autonomous_f_150_2(num1 int) return int
  is
  declare PRAGMA AUTONOMOUS_TRANSACTION;
  re_int int;
  begin
  return 2;
  end;
function autonomous_f_150_2_private(pnum1 int) return int
  is
  declare PRAGMA AUTONOMOUS_TRANSACTION;
  re_int int;
  begin
  autonomous_pkg_150_1.autonomous_f_150_1_private(1);
  return 2;
  end;
end autonomous_pkg_150_2;
/

select autonomous_pkg_150_2.autonomous_f_150_2_private(1);

drop table if exists au_pkg;
create table au_pkg(id int,name varchar);
create or replace package autonomous_pkg_150_1 IS
  count int := 1;
  function autonomous_f_150_1(num1 int) return int;
end autonomous_pkg_150_1;
/

create or replace package body autonomous_pkg_150_1 as
  autonomous_1 int :=10;
  autonomous_count int :=1;
function autonomous_f_150_1(num1 int) return int
  is
  declare PRAGMA AUTONOMOUS_TRANSACTION;
  re_int int;
  begin
  re_int:=autonomous_1;
  insert into au_pkg values(count,'autonomous_f_150_1_public_count');
  insert into au_pkg values(autonomous_count,'autonomous_f_150_1_count');
  count:=count+1;
  autonomous_count:=autonomous_count+1;
  return re_int+num1;
  end;
function autonomous_f_150_1_private(pnum1 int) return int
  is
  declare PRAGMA AUTONOMOUS_TRANSACTION;
  re_int int;
  begin
  re_int:=autonomous_1;
  insert into au_pkg values(count,'autonomous_f_150_1_private_public_count');
  insert into au_pkg values(autonomous_count,'autonomous_f_150_1_private_private_count');
  count:=count+1;
  autonomous_count:=autonomous_count+1;
  return re_int+pnum1;
  end;
begin
perform autonomous_f_150_1(autonomous_f_150_1_private(1));
perform autonomous_f_150_1_private((select autonomous_f_150_1(2)));
end autonomous_pkg_150_1;
/

declare
begin
perform autonomous_pkg_150_1.autonomous_f_150_1(2);
end;
/

create or replace package pack_log
is
ab varchar2(10)='asdf';
bb int = 11;
procedure p1(a varchar2(10));
procedure p2();
end pack_log;
/
 
 
create or replace package body pack_log
is
procedure p1(a varchar2(10))
is
begin
null;
end;
procedure p2()
is
begin
null;
end;
end pack_log;
/

declare
ab varchar2(10):='11';
BEGIN
pack_log.p1(pack_log.ab || '11');
insert into test_package1 values(pack_log.bb);
END;
/

CREATE OR REPLACE PACKAGE CTP_MX_PCKG_INIT AS

  type ref_cursor IS ref CURSOR;
  --rcuror ref_cursor;

  PROCEDURE proc_get_appinfo(appinfo OUT ref_cursor);

  PROCEDURE proc_get_servinfo(appname IN varchar2, servinfo OUT ref_cursor);
  --end proc_get_servinfo;

  PROCEDURE proc_get_monitor_switch(appname IN varchar2,
                                    switchinfo OUT ref_cursor);
  --end proc_get_monitor_switch;

  PROCEDURE proc_get_useablity_info(checkers OUT ref_cursor);
  --end proc_get_useablity_info;

  PROCEDURE proc_get_trade_define(trades OUT ref_cursor);
  --end proc_get_trade_define;

  PROCEDURE proc_get_resource_define(resources OUT ref_cursor);
  --end proc_get_resource_define;
  PROCEDURE proc_get_trade_info(tradeRef OUT ref_cursor);

  PROCEDURE proc_get_resource_info(resourceRef OUT ref_cursor);
END CTP_MX_PCKG_INIT;
/
reset session AUTHORIZATION;
create or replace package cnt as
end cnt;
/


create user hwpackage password 'huawei@123';
set session AUTHORIZATION hwpacakge PASSWORD 'huawei@123';
reset session AUTHORIZATION;


create or replace package commit_rollback_test as
  function exec_func3() return int;
  procedure exec_func4(add_num in int);
end commit_rollback_test;
/
create or replace package body commit_rollback_test as
  function exec_func3() return int as
  ret_num int;
  begin
    ret_num := 1+1;
    commit;
    return ret_num;
  end;

  procedure exec_func4(add_num in int)
  as
    sum_num int;
  begin
    sum_num := add_num + exec_func3();
    commit;
  end;
end commit_rollback_test;
/

call commit_rollback_test.exec_func4(1);

create or replace package multi_sql as
function func5() return int;
function func16() return int;
end multi_sql;
/

create or replace package body multi_sql as
function func5() return int as
begin
  return (data5);
end;

function func16() return int as
begin
  alter function func5() rename to func25;
  return 0;
end;
end multi_sql;
/

create or replace package cnt as
  c1 sys_refcursor;
end cnt;
/
select multi_sql.func16();


create or replace package aa
is
type students is varray(5) of int;
procedure kk();
end aa;
/

create or replace package body aa
is
names students;
procedure kk 
is
begin
    names := students(1, 2, 3, 4, 5); -- should be able read all values correctly --
    for i in 1 .. 5 loop
        insert into test_package1 values(names(i));
    end loop;
end;
end aa;
/

call aa.kk();

CREATE OR REPLACE PACKAGE dams_ci.emp_bonus10 AS
da int:=4;
qq int:=3;
PROCEDURE asb();
END emp_bonus10;
/

CREATE OR REPLACE PACKAGE BODY dams_ci.emp_bonus10 IS
dd int:=2;
dsadd int:=3;  
cursor c1 is select * from t1;
PROCEDURE asb()
IS
BEGIN
insert into test_package1 values(100);
rollback;
END;
PROCEDURE bb(kk  int,gg int)
IS
BEGIN
insert into test1 values(da);
insert into test1 values(dd);
asb();
commit;
END;     
BEGIN
insert into test1 values(qq);
insert into test1 values(da);
END emp_bonus10;
/
                                              
CREATE OR REPLACE PACKAGE dams_ci.emp_bonus11 AS
da int:=4;
qq int:=3;
PROCEDURE asb();
END emp_bonus11;
/

CREATE OR REPLACE PACKAGE BODY dams_ci.emp_bonus11 IS
dd int:=2;
dsadd int:=3;  
cursor c1 is select * from t1;
PROCEDURE asb()
IS
BEGIN
insert into test_package1 values(100);
dams_ci.emp_bonus10.asb;
END;
PROCEDURE bb(kk  int,gg int)
IS
BEGIN
insert into test_package1 values(da);
insert into test_package1 values(dd);
asb();
commit;
END;     
BEGIN
insert into dams_ci.test1 values(qq);
insert into dams_ci.test1 values(da);
END emp_bonus11;
/

select definer_current_user()::int;
call multi_sql.func16();

create or replace package pkgschema1.aa
is
a int:=1;
end aa;
/

create or replace package body pkgschema1.aa
is
b int:=2;
end aa;
/

create or replace package pkgschema2.aa
is
a int:=test1.aa.a;
end aa;
/

create or replace package aa
is
a int:=1;
end aa;
/

create or replace package body aa
is
b int:=2;
end aa;
/

begin
insert into test_package1 values(pkgschema1.aa.a);
end;
/


create or replace package pkg10
is 
a int:=2;
end pkg10;
/
create or replace package body pkg10
is 
end pkg10;
/

create or replace package pkg11
is
c int:=pkg10.a;
end pkg11;
/

create or replace package test1
is
procedure proc_a(a in varchar2,
                in_area_code in varchar2,
                out_flag out varchar2,
                out_message out varchar2);
procedure proc_b(a in varchar2,
                in_area_code in varchar2,
                out_flag out varchar2,
                out_message out varchar2);
end test1;
/

create or replace package body test1
is
procedure proc_a(a in varchar2,
                in_area_code in varchar2,
                out_flag out varchar2,
                out_message out varchar2)
is
begin
    for rec in (select 1) loop
        begin
            test1.a:=case when 1>2 then 1 else 1 end;
            test1.a:=case when 1>2 then 1 else 1 end;
        end;
    end loop;
end;
procedure proc_b(a in varchar2,
                in_area_code in varchar2,
                out_flag out varchar2,
                out_message out varchar2)
is
begin
    for rec in (select 1) loop
        begin
            begin
            end;
            BEGIN 
            END;
        end;
    end loop;
end;
end test1;
/

create or replace package pack_test_a
is
v_a varchar2;
type t_1 is table of varchar2;
v_t t_1;
type rec_1 is record(col1 int);
v_rec rec_1;
procedure proc_test1(i_col1 in varchar2);
end pack_test_a;
/

create or replace package body pack_test_a
is
procedure proc_test1(i_col1 in varchar2)
is
cursor c1 is select * from test_package1;
begin
open c1;
loop
fetch c1 into v_rec;
exit when c1%notfound;
--v_t(v_idx):=v_rec.col1;
end loop;
insert into test_package1 values(v_rec.col1);
end;
end pack_test_a;
/
call pack_test_a.proc_test1('a');
select * from test_package1;

create or replace package test_cursor 
is
cursor test_cur(v1 varchar2)
is
select 1 from dual where 1=v1;
procedure proc_test;
end test_cursor;
/

--test:array with subscipt for out param
create or replace package PCKG_EXCHANGE_RATE as
procedure rate_exchange(i out NUMBER, j in varchar2);
end PCKG_EXCHANGE_RATE;
/
create or replace package body PCKG_EXCHANGE_RATE as
procedure rate_exchange(i out NUMBER, j in varchar2) as
begin
NULL;
end;
end PCKG_EXCHANGE_RATE;
/

create or replace package pckg_test as
procedure proc_test(i_col1 in varchar2);
end pckg_test;
/
create or replace package body pckg_test as
procedure proc_test(i_col1 in varchar2) as
type t_huilv is varray(10)of NUMBER;
t_hl t_huilv;
v_curr varchar2;
begin
PCKG_EXCHANGE_RATE.rate_exchange(t_hl(v_curr), v_curr);
end;
end pckg_test;
/
DROP PACKAGE pckg_test;
DROP PACKAGE PCKG_EXCHANGE_RATE;

--test: overloaded function with array param
create or replace package PCKG_EXCHANGE_RATE as
procedure rate_exchange(j INOUT varchar2, i INOUT NUMBER);
procedure rate_exchange(j OUT int, i INOUT NUMBER);
procedure rate_exchange(j OUT varchar2, i OUT varchar);
end PCKG_EXCHANGE_RATE;
/
create or replace package body PCKG_EXCHANGE_RATE as
procedure rate_exchange(j INOUT varchar2, i INOUT NUMBER) as
begin
NULL;
end;

procedure rate_exchange(j OUT int, i INOUT NUMBER) as
begin
NULL;
end;

procedure rate_exchange(j OUT varchar2, i OUT varchar) as
begin
NULL;
end;

end PCKG_EXCHANGE_RATE;
/

create or replace package pckg_test as
procedure proc_test(i_col2 in varchar2, i_col1 in varchar2);
end pckg_test;
/
create or replace package body pckg_test as
procedure proc_test(i_col2 in varchar2, i_col1 in varchar2) as
type t_huilv is table of NUMBER index by varchar2(10);
t_hl t_huilv;
v_curr varchar2;
begin
PCKG_EXCHANGE_RATE.rate_exchange( t_hl(v_curr),v_curr);
end;
end pckg_test;
/
DROP PACKAGE pckg_test;
DROP PACKAGE PCKG_EXCHANGE_RATE;

--test: array as INOUT param for function
create or replace package PCKG_EXCHANGE_RATE as
procedure rate_exchange(j INOUT varchar2, i INOUT NUMBER);
end PCKG_EXCHANGE_RATE;
/
create or replace package body PCKG_EXCHANGE_RATE as
procedure rate_exchange(j INOUT varchar2, i INOUT NUMBER) as
begin
NULL;
end;
end PCKG_EXCHANGE_RATE;
/

create or replace package pckg_test as
procedure proc_test(i_col2 in varchar2, i_col1 in varchar2);
end pckg_test;
/
create or replace package body pckg_test as
procedure proc_test(i_col2 in varchar2, i_col1 in varchar2) as
type t_huilv is table of NUMBER index by varchar2(10);
t_hl t_huilv;
v_curr varchar2;
begin
PCKG_EXCHANGE_RATE.rate_exchange( t_hl(v_curr),v_curr);
end;
end pckg_test;
/

create or replace package pck1 is
type r1 is record (a int, b int);
va r1;
end pck1;
/

create or replace package pck2 is
--vb pck1.va%TYPE;
procedure p1;
end pck2;
/
create or replace package body pck2  is
procedure p1 as 
begin
pck1.va := (1,2);
raise info '%', pck1.va;
end;
end pck2;
/

call pck2.p1();
create or replace package pckg_test
is
v_a varchar2:=1;
function proc_test(i_col1 in varchar2) return sys_refcursor;
end pckg_test;
/

create or replace package body pckg_test
is 
function proc_test(i_col1 in varchar2) return sys_refcursor
is
v_t tb_test;
o_list sys_refcursor;
begin
for rec in (select col1,col2 from tb_test where col1<i_col1) loop
insert into tb_test values(rec.col1,rec.col2);
end loop;
open o_list for select count(*) from tb_test;
return o_list;
end;
end pckg_test;
/

select * from pckg_test.proc_test(2);

DROP PACKAGE pckg_test;
DROP PACKAGE PCKG_EXCHANGE_RATE;


drop table if exists tb_test;
drop synonym if exists tb_test;
create table tb_test(col1 int,col2 int,col3 int);
create or replace package pckg_test1 as
procedure pr_test(i_col1 in varchar2,o_ret inout varchar2,o_ret1 out varchar2);
procedure pr_test1(i_col1 in varchar2);
end pckg_test1;
/
create or replace package body pckg_test1 as
procedure pr_test(i_col1 in varchar2,o_ret inout varchar2,o_ret1 out varchar2)as
begin
raise info '%', i_col1;
raise info '%', o_ret;
raise info '%', o_ret1;
o_ret:=0;
o_ret1:=0;
end;
procedure pr_test1(i_col1 in varchar2)as
begin
for rec in (select col1,col2,col3 from tb_test) loop
pr_test(rec.col1,rec.col2,rec.col3);
end loop;
end;
end pckg_test1;
/

create or replace package pck1 is
procedure pp1(a in varchar2 default 'no value');
procedure pp2;
end pck1;
/

create or replace package body pck1 is
procedure pp1(a in varchar2 default 'no value') is
begin
raise notice 'a:%', a;
end;
procedure pp2 is
begin
pck1.pp1;
pck1.pp1();
pck1.pp1('assign value');
end;
end pck1;
/

call pck1.pp2();

create table test2(col1 int);
create or replace package test1
is
col1 int;
end test1;
/

create or replace package body test1
is
end test1;
/

create or replace  package test2
is
procedure b;
end test2;
/
create or replace package body test2
is
cursor c1 is select * from test2 where col1=test1.col1;
procedure b
is
begin
null;
end;
end test2;
/ 

--call pckg_test1.pr_test1('a');
create or replace package pck20 is
procedure read_proc1(a int);
procedure read_proc1;
end pck20;
/

create or replace package body pck20 is
procedure read_proc1(a int) is
begin
read_proc1();
raise info 'bb';
end;
procedure read_proc1 is
begin
raise info 'aa';
end;
end pck20;
/

call pck20.read_proc1(1);

create or replace procedure read_pro1
 is
 begin
    raise info 'aa';
end;
/

create or replace procedure read_pro2
 is
 begin
    read_pro1;
end;
/

call read_pro2();

--test anoymous block
declare
my_var VARCHAR2(30);
begin transaction;
begin
my_var :='world';
dbe_output.print_line('hello'||my_var);
end;
/

create or replace package pck1 is
type r0 is record (a int, b int);
type r1 is ref cursor;
procedure p1(a out r1);
end pck1;
/

create or replace package body pck1 is
procedure p1(a out r1) is
begin
open a for select * from test_package1;
end;
end pck1;
/

select pck1.p1();

create or replace package pckg_test1
is
procedure proc_test1(a int) immutable;
end pckg_test1;
/

create or replace package body pckg_test1
is
procedure proc_test1(a int)
is
begin
null;
end;
end pckg_test1;
/

drop procedure read_pro1();
drop procedure read_pro2();

drop table tb_test;
drop package pckg_test1;
drop package test1.aa;
drop package test2.aa;
drop package pack_test_a;
drop package pkg10;
drop package pkg11;
drop package pck20;
drop package if exists test2;
drop package if exists aa;
drop package if exists dams_ci.emp_bonus10;
drop package if exists dams_ci.emp_bonus11;
drop package if exists multi_sql;
drop package if exists commit_rollback_test;

drop package if exists cnt;

drop package pack_log;
drop package CTP_MX_PCKG_INIT; 

CREATE TABLE test.emp_t (empno NUMBER(6), ename VARCHAR2(64), deptno NUMBER(4), salary NUMBER(10,2));

CREATE OR REPLACE PACKAGE test.emp_admin6 AS
   FUNCTION fn_get_emp_name6 (l_empno NUMBER)
   RETURN VARCHAR2;
   PROCEDURE pr_raise_salary6 (l_empno NUMBER);
END emp_admin6;
/

CREATE OR REPLACE PACKAGE BODY test.emp_admin6
AS
 FUNCTION fn_get_emp_name6 (l_empno NUMBER)
 RETURN VARCHAR2 
 IS
  V_EMPNAME VARCHAR2(64);
 BEGIN
  SELECT ename INTO V_EMPNAME
    FROM emp_t 
   WHERE empno = l_empno;
  RETURN V_EMPNAME;
 END;
 
 PROCEDURE pr_raise_salary6 (l_empno NUMBER) 
 IS
 BEGIN
  UPDATE emp_t 
     SET salary = salary + (salary * .1)
  WHERE empno = l_empno;
 END;
END emp_admin6;
/

create or replace package pckg_test1 as
procedure p1;
end pckg_test1;
/

create or replace package body pckg_test1 as
procedure p1() is 
a number;
begin 
a := 2/0;
end;
end pckg_test1;
/

create or replace package pckg_test2 as
procedure p1;
procedure p2;
end pckg_test2;
/

create or replace package body pckg_test2 as
procedure p2() is
begin
null;
end;

procedure p1() is 
a number;
begin 
pckg_test1.p1();
exception 
when others then 
raise notice '%', '1111';
p2();
end;
end pckg_test2;
/

create user test1 password 'Gauss123';
create user test2 password 'Gauss123';
ALTER DEFAULT PRIVILEGES IN SCHEMA test1 grant execute on packages to test2;
SET SESSION AUTHORIZATION test1 password 'Gauss123';
set behavior_compat_options='plsql_security_definer';
drop package if exists pkg_auth_1;
CREATE OR REPLACE package pkg_auth_1
is
a int;
END pkg_auth_1;
/
CREATE OR REPLACE package body pkg_auth_1
is
END pkg_auth_1;
/
drop package if exists pkg_auth_2;
CREATE OR REPLACE package pkg_auth_2
is
b int;
procedure a();
END pkg_auth_2;
/
CREATE OR REPLACE package body pkg_auth_2
is
procedure a 
is
begin
pkg_auth_1.a:=1;
end;
END pkg_auth_2;
/

grant usage on schema test1 to test2;
grant execute on package test1.bb to test2; 
SET SESSION AUTHORIZATION test2 password 'Gauss123';

begin
test1.pkg_auth_1.a:=1;
end;
/

begin
test1.pkg_auth_2.b:=1;
end;
/

SET SESSION AUTHORIZATION test1 password 'Gauss123';
drop package test1.pkg_auth_1;
drop package test1.pkg_auth_2;
reset session AUTHORIZATION;
drop user test1;
drop user test2;

call pckg_test2.p1();

create user t2 password 'Gauss_234';
create user t3 password 'Gauss_234';
create user t4 password 'Gauss_234';
create user t5 password 'Gauss_234';
SET SESSION AUTHORIZATION t2 password 'Gauss_234';

create table tab1(col1 int);
set behavior_compat_options='plsql_security_definer';
create or replace package a3 authid current_user
is
procedure func_1();
end a3; 
/
create or replace package body a3
is
procedure func_1()
is
begin
insert into test1 values(1);
end;
end a3;
/
\sf a3.func_1
create or replace procedure test2
is
curruser varchar2;
begin
select current_user into curruser;
raise notice '%',curruser;
insert into t2.tab1 values(1);
commit;
select current_user into curruser;
raise notice '%',curruser;
insert into t2.tab1 values(2);
end;
/
select proacl,prosecdef from pg_proc where proname='test2';
grant usage on schema t2 to t3;
grant usage,create on schema t2 to t3;
grant execute on all functions in schema t2 to t3;
SET SESSION AUTHORIZATION t3 password 'Gauss_234';
call t2.test2();
set behavior_compat_options='plsql_security_definer';
create or replace procedure test3
is
a int:=1;
begin
a:=2/0;
exception when others then
t2.test2();
raise;
end;
/
select proacl,prosecdef from pg_proc where proname='test3';
grant usage on schema t3 to t3;
grant usage,create on schema t3 to t4;
grant execute on all functions in schema t3 to t4;
SET SESSION AUTHORIZATION t4 password 'Gauss_234';
set behavior_compat_options='plsql_security_definer';
create or replace procedure test4
is
a int:=1;
begin
a:=2/0;
exception when others then
t3.test3();
commit;
raise;
end;
/
select proacl,prosecdef from pg_proc where proname='test4';
grant usage on schema t4 to t5;
grant usage,create on schema t4 to t5;
grant execute on all functions in schema t4 to t5;
SET SESSION AUTHORIZATION t5 password 'Gauss_234';
set behavior_compat_options='plsql_security_definer';
create or replace procedure test5
is
a int:=1;
begin
a:=2/0;
exception when others then
t4.test4();
commit;
raise;
end;
/
select proacl,prosecdef from pg_proc where proname='test5';
call t5.test5();
reset session AUTHORIZATION;
drop user t2 cascade;
drop user t3 cascade;
drop user t4 cascade;
drop user t5 cascade;

create or replace package pkg_same_arg_1
is
procedure a();
end pkg_same_arg_1;
/
create or replace package body pkg_same_arg_1
is
procedure a()
is
begin
insert into test_package1 values(1);
end;
end pkg_same_arg_1;
/ 
call pkg_same_arg_1.a();

create or replace package pkg_same_arg_2
is
procedure a();
end pkg_same_arg_2;
/

create or replace package body pkg_same_arg_2
is
procedure a()
is
begin
insert into test_package1 values(1);
end;
end pkg_same_arg_2;
/ 

call pkg_same_arg_2.a();

create or replace package pck1 is
procedure pro1();
end pck1;
/

START TRANSACTION;
drop package if exists pck1;
create or replace package pck1 is
procedure pro1();
end pck1;
/
CREATE TABLE DAMS_CI.DOC_BRANCH (STRU_ID VARCHAR2(10),AREA_CODE VARCHAR2(10));

CREATE OR REPLACE PACKAGE DAMS_CI.PCKG_DAMS_PARAMETER_SET IS
 FUNCTION fun_branch_lv1_doc_branch(i_branch_id IN VARCHAR2) RETURN VARCHAR2;
END pckg_dams_parameter_set;
/

CREATE OR REPLACE PACKAGE BODY DAMS_CI.PCKG_DAMS_PARAMETER_SET IS
FUNCTION fun_branch_lv1_doc_branch(i_branch_id IN VARCHAR2) RETURN VARCHAR2 IS
  BEGIN
   return 'aa';
  END ;
END pckg_dams_parameter_set;
/


SELECT MAX(t.area_code) INTO o_area_code FROM dams_ci.doc_branch t WHERE t.stru_id = DAMS_CI.pckg_dams_parameter_set.fun_branch_lv1_doc_branch('0010100000');
 
rollback;
drop package pkg_same_arg_1;
drop package pkg_same_arg_2;
CREATE OR REPLACE VIEW test.my_view AS
SELECT t.empno, test.emp_admin6.fn_get_emp_name6 (t.empno) my_alias
FROM test.emp_t t;
drop package if exists test.emp_admin6;
drop view if exists test.my_view;
drop table if exists test.emp_t;
drop schema if exists test cascade;
drop table if exists au_pkg;
drop package autonomous_pkg_150_2;
drop package autonomous_pkg_150_1;
drop package autonomous_pkg_150;
drop package feature_cross_test;
drop function func1;

drop package dams_ci.emp_bonus13;
drop package if exists exp_pkg;
drop trigger if exists insert_trigger on test_trigger_src_tbl;
drop table if exists dams_ci.DB_LOG;
drop table if exists test_trigger_des_tbl;
drop table if exists test_trigger_src_tbl;
drop package if exists dams_ci.pack_log;
drop package if exists dams_ci.ut_p_pckg_dams_dept_issue;
drop package if exists dams_ci.ctp_mx_pckg_init;
drop package if exists trigger_test;
drop table if exists test_package1;
drop table if exists dams_ci.test1;
drop package if exists trigger_test;
drop package if exists dams_ci;
drop package if exists pck1;
drop schema if exists dams_ci cascade;
drop schema if exists test1 cascade;
drop schema if exists test2 cascade;

CREATE OR REPLACE PACKAGE aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa AS
  function set_seed (seed number) return number;
END aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa;
/

CREATE OR REPLACE PACKAGE BODY aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa AS
  function set_seed (seed number) return number is
  begin
  return 0;
  end;
END aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa;
/

drop package if exists aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa;

drop package if exists pck1;
create or replace package pck1 as
-- function func() return int;
end pck1;
/
create or replace package body pck1 as
-- v_1 t1 := (1,'a');
-- function func() return int as
-- begin
--
-- end;
end pck1;
/
create or replace package body pck1 as
/* 
v_1 t1 := (1,'a');
function func() return int as
begin
end;
*/
end pck1;
/
drop package if exists pck1;

 create or replace package pck1 as
   type t1 is record(c1 int,c2 varchar2);
   type t2 is table of int;
   type t3 is varray(10) of int;
   type t4 is ref cursor;
   v1 t1;
   v2 t2;
   v3 t3;
   function func()return int;
 end pck1;
 /
 create or replace package body pck1 as
   type t5 is record(c1 int,c2 varchar2);
   type t6 is table of int;
   type t7 is varray(10) of int;
   type t8 is ref cursor;
   v5 t5;
   v6 t6;
   v7 t7;
   v_c1 int;
   v_c2 varchar2;
   function func()return int as
   v4 t4;
   v8 t8;
   begin
 --包头变量
   end;
 end pck1;
 /

 create or replace procedure func1() as
   begin
     pck1.v1 := (1,'a');
   end;
 /
 call func1();

 start transaction;
 create or replace package pck1 as
   type t1 is record(c1 int,c2 varchar2);
 end pck1;
 /
 commit;

 drop package if exists pck1;
 drop procedure if exists func1;

drop package if exists pck_logfunc;
create or replace package pck_logfunc is
procedure log;
procedure p1;
end pck_logfunc;
/
create or replace package body pck_logfunc is
procedure log is
begin
end;
procedure p1 is
begin
log();
end;
end pck_logfunc;
/
drop package if exists pck_logfunc;

CREATE OR REPLACE PACKAGE UT_P_PCKG_DAMS_RECEIVE AUTHID CURRENT_USER
IS
    PROCEDURE ut_setup_receive ;
    PROCEDURE ut_teardown_receive ;
    --For each procedure case to be tested...
    PROCEDURE ut_PROC_SAVE_1_receive;
END UT_P_PCKG_DAMS_RECEIVE;
--package body definition of UT_P_PCKG_DAMS_RECEIVE
/

create or replace package pck1 as
procedure p1;
procedure p2;
end pck1;
/
create or replace package body pck1 as
procedure p1 as
begin
null;
end;
procedure p2 as 
begin
drop package pck1;
end;
end pck1;
/
call pck1.p2();
--test online help
\h CREATE PACKAGE
\h CREATE PACKAGE BODY
\h DROP PACKAGE
\h DROP PACKAGE BODY

create schema pkgsch059;
set current_schema=pkgsch059;
create table pkgtbl059(c0 int,c1 number(5),c2 varchar2(20),c3 clob,c4 blob);
insert into pkgtbl059 values(1,1,'varchar1',repeat('clob1',2),'abcdef1');
insert into pkgtbl059 values(2,2,'varchar10',repeat('clob2',2),'abcdef2');

create type type001 is(c1 int,c2 number,c3 varchar2(30),c4 clob,c5 blob);

create or replace package pkg059
is
  type type001 is record(c1 int,c2 number,c3 varchar2(30),c4 clob,c5 blob);
  type type002 is table of pkgsch059.type001 index by integer;
  type type003 is table of type001 index by integer;
  col1  type002:=type002();
  col2  type003:=type003();
  procedure proc059_1(col3 type002,col4 type003);
  function func059_2(col5 int) return int;
end pkg059;
/

create or replace package body pkg059
is
procedure proc059_1(col3 type002,col4 type003)
is
begin
  raise info 'col3 is %',col3;
  raise info 'col4 is %',col4;
end;
function func059_2(col5 int) return int
is
begin
   pkg059.col1(1):=(1,1,'varchar1',repeat('clob1',2),'abcdef1');
   pkg059.col1(2):=(2,2,'varchar10',repeat('clob2',2),'abcdef2');
   pkg059.col2('1'):=col1(2);
   pkg059.col2('-1'):=col1(1);
   proc059_1(pkg059.col1,pkg059.col2);
   return pkg059.col1(1).c1;
end;
end pkg059;
/

create or replace package pkg059_1
is
procedure proc059_1_1(cp1 pkg059.type002,cp2 out pkg059.type003);
procedure func059_1_2(cf1 pkg059.type002,cf2 out pkg059.type003);
end pkg059_1;
/


create or replace package body pkg059_1
is
procedure proc059_1_1(cp1 pkg059.type002,cp2 out pkg059.type003)
is
cp3 varchar2(30);
begin
   raise info 'pkg059.col1 %',pkg059.col1;
   raise info 'pkg059.col2 %',pkg059.col2;
   func059_1_2(cf1=>pkg059.col1,cf2=>pkg059.col2);
   raise info 'cp1 is %',cp1;
   raise info 'cp2 is %',cp2;
   raise info 'cp3 is %',cp3;
end;
procedure func059_1_2(cf1 pkg059.type002,cf2 out pkg059.type003)
is
cf3 number;
cf4 varchar2(30):='cf4';
begin
   cf3:=3;
   pkg059.func059_2(cf3);
   raise info 'cf2(1).c1 is %',cf2(1);
  -- return cf4;
end;
end pkg059_1;
/


declare
de1 pkg059.type002;
de2 pkg059.type003;
count int:=2;
var2  varchar2(30);
begin
for i in 1..count loop
select c0,c1,c2,c3,c4 into de1(i).c1,de1(i).c2,de1(i).c3,de1(i).c4,de1(i).c5 from pkgtbl059 where c0=i;
select c0+200,c1+200,c2||'200',c3||'200',c4||'200' into de2(i).c1,de2(i).c2,de2(i).c3,de2(i).c4,de2(i).c5 from pkgtbl059 where c0=i;
end loop;
  raise info 'de1 is %',de1;
  raise info 'de2 is %',de2;
  pkg059_1.proc059_1_1(de1,de2);
  raise info 'de2 out is %',de2;
end;
/



create or replace package body pkg059
is
procedure proc059_1(col3 type002,col4 type003)
is
begin
  raise info 'col3 is %',col3;
  raise info 'col4 is %',col4;
end;
function func059_2(col5 int) return int
is
begin
   pkg059.col1(1):=(1,1,'varchar1',repeat('clob1',2),'abcdef1');
   pkg059.col1(2):=(2,2,'varchar10',repeat('clob2',2),'abcdef2');
   col2('1'):=col1(2);
   col2('-1'):=col1(1);
   proc059_1(pkg059.col1,pkg059.col2);
   return pkg059.col1(1).c1;
end;
end pkg059;
/

declare
de1 pkg059.type002;
de2 pkg059.type003;
count int:=2;
var2  varchar2(30);
begin
for i in 1..count loop
select c0,c1,c2,c3,c4 into de1(i).c1,de1(i).c2,de1(i).c3,de1(i).c4,de1(i).c5 from pkgtbl059 where c0=i;
select c0+200,c1+200,c2||'200',c3||'200',c4||'200' into de2(i).c1,de2(i).c2,de2(i).c3,de2(i).c4,de2(i).c5 from pkgtbl059 where c0=i;
end loop;
  raise info 'de1 is %',de1;
  raise info 'de2 is %',de2;
  pkg059_1.proc059_1_1(de1,de2);
  raise info 'de2 out is %',de2;
end;
/

--test alter package owner
create user alt_package PASSWORD 'gauss@123';
create user alt_package_2 PASSWORD 'gauss@123';
create package alt_package.pck1_alter as
procedure p1();
type r1 is record(a int, b int);
type r2 is table of r1;
type r3 is varray(10) of r1;
type r4 is ref cursor;
end pck1_alter;
/
create package body alt_package.pck1_alter as
type r5 is record(a int, b int);
type r6 is table of r1;
type r7 is varray(10) of r1;
type r8 is ref cursor;
procedure p1 is 
begin
null;
end;
procedure p2 is 
begin
null;
end;
end pck1_alter;
/
select usename from pg_user where usesysid = (select pkgowner from gs_package where pkgname = 'pck1_alter');
SET SESSION AUTHORIZATION alt_package_2 password 'gauss@123';
alter package alt_package.pck1_alter owner to alt_package_2;
SET SESSION AUTHORIZATION alt_package password 'gauss@123';
alter package alt_package.pck1_alter owner to alt_package_2;
reset session AUTHORIZATION;
alter package alt_package.pck1_alter owner to alt_package_2;
SET SESSION AUTHORIZATION alt_package password 'gauss@123';
alter package alt_package.pck1_alter owner to alt_package;
reset session AUTHORIZATION;
select usename from pg_user where usesysid = (select pkgowner from gs_package where pkgname = 'pck1_alter');
SET SESSION AUTHORIZATION alt_package_2 password 'gauss@123';
call alt_package.pck1_alter.p1();
reset session AUTHORIZATION;
grant usage on schema alt_package to alt_package_2;
grant execute on package alt_package.pck1_alter to alt_package_2; 
SET SESSION AUTHORIZATION alt_package_2 password 'gauss@123';
call alt_package.pck1_alter.p1();
declare
va alt_package.pck1_alter.r1;
vb alt_package.pck1_alter.r2;
vc alt_package.pck1_alter.r3;
vd alt_package.pck1_alter.r4;
begin
va := (1,1);
vb(1) := (2,3);
vc(1) := (3,4);
raise info '%,%,%', va,vb,vc;
end;
/
reset session AUTHORIZATION;
drop package alt_package.pck1_alter;
drop user alt_package cascade;
drop user alt_package_2 cascade;

-- test \h alter package
\h alter package

-- test \sf procedure with authid
create or replace procedure p1()
AUTHID CURRENT_USER
is 
begin
null;
end;
/

create or replace procedure p2()
AUTHID DEFINER
is 
begin
null;
end;
/

create or replace procedure p3()
is
begin
null;
end;
/
CREATE OR REPLACE PACKAGE ABORT IS
PROCEDURE testpro1(var3 int);
END ABORT;
/
CREATE OR REPLACE PACKAGE body ABORT IS
PROCEDURE testpro1(var3 int)
is
begin
null;
end;
END ABORT;
/
create or replace package autonomous_pkg_tmp 
IS 
count_public int := 10; 
function autonomous_f_public(num1 int) 
return int;
end autonomous_pkg_tmp;
/
create or replace package body autonomous_pkg_tmp as 
count_private int:=20; 
function autonomous_f_public(num1 int) 
return int 
is 
declare 
re_int int; 
begin count_public = num1 + count_public; 
count_private = num1 + count_private; 
re_int = count_public +count_private; 
return re_int; 
end;
begin 
count_public:=0;
count_private:=0; 
end autonomous_pkg_tmp;
/
create function package_func_overload(col int, col2 out int)
return integer  package
as
declare
    col_type text;
begin
     col := 122;
     return 0;
end;
/

create procedure package_func_overload(col int, col2 out varchar)
package
as
declare
    col_type text;
begin
     col2 := '122';
end;
/

reset session AUTHORIZATION;
begin
raise notice '%',autonomous_pkg_tmp.count_public;
end;
/
create or replace package pck1 is
type tp1 is varray(10) of int;
function f1(in a int,c out tp1) return int;
end pck1;
/

create or replace package body pck1 is
function f1(in a int,c out tp1) return int
as
declare
begin
c(1):=a;
return a;
end;
end pck1;
/

declare
kk pck1.tp1;
x int := 10;
res int;
begin
res := pck1.f1(x,kk)+1;
raise info 'res:%',res;
end;
/

drop package if exists pck1;
drop package if exists pck2;

create or replace package pck1 as
function func1() return int;
end pck1;
/
create or replace package body pck1 as
xx int :=10;
function func1() return int as
begin
  xx := xx + 1;
  return xx;
end;
end pck1;
/

create or replace package pck2 as
function func1() return int;
end pck2;
/
create or replace package body pck2 as
yy int := pck1.func1();
function func1() return int as
begin
return yy;
end;
end pck2;
/

call pck2.func1();

drop package if exists pck1;
drop package if exists pck2;

create or replace package pck1 as
function func2() return int;
end pck1;
/
create or replace package body pck1 as
function func1() return int as
begin
  return 10;
end;
function func2() return int as
begin
  return func1();
end;
end pck1;
/

create or replace package pck2 as
function func1() return int;
end pck2;
/
create or replace package body pck2 as
xx int := pck1.func2();
function func1() return int as
begin
  return xx;
end;
end pck2;
/
call pck2.func1();
call pck1.func2();

\sf p1
\sf p2
\sf p3
drop package if exists pck1;
drop function if exists func1;

create or replace function func1() return int as
begin
return 5;
end;
/

create or replace package pck1 as
procedure proc();
function func2() return int;
end pck1;
/
create or replace package body pck1 as
xx integer := func1;
procedure proc() as
begin
raise info 'xx is %',xx;
end;
function func2() return int as
begin
return 10;
end;
function func1() return int as
begin
return 20;
end;
end pck1;
/

call pck1.proc();

drop function func1;

create or replace package body pck1 as
xx integer := func1;
procedure proc() as
begin
raise info 'xx is %',xx;
end;
function func2() return int as
begin
return 10;
end;
end pck1;
/
call pck1.proc();

--退出会话，重连调用 xx不应该是20，应该在定义时或者调用时就报函数不存在
call pck1.proc();
set behavior_compat_options='proc_outparam_override';

create or replace package pck1 is
type tp1 is record(v01 number, v03 varchar2, v02 number);
function f1(in a int, out c tp1) return int;
end pck1;
/

create or replace package body pck1 is
function f1(in a int, out c tp1) return int
as
declare
begin
c.v01:=a;
return a;
end;
end pck1;
/
declare
x int := 10;
z pck1.tp1;
res int;
begin
res := pck1.f1(x,z); -- 变量
raise info 'res:%',res;
raise info 'z:%',z;
end;
/

declare
x int := 10;
z pck1.tp1;
begin
pck1.f1(a => x, c => z); -- 箭头变量
raise info 'z:%',z;
end;
/

declare
x int := 10;
z pck1.tp1;
begin
pck1.f1(x,z); -- 变量
raise info 'z:%',z;
end;
/

declare
x int := 10;
z pck1.tp1;
res int;
begin
select pck1.f1(x,z) into res; -- 变量
raise info 'res:%',res;
raise info 'z:%',z;
end;
/

create or replace package pck1 is
type tp1 is record(v01 number, v03 varchar2, v02 number);
type tp2 is record(v01 tp1, v03 varchar2, v02 number);
function f1(in a int, out c tp2) return int;
end pck1;
/

create or replace package body pck1 is
function f1(in a int, out c tp2) return int
as
declare
begin
c.v01.v01:=a;
return a;
end;
end pck1;
/

--调用报错
declare
x int := 10;
z pck1.tp2;
begin
pck1.f1(a => x, c => z); -- 箭头变量
raise info 'z:%',z;
end;
/

--调用结果不正确
declare
x int := 10;
z pck1.tp2;
res int;
begin
res := pck1.f1(a => x,c=>z); -- 箭头变量
raise info 'res:%',res;
raise info 'z:%',z;
end;
/

declare
x int := 10;
z pck1.tp2;
res int;
begin
select pck1.f1(x,z) into res; -- 变量
raise info 'res:%',res;
raise info 'z:%',z;--应该返回null
end;
/

create or replace package pck1 is
type tp1 is varray(10) of int;
type tp2 is record(v01 tp1, v03 varchar2, v02 number);
function f1(in a int, inout c tp2) return int;
end pck1;
/

create or replace package body pck1 is
function f1(in a int, inout c tp2) return int
as
declare
begin
c.v01:=array[a];
return a;
end;
end pck1;
/

declare
x int := 10;
z pck1.tp2;
res int;
begin
res := pck1.f1(x,z); -- 变量
raise info 'res:%',res;
raise info 'z:%',z;
end;
/

declare
x int := 10;
z pck1.tp2;
begin
pck1.f1(a => x, c => z); -- 箭头变量
raise info 'z:%',z;
end;
/

declare
x int := 10;
z pck1.tp2;
begin
pck1.f1(x,z); -- 变量
raise info 'z:%',z;
end;
/

declare
x int := 10;
z pck1.tp2;
res int;
begin
select pck1.f1(x,z) into res; -- 变量
raise info 'res:%',res;
raise info 'z:%',z;--应该返回null
end;
/

declare
res int;
x int := 10;
z pck1.tp2;
begin
select * into res from pck1.f1(a => x, c => z); -- 箭头变量
raise info 'res:%',res;
raise info 'z:%',z;--应该返回null
end;
/

create or replace package pck1 is
type tp1 is table of int;
type tp2 is record(v01 tp1, v03 varchar2, v02 number);
function f1(in a int, inout c tp2) return int;
end pck1;
/

create or replace package body pck1 is
function f1(in a int, inout c tp2) return int
as
declare
begin
c.v01:=array[a];
return a;
end;
end pck1;
/

declare
x int := 10;
z pck1.tp2;
res int;
begin
res := pck1.f1(a => x,c=>z); -- 箭头变量
raise info 'res:%',res;
raise info 'z:%',z;
end;
/

declare
x int := 10;
z pck1.tp2;
begin
pck1.f1(a => x, c => z); -- 箭头变量
raise info 'z:%',z;
end;
/

declare
x int := 10;
z pck1.tp2;
begin
pck1.f1(x,z); -- 变量
raise info 'z:%',z;
end;
/

declare
x int := 10;
z pck1.tp2;
res int;
begin
select pck1.f1(x,z) into res; -- 变量
raise info 'res:%',res;
raise info 'z:%',z;
end;
/

--inout参数是table%rowtype类型
drop table if exists test_tb;
create table test_tb(c1 int,c2 varchar2);


create or replace package pck1 is
function f1(in a int, inout c test_tb%rowtype) return int;
end pck1;
/

create or replace package body pck1 is
function f1(in a int, inout c test_tb%rowtype) return int
as
declare
begin
c.c1:=a+1;
return a;
end;
end pck1;
/

declare
x int := 10;
z test_tb%rowtype;
begin
pck1.f1(a => x, c => z); -- 箭头变量
raise info 'z:%',z;--赋值错误
end;
/

set behavior_compat_options = 'allow_procedure_compile_check';
create or replace function f_1(i varchar2) return varchar2 is
begin
 return i;
end;
/

create or replace package pck3 as
procedure p1;
function f_1(i varchar2) return varchar2;
end pck3;
/

create or replace package body pck3 as
procedure p1 as
va varchar2;
c1 sys_refcursor;
begin
--open c1 for select f_1('0') DATA_SOURCE from np_due_bill a limit 1;
open c1 for select f_1('0') DATA_SOURCE;
end;
function f_1(i varchar2) return varchar2 is
begin
 return i;
end;
end pck3;
/

create user package_user password 'gauss@123';
alter package pck3 owner to package_user;

drop package pck1;
drop package pck2;
drop package pck3;
drop procedure p1;
drop procedure p2;
drop procedure p3;
reset behavior_compat_options;
drop package autonomous_pkg_tmp;
drop package abort;
drop schema pkgsch059 cascade;
drop user package_user;
