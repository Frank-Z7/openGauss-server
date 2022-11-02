-- test create type table of 
-- check compatibility --
show sql_compatibility; -- expect A --
-- create new schema --
drop schema if exists plpgsql_table;
create schema plpgsql_table;
set current_schema = plpgsql_table;
set behavior_compat_options='allow_procedure_compile_check';

create type s_type as (
    id integer,
    name varchar,
    addr text
);

create type typeA as table of s_type;
create type typeB as table of s_type.id%type;
create type typeC as table of s_type.name%type;
create type typeD as table of varchar(100);

-- test alter
alter type typeA drop ATTRIBUTE s_type;
alter type typeA ADD ATTRIBUTE a int;
create type typeC2 as table of s_type.name%type;
alter type typeC2 RENAME TO typeC3;

create or replace procedure tableof_alter()
is
a typeC3;
begin
	a(1) = (1, 'zhangsan', 'shanghai');
	RAISE INFO 'call a(1): %' ,a(1);
end;
/

call tableof_alter();

-- test is 
create type s_type_1 is (
	id integer,
	name varchar,
	addr text
);

create type typeA1 is table of s_type_1;
create type typeB1 is table of s_type_1.id%type;
create type typeC1 is table of s_type_1.name%type;
create type typeD1 is table of varchar(100);

create or replace function tableof_5_1()
  return typeA1 as  
	a typeA1;
	b typeA1;
 begin
	a(1) = (1, 'lisi', 'beijing'); 
	b = a;
	b(2) = (2, 'zahngwu', 'chengdu');
	RAISE INFO 'a:%' ,a;
	return b;
end;
/

select tableof_5_1();
drop procedure tableof_5_1;

-- test as
create or replace procedure tableof_12_1
 is
    TYPE SalTabTyp as TABLE OF varchar(10) index by BINARY_INTEGER;  
	aa SalTabTyp;
 begin
	aa(0) = 1;
	aa(1) = 2;
	RAISE INFO '%' ,aa(0);
	RAISE INFO '%' ,aa(1);
end;
/

call tableof_12_1();

create or replace procedure tableof_12_2
 is
    TYPE SalTabTyp as TABLE OF varchar(10) index by BINARY_INTEGER;  
    aa SalTabTyp;
 begin
    aa(-1) = 1;
    aa(2) = 2;
    RAISE INFO '%' ,aa(0);
    RAISE INFO '%' ,aa(1);
    RAISE INFO '%', aa.count;
    RAISE INFO '%', aa;
end;
/

call tableof_12_2();

drop procedure tableof_12_1;
drop procedure tableof_12_2;
drop type s_type_1;
drop type typeA1;
drop type typeB1;
drop type typeC1;
drop type typeD1;

-- test table of nest table of  error
create type typeF as table of typeD;
-- don't support alter attr
alter type typeA ADD ATTRIBUTE a int;

--  test in paramter
create or replace procedure tableof_1(a typeA)
is
	
begin
	RAISE INFO 'a(1): %' ,a(1);
	a(1) = (2, 'lisi', 'beijing');
	a(2) = (3, 'zahngwu', 'chengdu');
end;
/

create or replace procedure tableof_2()
is
	a typeA;
begin
	a(1) = (1, 'zhangsan', 'shanghai');
	RAISE INFO 'before call a(1): %' ,a(1);
	perform tableof_1(a);
	RAISE INFO 'after call a(2): %' ,a(2);
end;
/

call tableof_2();

-- don't support create type = ()
create or replace procedure tableof_3
 is
    aa typeA = typeA();
 begin
	RAISE INFO '%' ,aa;
end;
/

call tableof_3();

-- test return 
create or replace function tableof_4()
  return typeA as  
	a typeA;
 begin
	a(1) = (1, 'lisi', 'beijing'); 
	return a;
end;
/

select tableof_4();

create or replace function tableof_4()
  return typeA as  
	a typeA;
 begin
	a(1) = (1, 'lisi', 'beijing'); 
	return a;
end;
/

select tableof_4();

create or replace function tableof_5()
  return typeA as  
	a typeA;
	b typeA;
 begin
	a(1) = (1, 'lisi', 'beijing'); 
	b = a;
	b(2) = (2, 'zahngwu', 'chengdu');
	RAISE INFO 'a:%' ,a;
	return b;
end;
/

select tableof_5();

-- test cast 
create or replace function tableof_6()
  return typeC as  
	a typeA;
	b typeC;
 begin
	a(1) = (1, 'lisi', 'beijing'); 
	b = a;
	b(2) = (2, 'zahngwu', 'chengdu');
	RAISE INFO 'a:%' ,a;
	return b;
end;
/

select tableof_6();

--test return wrong type
create or replace function tableof_7()
  return typeB as  
	a typeA;
	b typeC;
 begin
	a(1) = (1, 'lisi', 'beijing'); 
	b = a;
	b(2) = (2, 'zahngwu', 'chengdu');
	RAISE INFO 'a:%' ,a;
	return b;
end;
/

select tableof_7();

-- add one column from s_type
create type s_type_extend as (
	id integer,
	name varchar,
	addr text,
	comment varchar
);

create type typeA_ext as table of s_type_extend;

create or replace function tableof_8()
  return typeA_ext as  
	a typeA;
	b typeA_ext;
 begin
	a(1) = (1, 'lisi', 'beijing'); 
	b = a;
	b(2) = (2, 'zahngwu', 'chengdu','good');
	RAISE INFO 'a:%' ,a;
	return b;
end;
/

select tableof_8();

-- test return index
create or replace function tableof_9()
  return typeA as  
	a typeA;
 begin
	a(-1) = (1, 'lisi', 'beijing'); 
	a(2) = (2, 'zahngwu', 'chengdu');
	return a;
end;
/

select tableof_9();

create or replace procedure tableof_10()
 as  
	a typeA;
 begin
	a = tableof_9();
	RAISE INFO 'a(-1):%' ,a(-1);
	RAISE INFO 'a(0):%' ,a(0);
	RAISE INFO 'a(2):%' ,a(2).id;
end;
/

call tableof_10();

create or replace procedure tableof_11()
 as  
	a typeA;
 begin
	a = tableof_9();
	RAISE INFO 'a(-1):%' ,a(-1);
end;
/

call tableof_11();

-- test index by
create or replace procedure tableof_12
 is
    TYPE SalTabTyp is TABLE OF varchar(10) index by BINARY_INTEGER;  
	aa SalTabTyp;
 begin
	aa('aa') = 1;
	aa('bb') = 2;
	RAISE INFO '%' ,aa('aa');
	RAISE INFO '%' ,aa('bb');
end;
/

call tableof_12();

create or replace procedure tableof_13
 is
    TYPE SalTabTyp is TABLE OF integer index by varchar(10);  
	aa SalTabTyp;
 begin
	aa('aa') = 1;
	aa('bb') = 2;
	RAISE INFO '%' ,aa(0);
	RAISE INFO '%' ,aa('bb');
end;
/

call tableof_13();

create or replace procedure tableof_14
 is
    TYPE SalTabTyp is TABLE OF integer index by varchar(10);  
	aa SalTabTyp;
	b varchar(10);
 begin
	aa('a') = 1;
	b = 'aa';
	aa(b) = 2;
	RAISE INFO '%' ,aa('a');
	RAISE INFO '%' ,aa('aa');
	RAISE INFO '%' ,aa(b);
end;
/

call tableof_14();
 
create or replace procedure tableof_15
 is
    TYPE SalTabTyp is TABLE OF varchar(10) index by date;
	aa SalTabTyp;
 begin
	
end;
/

create or replace procedure tableof_15
 is
    TYPE SalTabTyp is TABLE OF varchar(10) index by text;
	aa SalTabTyp;
 begin
	
end;
/

-- test table = table
create or replace procedure tableof_16
 is
    TYPE SalTabTyp is TABLE OF varchar(10) index by BINARY_INTEGER;  
	aa SalTabTyp;
	bb SalTabTyp;
 begin
	aa(-1) = 'b';
	aa(1) = 'a';
	RAISE INFO '%' ,aa(-1);
	bb = aa;
	RAISE INFO '%' ,bb(-1);
	bb(8) = 'g';
	RAISE INFO '%' ,bb(8);
	RAISE INFO '%' ,aa(8);
 end;
/

call tableof_16();

-- test define
create or replace procedure tableof_17
 is
    TYPE SalTabTyp is TABLE OF s_type%rowtype index by varchar(10);  
	aa SalTabTyp;
 begin
	aa('a') = (1, 'zhangsan', 'shanghai');
	aa('b') = (2, 'lisi', 'beijing');
	RAISE INFO '%' ,aa('a').id;
	RAISE INFO '%' ,aa('b');
end;
/
call tableof_17();

create or replace procedure tableof_18
 is
 declare
    TYPE SalTabTyp is TABLE OF s_type.id%type index by varchar(10);  
	aa SalTabTyp;
 begin
	aa('a') = 1;
	aa('b') = 2;
	aa = NULL;
	RAISE INFO '%' ,aa('a');
	RAISE INFO '%' ,aa('b');
	aa('a') = 1;
	aa('C') = 2;
	aa('b') = 3;
	RAISE INFO '%' ,aa;
end;
/

call tableof_18();


-- test not null gram
create or replace procedure tableof_19
 is
    TYPE SalTabTyp is TABLE OF s_type%rowtype not null index by varchar(10);  
	aa SalTabTyp;
 begin
	aa('a') = (1, 'zhangsan', 'shanghai');
	RAISE INFO '%' ,aa('a');
end;
/

call tableof_19();

-- test assign one attr 
create or replace procedure tableof_20
 is
    TYPE SalTabTyp is TABLE OF s_type%rowtype not null index by varchar(10);  
	aa SalTabTyp;
 begin
	aa('a') = (1, 'zhangsan', 'shanghai');
	aa('a').id = 1;
end;
/

call tableof_20();

create type info as (name varchar2(50), age int, address varchar2(20), salary float(2));
create type customer as (id number(10), c_info info);
create table customers (id number(10), c_info info);

insert into customers (id, c_info) values (1, ('Vera' ,32, 'Paris', 22999.00));
insert into customers (id, c_info) values (2, ('Zera' ,25, 'London', 5999.00));
insert into customers (id, c_info) values (3, ('Alice' ,22, 'Bangkok', 9800.98));
insert into customers (id, c_info) values (4, ('Jim' ,26, 'Dubai', 18700.00));
insert into customers (id, c_info) values (5, ('Kevin' ,28, 'Singapore', 18999.00));
insert into customers (id, c_info) values (6, ('Gauss' ,42, 'Beijing', 32999.00));
-- test curosor fetch into
create or replace procedure tableof_21
as
declare
	TYPE id_1 is TABLE OF customer.id%type index by varchar(10); 
	TYPE c_info_1 is TABLE OF customers.c_info%type index by varchar(10);  
    CURSOR C1 IS SELECT id FROM customers order by id;
    CURSOR C2 IS SELECT c_info FROM customers order by id;
    info_a c_info_1:=c_info_1();
	id_a id_1:=id_1();
begin
    OPEN C1;
    OPEN C2;
    FETCH C1 into id_a(2);
    FETCH C2 into info_a(2);
    FETCH C1 into id_a(3);
    FETCH C2 into info_a(3);
    CLOSE C1;
    CLOSE C2;
	RAISE INFO '%', id_a;
	RAISE INFO '%', info_a;
end;
/

call tableof_21();

-- test select into 
create or replace procedure tableof_22
as  
declare
	TYPE id_1 is TABLE OF customer.id%type index by varchar(10); 
	TYPE c_info_1 is TABLE OF customers.c_info%type index by varchar(10);  
    info_a c_info_1:=c_info_1();
	id_a id_1:=id_1();
begin
    select id into id_a(2) from customers where id = 3;
    select c_info into info_a(2) from customers where id = 3;
    select id into id_a(3) from customers where id = 4;
    select c_info into info_a(3) from customers where id = 4;
	RAISE INFO '%', id_a(2);
	RAISE INFO '%', info_a(3).age;
end;
/

call tableof_22();

-- test curosor for
create or replace procedure tableof_23 
as 
declare
    type c_list is TABLE of customer; 
    customer_table c_list:=c_list();
    CURSOR C1 IS SELECT * FROM customers order by id;
    counter int := 0;
begin 
    for n in C1 loop
	    counter := counter + 1;
        customer_table(counter) := n;
	end loop;
	RAISE INFO '%', customer_table(3);
end;
/

call tableof_23();

create or replace procedure tableof_24 
as 
declare
    type c_list is TABLE of customers%rowtype; 
    customer_table c_list:=c_list();
    CURSOR C1 IS SELECT * FROM customers order by id;
    counter int := 0;
begin 
    for n in C1 loop
	    counter := counter + 1;
        customer_table(counter) := n;
	end loop;
	RAISE INFO '%', customer_table(4);
end;
/

call tableof_24();

-- test row type
create type typeE as table of s_type%rowtype;
create type typeE as table of customers%rowtype;

create or replace procedure tableof_25
as 
declare
    customer_table typeE;
    CURSOR C1 IS SELECT * FROM customers order by id;
    counter int := 0;
begin 
    for n in C1 loop
	    counter := counter + 1;
        customer_table(counter) := n;
	end loop;
	RAISE INFO '%', customer_table(4);
end;
/

call tableof_25();

-- test insert
create or replace procedure tableof_26
as 
declare
	type c_list is TABLE of customers%rowtype; 
    customer_table c_list:=c_list();
begin 
    customer_table(1) := (7, ('Vera' ,32, 'Paris', 22999.00));
	customer_table(2) := (8, ('Vera' ,32, 'Paris', 22999.00));
	insert into customers values (customer_table(1).id, customer_table(1).c_info);
	insert into customers values (customer_table(2).id, customer_table(2).c_info);
end;
/

call tableof_26();
select * from customers where id = 7;

-- expect error table[]
create or replace procedure tableof_27
as 
declare
	type c_list is TABLE of customers%rowtype; 
    customer_table c_list:=c_list();
begin 
    customer_table(1) := (7, ('Vera' ,32, 'Paris', 22999.00));
	insert into customers values (customer_table[1].id, customer_table[1].c_info);
end;
/

-- test deault
declare
    type students is table of varchar2(10);
    type grades is table of integer;
    marks grades := grades(98, 97, 74 + 4, (87), 92, 100); -- batch initialize --
    names students default students('none'); -- default --
    total integer;
begin
    names := students();  -- should append NULL then do the coerce --
    names := students('Vera ', 'Zera ', 'Alice', 'Jim  ', 'Kevin', to_char('G') || 'auss'); -- batch insert --
    total := names.count;
    dbe_output.print_line('Total '|| total || ' Students'); 
    for i in 1 .. total loop
        dbe_output.print_line('Student: ' || names(i) || '  Marks: ' || marks(i));
    end loop;
end;
/

create type mytype as (
    id integer,
    biome varchar2(100)
);

create type mytype2 as (
    id integer,
    locale myType
);
declare
    type finaltype is table of mytype2;
    aa finaltype := finaltype(
        mytype2(1, mytype(1, 'ground')),
        mytype2(1, mytype(2, 'air'))
    );
begin
    aa.extend(10);
    aa(2) := (2, (3, 'water')); -- overwrite record (1, (2, 'air')) --
    dbe_output.print_line('locale id is: ' || aa(1).id);
    dbe_output.print_line('biome 1.3 is: ' || aa(2).locale.biome); -- ... water (not air) --
end;
/

-- test of uneven brackets --
-- error out --
declare
    type students is table of varchar2(10);
    names students;
begin
    names := students(1, 'Zera ', 'Alice', 'Jim  ', 'Kevin'); -- should be able read all values correctly --
    for i in 1 .. 5 loop
        dbe_output.print_line('Student: ' || names(i]);
    end loop;
end;
/

-- Using composite type defined outside of precedure block --
declare
    type finaltype is varray(10) of mytype2;
    aa finaltype := finaltype(
        mytype2(1, (1, 'ground')),
        mytype2(1, (2, 'air'))
    );
begin
    aa(2) := (2, (3, 'water')); -- overwrite record (1, (2, 'air')) --
    dbe_output.print_line('locale id is: ' || aa(1).id);
    dbe_output.print_line('biome 1.3 is: ' || aa(2).locale.biome); -- ... water (not air) --
end;
/

declare
    type finaltype is table of mytype2;
    aa finaltype := finaltype(
        mytype2(1, mytype(1, 'ground')),
        mytype2(1, mytype(2, 'air'))
    );
begin
    aa.extend(10);
    aa(2) := mytype2(2, mytype(3, 'water'));
    dbe_output.print_line('locale id is: ' || aa(1).id);
    dbe_output.print_line('biome 1.3 is: ' || aa(2).locale.biome); -- ... water (not air) --
end;
/

create type functype as (
    id integer,
    locale myType
);

create or replace function functype(habitat in mytype2)
return mytype2
is
    ret mytype2;
begin
    ret := (-1, (1, 'unknown realm'));
    return ret;
end;
/

declare
    type finaltype is table of mytype2;
    aa finaltype := finaltype(
        functype(1, mytype(1, 'ground')), -- we are prioritizing types here --
        functype(1, mytype(2, 'air'))
    );
begin
    dbe_output.print_line('locale id is: ' || aa(1).id);
    dbe_output.print_line('biome 1.2 is: ' || aa(2).locale.biome); -- air --
end;
/
-- abandon type functype
drop type functype; 

declare
    type finaltype is table of mytype2;
    aa finaltype := finaltype(
        functype((1, mytype(1, 'ground'))), -- here we have to use function functype --
        functype((1, mytype(2, 'air')))
    );
begin
    aa.extend(10);
    dbe_output.print_line('locale ?? is: ' || aa(1).id);
    dbe_output.print_line('biome ??? is: ' || aa(2).locale.biome); -- weird places --
end;
/

drop function functype;
-- error
declare
    type finaltype is table of mytype2;
    aa finaltype := finaltype(
        functype((1, mytype(1, 'ground'))), -- not sure --
        functype((1, mytype(2, 'air')))
    );
begin
    aa.extend(10);
    dbe_output.print_line('This message worth 300 tons of gold (once printed).');
end;
/

-- test table of array
declare
    type arrayfirst is table(10) of int[];
    arr arrayfirst := arrayfirst();
begin
    
end;
/

create type typeG as (a int[]);
declare
    type arrayfirst is table of typeG;
    arr arrayfirst := arrayfirst();
begin
    arr(1) = row(ARRAY[1, 2, 3]);
	dbe_output.print_line(arr(1).a[1]);
end;
/

-- test unreserved key word
declare 
    index int;
begin
	index = 1;
end;
/

-- test package
create or replace package aa
is
type students is table of int;
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
        raise info '%', names[i]; 
    end loop;
end;
end aa;
/

call aa.kk();
drop package if exists aa;

create or replace package pck2 is
procedure p1;
type r2 is table of int index by varchar(10);
va r2;
end pck2;
/
create or replace package body pck2  is
procedure p1 as 

begin

select 11 into va('a');
select 111 into va('b');
va('a') := 1111;

raise info '%,', va;
end;
end pck2;
/

call pck2.p1();
call pck2.p1();
drop package pck2;

reset current_schema;
show current_schema;
declare
	type students is table of plpgsql_table.s_type;
	a students;
begin
	a(1) = (1, 'lisi', 'beijing'); 
end;
/
set current_schema = plpgsql_table;
-- test [:]
declare
    TYPE SalTabTyp is TABLE OF integer index by varchar(10);
aa SalTabTyp;
 begin
aa(1) = 1;
aa(2) = 2;
RAISE INFO '%' ,aa(1);
RAISE INFO '%' ,aa[1:2];
end;
/

-- test [,]
declare
    TYPE SalTabTyp is TABLE OF integer index by varchar(10);
aa SalTabTyp;
 begin
aa(1) = 1;
aa(2) = 2;
RAISE INFO '%' ,aa(1);
RAISE INFO '%' ,aa[1,2];
end;
/

-- test functions
declare
  type b is table of int index by varchar;
  a b;
  c bool;
begin
  a('a') = 1;
  a('b') = 2;
  c =  a.exists('b');
  raise info '%', c;
end;
/

declare 
    TYPE SalTabTyp is TABLE OF varchar(10) index by varchar(10);  
	aa SalTabTyp;  
    c int;
 begin
    aa('a') = 'abcde';
	aa('b') = 'fghij';
    c = aa.first;
end;
/

declare 
    TYPE SalTabTyp is TABLE OF varchar(10) index by varchar(10);  
	aa SalTabTyp;  
 begin
    aa('a') = 'abcde';
	aa('b') = 'fghij';
    aa.delete;
end;
/

declare 
    TYPE SalTabTyp is TABLE OF varchar(10) index by varchar(10);  
	aa SalTabTyp;  
 begin
    aa('a') = 'abcde';
	aa('b') = 'fghij';
    aa.trim;
end;
/

declare 
    TYPE SalTabTyp is TABLE OF varchar(10) index by int;  
	aa SalTabTyp;  
 begin
    aa(1) = 'abcde';
	aa(2) = 'fghij';
    aa.trim;
end;
/

declare 
    TYPE SalTabTyp is TABLE OF varchar(10) index by varchar(10);  
	aa SalTabTyp;  
 begin
    aa.extend;
    aa('a') = 'abcde';
	aa('b') = 'fghij';
end;
/

declare 
    TYPE SalTabTyp is TABLE OF varchar(10) index by int;  
	aa SalTabTyp;  
 begin
    aa.extend;
    aa(1) = 'abcde';
	aa(2) = 'fghij';
end;
/

declare 
    TYPE SalTabTyp is TABLE OF varchar(10) index by varchar(10);  
	aa SalTabTyp;  
    c varchar(10);
 begin
    aa('a') = 'abcde';
    aa('b') = 'fghij';
    c = aa.next(aa.first);
end;
/

declare 
    TYPE SalTabTyp is TABLE OF varchar(10) index by varchar(10);  
	aa SalTabTyp;  
    c varchar(10);
 begin
    aa('a') = 'abcde';
    aa('b') = 'fghij';
    c = aa.prior('a');
end;
/

declare 
    TYPE SalTabTyp is TABLE OF varchar(10) index by varchar(10);  
	aa SalTabTyp;  
    c varchar(10);
 begin
    aa('a') = 'abcde';
	aa('b') = 'fghij';
    c = aa.last;
end;
/

declare 
    TYPE SalTabTyp is TABLE OF varchar(10) index by varchar(10);  
	aa SalTabTyp;  
    c int;
 begin
    aa('a') = 'abcde';
    RAISE INFO '%', aa.exists('a');
end;
/

declare 
    TYPE SalTabTyp is TABLE OF varchar(10) index by integer;  
	aa SalTabTyp;  
    c int;
 begin
    aa(1) = 'a';
	aa(-1) = 'c';
	aa(2) = 'b';
    raise info '%', aa.next(1);
	raise info '%', aa.prior(1);
end;
/

declare
    type ta is table of varchar(100);
    tb constant ta := ta('10','11');
begin
    tb(1) := 12;
    dbe_output.print_line(tb[1]);
end;
/

declare
    type ta is table of varchar(100);
    tb constant ta := ta('10','11');
begin
    tb := ta('12','13');
    dbe_output.print_line(tb[1]);
end;
/

reset sql_beta_feature ;
create or replace package pcknesttype is
    type aa is table of int;
    type bb is table of aa;
    procedure proc1();
end pcknesttype;
/

create or replace package body pcknesttype
is
    mytab aa;
    my2 bb;
procedure proc1 
    is    begin
        mytab := aa(1,2,3,4);
        my2 := bb(mytab);

end;
end pcknesttype;
/

create or replace procedure tableof_nest1()
is
    type data_type1 is table of s_type index by integer;
    type data_table_type1 is table of data_type1 index by integer;
    MyTab   data_type1;
    tmp_y data_type1;
    yy data_table_type1;
begin
   MyTab(1).id :=  1;
   MyTab(2).name :=  'B';
   MyTab(3).addr :=  'addr';
   yy(0) := MyTab;
   yy(1)(1).id := 1;
   yy(1)(1).name := 'yy';
   RAISE INFO 'call yy: %' ,yy(1)(1);
   RAISE INFO 'call yy count: %' ,yy(0).count;
   tmp_y := yy(1);
   --RAISE INFO 'call yy(1) next: %' ,tmp_y.next(1);
   --RAISE INFO 'call yy first: %' ,yy.first;
   --RAISE INFO 'call yy next: %' ,yy.next(1);
end;
/
call tableof_nest1();

create or replace procedure tableof_nest2()
is
    type data_type1 is table of varchar2(100) index by integer;
    type data_table_type1 is table of data_type1 index by integer;
    MyTab   data_type1;
    tmp_y data_type1;
    yy data_table_type1;
begin
   MyTab(1) :=  'A';
   MyTab(2) :=  'B';
   MyTab(3) :=  'C';
   yy(0) := MyTab;
   yy(1)(1) := 'o';
   RAISE INFO 'call yy: %' ,yy(1)(1);
   RAISE INFO 'call yy count: %' ,yy(0).count;
   tmp_y := yy(1);
   --RAISE INFO 'call yy(1) next: %' ,tmp_y.next(1);
   --RAISE INFO 'call yy first: %' ,yy.first;
   --RAISE INFO 'call yy next: %' ,yy.next(1);
end;
/

call tableof_nest2();

create or replace procedure tableof_nest3()
is
    type data_type1 is table of varchar2(100) index by varchar2(24);
    type data_table_type1 is table of data_type1 index by varchar2(24);
    MyTab   data_type1;
    tmp_y data_type1;
    yy data_table_type1;
begin
   MyTab('a') :=  'A';
   MyTab('b') :=  'B';
   MyTab('c') :=  'C';
   yy('a') := MyTab;
   yy('b')('c') := 'o';
   RAISE INFO 'call yy: %' ,yy('a')('c');
   RAISE INFO 'call yy count: %' ,yy('a').count;
   tmp_y := yy('b');
   --RAISE INFO 'call yy next: %' ,tmp_y.next('c');
   --RAISE INFO 'call yy first: %' ,tmp_y.first;
   --RAISE INFO 'call yy next: %' ,yy.next('a');
end;
/
call tableof_nest3();

DECLARE
  TYPE r1 is TABLE OF int;
  type r2 is table of r1;
  emp_id r2;
BEGIN
  emp_id(1)(1) := 5*7784;
  raise info '%,%', emp_id,emp_id(1)(1);
END;
/

create type type001 as(c1 int,c2 varchar);
create type type002 as(c1 type001,c2 type001.c2%type,c4 int);
create type type003 as table of type002;
create type type004 as(c1 type003,c2 int);

create or replace procedure proc_1 as
typecol type004;
begin
typecol.c1(1).c1.c1=1;
typecol.c2=1;
raise info 'typecol %',typecol.c1(1).c1.c1;
raise info 'typecol %',typecol.c2;
raise info 'typecol %',typecol;
end;
/

call proc_1();

drop type type_nest_23,type_nest_22,type_nest_24,type_nest_25 cascade;
drop table type_nest_21 cascade;
create table type_nest_21 (c1 int,c2 text, c3 date);
create type type_nest_22 as(c1 type_nest_21,c2 type_nest_21.c2%type,c3 type_nest_21%rowtype);
create type type_nest_23 is table of type_nest_22;
create type type_nest_24 is table of type_nest_21;
create type type_nest_25 as(c1 type_nest_21,c2 type_nest_23);

declare
  type type1 is varray(6) of varchar2(10);
  TYPE type2 is TABLE OF type_nest_21;
  TYPE type3 is TABLE OF type2;
  TYPE type4 is TABLE OF type3;
  vtype5 type3;
  vtype6 type_nest_25;
begin
  vtype5(1)(1).c2 := 'abc';
  raise info '%', vtype5(1)(1).c2;
end;
/

declare
  type type1 is varray(6) of varchar2(10);
  TYPE type2 is TABLE OF type_nest_21;
  TYPE type3 is TABLE OF type2;
  vtype6 type3;
begin
  vtype6(1)(1)(1).c2 := 'abc';
end;
/

declare
  TYPE record_user1 is table of type_nest_21;
  TYPE record_user2 is table of record_user1;
  TYPE record_user3 is table of record_user2;
  v_record_user2 record_user2;
  v_record_user3 record_user3;
begin
  v_record_user2(1) :=1;
end;
/

declare
  TYPE record_user1 is table of type_nest_21;
  TYPE record_user2 is table of record_user1;
  TYPE record_user3 is table of record_user2;
  v_record_user2 record_user2;
  v_record_user3 record_user3;
begin
  v_record_user3(1)(1):=1;
  v_record_user2(1).c1 :=1;
end;
/
drop table customers cascade;
create table customers (
    id number(10) not null,
    c_name varchar2(50),
    c_age number(8) not null,
    c_address varchar2(50),
    salary float(2) not null,
    constraint customers_pk primary key (id)
);

--test collect in null 
declare
    cursor c_customers is select c_name from customers order by id;
    type c_list is table of customers.c_name%type index by integer;
    name_arr c_list := c_list();
begin
    name_arr(2) = (-1, 'Vera' ,32, 'Paris', 22999.00);
    name_arr(7) = (-1, 'Vera' ,32, 'Paris', 22999.00);
    -- bulk collect + cursor
    open c_customers;
    fetch c_customers bulk collect into name_arr;
    close c_customers;
    raise info '%', name_arr.count;
    raise info '%', name_arr.last;
    raise info '%', name_arr.exists(7);
end;
/

declare
    type id_list is varray(6) of customers.id%type;
    id_arr id_list;
begin
    id_arr(1) = 1;
    raise info '%', id_arr;
    select id bulk collect into id_arr from customers order by id DESC;
    raise info '%', id_arr;
end;
/

create type mytype1 as (
    id integer,
    biome varchar2(100)
);

-- success, multi target support
declare
    type tab is varray(6) of mytype1;
    tab1 tab := tab();
begin
    tab1(1) = (1,'a');
    raise info '%', tab1;
    select id, c_name bulk collect into tab1 from customers order by id DESC;
    raise info '%', tab1;
end;
/

insert into customers (id, c_name, c_age, c_address, salary) values (1, 'Vera' ,32, 'Paris', 22999.00);

--test bulk collect into
declare
    cursor c_customers is select c_name from customers order by id;
    type c_list is table of customers.c_name%type index by integer;
    name_arr c_list := c_list();
begin
    name_arr(2) = (-1, 'Vera' ,32, 'Paris', 22999.00);
    name_arr(7) = (-1, 'Vera' ,32, 'Paris', 22999.00);
    -- bulk collect + cursor
    open c_customers;
    fetch c_customers bulk collect into name_arr;
    exit when c_customers%NOTFOUND;
    close c_customers;
    raise info '%', name_arr.count;
    raise info '%', name_arr.last;
    raise info '%', name_arr.exists(7);
end;
/

insert into customers (id, c_name, c_age, c_address, salary) values (2, '' ,25, 'London', 5999.00);     -- a missing value here
insert into customers (id, c_name, c_age, c_address, salary) values (3, 'Alice' ,22, 'Bangkok', 9800.98);
insert into customers (id, c_name, c_age, c_address, salary) values (4, 'Jim' ,26, 'Dubai', 18700.00);
insert into customers (id, c_name, c_age, c_address, salary) values (5, 'Kevin' ,28, 'Singapore', 18999.00);
insert into customers (id, c_name, c_age, c_address, salary) values (6, 'Gauss' ,42, 'Beijing', 32999.00);
--test bulk collect into
declare
    cursor c_customers is select c_name from customers order by id;
    type c_list is table of customers.c_name%type index by integer;
    name_arr c_list := c_list();
begin
    -- bulk collect + cursor
    open c_customers;
    fetch c_customers bulk collect into name_arr limit 4;
    exit when c_customers%NOTFOUND;
    close c_customers;

    for i in 1..6 loop
        dbe_output.print_line('name(' || i || '): ' || name_arr(i));
    end loop;

    -- assign values directly
    name_arr := ARRAY['qqqq', 'sfsafds', 'sadsadas'];

    for i in 1..6 loop
        dbe_output.print_line('name(' || i || '): ' || name_arr(i));
    end loop;
end;
/

declare
    cursor c_customers is select c_name from customers order by id;
    type c_list is table of customers.c_name%type index by varchar;
    name_arr c_list := c_list();
begin
    -- bulk collect + cursor
    open c_customers;
    fetch c_customers bulk collect into name_arr limit 4;
    exit when c_customers%NOTFOUND;
    close c_customers;
end;
/

-- table of null && delete
declare
    cursor c_customers is select c_name from customers order by id;
    type c_list is table of customers.c_name%type index by integer;
    name_arr c_list := c_list();
begin
    -- bulk collect + cursor
    open c_customers;
    fetch c_customers bulk collect into name_arr;
	name_arr.delete();
    close c_customers;
    raise info '%', name_arr.count;
    raise info '%', name_arr.last;
    raise info '%', name_arr.exists(7);
end;
/

create table pro_tblof_tbl_018_1(c1 int,c2 varchar(20));
create table pro_tblof_tbl_018(c1 int,c2 pro_tblof_tbl_018_1);
create type pro_tblof_018 is table of pro_tblof_tbl_018%rowtype;

insert into pro_tblof_tbl_018 values (1,(2,'aaa'));
 
create or replace procedure pro_tblof_pro_018_11()
as
  tblof001 pro_tblof_018;
 cursor cor1 is select c2 from pro_tblof_tbl_018 order by c1 desc;
 cursor cor2 is select c1 from pro_tblof_tbl_018 order by c1 desc;
 tblcount int;
begin
  select count(*) into tblcount from pro_tblof_tbl_018;
  for i in 1..tblcount
  loop
  --open cor1;
  --  fetch cor1 bulk collect into tblof001(i).c2;
-- EXIT WHEN cor1%NOTFOUND;
  --close cor1;
  open cor2;
   fetch cor2 bulk collect into tblof001(i).c1;
 exit when cor2%notfound;
    close cor2;
   i=i+1;
  end loop;
  for i in tblof001.first..tblof001.last
   loop
     if tblof001(i) is null then
      tblof001(i)=tblof001(tblof001.next(i));
     end if;
   dbe_output.print_line('tblof001 ('||i||')is '||tblof001(i).c1||'-----'||tblof001(i).c2);
   end loop;
   raise info 'tblof001 is %',tblof001;
end;
/

call pro_tblof_pro_018_11();

create or replace procedure p155() as
type t is table of varchar2 index by integer;
v t;
begin
raise info '%', v.count;
for i in 1..v.count loop
v(i):=0;
end loop;
end;
/

call p155();

create or replace procedure p156() as
type t is table of varchar2 index by varchar;
v t;
begin
raise info '%', v.count;
for i in 1..v.count loop
v(i):=0;
end loop;
end;
/

call p156();

 create or replace procedure table_column
 is
    type rec_type is record (name  varchar2(100), epno int);
    TYPE SalTabTyp as TABLE of rec_type index by BINARY_INTEGER;  
    aa SalTabTyp;
 begin
   aa(0).epno = 1;
   raise info '%', aa;
   select '' into aa(0).name;
   raise info '%', aa;
end;
/

call table_column();

create table pkgtbl054(c0 int,c1 number(5),c2 varchar2(20),c3 clob,c4 blob);
insert into pkgtbl054 values(1,1,'varchar1',repeat('clob1',20),'abcdef1');
insert into pkgtbl054 values(2,2,'varchar10',repeat('clob2',20),'abcdef2');

create type type0011 as(c0 int,c1 number(5),c2 varchar2(20),c3 clob,c4 blob);

create or replace package pkg054
is
type type0011 is table of type0011%rowtype index by varchar2(20);
type type002 is table of type0011.c2%type index by integer;
col1  type0011;
col2  type002;
procedure proc054_1(col3 type0011,col4 type002);
function proc054_2(col5 int) return integer;
end pkg054;
/

create or replace package body pkg054
is
procedure proc054_1(col3 type0011,col4 type002)
is
begin	
raise info 'col13 is %',col3;
raise info 'col14 is %',col4;
exception
  when others then
    raise info 'sqlerrm is %',sqlerrm;
end;
function proc054_2(col5 int) return integer
as
begin
  col1('1').c0:=128909887;
col1('1').c1:=12345;
col1('2').c2:='var2';
col1('2').c3:='clobcol1';
col1('2').c4:='123456';
col2(1):=col1('2').c2;
col2(3):=col1('1').c3;
raise info 'col1 is %',col1;
raise info 'col2 is %',col2;
  proc054_1(col3=>pkg054.col1,col4=>pkg054.col2);
return 1;
end;
end pkg054;
/

call pkg054.proc054_2(1);

create or replace package body pkg054
is
procedure proc054_1(col3 type0011,col4 type002)
is
begin	
raise info 'col13 is %',col3;
raise info 'col14 is %',col4;
exception
  when others then
    raise info 'sqlerrm is %',sqlerrm;
end;
function proc054_2(col5 int) return integer
as
begin
  col1('1').c0:=128909887;
col1('1').c1:=12345;
col1('2').c2:='var2';
col1('2').c3:='clobcol1';
col1('2').c4:='123456';
col2(1):=col1('2').c2;
col2(3):=col1('1').c3;
raise info 'col1 is %',col1;
raise info 'col2 is %',col2;
  proc054_1(pkg054.col1,pkg054.col2);
return 1;
end;
end pkg054;
/

call pkg054.proc054_2(1);

drop package pkg054;
drop type type_nest_23,type_nest_22,type_nest_24,type_nest_25 cascade;
drop table type_nest_21;

create or replace package pkg049
is
type type001 is table of number(8) index by varchar2(30);
type type002 is record(c1 type001,c2 varchar2(30));
function proc049_2(col1 int) return type001;
end pkg049;
/

create or replace function tableof_return_1(col1 int) return s_type[]
is
type type001 is table of s_type index by varchar2(30);
a type001;
begin
return a;
end;
/

create or replace function tableof_return_2(col1 int) return integer
is
type type001 is table of s_type index by varchar2(30);
a type001;
begin
a(1) = (1, 'lisi', 'beijing'); 
return a(1).id;
end;
/

call tableof_return_2(1);

create or replace function tableof_return_3(col1 int) return integer
is
type type001 is table of integer index by varchar2(30);
a type001;
begin
a(1) = 1;
a(2) = 2;
return a(1);
end;
/

call tableof_return_3(1);

-- test varchar as index and text as index
drop table t1;
create table t1 (a varchar2(100), b varchar2(100), c number(10,0), d number(10,0), e number(10,0));

create or replace package pck1 as
type ra is table of varchar2 index by varchar2(100);
procedure p1 (v01 out ra);
end pck1;
/
create or replace package body pck1 as
type rb is table of t1 index by varchar;
v02 rb;
v_buff varchar2(1000);
procedure p1(v01 out ra) as
v_value  varchar2(200);
v_index  varchar2(200);
i int := 1;
begin
v_value := 'testdaa11'||i;
v_index := 'test_' || i;
v02(v_index).a = v_value;
v01(v02(v_index).a) := v_value ||i;
raise info 'v02.a : %', v02(v_index).a;
raise info 'v01.first : %', v01.first();
raise info 'v01(testdaa111) : %', v01('testdaa111');
raise info 'v01(v01.first()) : %' ,v01(v01.first());
raise info 'v01(v02(v_index).a) : %' ,v01(v02(v_index).a);
end;
end pck1;
/

call pck1.p1('');

drop package pck1;
drop table t1;

create table blob1(c1 blob);
create or replace procedure testblob1(count int)
IS
begin
execute immediate 'insert into blob1 values(:p1);' using 1::bit(100)::varchar::blob;
end;
/

call testblob1(1);
drop table blob1;

-- test table of as out param
create or replace package pck1 as
type r1 is table of int index by int;
type r2 is record(a int, b int);
procedure p1;
procedure p2(va out r2,vb out r1);
procedure p2(vc int, va out r2,vb out r1);
end pck1;
/
create or replace package body pck1 as
procedure p1 as
va r2;
vb r1;
begin
p2(va, vb);
raise info '%',vb.first;
end;
procedure p2(va out r2, vb out r1) as
vc int;
begin
p2(vc,va,vb);
end;
procedure p2(vc int, va out r2, vb out r1) as
begin
va := (1,2);
vb(2) := 2;
end;
end pck1;
/
call pck1.p1();
drop package pck1;

create or replace package pkgnest002
as
type ty0 is table of integer index by integer;
type ty1 is table of ty0;
type ty3 is table of ty1 ;
procedure p1;
end pkgnest002;
/

create or replace package body pkgnest002
as
procedure p1
is
v1 ty0:=ty0();
v2 ty1:=ty1();
v21 ty1;
v22 ty3;
v31 ty3:=ty3();
begin
raise info 'v1 is %',v1;
raise info 'v31 is %',v31;
v1(1):=1;
v1(2):=2;
v2(1):=v1;
v1(5):=5;
v2(2):=v1;
raise info 'v1 is %',v1(1);
raise info 'v2 is %',v2(1);
raise info 'v2 is %',v2(2);
v31(4):=v21;
raise info 'v31(4) is %', v31(4);
v21(1)(1):=-1;
raise info 'v21(1) is %',  v21(1);
v21(2)(2):=-2;
v31(3):=v21;
v22:=v31;
raise info 'v31 is %', v31(3)(2);
v22:=v2;
end;
end pkgnest002;
/

call pkgnest002.p1();
call pkgnest002.p1();

create or replace package pkgnest_auto
as
type ty1 is table of varchar2(20) index by varchar2;
type ty2 is table of ty1 index by varchar2;
type ty3 is table of ty2 index by varchar2;
function p1() return varchar2(20);
pv1 ty1;
pv2 ty2;
pv3 ty3;
end pkgnest_auto;
/

create or replace package body pkgnest_auto
as
function p1() return varchar2(20)
is
PRAGMA AUTONOMOUS_TRANSACTION;
begin
pv1(1):=10000;
pv1(2):=20000;
pv1(3):=30000;
pv2(1):=pv1;
pv2(2):=pv1;
pv2(3):=pv1;
pv3(1):=pv2;
pv3(2):=pv2;
pv3(3):=pv2;
return pv6.first;
end;
end pkgnest_auto;
/

call pkgnest_auto.p1();

-- nested table of in auto session
create or replace package pck1 as
type r1 is table of int;
type r2 is table of r1;
va r2;
procedure p1;
end pck1;
/

create or replace procedure p2() as
va int;
begin
va := pck1.va(1)(1);
end;
/

create or replace package body pck1 as
procedure p1 as
PRAGMA AUTONOMOUS_TRANSACTION;
begin
p2();
end;
end pck1;
/
call pck1.p1();

create or replace procedure p2() as
va int;
begin
pck1.va(1)(1) := 1;
end;
/

call pck1.p1();
drop procedure p2();
drop package pck1;

create or replace package pkgnest021
 as
 type ty1 is table of varchar2(20);
 type ty2 is table of ty1;
 type ty3 is table of ty2;
 type ty4 is table of ty3;
 type ty5 is table of ty4;
 type ty6 is table of ty5;
 procedure p1;
 pv1 ty1;
 pv2 ty2;
 pv3 ty3; 
 pv4 ty4;
 pv5 ty5; 
 pv6 ty6;
 end pkgnest021;
 /
 
create or replace package body pkgnest021
as
procedure p1
is
v1 ty6;
begin
pv6.extend();
pv6(1)(1)(1)(1)(1)(1):='1'; pv6(1)(1)(1)(1)(1)(2):='2'; pv6(1)(1)(1)(1)(1)(4):='3'; pv6(2)(1)(1)(1)(3)(1):='4'; pv6(2)(1)(1)(1)(3)(2):='5'; pv6(2)(1)(1)(1)(3)(3):='6'; pv6(4)(1)(1)(4)(3)(1):='7'; pv6(4)(1)(1)(5)(3)(2):='8'; pv6(4)(1)(1)(6)(3)(3):='9'; 
end;
end pkgnest021;
/

drop package pkgnest021;

---- clean ----
drop type s_type;
drop type typeA;
drop type typeB;
drop type s_type cascade;
drop type typeC;
drop type typeE;
drop type typeG;
drop type s_type_extend cascade;
drop type typeA_ext;
drop type info cascade;
drop type customer;
drop type mytype cascade;
drop type mytype2;
drop procedure tableof_1;
drop procedure tableof_2;
drop procedure tableof_3;
drop function tableof_6;
drop function tableof_7;
drop function tableof_8;
drop procedure tableof_10;
drop procedure tableof_11;
drop procedure tableof_12;
drop procedure tableof_13;
drop procedure tableof_14;
drop procedure tableof_16;
drop procedure tableof_17;
drop procedure tableof_18;
drop procedure tableof_19;
drop procedure tableof_21;
drop procedure tableof_22;
drop procedure tableof_23;
drop procedure tableof_24;
drop procedure tableof_25;
drop procedure tableof_26;
drop procedure tableof_27;
drop package pcknesttype;
drop procedure tableof_nest2;
drop procedure tableof_nest3;
drop table customers;
drop package pkgnest002;
drop package pkgnest_auto;
drop schema if exists plpgsql_table cascade;
