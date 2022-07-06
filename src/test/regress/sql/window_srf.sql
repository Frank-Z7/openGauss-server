
create schema windows_srf;
set search_path to windows_srf;

create table empsalary (id int, depname text, empno int, salary int);

INSERT INTO empsalary (id, depname, empno, salary) VALUES 
    (1,'develop',11,5200), (2, 'develop',7,4200),
    (3, 'personnel', 9, 4500), (4, 'personnel', 8, 6000),
    (5, 'sales', 10, 5300) , (6, 'sales', 18, 6200);

explain (costs off, verbose) 
SELECT generate_series(1, id), depname, empno, salary, rank() OVER (PARTITION BY depname ORDER BY salary DESC) FROM empsalary;
SELECT generate_series(1, id), depname, empno, salary, rank() OVER (PARTITION BY depname ORDER BY salary DESC) FROM empsalary;

explain (costs off, verbose) 
SELECT generate_series(id, generate_series(1, 2)), depname, empno, salary, rank() OVER (PARTITION BY depname ORDER BY salary DESC) FROM empsalary;
SELECT generate_series(id, generate_series(1, 2)), depname, empno, salary, rank() OVER (PARTITION BY depname ORDER BY salary DESC) FROM empsalary;


explain (costs off, verbose) 
SELECT id, generate_series(1, id), salary, sum(salary) OVER () FROM empsalary;
SELECT id, generate_series(1, id), salary, sum(salary) OVER () FROM empsalary;


explain (costs off, verbose) 
SELECT id, generate_series(1, id), salary, sum(salary) OVER (ORDER BY salary) FROM empsalary;
SELECT id, generate_series(1, id), salary, sum(salary) OVER (ORDER BY salary) FROM empsalary;

explain (costs off, verbose) 
SELECT generate_series(1,id), sum(salary) OVER w, avg(salary) OVER w
  FROM empsalary
  WINDOW w AS (PARTITION BY depname ORDER BY salary DESC);
SELECT generate_series(1,id), sum(salary) OVER w, avg(salary) OVER w
  FROM empsalary
  WINDOW w AS (PARTITION BY depname ORDER BY salary DESC);


-- windows + sort
explain (costs off, verbose)
SELECT id, generate_series(1, id) as g, salary, sum(salary) OVER (ORDER BY salary) FROM empsalary order by g;
SELECT id, generate_series(1, id) as g, salary, sum(salary) OVER (ORDER BY salary) FROM empsalary order by g;

drop schema windows_srf cascade;
