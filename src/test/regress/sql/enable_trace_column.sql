show enable_trace_column;
--ok
SELECT num::int8 as r, generate_series(1, 3) FROM (VALUES (65538)) AS t (num);
SELECT num::int8 as r FROM (VALUES (65538)) AS t (num);

--failed
SELECT num::int2 as r, generate_series(1, 3) FROM (VALUES (65538)) AS t (num);
SELECT num::int2 as r FROM (VALUES (65538)) AS t (num);

set enable_trace_column=off;

--ok
SELECT num::int8 as r, generate_series(1, 3) FROM (VALUES (65538)) AS t (num);
SELECT num::int8 as r FROM (VALUES (65538)) AS t (num);

--failed
SELECT num::int2 as r, generate_series(1, 3) FROM (VALUES (65538)) AS t (num);
SELECT num::int2 as r FROM (VALUES (65538)) AS t (num);


