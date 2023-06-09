--
-- XC_NODE
--

-- Tests involving node DDLs related to Postgres-XC settings

-- Default values
CREATE NODE dummy_node_coordinator WITH (TYPE = 'coordinator');
CREATE NODE dummy_node_datanode WITH (TYPE = 'datanode');
SELECT node_name, node_type, node_port, node_host FROM pgxc_node
WHERE node_name IN ('dummy_node_coordinator',  'dummy_node_datanode')
ORDER BY 1;
-- test to make sure that node_id is generated correctly for the added nodes
select hashname(node_name) = node_id from pgxc_node
WHERE node_name IN ('dummy_node_coordinator',  'dummy_node_datanode');
-- Some modifications
ALTER NODE dummy_node_coordinator WITH (PORT = 5466, HOST = 'target_host_1');
ALTER NODE dummy_node_datanode WITH (PORT = 5689, HOST = 'target_host_2', PREFERRED);
SELECT node_name, node_type, node_port, node_host, nodeis_preferred FROM pgxc_node
WHERE node_name IN ('dummy_node_coordinator',  'dummy_node_datanode')
ORDER BY 1;
DROP NODE dummy_node_coordinator;
DROP NODE IF EXISTS dummy_node_coordinator;
DROP NODE dummy_node_datanode;
DROP NODE IF EXISTS dummy_node_datanode;

-- Check for error messages
CREATE NODE dummy_node WITH (TYPE = 'dummy'); -- fail
CREATE NODE dummy_node WITH (PORT = 6543, HOST = 'dummyhost'); -- type not specified
CREATE NODE dummy_node WITH (PORT = 99999, TYPE = 'datanode'); -- port value error
CREATE NODE dummy_node WITH (PORT = -1, TYPE = 'datanode'); -- port value error
CREATE NODE dummy_node WITH (TYPE = 'coordinator', PREFERRED = true); -- fail
ALTER NODE dummy_node WITH (PREFERRED = false); -- does not exist
DROP NODE dummy_node; -- does not exist
-- Additinal checks on type and properties
CREATE NODE dummy_node WITH (TYPE = 'datanode');
ALTER NODE dummy_node WITH (TYPE = 'coordinator');
DROP NODE IF EXISTS dummy_node;
CREATE NODE dummy_node WITH (TYPE = 'coordinator');
ALTER NODE dummy_node WITH (PREFERRED);
ALTER NODE dummy_node WITH (PRIMARY);
ALTER NODE dummy_node WITH (TYPE = 'datanode');
DROP NODE IF EXISTS dummy_node;

-- drop node 
START TRANSACTION;
DROP NODE datanode1;
DROP NODE IF EXISTS datanode1;
DROP NODE coordinator3;
DROP NODE IF EXISTS coordinator3;
select node_name from pgxc_node order by node_name;
execute direct on (coordinator2) 'select node_name from pgxc_node order by node_name;';
ABORT;
select node_name from pgxc_node order by node_name;
execute direct on (coordinator2) 'select node_name from pgxc_node order by node_name;';

-- drop node with
DROP NODE coordinator3 with;
DROP NODE coordinator3 with ();
DROP NODE coordinator3 with (datanode1);
DROP NODE coordinator3 with (coordinator3);
DROP NODE IF EXISTS fake_node with (coordinator1, coordinator3);
START TRANSACTION;
DROP NODE datanode1 with (coordinator1);
DROP NODE coordinator3 with (coordinator1);
select node_name from pgxc_node order by node_name;
execute direct on (coordinator2) 'select node_name from pgxc_node order by node_name;';
ABORT;
START TRANSACTION;
DROP NODE datanode1 with (coordinator2);
DROP NODE coordinator3 with (coordinator2);
select node_name from pgxc_node order by node_name;
execute direct on (coordinator2) 'select node_name from pgxc_node order by node_name;';
ABORT;
select node_name from pgxc_node order by node_name;
execute direct on (coordinator2) 'select node_name from pgxc_node order by node_name;';

create table TESTTABLE_t1 (id int, num int) distribute by replication;
execute direct on (coordinator1) 'select * from pgxc_node_str()';
execute direct on (coordinator2) 'select * from pgxc_node_str()';
execute direct on (datanode1) 'select * from pgxc_node_str()';

execute direct on (coordinator1) 'select * from TESTTABLE_t1';
execute direct on (coordinator2) 'select * from TESTTABLE_t1';
execute direct on (datanode1) 'select * from TESTTABLE_t1';

execute direct on (coordinator1) 'execute direct on (coordinator1) ''select * from TESTTABLE_t1''';
execute direct on (coordinator2) 'execute direct on (coordinator1) ''select * from TESTTABLE_t1''';
execute direct on (datanode1) 'execute direct on (coordinator1) ''select * from TESTTABLE_t1''';
execute direct on (coordinator1) 'execute direct on (datanode1) ''select * from TESTTABLE_t1''';
execute direct on (coordinator2) 'execute direct on (datanode1) ''select * from TESTTABLE_t1''';
execute direct on (datanode1) 'execute direct on (datanode1) ''select * from TESTTABLE_t1''';

execute direct on (coordinator1)'select count(*) from gs_wlm_operator_info';
execute direct on (coordinator2)'select count(*) from gs_wlm_operator_info';

drop table TESTTABLE_t1;

execute direct on (datanode1) '';
