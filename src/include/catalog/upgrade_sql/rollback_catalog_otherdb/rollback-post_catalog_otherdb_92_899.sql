do $$
DECLARE
ans boolean;
BEGIN
    for ans in select case when count(*)=1 then true else false end as ans  from (select extname from pg_extension where extname='dolphin' and extversion = '1.1')
    LOOP
        if ans = true then
            ALTER EXTENSION dolphin UPDATE TO '1.0';
        end if;
        exit;
    END LOOP;
END$$;