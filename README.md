# Full version of SIGMOD '23 paper
* We attach our full version paper to this repository. You can find the pdf document (Efficient_Query_Re_optimization_with_Judicious_Subquery_Selections__full_version_.pdf) under the main directory.


# Compilation
* In ./src directory, we give all modified files and our new-created files (query_split.h/.c). To compile our codes, you need to first get the source codes of PostgreSQL 12.3. And then placing the given files into corresponding file folder. All needed file folders are given by Postgres.
* Adding the given files to the postgres project or do corresponding modification to makefile, and compiling the postgres project.
* When you install our modifed PostgreSQL, the default query processing mode is orignial PostgreSQL. By embedded command "switch to Postgres;", you can switch the current mode to original PostgreSQL as well.


# Reproduction
* After compilation, you can reproduce the results in our paper.
* Query split consists of two parts: query splitting algorithm and execution ordr decision. By command "switch to minsubquery;", "switch to relationshipcenter;" and "switch to entitycenter;", you change the query splitting algorithm. By command "switch to oc;"(cost(q)), "switch to or;"(row(q)), "switch to c_r;"(hybrid_row), "switch to c_rsq;"(hybrid_sqrt), "switch to c_rlg;"(hybrid_log) and "switch to global;" (global_sel), you change the execution ordr decision. 
* To use the default PostgrteSQL, you can enter the command "switch to Postgres;".
* Note that When you enter these commands, the database will return "ERROR: syntax error at or near "switch" at character 1", this is OK. Because PostgreSQL parser cannot identify these code correctly, however, the parameters are actually changed by our embedded code.
* The command "explain" is not supported yet in query split.

# Non-SPJ Support
* We try to make our Non-SPJ extension more stable and will upload the first version soon, as a new branch in the repository, at the beginning of February.
* However, Non-SPJ is not the focus of our paper, and its performance is close to the default Postgres. When you choose the pure SPJ workloads for test, we recommand you use the SPJ version.


# Potential Bugs
* The local buffer would be released after the end of a session. We recommand execute one query each session for reproducing query split, as the local buffer consumpition is very huge in query split. Executing too many queries in one session may lead to some unfixed bugs. In future, we will improve this part.
* Obviously, our work can be further improved. And there would be many potential bugs in our codes. If you meet these bugs, thank you for contacting us. Your contact will greatly help us fix these bugs.
