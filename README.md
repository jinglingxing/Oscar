# Oscar
### Reasons for not cloning the oscarlib 
Since the official oscarlib(https://bitbucket.org/oscarlib/oscar/wiki/Home) on github is not updated for many years, I would like to only share the main files I changed in Oscar for my master project. In the following paragraphs, I will simply explain what I mainly changed.<br />


### Changed in compact table
In the tableCT file, we need to get the support count to calcuate the solution density for our counting-base search. Then, we called the function 'changeCount' in cp/package to update the support count and unique ID for variables and constraints. <br />

### The variable and value heuristic searches
In cp/package, we created an object named CPIntVarOps, it has the same name as the class in which we will create our method to update the supportCount. In object CPIntVarOps, we defined a map named mapcount to store the variable ID, constraint ID and supportCount, while we will define changeCount method to update them in the class CPIntVarOps. The TableCT(compact table) will call the method changeCount to fill the mapcount to update the supportCount.<br />

In cp/package, we also defined our variable heuristic search and value heuristic search.<br />

### The changes in UML
![The changes are in blue](https://github.com/jinglingxing/Oscar/blob/master/Oscar_uml_after.png)
