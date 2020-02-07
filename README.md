# RT-PROOFS

This repository contains the main Coq proof spec & proof development of the RT-PROOFS project.


## Plan

For now, this is more or less just a "code dump" with a flat hierarchy to get things started.

Going forward, the goal is to both

- restructure the repository as it grows in scope, and to

- add significant documentation to make it easier to bring new collaborators who are not yet familiar with Coq into the project.
 

A brief introduction for the professor can be found here

    git@gitlab.cs.hs-rm.de:almeroth/coq_praesentation.git


## Commit and Development Rules

1. Always follow the project [coding and writing guidelines](doc/guidelines.md).
    This is my PROSA_ Working Dir
    For participating the development please follow this workflow without the git worlflow extension:
 
     https://www.atlassian.com/git/tutorials/comparing-workflows/gitflow-workflow 

    To get the working enviroment follow these instructions:
 
    https://prosa.mpi-sws.org/releases/v0.1/artifact/ 

    WORKFLOW RULES:

    These are the allowed branches:
        master
        Develop
        Features
        Hotfixes
        
        Master must be running.
        Only Tanja Almeroth may push to master.
        
        master ----------------------------------------
                  \       \
                   \       \
                    \       \
        Develop ---------------------------------
                    \         \      
                     \         \      
                      \         \        
                       \         \     
        Feature A       \         --------------
                         \            
                          \  
        Hotfix             --------------------



        Feature B          ------------------

2. Make sure the master branch "compiles" at each commit. This is not true for the early history of the repository, but going forward we should strive to keep it working at all times. 

3. It's ok to develop in a (private) dirty branch, but then clean up and `git-rebase -i` on top of the current master before merging your work into master.

4. It's usually a good idea to ask first on the mailing list before merging a substantial change.

5. Pushing fixes, small improvements, etc. is always ok. 

6. Document the tactics that you use in the [list of tactics](doc/tactics.md).
