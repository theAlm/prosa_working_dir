# RT-PROOFS

This repository contains the main Coq proof spec & proof development of the RT-PROOFS project.


## Plan

For now, this is more or less just a "code dump" with a flat hierarchy to get things started.

Going forward, the goal is to both

- restructure the repository as it grows in scope, and to

- add significant documentation to make it easier to bring new collaborators who are not yet familiar with Coq into the project.


## Commit and Development Rules

1. Always follow the project [coding and writing guidelines](doc/guidelines.md).

2. Make sure the master branch "compiles" at each commit. This is not true for the early history of the repository, but going forward we should strive to keep it working at all times. 

3. It's ok to develop in a (private) dirty branch, but then clean up and `git-rebase -i` on top of the current master before merging your work into master.

4. It's usually a good idea to ask first on the mailing list before merging a substantial change.

5. Pushing fixes, small improvements, etc. is always ok. 

6. Document the tactics that you use in the [list of tactics](doc/tactics.md).