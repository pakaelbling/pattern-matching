# pattern-matching
This repo implements a simple language with deep pattern matching for case statements and recursive types. It was completed as an assignment for Design of Programming Languages at Wesleyan University (COMP321). The assignment is included in its entirety in ```hw04.pdf```. Original work was done in ```check.sml```, ```step.sml```, ```tasks.fpc```, and the end of ```syntax.sml```. The other files were provided as a part of the assignment.

With a working ```smlnj``` install, do the following in BASH to test:
```
smlnj
CM.make "sources.cm";
Top.file_eval "examples.fpc";
```
or 
```
smlnj
CM.make "sources.cm";
Top.file_eval "tasks.fpc";
```
