#########################################################################
                           SIMPLE KALLOC VERIFIED
#########################################################################


NOTE ABOUT VST VERSION:

Preface.v checks that you are using a version of VST that is well matched. 
If you have installed VST by the standard Coq Platform
or by opam, then it will be found automatically in coq/lib/coq/user-contrib.
If that's the right version (as checked by Preface.v) then everything is easy.

- Compile c-code to Rocq-code: clightgen -normalize <c-file>.c

- In this directory, "make clean" and "make" will clean and make the Rocq-files.

- Edit the ALLVFILES line of the Makefile to compile less or more files,
