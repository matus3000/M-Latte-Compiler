# Compiler for Latter
Following project is a solution for a task done as a part of the course about compilers. For the requirements of the task please lookup file Task.md, for specification of Latte language lookup file Latte.md (Both files are written in Polish, so please use automatic translation if you are not a polish speaker. I did not feel need to translate it by hand because for such simple texts the current state of translators is entirely sufficient.)

## Functionalities
This projects implements following functionalities form Task.md
1. Front-end
2. Back-end LLVM
3. Usage of Phi registers
4. LCSE and GCSE optimizations
5. Objects with virtual methods
6.  

## Running.
Solution uses Makefile to build itself. One needs only basic haskell libraries.

## Remarks
This solution is definetly not well optimized. Especially because it uses for no reason foldl instead of foldl'. However having to fight against time one needs to sacrifice sometimes performance for a delivery of solution.
