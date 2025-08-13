# C4 Compiler Architecture

## Table of Contents
- AST Parse
- Sema AST
- ASM

## AST Parse
- straight forward parsing of program src to tree
- fails on syntax errors

### Sema Ast
- here there isn't a more traditional pass system, but a graph of lazily phased nodes
in which compile time functions lazily cycle check and evaluate the nodes they need, so when functions are
compiled down to IR, there needs to be little difference between compile time functions and runtime functions,
as they use the same representation with differing rules

## ASM
- very much a stub rn, working on SysV ABI (why did I decide to implement funcalls so early)?
