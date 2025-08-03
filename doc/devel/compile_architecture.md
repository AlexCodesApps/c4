# C4 Compiler Architecture

## Table of Contents
- AST Parse
- Sema Ast Init
- Sema Ast Declaration
- Sema Ast Completion
- Sema Ast Implementation
- ASM

## AST Parse
- straight forward parsing of program src to tree
- fails on syntax errors

## Sema Ast Init
- fills the global scope with ast stubs
- can't really fail

## Sema Ast Declaration
- goes through and replaces the ast stubs
with structures more suited to semantic analysis
- here global symbol identifiers relationships are linked,
but not truly resolved (cycles still need to be checked)
- can fail on unknown identifier or identifier referencing wrong class of symbol

## Sema Ast Completion
- checks for cycles in types and expressions
- this where comptime evaluation will probably take place
- 'Completes' compile time constructs
- Type Aliases should disappear from types (source of multiple bugs, I think its ok now)
- Lookup strategy is switched to automatically deref type aliases
- Can fail on cycles

## Sema Ast Implementation
- implements the runtime code
- fn ast is implemented on the fly from the ground up similar to an interpreter
- pretty straightforward

## ASM
- very much a stub rn, working on SysV ABI (why did I decide to implement funcalls so early)?
