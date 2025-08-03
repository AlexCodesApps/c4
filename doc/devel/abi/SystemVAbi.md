### System V ABI Documentation

# Stack
## Alignment
- RSP (Stack Pointer) must always be aligned to 16 bytes

# Stack
## Params
- Parameters on the stack are passed directly and not was pointers
- The beginning of parameters on the stack is always aligned to at least 8 bytes
- Parameters go on the stack before the next function frame but are passed in forward order
(Forward meaning RSP - offset)
- The slots start at the stack pointer and grow backwards (RSP + offset) up the stack
- values with alignments bigger than 8 bytes are padded if needed

# General
## Primitive Types
- Integer registers are in order rdi, rdi, rdx, rcx, r8 and r9
- SSE (floating point) registers are xmm0 to xmm7

- Integers go into integer registers and then stack
- (f64, f32) go into SSE registers and then stack

- (i128|u128) act like
```c
struct __attribute__((aligned(16))) {
    u64 higher;
    u64 lower;
}
```
- Other integer types are too niche to document and make sense of rn

## Structs, Arrays, and Unions (Aggregates)
- Aggregates that don't obey proper alignment are always in the stack
With 128 bit numbers split as above, properly aligned aggregates can be split
nicely into 64bit chunks.
- Aggregates bigger than 2 chunks go into memory, except if
    the first chunk comprises only of floats
- Aggregates that contain a memory only field go into memory aswell
- Aggregates are split into their primitives and spread into their appropriate registers,
    with the caveat that if a chunk features both floating point and integer primitives,
    it is passed as an integer (esp in case of a union)
- If not every chunk of the aggregate can go into a register, it is passed in whole into memory

## Returning Values
- An approximation of the above rules for
    integer registers  rax, rdx
    SSE registers xmm0, xmm1
With the extra caveat that if a value is returned by memory,
it becomes a nonaliasing out ptr in rdi

For all practical needs this should be about it. (for now)

# Extra
- Functions are granted 128-bytes past the stack ptr for temporary work
    with signal and interrupt handlers not allowed to modify this 'red zone'
    Don't try this with between function calls though
