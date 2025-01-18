.text
.globl foo
foo:
	pushq %rbp
	movq %rsp, %rbp
	movl $10, %eax
	leave
	ret
.type foo, @function
.size foo, .-foo
/* end function foo */

.text
.globl forward_ref
forward_ref:
	pushq %rbp
	movq %rsp, %rbp
	movq %rdi, %rax
	leave
	ret
.type forward_ref, @function
.size forward_ref, .-forward_ref
/* end function forward_ref */

.text
.globl main
main:
	pushq %rbp
	movq %rsp, %rbp
	movl (%rsi), %eax
	leave
	ret
.type main, @function
.size main, .-main
/* end function main */

.section .note.GNU-stack,"",@progbits
