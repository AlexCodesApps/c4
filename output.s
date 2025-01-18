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
