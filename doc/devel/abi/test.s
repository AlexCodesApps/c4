	.intel_syntax noprefix
	.file	"test.c"
	.section	.rodata.cst8,"aM",@progbits,8
	.p2align	3, 0x0                          # -- Begin function wool
.LCPI0_0:
	.quad	0x4037000000000000              # double 23
	.text
	.globl	wool
	.p2align	4
	.type	wool,@function
wool:                                   # @wool
	.cfi_startproc
# %bb.0:
	movsd	xmm0, qword ptr [rip + .LCPI0_0] # xmm0 = [2.3E+1,0.0E+0]
	mov	eax, 10
	ret
.Lfunc_end0:
	.size	wool, .Lfunc_end0-wool
	.cfi_endproc
                                        # -- End function
	.ident	"clang version 20.1.8 (Fedora 20.1.8-1.fc42)"
	.section	".note.GNU-stack","",@progbits
	.addrsig
