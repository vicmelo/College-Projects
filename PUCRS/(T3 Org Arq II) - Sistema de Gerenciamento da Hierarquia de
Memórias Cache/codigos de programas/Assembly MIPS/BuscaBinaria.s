	.text
	.globl main
	main:
fac:
	addiu            $sp,$sp,-8		# push space for activation frame
	sw		$s0,0($sp)		# save $s0, which we use
	sw		$ra,4($sp)		# save return address
	addu           	$s0,$a0,0			# get argument ($a0)
	li		$v0,0x00000001	# 1
	beq		$s0,$v0,L2		# end of recursion?
	addiu            $a0,$s0,-1		# set up argument (f-1)
	jal		fac			# recursive call 
	mult            $v0,$s0			# multiply
	mflo            $v0			# return mul result
	j		L3			# exit procedure via epilogue
	
L2:
	li		$v0,0x00000001          # return value
L3:
	lw		$ra,4($sp)		# restore $ra
	lw		$s0,0($sp)		# restore $s0
	addiu            $sp,$sp,8		# pop activation frame
	jr		$ra				# return
