.text
.globl main
main:
lui $at,0x1001
ori $a0,$at,0x4
lw $a1,size
j BubbleSort
.text
#$a0 - array
#$a1-array size
#$s0 -array base
#$s1 -array size
#$s2 -outer loop counter
#$s3 -inner loop counter
BubbleSort:
addiu $sp, $sp, -20  
# save stack information
sw $ra, 0($sp)
sw $s0, 4($sp)
# need to keep and restore save registers
sw $s1, 8($sp) 
sw $s2, 12($sp)  
sw $s3, 16($sp)
addu $s0, $a0,0
addu $s1, $a1,0
addiu $s2, $zero, 0
#outer loop counter
OuterLoop:
addiu $t1, $s1, -1
slt $t0, $s2, $t1
beq $t0,$zero,EndOuterLoop
addiu $s3, $zero, 0 #inner loop counter
InnerLoop:
addiu $t1, $s1, -1
sub $t1, $t1, $s2
slt $t0, $s3, $t1
beq $t0,$zero,EndInnerLoop
sll $t4, $s3, 2
# load data[j].  Note offset is 4 bytes
addu $t5, $s0, $t4
lw $t2, 0($t5)
addiu $t6, $t5, 4
# load data[j+1]
lw $t3, 0($t6)
slt $t0, $t3, $t2
beq $t0,$zero,NotGreater
addu $a0, $s0,0
addu $a1, $s3,0
addiu $t0, $s3, 1
addu $a2, $t0,0
lui $at,0x40
ori $s7,$at,0xE4
jalr $s7  
# t5 is &data[j], t6 is &data[j=1]
NotGreater:    
addiu $s3,$s3, 1
j InnerLoop
EndInnerLoop:
addiu $s2, $s2, 1
j OuterLoop
EndOuterLoop:
lw $ra, 0($sp)
#restore stack information
lw $s0, 4($sp)
lw $s1, 8($sp) 
lw $s2, 12($sp)  
lw $s3, 16($sp)  
addiu $sp, $sp 20
jr $ra
# Subprogram: swap
# Purpose: to swap values in an array of integers
# Input parameters:$a0 -the array containing elements to swap
# $a1 -index of element 1
#$a2-index of elelemnt 2
# Side Effects:Array is changed to swap element 1 and 2
Swap:
sll $t0, $a1, 2
# calcualate address of element 1
addu $t0, $a0, $t0
sll $t1, $a2, 2
# calculate address of element 2
addu $t1, $a0, $t1
lw $t2, 0($t0) 
#swap elements
lw $t3, 0($t1)
sw $t2, 0($t1)
sw $t3, 0($t0)
jr $ra
.data 
size: .word 17
array: .word 55 27 -13 5 -44 36 0 8 3 9 -2 14 1000000 2000000 -2000000 -20 2500000
