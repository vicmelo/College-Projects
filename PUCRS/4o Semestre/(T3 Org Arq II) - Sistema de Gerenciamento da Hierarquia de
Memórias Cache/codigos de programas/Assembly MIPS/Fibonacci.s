.text
.globl main
li $v0,20
addu $a0,$v0,0
addu $a1,$a0,0
main:
addiu $sp, $sp, -12
sw $ra, 8($sp)
sw $s0, 4($sp)
sw $s1, 0($sp)
addu $s0,$a0,0
li $v0, 1 # return value for terminal condition
subu $t2,$s0,2
blez $t2,fibonacciExit #check terminal condition
addi $a0, $s0, -1 # set args for recursive call to f(n-1)
jal main
addu $s1,$v0,0 # store result of f(n-1) to s1
addiu $a0, $s0, -2 # set args for recursive call to f(n-2)
jal main
addu $v0, $s1, $v0 # add result of f(n-1) to it
fibonacciExit:
lw $ra, 8($sp)
lw $s0, 4($sp)
lw $s1, 0($sp)
addiu $sp, $sp, 12
jr $ra
## End of function fibonacci
