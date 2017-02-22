.text
main:
lw $s7, size # get size of list
addu $s1, $zero,0  # set counter for # of elems printed
addu $s2, $zero,0  # set offset from Array
j start
quickSort:
addu $s0, $a0,0					#i = left
addu $s1, $a1,0						#j = right
addu $t0, $a0, $a1					#left + right
srl $t0, $t0, 1						#(left + right) / 2
sll $s4, $t0, 2						#array access 
lw $s3, array($s4)					#pivot = arr[(left + right) / 2]
outsideWhile:
	
	slt $at,$s1,$s0
	bne $at,$zero,outsideWhileEnd			#if i > j escape while
	insideWhile1:
		sll $s4, $s0, 2
		lw $t0, array($s4) 			#arr[i]
		slt $at,$t0,$s3
		beq $at,$zero,insideWhile1End		#escape inside if arr[i] >= pivot
		addiu $s0, $s0, 1			#i++
		j insideWhile1
	insideWhile1End:
	#       while (arr[j] > pivot)
        #      		j--;
	insideWhile2:
		sll $s4, $s1, 2
		lw $t0, array($s4) 			#arr[j]
		slt $at,$s3,$t0
		beq $at,$zero,insideWhile2End		#escape inside if arr[i] >= pivot
		subu $s1, $s1, 1			#i++
		j insideWhile2
	insideWhile2End:
	slt $at,$s1,$s0
	bne $at,$zero,whileIfFalse			#if (i <= j) {
		sll $s4, $s0, 2
		lw $s2, array($s4)				#tmp = arr[i]
		sll $s4, $s1, 2
		lw $t0, array($s4)				#access arr[j]
		sll $s4, $s0, 2
		sw $t0, array($s4)				#arr[i] = arr[j]
		sll $s4, $s1, 2
		sw $s2, array($s4)				#arr[j] = tmp;
		addiu $s0, $s0, 1				#i++
		subu $s1, $s1, 1				#j--
	whileIfFalse:
	j outsideWhile
outsideWhileEnd:
bge $a0, $s1, if1False					#if left < j{
	subu $sp, $sp, 12
	sw $ra, 8($sp)
	sw $a0, 4($sp)
	sw $a1, 0($sp)
	addu $a0, $a0,0					#left = left
	addu $a1, $s1,0					#right = j
	jal quickSort
	lw $ra, 8($sp)
	lw $a0, 4($sp)
	lw $a1, 0($sp)
	addu $sp, $sp, 12
if1False:

bge $s0, $a1, if2False
	sub $sp, $sp, 12
	sw $ra, 8($sp)
	sw $a0, 4($sp)
	sw $a1, 0($sp)
	addu $a0, $s0,0					#left = i
	addu $a1, $a1,0					#right = right
	jal quickSort
	lw $ra, 8($sp)
	lw $a0, 4($sp)
	lw $a1, 0($sp)
	addu $sp, $sp, 12
if2False:
jr $ra
start:
addiu $a0, $a0, 0
addu $a1, $s7,0
sub $sp, $sp, 12
sw $ra, 8($sp)
sw $a0, 4($sp)
sw $a1, 0($sp)
jal quickSort
lw $ra, 8($sp)
lw $a0, 4($sp)
lw $a1, 0($sp)
addu $sp, $sp, 12
addu $s1, $zero,0
addu $s2, $zero,0
jr $ra
.data
size: .word 100
array: 7, 5, 4, 1, 6, 8, 3, 2, 9, 0, 8, 3, 2, 4,
 -111, 0, 6, -973, 5, 1, 1, 6, -83, 7, 4, 8, 2, -43, 9, 
 0, 2, 8, 5, 1, 3, 33, 6, 0, 7, 4, 5, 8, 1, 65, 0, 7, 9, 
 2, 3, 4, 7, 9, 21, 2, 5, 1, 8, 6, 34, 4, 2, 8, 4, 78, 0, 
 7, 3, 9, 691, 1, 2, -6, 3, 6, 5, 4, 7, 9, 1, 8, 5, 6, 8,
  1, 3, 2, 0, 9, 7, 4, 9, 3, 2, 1, 7, 5, 6, 8, 0, 4

