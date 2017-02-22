.text
.globl main

main:
        j MyMain
DesvioParaTratamentoDeInterrupcoes:
		
        subu $sp, $sp, 4
        sw $ra, 0($sp)
        la $k0, EnderecoUART
        lw $k0, 0($k0)
        sll $k0, $k0, 0x02
        la $k1, TabelaDeInterrupcoes
        addu $k0, $k0, $k1
        jalr $k0
        lw $ra, 0($sp)
        addiu $sp, $sp, 4
        eret
        jr $ra

TabelaDeInterrupcoes:
        j UART_CIN
        j UART_COUT

# ROTINAS PARA TRATAR AS INTERRUPÇÕES
#####################################
UART_CIN:
        subu $sp, $sp, 40
        sw $t0, 0($sp)
		sw $t1, 4($sp)
        sw $t2, 8($sp)
		sw $t3, 12($sp)
       	sw $t4, 16($sp)
		sw $t5, 20($sp)
       	sw $t6, 24($sp)
		sw $t7, 28($sp)
		sw $t8, 32($sp)
		sw $t9, 36($sp)
		sw $ra, 40($sp)

#Procura um espaço em branco a partir de EnderecoUART+12
		la $t0,EnderecoUART
		lw $t0,8($t0) #carrega RR 
		la $t2,EnderecoUART+12 #Carrega o endereco
		lw $t3,0($t2) #Carrega o valor em EnderecoUART+12
		beq $t3,$0,FoundZero	
LookForZero:
		addiu $t2,$t2,4 
		lw $t3,0($t2) #carrega o próximo valor
		bne $t3,$0,LookForZero
FoundZero:			#achei um zero! posso guardar o t3 aqui!
	sw $t3,0($t2)
    
	lw $t0, 0($sp)
	lw $t1, 4($sp)
    lw $t2, 8($sp)
	lw $t3, 12($sp)
    lw $t4, 16($sp)
	lw $t5, 20($sp)
    lw $t6, 24($sp)
	lw $t7, 28($sp)
	lw $t8, 32($sp)
	lw $t9, 36($sp)
	lw $ra, 40($sp)
    addiu $sp, $sp, 44
    jr $ra

#############################################
UART_COUT:
		subu $sp, $sp, 40
		sw $t0, 0($sp)
		sw $t1, 4($sp)
		sw $t2, 8($sp)
		sw $t3, 12($sp)
		sw $t4, 16($sp)
		sw $t5, 20($sp)
		sw $t6, 24($sp)
		sw $t7, 28($sp)
		sw $t8, 32($sp)
		sw $t9, 36($sp)
		sw $ra, 40($sp)
		
		#De onde sai o dado para o rw?
		sw $t0,4(EnderecoUART) #Guarda um dado no rw para enviar

		lw $t0, 0($sp)
		lw $t1, 4($sp)
		lw $t2, 8($sp)
		lw $t3, 12($sp)
		lw $t4, 16($sp)
		lw $t5, 20($sp)
		lw $t6, 24($sp)
		lw $t7, 28($sp)
		lw $t8, 32($sp)
		lw $t9, 36($sp)
		lw $ra, 40($sp)
		addiu $sp, $sp, 44

# INICIO DO PROGRAMA DO USUÁRIO NO ENDERE€O
#############################################
MyMain:
        li $t0, 0
        li $t1, 0
        li $t2, 0
SaltoMyMain:
        addiu $t0, $t0, 1
        addu $t1, $t1, $t0
        addu $t2, $t1, $t0
        j SaltoMyMain

# ENDEREÇO DA UART
##################
.data  EnderecoUART: 0xFFE00000
MeuDado: .asciiz "T2 - Organizacao e Arquitetura de Computadores II - 2016/2"

