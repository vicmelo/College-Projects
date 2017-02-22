/*
Problema dos Readers/Writers
Autores: Vinicius Sesti, Victor Melo
*/

package main

import (
	"fmt"
	"time"
	"math/rand"
	"sync"
)

type empty struct{}

func semaphore(unblock chan empty, block chan empty, v int){
	//apenas um semáforo
	for{
		if(v == 0){
			<-unblock //unblock?j:Procs->SEM(s+1)
			v = v+1
		}else{
			select{
				case <- unblock: //unblock?j:Procs->SEM(s+1)
					v = v+1
				case <- block: //block?j:Procs->SEM(s-1)
					v = v-1
			}
		}
	}
}

func Unblock(unblock chan empty){
	unblock<-*new(empty)
}

func readers(block chan empty,unblock chan empty, RN int){
			var wantRead bool = rand.Int31n(2) == 0
			if wantRead{
				block<-*new(empty) //block.(N+1) (sincronizado)
				var wg sync.WaitGroup
				wg.Add(RN)
				startRead,stopRead := make(chan empty),make(chan empty)
				for i := 0; i < RN; i++ { //RDRS = || i: Readers @ [RI(i)] Proc(i,1)
						go rs(block,unblock,startRead, stopRead,i,&wg)		
					}
				wg.Wait() /*/espera todos os readers pararem de ler
				quando todos pararem, libera o recurso				
				*/
				unblock<-*new(empty) //unblock.(N+1) (sincronizado)
				fmt.Println("<<TODOS OS READERS LIBERARAM>>")
			}
	readers(block,unblock,RN)
}

func rs(block chan empty,unblock chan empty,startRead chan empty, stopRead chan empty,i int,wg *sync.WaitGroup){
	defer wg.Done() //ao fim da execução, sinaliza ao WaitGroup que liberou o recurso
	fmt.Println("Reader",i,"bloqueou")
	//RS(i) = block.(N+1) -> R(i)
	reader(block,unblock,startRead,stopRead,i,wg)
}

func reader(block chan empty, unblock chan empty,startRead chan empty,stopRead chan empty,i int,wg *sync.WaitGroup){
	//aleatório: simulação de escolha externa
	/*
	R(i) = read_start.i -> read_stop.i -> R(i)
	   []
	   unblock.(N+1) -> Proc(i,1)
	*/
	var wantRead bool = rand.Int31n(2) == 0
	if !wantRead{ //escolha externa - aqui, ele opta por read_start -> read_stop -> R(i)
		fmt.Println("Reader",i,"entrando na secao critica.") //startRead
		time.Sleep(time.Duration(rand.Int31n(1000))*time.Millisecond)
		fmt.Println("Reader",i,"saindo da secao critica.") //stopRead
		reader(block,unblock,startRead,stopRead,i,wg)
	}else{ //aqui, ele opta por unblock -> Proc
		fmt.Println("Reader",i,"liberou.")
	}
}

func writers(block chan empty,unblock chan empty,WN int){
		for i := 0; i < WN; i++ { //WRTS = || i: Writers @ [WI(i)] Proc(i,0)
			go write(block,unblock,i)
		}
}

func write(block chan empty,unblock chan empty,index int){
		//W(i) = block.i -> write_start.i -> write_stop.i -> unblock.i -> Proc(i,0)
		fmt.Println("Writer",index,"block")
		block<-*new(empty)
		//liberou. entrada da seção crítica
		fmt.Println("Writer",index,"start_write")
		time.Sleep(time.Duration(rand.Int31n(1000))*time.Millisecond)
		fmt.Println("Writer",index,"stop_write")
		//saída da seção crítica
		fmt.Println("Writer",index,"unblock")
		unblock<-*new(empty)
		write(block,unblock,index)
}

func main() {
	var WN int = 3
	var RN int = 3
	unblock,block := make(chan empty),make(chan empty)
	go semaphore(unblock,block,1) //SYS = (WRTS ||| RDRS) [{|...|}] SEM(1)
	go writers(block,unblock,WN)
	go readers(block,unblock,RN)
	time.Sleep(100*time.Second) /*timer de segurança para impedir que o 
	programa termine enquanto as goroutines ainda estão executando
	(não conseguimos contornar isso de uma forma mais inteligente)
	*/
}

