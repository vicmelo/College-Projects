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
			<-unblock
			v = v+1
		}else{
			select{
				case <- unblock:
					v = v+1
				case <- block:
					v = v-1
			}
		}
	}
}

func Unblock(unblock chan empty){
	unblock<-*new(empty)
}

func readers(block chan empty,unblock chan empty, RN int,wantWrite *bool){
			var wantRead bool = rand.Int31n(2) == 0
			if wantRead{
				block<-*new(empty)
				var wg sync.WaitGroup
				wg.Add(RN)
				startRead,stopRead := make(chan empty),make(chan empty)
				for i := 0; i < RN; i++ {
					go rs(block,unblock,startRead, stopRead,i,&wg, wantWrite)
					
				}
					
				wg.Wait()
				unblock<-*new(empty)
				fmt.Println("<<TODOS OS READERS LIBERARAM>>")
			}
	readers(block,unblock,RN,wantWrite)
}

func rs(block chan empty,unblock chan empty,startRead chan empty, stopRead chan empty,i int,wg *sync.WaitGroup, wantWrite *bool){
	defer wg.Done()
	if(*wantWrite == false){
	
		fmt.Println("Reader",i,"bloqueou")
		reader(block,unblock,startRead,stopRead,i,wg,wantWrite)
		
	}else{
	
		fmt.Println("Reader",i,"não bloqueou")
	
	}
}

func reader(block chan empty, unblock chan empty,startRead chan empty,stopRead chan empty,i int,wg *sync.WaitGroup,wantWrite *bool){
	//aleatório: simulação de escolha externa
	if(*wantWrite == false){
	/*
	R(i) = wantWrite.false -> reading.true -> RAux(i)
	   []
	   wantWrite.true -> reading.false -> R(i)
	*/
		var wantRead bool = rand.Int31n(2) == 0
		if !wantRead{ //escolha externa - aqui, ele opta por read_start -> read_stop -> R(i)
			fmt.Println("Reader",i,"read_start") //startRead
			time.Sleep(time.Duration(rand.Int31n(1000))*time.Millisecond)
			fmt.Println("Reader",i,"read_stop") //stopRead
	/*
	RAux(i) = read_start.i -> VerifR(i)
	   []
	   wantWrite.true -> reading.false -> R(i)
	a verificação com o uso de VerifR já é feita no começo da próxima chamada recursiva
	*/
			reader(block,unblock,startRead,stopRead,i,wg,wantWrite)
		}else{ //aqui, ele opta por unblock -> Proc
			fmt.Println("Reader",i,"unblock")
		}
	}
	
}

func writers(block chan empty,unblock chan empty,WN int,wantWrite *bool){
		for i := 0; i < WN; i++ {
			go write(block,unblock,i,wantWrite)
		}
}

func write(block chan empty,unblock chan empty,index int,wantWrite *bool){
	/*
		W(i) = wantWrite.true -> reading.false -> WAux(i)
	   []
	   wantWrite.false -> W(i)
	*/
	fmt.Println("Writer",index,"wantWrite.true")
	*wantWrite = true
	block<-*new(empty)
	/*
		WAux(i) = block.i -> write_start.i -> write_stop.i -> unblock.i -> WAux(i)
		   []
		   wantWrite.false -> W(i)
	*/
	//liberou. entrada da seção crítica
	fmt.Println("Writer",index,"write_start")
	time.Sleep(time.Duration(rand.Int31n(1000))*time.Millisecond)
	fmt.Println("Writer",index,"write_stop")
	//saída da seção crítica
	fmt.Println("Writer",index,"unblock")
	unblock<-*new(empty)
	write(block,unblock,index,wantWrite)
	*wantWrite = false
	fmt.Println("Writer",index,"wantWrite.false")
}

func main() {
	var WN int = 3
	var RN int = 3
	unblock,block := make(chan empty),make(chan empty)
	var wantWrite bool = false
	go semaphore(unblock,block,1) //SEM(1)
	go writers(block,unblock,WN,&wantWrite) //SYSW
	go readers(block,unblock,RN,&wantWrite) //SYSR
	/*as goroutines semaphore, writers e readers em paralelo representam
	SYSW (writers com semaphore em paralelo) em paralelo com SYSR (readers)
	*/
	time.Sleep(100*time.Second) /*timer de segurança para impedir que o 
	programa termine enquanto as goroutines ainda estão executando
	(não conseguimos contornar isso de uma forma mais inteligente)
	*/
}
