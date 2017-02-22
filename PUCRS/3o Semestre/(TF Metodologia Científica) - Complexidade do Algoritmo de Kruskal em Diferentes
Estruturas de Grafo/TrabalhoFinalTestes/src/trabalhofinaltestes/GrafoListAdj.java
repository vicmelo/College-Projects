package trabalhofinaltestes;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Scanner;
import java.util.Set;
import trabalhofinaltestes.GrafoTabelasHash;
import trabalhofinaltestes.IEdge;

public class GrafoListAdj<N,E> {

    private int getEdgeSize() {
        return adjs.size();
    }

	class Nodo<N> implements INodo<N>{
		
		N data;
		
		public Nodo(N data){
			
			this.data = data;
			
		}
		
		public N getData(){ return data;}
                
                public String toString(){
                    
                    return data.toString();
                    
                }
		
	}
	
	class Aresta<N,E> implements Comparator, IAresta<N,E>{
		
		E value;
		Nodo<N> origem, destino;
		
		public Aresta(E value, Nodo<N> orig, Nodo<N> dest){
		
			this.value = value;
                        this.origem = orig;
			this.destino = dest;
		
		}
		
		public E getValue(){
			return value;
		}
		
		public INodo<N> getDestino(){
			return destino;
		}
                
                public INodo<N> getOrigem(){
                    return origem;
                }
                
                @Override
		public int compare(Object o1, Object o2) {
			
			Aresta e1 = (Aresta) o1;
			Aresta e2 = (Aresta) o2;
			if((Integer)e1.getValue() > (Integer)e2.getValue()) return 1;
			if((Integer)e1.getValue() < (Integer)e2.getValue()) return -1;
			return 0;
			
		
		}
		
	}
	
	List<Nodo<N>> nodes;	
	
	//lista de nodos, cada "elemento" eh uma lista linkada de pares <Nodo destino, valor da aresta>
	List<LinkedList<IAresta>> adjs;
	
	public GrafoListAdj(){
		
		nodes = new ArrayList<>();
		adjs = new ArrayList<LinkedList<IAresta>>();
		
	}
	
	public boolean addNode(N value){
		
		for(Nodo n : nodes){
			
			if(n.getData() == value) return false;
		
		}
                		
		Nodo<N> novoNodo = new Nodo(value);
		nodes.add(novoNodo);
		adjs.add(getNodeIndex(novoNodo.getData()), new LinkedList<>());
                
		return true;
		
	}
	
	public Integer getNodeIndex(N data){
		
		for(Integer i=0; i< nodes.size();i++){
			
			if(nodes.get(i).getData().equals(data)) return i;
			
		}
		
		return -1;
		
	}
	
	public boolean addAdj(N orig, N dest, E value){
		
		int indOrig = getNodeIndex(orig);
		int indDest = getNodeIndex(dest);
		
		if(indOrig == -1 || indDest == -1) return false;
		
		Aresta aresta = new Aresta(value, nodes.get(indOrig), nodes.get(indDest));
		adjs.get(indOrig).add(aresta);
		
		return true;
		
	}
	
	
	public String toString(){
		
		StringBuffer str = new StringBuffer();
		
		str.append("Nodes:\n");
		for(Nodo n : nodes) str.append(n.getData()+"\n");
		
		str.append("Adjacências:\n");
		
		for(Integer i=0;i<adjs.size();i++){
			
			LinkedList<IAresta> l = adjs.get(i);
			
			
			str.append("("+nodes.get(i).getData()+",{");
			
			boolean primeiroDestino = true;
			
			for(IAresta a : l){
				if(primeiroDestino != true) str.append(",");
				
				str.append(a.getDestino().getData()+"["+a.getValue()+"]");
				
				primeiroDestino = false;
			}
			
			str.append("})");
			
		}
		
		return str.toString();
		
		
	}
        
        /*
	 * requer label das edges do tipo inteiro. Considera grafo como não-direcionado. Retorna um conjunto de arestas (representando a árvore)
	 */
	public Set<IAresta<N,E>> getMSTKruskal(){
		
                                
		GrafoListAdj<N,E> mst = new GrafoListAdj<>();
		Set<IAresta<N,E>> A = new HashSet<>();
		                
		HashMap<INodo<N>,Set<INodo<N>>> setsNodes = new HashMap<>();
		List<IAresta> orderedEdges = new ArrayList<>();
		
		//Cria a floresta e a lista de edges desordenada (linha 2-3)
		for(Integer i=0; i < nodes.size(); i++){
                    
                    INodo<N> n = nodes.get(i);
                    setsNodes.put(n, makeSet(n));
                    //adiciona edges adjacentes de n na lista de edges
                                        
                    for(Integer j=0; j < adjs.get(i).size();j++){
                        //adiciona desordenado
                        orderedEdges.add(adjs.get(i).get(j));
                    }
                             			
		}
                
                
                
		//ordena orderedEdges (linha 4)
		Collections.sort(orderedEdges, new Comparator<IAresta>() {

                    @Override
                    public int compare(IAresta o1, IAresta o2) {

                        return o1.compare(o1, o2);

                    }
		
		});
                
                		
		//unifica sets (linhas 5-8)
		
		for(IAresta e : orderedEdges){
			
			Set<INodo<N>> setOrig = setsNodes.get(e.getOrigem());
			Set<INodo<N>> setDest = setsNodes.get(e.getDestino());
//                        String resultSet = "";	
			if(setOrig != setDest){
				
//                                String origOld = "{";
//                                String destOld = "{";
//                                for(Nodo<N> n : setOrig) origOld+=n.getData()+",";
//                                for(Nodo<N> n : setDest) destOld+=n.getData()+",";
//                                origOld += "}";
//                                destOld += "}";
                                
				//uniao entre A e edge (linha 7)
				A.add(e);
				
				//uniao entre os sets (setOrig add setDest, setDest aponta para setOrig) (linha 8)
				setOrig.addAll(setDest);
				setDest.addAll(setOrig);
				
				for(INodo<N> n : setOrig) setsNodes.put(n,setOrig);
				for(INodo<N> n : setDest) setsNodes.put(n,setOrig);
                                
//                                resultSet = "{";
//                                for(Nodo<N> n : setOrig) resultSet+=n.getData()+",";
//                                resultSet +="}";
                                				
			}
			
                       
		}
                
		return A;
	
        }
        
        /*
	 * Metodo auxiliar para getMSTKruskall();
	 */
	private Set<INodo<N>> makeSet(INodo<N> n){
		
		Set<INodo<N>> u = new HashSet<>();
		u.add(n);
		return u;
		
	}
	
	public static void main(String[] args) {
		GrafoListAdj<Integer, Integer> grafo = new GrafoListAdj<>();
		
//		grafo.addNode("A");
//		grafo.addNode("B");
//		grafo.addNode("C");
//                grafo.addNode("D");
//                grafo.addNode("E");
//		
//                grafo.addAdj("A", "E", 10);
//                grafo.addAdj("A", "C", 80);
//                grafo.addAdj("A", "B", 9);
//                grafo.addAdj("B", "C", 30);
//                grafo.addAdj("B", "E", 27);
//                grafo.addAdj("D", "A", 6);
//                grafo.addAdj("D", "E", 1);
                
		System.out.println(grafo);
                
                Scanner in = new Scanner(System.in);      
                    
                MyTimer timer = new MyTimer();
                System.out.println("Digite a quantidade máxima de nodos para o teste");
                
                int qtdNodos = in.nextInt();
                
                System.out.println("qtdNodos : Tempo");
                timer = new MyTimer();
                
//                for(Integer j=0; j < qtdNodos; ++j){
//
//                    grafo.addNode(j);
//                    
//                }
//                
//                for(Integer j=1; j < qtdNodos; ++j){
//
//                    
//                    grafo.addAdj(j, (j+1), j+1);
//                    grafo.addAdj(j, (j-1), j+1);
//
//                }
//                
//                
//                timer.start();
//                
//                Set<IAresta<Integer,Integer>> s = grafo.getMSTKruskal();
//                
//                timer.stop();
//                System.out.println(qtdNodos+" : "+timer.getTempo());
//                
//                System.out.println("Size: "+s.size());
//                
//                for(IAresta<Integer,Integer> a : s){
//                    
//                    System.out.println(a.getOrigem()+" "+a.getDestino()+" "+a.getValue());
//                    
//                }
            
                for(int i = qtdNodos; i < qtdNodos+1; i+=50){
                    grafo = new GrafoListAdj<>();
                    timer = new MyTimer();
                    for(int j=0; j < i; j++){

                        grafo.addNode(j);

                    }

                    for(int j=0; j < i-1; j++){

                        grafo.addAdj(j, (j+1), 50);

                    }
                    timer.start();
                    Set<IAresta<Integer,Integer>> s = grafo.getMSTKruskal();
                    timer.stop();
                    System.out.println(i+" : "+timer.getTempo());
                }
        }
	
	
}
