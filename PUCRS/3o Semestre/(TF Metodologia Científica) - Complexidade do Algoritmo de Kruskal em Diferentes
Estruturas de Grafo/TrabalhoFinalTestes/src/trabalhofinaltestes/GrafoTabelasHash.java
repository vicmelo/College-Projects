package trabalhofinaltestes;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.PriorityQueue;
import java.util.Scanner;
import java.util.Set;
import java.util.Stack;

//V é o tipo do valor do nodo, E é o tipo do valor do label
public class GrafoTabelasHash<V,E> implements Iterable<V>, IGrafo<V,E>{
	
	private class Node<V,E> implements Comparable<Node<V,E>>, INode<V,E>{
		
		private V value;

		//Key de adjs = nodos destino. Key de incid = nodos origem

		private Map<V,IEdge<V,E>> adjs,incid;//adjs saem do nodo, incid chegam no nodo
		
		private Double dnumber;
				
		public Node(V nodeValue){
			
			value = nodeValue;
			adjs = new HashMap<V,IEdge<V,E>>(); //V é o valor do nodo destino
			incid = new HashMap<V,IEdge<V,E>>(); //V é o valor do nodo origem
			
		}
		
		public void addAdj(E edgeValue, INode<V,E> dest) throws IllegalArgumentException{
			
			//verifica se ja existe adj
			if(adjs.containsKey(dest.getValue())) throw new IllegalArgumentException("The edge from node "+this.getValue()+" to "+dest.getValue()+" already exists");
			
			//add adjacencia
			
			Edge<V,E> newAdj = new Edge<V,E>(this, dest, edgeValue);
			adjs.put(dest.getValue(), newAdj);
			
			//add incid no destino
			
			((Node<V,E>)dest).addIncid(edgeValue,this);
			
		}
		
		private void addIncid(E edgeValue, Node<V,E> orig){
			
			//verifica se ja existe adj
			if(incid.containsKey(orig.getValue())) throw new IllegalArgumentException("The edge from node "+orig.getValue()+" to "+this.getValue()+" already exists");
			
			Edge<V,E> newIncid = new Edge<V,E>(orig, this, edgeValue);
			incid.put(orig.getValue(), newIncid);
			
		}
		
		private void removeAdj(V dest){
			
			IEdge<V,E> edge = this.getAdjs().get(dest);
			
			//Remove o edge da lista de incidentes do nodo destino
			
			edge.getDest().getIncid().remove(this.getValue());
			
			this.getAdjs().remove(dest);
			
		}
		
		public V getValue(){ return value; }
		
		public Map<V,IEdge<V,E>> getAdjs(){ return adjs; }
		
		public Map<V,IEdge<V,E>> getIncid(){ return incid; }
		
		public Double getDNumber() {
			return dnumber;
		}

		public void setDNumber(Double dnumber) {
			this.dnumber = dnumber;
		}
		
		public int compareTo(Node<V, E> n){
			return dnumber.compareTo(n.getDNumber());
		}
		
		public String toString(){
			return value.toString();
		}
	
	}
	
	private class Edge<V,E> implements Comparator, IEdge<V,E>{
		
		private E label;
		private INode<V,E> orig;
		private INode<V,E> dest;
		
		public Edge(INode<V,E> orig, INode<V,E> dest, E label){

			this.label = label;
			this.orig = orig;
			this.dest = dest;
			
		}
		
		public E getLabel(){ return label; }
		
		public INode<V,E> getOrigin(){ return orig; }
		
		public INode<V,E> getDest(){ return dest; }

		@Override
		public int compare(Object o1, Object o2) {
			
			Edge<V,E> e1 = (Edge<V,E>) o1;
			Edge<V,E> e2 = (Edge<V,E>) o2;
			if((Integer)e1.getLabel() > (Integer)e2.getLabel()) return 1;
			if((Integer)e1.getLabel() < (Integer)e2.getLabel()) return -1;
			return 0;
			
		
		}
		
	}
	
	private class CaminLargIterator implements Iterator<V>{
	
		private	List<INode<V,E>> nodosJaVistos;
		private List<INode<V,E>>	filaNodos;
		
		public CaminLargIterator() {
			
			nodosJaVistos = new LinkedList<INode<V,E>>();
			filaNodos = new LinkedList<INode<V,E>>();
			filaNodos.add(originCaminha);
		
		}
		
		@Override
		public boolean hasNext() {
			
			if(filaNodos.isEmpty()) return false;
			return true;
			
		}

		@Override
		public V next() {
			
			if(!hasNext()) return null;
			
			INode<V,E> atual = filaNodos.get(0);
			for(IEdge<V,E> edge : atual.getAdjs().values()){
				
				if(nodosJaVistos.contains(edge.getDest())) continue;
				filaNodos.add(edge.getDest());
				
			}
			
			filaNodos.remove(0);
			nodosJaVistos.add(atual);
			return atual.getValue();
			
		}

		@Override
		public void remove() {
			
			filaNodos.remove(filaNodos.size()-1);
		
		}
		
	}

	private class CaminProfIterator implements Iterator<V>{
		
		private	List<INode<V,E>> nodosJaVistos;
		private Stack<INode<V,E>>	pilhaNodos;
		
		public CaminProfIterator() {
			
			nodosJaVistos = new LinkedList<INode<V,E>>();
			pilhaNodos = new Stack<INode<V,E>>();
			pilhaNodos.push(originCaminha);
		
		}
		
		@Override
		public boolean hasNext() {
			
			if(pilhaNodos.isEmpty()) return false;
			return true;
			
		}

		@Override
		public V next() {
			
			if(!hasNext()) return null;
			
			INode<V,E> atual = pilhaNodos.pop();
			for(IEdge<V,E> edge : atual.getAdjs().values()){
				
				if(nodosJaVistos.contains(edge.getDest())) continue;
				pilhaNodos.push(edge.getDest());
				
			}
			
			nodosJaVistos.add(atual);
			return atual.getValue();
			
		}

		@Override
		public void remove() {
			
			pilhaNodos.pop();
		
		}
		
	}
	
	private class DijkstraResult<D> {
		private D origin;
		private Map<D, D> previousNodes;
		private Map<D, Double> costs;
		
		public DijkstraResult(D origin) {
			this.origin = origin;
			previousNodes = new HashMap<>();
			costs = new HashMap<>();
		}

		public D getOrigin() {
			return origin;
		}
		
		public List<D> getPath(D dest) {
			List<D> res = null;
			D aux;
			
			if (previousNodes.containsKey(dest)) {
				res = new LinkedList<D>();
				res.add(0,dest);
		
				aux = previousNodes.get(dest);
				while (aux !=null) {
					res.add(0, aux);
					aux = previousNodes.get(aux);
				}
			}
			return res;
		}

		public Double getCost(D dest) {
			Double res = -1.0;
			
			if (costs.containsKey(dest))
				res = costs.get(dest);
			
			return res;
		}
		
		public boolean addNode(D it, D previous, Double cost) {
			boolean res = false;
			
			if (!previousNodes.containsKey(it) && it != null &&
				 cost >= 0) {
				previousNodes.put(it, previous);
				costs.put(it, cost);
				res = true;
			}
			
			return res;
		}
		
		public boolean setNode(D it, D previous, Double cost) {
			boolean res = false;
			
			if (previousNodes.containsKey(it) && it != null &&
					cost >= 0) {
				previousNodes.replace(it, previous);
				costs.replace(it, cost);
				res = true;
			}
			
			return res;
		}
		@Override
		public String toString() {
			StringBuilder res = new StringBuilder();
			
			res.append("Origem: " + getOrigin() + "\n");
			for (Map.Entry<D, D> c:previousNodes.entrySet()){
				res.append("Nodo: ");
				res.append(c.getKey());
				res.append(" Anterior: ");
				res.append(c.getValue());
				res.append(" Cost: ");
				res.append(costs.get(c.getKey()));
				res.append("\n");
			}
				
			return res.toString();
		}
		
	}
	
	private Map<V,Node<V,E>> nodeList;
	
	//originCaminha é usado nas operações de caminhamento (é o nodo origem)
	
	private Node<V,E> originCaminha;

	private TipoCamin tipo;

	/**
	 * tipo = TipoCamin.LARGURA
	 */
	public GrafoTabelasHash(){
		
		nodeList = new HashMap<V,Node<V,E>>();
		tipo = TipoCamin.LARGURA;
	
	}
	
	public void addNode(V nodeValue) throws IllegalArgumentException{
		
		//se nodo já existir, da excessão
		
		if(nodeList.containsKey(nodeValue)) throw new IllegalArgumentException("The node "+nodeValue+" already exists");
		
		//adiciona nodo
		
		nodeList.put(nodeValue, new Node<V,E>(nodeValue));
		
	}
	
	public void addEdge(V nodeOrig, V nodeDest, E edgeValue){
		
		Node<V,E> orig = getNode(nodeOrig);
		Node<V,E> dest = getNode(nodeDest);
		
		orig.addAdj(edgeValue, dest);
		
	}
	
	private Node<V,E> getNode(V nodeValue) throws IllegalArgumentException{
		
		Node<V,E> node = nodeList.get(nodeValue);
	
		if(node == null) throw new IllegalArgumentException("The node "+nodeValue+" does not exist");
		
		return nodeList.get(nodeValue);
		
	}
	
	public void removeNode(V nodeValue){
		
		Node<V,E> nodo = nodeList.get(nodeValue);
                
		//Remove as arestas que possuem o nodo como destino
		
		for(IEdge<V,E> incid : nodo.getIncid().values()){
			
			incid.getOrigin().getAdjs().remove(nodeValue);
			
		}
		
		nodeList.remove(nodeValue);
	
	}
	
	public void removeEdge(V origValue, V destValue){
		
		nodeList.get(origValue).removeAdj(destValue);

	}
	
	//Utiliza o algoritmo de Dijkstra e a classe auxiliar DijkstraResult para retornar o menor caminho entre 2 Nodes
	
	public List<INode<V,E>> pathFromTo(V orig, V dest){
		
		//cria um objeto DijkstraResult x, para fins de auxilio na obtencao do caminho
		
		DijkstraResult<INode<V,E>> x = new DijkstraResult<INode<V,E>>(nodeList.get(orig));
		
		//cria um map de inteiros mapeados por nodos
		
		HashMap<Node<V,E>, Double> d = new HashMap<Node<V,E>, Double>();
		
		//inicia o map com o nodo origem e o valor 0
		
		d.put(nodeList.get(orig), 0.0);
		
		//coloca o valor maximo em todos os nodos diferentes de orig
		
		for(V n: nodeList.keySet())
			if (!n.equals(orig)) d.put(nodeList.get(n), Double.MAX_VALUE);
		
		//inicia a fila prioritaria com nodos e adiciona todos os nodos  da nodeList
		//a fila prioritaria se guia pela propriedade dnumber do Node que eh setada usando os valores de d, de acordo com o compareTo de Node
		
		PriorityQueue<Node<V, E>> q = new PriorityQueue<Node<V, E>>(); 
		
		for(V v: nodeList.keySet()){
			
			Node<V, E> aux = nodeList.get(v);
			
			//pra cada valor adicionado na fila, eh definido o dnumber com os valores de d.
			
			aux.setDNumber(d.get(aux).doubleValue());
			q.add(aux);
	
		}
		
		while(q.size()>0){
			
			//remove o elemento com o menor dnumber
			
			Node<V, E> u = q.remove();
			
			//pra cada Node de chave z nas adjacencias de u
			
			for(V z : u.adjs.keySet()){
				
				//auxiliar recebe o valor inteiro do mapa d com chave u.value somado da distancia de u at� o nodo de z
				
				Double aux = d.get(u)+getValue(u.value, z);
				
				//aux2 recebe o nodo de valor z
				
				Node<V, E> aux2 = nodeList.get(z);
				
				//se aux2 esta em q, e aux � menor q o nodo de z
				if(q.contains(aux2)&& aux<d.get(aux2)){
					
					//atualiza valor de aux2 com aux
					
					d.put(aux2, aux);
					
					//remove e atualiza o valor de aux2 em q
					
					q.remove(aux2);
					aux2.setDNumber(aux);
					q.add(aux2);
					
					//grava o Node anterior para fins de caminho
					x.setNode(aux2, u, Double.valueOf(aux));
					x.addNode(aux2, u, Double.valueOf(aux));
					
				}
			}
		}
		
		//retorna o menor caminho para o destino usando o objeto auxiliar x
		
		return x.getPath(nodeList.get(dest));
	}
	
	//retorna a distancia entre orig e dest, caso sejam adjacentes, caso contrario retorna MAX_VALUE
	private Double getValue(V orig, V dest){
		Node<V, E> aux = nodeList.get(orig);
		if(aux.adjs.containsKey(dest))return Double.parseDouble(aux.adjs.get(dest).getLabel().toString());
		else return Double.MAX_VALUE;
	}

	/*
	 * requer label das edges do tipo inteiro. Considera grafo como não-direcionado. Retorna um conjunto de arestas (representando a árvore)
	 */
	public Set<IEdge<V,E>> getMSTKruskal(){
		
		GrafoTabelasHash<V,E> mst = new GrafoTabelasHash<>();
		Set<IEdge<V,E>> A = new HashSet<>();
		                
		HashMap<Node,Set<Node<V,E>>> setsNodes = new HashMap<>();
		List<IEdge> orderedEdges = new ArrayList<>();
		
		//Cria a floresta e a lista de edges desordenada (linha 2-3)
		for(Node<V,E> n : nodeList.values()){
			setsNodes.put(n,makeSet(n));
			//adiciona edges adjacentes de n na lista de edges
			
			for(IEdge<V, E> e : n.adjs.values()){
                            
				//adiciona desordenado
				
				orderedEdges.add(e);
				
			}
			
		}

		//ordena orderedEdges (linha 4)
		Collections.sort(orderedEdges, new Comparator<IEdge>() {

			@Override
			public int compare(IEdge o1, IEdge o2) {
				
				return o1.compare(o1, o2);
				
			}
		
		});
                		
		//unifica sets (linhas 5-8)
		
		for(IEdge<V,E> e : orderedEdges){
			
			Set<Node<V,E>> setOrig = setsNodes.get(e.getOrigin());
			Set<Node<V,E>> setDest = setsNodes.get(e.getDest());
		
			if(setOrig != setDest){
				                                
				//uniao entre A e edge (linha 7)
				A.add(e);
				
				//uniao entre os sets (setOrig add setDest, setDest aponta para setOrig) (linha 8)
				setOrig.addAll(setDest);
				setDest.addAll(setOrig);
				for(Node<V,E> n : setOrig) setsNodes.put(n,setOrig);
				for(Node<V,E> n : setDest) setsNodes.put(n,setOrig);
                                                                				
			}
			
                       

			
		}
                
		return A;
	
        }
	
	/*
	 * Metodo auxiliar para getMSTKruskall();
	 */
	private Set<Node<V,E>> makeSet(Node<V,E> n){
		
		Set<Node<V,E>> u = new HashSet<>();
		u.add(n);
		return u;
		
	}
	
	public String toString(){
		
		StringBuilder graph = new StringBuilder("Grafo:");
		graph.append("\n");
		
		//StringBuilder nodesAdjs = new StringBuilder("Adjs:");
		
		for(Node<V,E> node : nodeList.values()){
			
			graph.append("(");
			graph.append(node.getValue());
			graph.append(",[");
			
			for(IEdge<V,E> edge : node.getAdjs().values()){
				V destValue = edge.getDest().getValue();
				
				graph.append(destValue);
				graph.append("{");
				graph.append(edge.getLabel());
				graph.append("}");
				graph.append(", ");
				
			}
			graph.append("])");
			
		}
		
		
		return graph.toString();
		
	}
	
	public void setCaminhamento(TipoCamin tipo){
		
		this.tipo = tipo;
		
	}
	
	public List<V>	getCaminhoAtom(V nodeOrig, TipoCamin tipo){
		
		if(!(tipo == TipoCamin.LARGURA) && !(tipo == TipoCamin.PROFUNDIDADE)) return null;
		

		List<V> caminhamento = new ArrayList<V>();
		caminhamento.add(nodeOrig);
		
		if(tipo == TipoCamin.LARGURA){
			
			
			int i = 0;

			while(i < caminhamento.size()){
				
				Node atual = getNode(caminhamento.get(i));
				Collection<Edge<V,E>> adjs = atual.getAdjs().values();
				
				for(Edge<V,E> edge : adjs){
					
					if(caminhamento.contains(edge.getDest().getValue())) continue;
					caminhamento.add(edge.getDest().getValue());					
					
				}
				
				i++;
				
			}
			
			return caminhamento;
			
		}else{
			
			Node fst = getNode(caminhamento.get(0));
			Collection<Edge<V,E>> adjs = fst.getAdjs().values();
			List<V> nodes = new ArrayList<V>();
			nodes.add((V) fst.getValue());
			
			for(IEdge<V,E> edge : adjs){
				
				List<V> lista = new ArrayList<V>();
				nodes.addAll(getCamAtomAux(nodes,edge.getDest(), lista));
				
			}
		
			return nodes;
			
		}
		
	}
	
	private List<V> getCamAtomAux(List<V> nodesSoFar, INode orig, List<V> listaRetorno){
		
		Collection<Edge<V,E>> adjs = orig.getAdjs().values();
		List<Node<V,E>> nodes = new ArrayList<Node<V,E>>();
		nodesSoFar.add((V) orig.getValue());
		
		for(Edge<V,E> edge : adjs){
			
			if(nodesSoFar.contains(edge.getDest().getValue())) continue;
			listaRetorno.addAll(getCamAtomAux(nodesSoFar,edge.getDest(),listaRetorno));
			
		}

		return listaRetorno;
		
	}
	
	/**
	 * Encapsula o processo de iteração da operação de caminhamento
	 * Este processo pode ser feita diretamente pelo programador,
	 * através de um loop de repetição. Porém, para usar um loop diretamente, o programador
	 * deve primeiro setar o valor originCaminha usando o método setOrigem(V origem).
	 * @param origem
	 * @return
	 */
	public List<V> getCaminhoIter(V origem, TipoCamin tipo){
		
		//determina a origem do caminhamento e a lista do caminhamento
		setCaminhamento(tipo);
		setOrigem(origem);
		List<V> trav = new ArrayList<V>();
		Iterator it = this.iterator();
		
		while(it.hasNext()){

			trav.add((V)it.next());
			
		}
		
		return trav;
		
	}
	
	public void setOrigem(V origem){
		
		originCaminha = nodeList.get(origem);
		
	}
	
	@Override
	public Iterator<V> iterator() {
	
		if(tipo == TipoCamin.LARGURA) return new CaminLargIterator();
		return new CaminProfIterator();
	
	}
	
 	public static void main(String[] args) {
		
		GrafoTabelasHash<Integer,Integer> grafo = new GrafoTabelasHash<Integer,Integer>();
		
//		g.addNode("A");
//		g.addNode("B");
//		g.addNode("C");
//		g.addNode("D");
//		g.addNode("E");
//		g.addNode("G");
//		g.addNode("F");
//		g.addNode("H");
//		g.addNode("I");
//	
//		g.addEdge("A", "B", 4);
//		g.addEdge("A", "H", 8);
//		g.addEdge("B", "H", 11);
//		g.addEdge("B", "C", 8);
//		g.addEdge("H", "I", 7);
//		g.addEdge("H", "G", 1);
//		g.addEdge("I", "G", 6);
//		g.addEdge("I", "C", 2);
//		g.addEdge("G", "F", 2);
//		g.addEdge("C", "F", 4);
//		g.addEdge("C", "D", 7);
//		g.addEdge("D", "F", 14);
//		g.addEdge("D", "E", 9);
//		g.addEdge("F", "E", 10);
		
//		g.addEdge(1, 2, 300);
//		g.addEdge(1, 3, 200);
//		g.addEdge(2, 4, 1);
//		g.addEdge(2, 5, 1);
//		g.addEdge(4, 8, 25);
//		g.addEdge(3, 6, 2);
//		g.addEdge(3, 7, 2);
//	
//		Set<IEdge<String,Integer>> mst = g.getMSTKruskal();
//		
//		for(IEdge<String,Integer> e : mst) System.out.println(e.getOrigin()+"-["+e.getLabel()+"]->"+e.getDest());
//		
		//Imprime o grafo de acordo com o padrão toString()
		//System.out.println(g.toString());
		
		//Imprime o caminhamento atômico em profundidade a partir de 1
		//System.out.println(g.getCaminhoAtom(1, TipoCamin.PROFUNDIDADE));
		
		//Imprime o caminhamento iterado em largura a partir de 1
		//System.out.println(g.getCaminhoIter(1, TipoCamin.LARGURA));
		
		//Imprime o menor caminho entre o nodo 1 e o nodo 8 considerando a aresta adicionada
		//abaixo:
		//g.addEdge(6, 8, 1);
		//System.out.println(g.pathFromTo(1, 8).toString());
		
                System.out.println(grafo);
                
                Scanner in = new Scanner(System.in);      
                    
                MyTimer timer = new MyTimer();
                System.out.println("Digite a quantidade máxima de nodos para o teste");
                
                int qtdNodos = in.nextInt();
                
                System.out.println("qtdNodos : Tempo");
                timer = new MyTimer();
                
                for(int i = qtdNodos; i < qtdNodos+1; i+=50){
                    grafo = new GrafoTabelasHash<>();
                    timer = new MyTimer();
                    for(int j=0; j < i; j++){

                        grafo.addNode(j);

                    }

                    for(int j=0; j < i-1; j++){

                        grafo.addEdge(j, (j+1), 50);

                    }
                    timer.start();
                    Set<IEdge<Integer,Integer>> s = grafo.getMSTKruskal();
                    timer.stop();
                    System.out.println(i+" : "+timer.getTempo());
                }
                
                
//                for(int j=0; j < qtdNodos; j++){
//
//                    grafo.addNode(j);
//
//                }
//
//                for(int j=1; j < qtdNodos-1; j++){
//
//                    grafo.addEdge(j, (j+1), j+1);
//                    grafo.addEdge(j, (j-1), j+1);
//                }
//                
//                
//                timer.start();
//                
//                Set<IEdge<Integer,Integer>> s = grafo.getMSTKruskal();
//                
//                timer.stop();
//                System.out.println(qtdNodos+" : "+timer.getTempo());
//                
//                System.out.println("Size: "+s.size());
                
//                for(IEdge<Integer,Integer> a : s){
//                    
//                    System.out.println(a.getOrigin()+" "+a.getDest()+" "+a.getLabel());
//                    
//                }
                
	}

}

