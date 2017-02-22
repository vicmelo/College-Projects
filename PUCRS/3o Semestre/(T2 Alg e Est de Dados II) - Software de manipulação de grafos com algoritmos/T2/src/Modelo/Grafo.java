package Modelo;

import Modelo.INode.Marca;
import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;
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
import java.util.Set;
import java.util.Stack;

//V é o tipo do valor do nodo, E é o tipo do valor do label
public class Grafo<V, E> implements Iterable<V>, IGrafo<V, E>,Serializable {

    private Map<V, INode<V, E>> nodeList;

    //originCaminha é usado nas operações de caminhamento (é o nodo origem)
    private INode<V, E> originCaminha;

    private TipoCamin tipo;
        
    private class Node<V, E> implements INode<V, E>, Serializable {

        private Marca mark = Marca.BRANCO;
        
        private final V value;

        //Key de adjs = nodos destino. Key de incid = nodos origem
        private final Map<V, IEdge<V, E>> adjs, incid;//adjs saem do nodo, incid chegam no nodo

        private Double dnumber;

        public Node(V nodeValue) {

            value = nodeValue;
            adjs = new HashMap<>(); //V é o valor do nodo destino
            incid = new HashMap<>(); //V é o valor do nodo origem

        }

        @Override
        public void addAdj(E edgeValue, INode<V, E> dest) throws IllegalArgumentException {

            //verifica se ja existe adj
            if (adjs.containsKey(dest.getValue())) {
                throw new IllegalArgumentException("The edge from node " + this.getValue() + " to " + dest.getValue() + " already exists");
            }

            //add adjacencia
            Edge<V, E> newAdj = new Edge<>(this, dest, edgeValue);
            adjs.put(dest.getValue(), newAdj);

            //add incid no destino
            ((Node<V, E>) dest).addIncid(edgeValue, this);

        }

        private void addIncid(E edgeValue, Node<V, E> orig) {

            //verifica se ja existe adj
            if (incid.containsKey(orig.getValue())) {
                throw new IllegalArgumentException("The edge from node " + orig.getValue() + " to " + this.getValue() + " already exists");
            }

            Edge<V, E> newIncid = new Edge<>(orig, this, edgeValue);
            incid.put(orig.getValue(), newIncid);

        }

        @Override
        public void removeAdj(V dest) {

            IEdge<V, E> edge = this.getAdjs().get(dest);

            //Remove o edge da lista de incidentes do nodo destino
            edge.getDest().getIncid().remove(this.getValue());

            this.getAdjs().remove(dest);

        }

        @Override
        public V getValue() {
            return value;
        }

        @Override
        public Map<V, IEdge<V, E>> getAdjs() {
            return adjs;
        }

        @Override
        public Map<V, IEdge<V, E>> getIncid() {
            return incid;
        }

        @Override
        public Double getDNumber() {
            return dnumber;
        }

        @Override
        public void setDNumber(Double dnumber) {
            this.dnumber = dnumber;
        }

        @Override
        public int compareTo(INode<V, E> n) {
            return dnumber.compareTo(n.getDNumber());
        }

        @Override
        public String toString() {
            return value.toString();
        }

        
        @Override
        public Marca getMark() { return mark; }

        @Override
        public void setMark(Marca m) { mark = m; }
        
        
    }

    private class Edge<V, E> implements Comparator, IEdge<V, E>, Serializable {

        private final E label;
        private final INode<V, E> orig;
        private final INode<V, E> dest;

        public Edge(INode<V, E> orig, INode<V, E> dest, E label) {

            this.label = label;
            this.orig = orig;
            this.dest = dest;

        }

        @Override
        public E getLabel() {
            return label;
        }

        @Override
        public INode<V, E> getOrigin() {
            return orig;
        }

        @Override
        public INode<V, E> getDest() {
            return dest;
        }

        @Override
        public int compare(Object o1, Object o2) {

            Edge<V, E> e1 = (Edge<V, E>) o1;
            Edge<V, E> e2 = (Edge<V, E>) o2;
            if ((Integer) e1.getLabel() > (Integer) e2.getLabel()) {
                return 1;
            }
            if ((Integer) e1.getLabel() < (Integer) e2.getLabel()) {
                return -1;
            }
            return 0;

        }

    }

    private class CaminLargIterator implements Iterator<V> {

        private List<INode<V, E>> nodosJaVistos;
        private List<INode<V, E>> filaNodos;

        public CaminLargIterator() {

            nodosJaVistos = new LinkedList<>();
            filaNodos = new LinkedList<>();
            filaNodos.add(originCaminha);

        }

        @Override
        public boolean hasNext() {

            return !filaNodos.isEmpty();

        }

        @Override
        public V next() {

            if (!hasNext()) {
                return null;
            }

            INode<V, E> atual = filaNodos.get(0);

            for (IEdge<V, E> edge : atual.getAdjs().values()) {

                if (nodosJaVistos.contains(edge.getDest())) {
                    continue;
                }
                filaNodos.add(edge.getDest());

            }

            filaNodos.remove(0);
            nodosJaVistos.add(atual);
            return atual.getValue();

        }

        @Override
        public void remove() {

            filaNodos.remove(filaNodos.size() - 1);

        }

    }

    private class CaminProfIterator implements Iterator<V> {

        private List<INode<V, E>> nodosJaVistos;
        private Stack<INode<V, E>> pilhaNodos;

        public CaminProfIterator() {

            nodosJaVistos = new LinkedList<>();
            pilhaNodos = new Stack<>();
            pilhaNodos.push(originCaminha);

        }

        @Override
        public boolean hasNext() {

            return !pilhaNodos.isEmpty();

        }

        @Override
        public V next() {

            if (!hasNext()) {
                return null;
            }

            INode<V, E> atual = pilhaNodos.pop();

            for (IEdge<V, E> edge : atual.getAdjs().values()) {

                if (nodosJaVistos.contains(edge.getDest())) {
                    continue;
                }
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
    
   //usado no algoritmo de ordenação topológica (para não alterar o grafo original, assim o usuário pode continuar executando algoritmos no grafo original).
   public static Grafo deepClone(Grafo object) {
       
        try {
          ByteArrayOutputStream baos = new ByteArrayOutputStream();
          ObjectOutputStream oos = new ObjectOutputStream(baos);
          oos.writeObject(object);
          ByteArrayInputStream bais = new ByteArrayInputStream(baos.toByteArray());
          ObjectInputStream ois = new ObjectInputStream(bais);
          return (Grafo) ois.readObject();
        }
        catch (Exception e) {
          e.printStackTrace();
          return null;
        }
   }

    public AlgorithmReport ordTopologica() throws Exception{
        
        Grafo grafoCopia = Grafo.deepClone(this);
        
        if(!grafoCopia.aciclico()) throw new Exception("Grafo contém ciclos");
        
        AlgorithmReport algReport = new AlgorithmReport();
        Report state = new Report();
        
        List<INode<V, E>> listaOrdenada = new LinkedList<>();
        Stack<INode<V, E>> nodosSemIncid = new Stack<>();
        HashMap<V, INode<V, E>> aux = new HashMap<>(grafoCopia.nodeList);
        
        for (V v : aux.keySet()) {
            
            INode n = aux.get(v);
            
            if (n.getIncid().isEmpty()) {
                
                nodosSemIncid.push(n);
                
            }
            
        }
        
        while (!nodosSemIncid.isEmpty()) {
            
            INode<V,E> n = nodosSemIncid.pop();
            listaOrdenada.add(n);
            
            state.addNode(nodeList.get(n.getValue()));
            
            for(IEdge<V,E> e : n.getAdjs().values()){
                            
                state.addEdge(e.getOrigin().getValue(), e.getDest().getValue(), e.getLabel());
                
            } 
            algReport.addState(state);
            
            Object[] values = n.getAdjs().keySet().toArray();
            
            for (int i = 0; i < values.length; i++) {
                V v = (V) values[i];
                INode m = aux.get((V) v);
                
                IEdge edgeState = (IEdge) n.getAdjs().get(v);
  
                n.removeAdj((V) v);
                if (m.getIncid().isEmpty()) {
                    nodosSemIncid.push(m);
                    
                }
            }

        }
        
        algReport.setReturn(listaOrdenada); // List<INode<V, E>>
                
        return algReport;
        
    }
    
    //não tá funcionando pra todos os casos
    private boolean aciclico() {
        resetMarks();
        V values[] = (V[]) nodeList.keySet().toArray();
        for(int i=0; i<values.length; i++){
            INode n = nodeList.get(values[i]);
            if(n.getMark() == Marca.PRETO) continue;
            n.setMark(Marca.CINZA);
            if(aciclicoAux(n)) return false;
        }
        return true;
    }
    private boolean aciclicoAux(INode n) {
        V[] values = (V[]) n.getAdjs().keySet().toArray();
        INode z;
        for(int i=0; i<values.length; i++){
            z = nodeList.get(values[i]);
            if(z.getMark() == Marca.PRETO) continue;
            if(z.getMark() == Marca.CINZA) return true;
            z.setMark(Marca.CINZA);
            if(aciclicoAux(z)) return true;
        }
        n.setMark(Marca.PRETO);
        return false;
    }
    
    public AlgorithmReport caminhoCritico(V orig, V dest) {
        try{
            AlgorithmReport algReport = new AlgorithmReport();
            Report state = new Report();

            //cria um objeto DijkstraResult x, para fins de auxilio na obtencao do caminho
            DijkstraResult<INode<V, E>> x = new DijkstraResult<>(nodeList.get(orig));
            //cria um map de inteiros mapeados por nodos
            HashMap<INode<V, E>, Double> d = new HashMap<>();

            //inicia o map com o nodo origem e o valor 0
            d.put(nodeList.get(orig), 0.0);

            //coloca o valor minimo em todos os nodos diferentes de orig
            for (V n : nodeList.keySet()) {
                if (!n.equals(orig)) {
                    d.put(nodeList.get(n), -Double.MAX_VALUE);
                }
            }

            //inicia a fila prioritaria com nodos e adiciona todos os nodos  da nodeList
            //a fila prioritaria se guia pela propriedade dnumber do Node que eh setada usando os valores de d, de acordo com o compareTo de Node
            PriorityQueue<INode<V, E>> q = new PriorityQueue<>(nodeList.keySet().size(), Collections.reverseOrder());

            for (V v : nodeList.keySet()) {

                INode<V, E> aux = nodeList.get(v);

                //pra cada valor adicionado na fila, eh definido o dnumber com os valores de d.
                aux.setDNumber(d.get(aux));
                q.add(aux);

            }

            while (q.size() > 0) {

                //remove o elemento com o maior dnumber por estar na ordem reversa
                INode<V, E> u = q.remove();


                //pra cada Node de chave z nas adjacencias de u
                for (V z : u.getAdjs().keySet()) {

                    //distancia de u até z, se não há então é -Double.MAX_VALUE;
                    Double aresta = getValueMin(u.getValue(), z);
                    //auxiliar recebe o valor inteiro do mapa d com chave u.value somado da distancia de u at� o nodo de z
                    Double aux = d.get(u) + aresta;

                    //aux2 recebe o nodo de valor z
                    INode<V, E> aux2 = nodeList.get(z);

                    //se aux � maior q o nodo de z
                    if ( aux > d.get(aux2)) {
                        //atualiza valor de aux2 com aux
                        d.put(aux2, aux);

                        //remove e atualiza o valor de aux2 em q
                        q.remove(aux2);
                        aux2.setDNumber(aux);
                        q.add(aux2);

                        //grava o Node anterior para fins de caminho
                        x.setNode(aux2, u, aux);
                        x.addNode(aux2, u, aux);

                    }
                }
            }


            //relatório
            List<INode<V,E>> resultado =  x.getPath(nodeList.get(dest));
            for(int i=0; i < resultado.size(); i++){

                state.addNode(resultado.get(i));
                if(i != 0){
                    IEdge<V,E> edge = resultado.get(i).getIncid().get(resultado.get(i-1).getValue());

                    state.addEdge(edge.getOrigin().getValue(),edge.getDest().getValue(),edge.getLabel());

                }

                algReport.addState(state);

            }

            //retorna o menor caminho para o destino usando o objeto auxiliar x
            algReport.setReturn(resultado); // retorno do tipo List<INode<V, E>>

            return algReport;
        }catch(NullPointerException e){
            
            return null;
            
        }
    }
	
    private Double getValueMin(V orig, V dest){
        Node<V, E> aux = (Node) nodeList.get(orig);
        if (aux.adjs.containsKey(dest)) {
            return Double.parseDouble(aux.adjs.get(dest).getLabel().toString());
        } else {
            return -Double.MAX_VALUE;
        }
    }

    private void resetMarks() {
        for (V v : nodeList.keySet()) {
            nodeList.get(v).setMark(Marca.BRANCO);
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
                res = new LinkedList<>();
                res.add(0, dest);

                aux = previousNodes.get(dest);
                while (aux != null) {
                    res.add(0, aux);
                    aux = previousNodes.get(aux);
                }
            }
            return res;
        }

        public Double getCost(D dest) {
            Double res = -1.0;

            if (costs.containsKey(dest)) {
                res = costs.get(dest);
            }

            return res;
        }

        public boolean addNode(D it, D previous, Double cost) {
            
            boolean res = false;

            if (!previousNodes.containsKey(it) && it != null
                    && cost >= 0) {
                previousNodes.put(it, previous);
                costs.put(it, cost);
                res = true;
            }

            return res;
        }

        public boolean setNode(D it, D previous, Double cost) {
            boolean res = false;

            if (previousNodes.containsKey(it) && it != null
                    && cost >= 0) {
                previousNodes.replace(it, previous);
                costs.replace(it, cost);
                res = true;
            }

            return res;
        }

        @Override
        public String toString() {
            StringBuilder res = new StringBuilder();

            res.append("Origem: ").append(getOrigin()).append("\n");
            for (Map.Entry<D, D> c : previousNodes.entrySet()) {
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

    /**
     * tipo = TipoCamin.LARGURA
     */
    public Grafo() {

        nodeList = new HashMap<>();
        tipo = TipoCamin.LARGURA;

    }

    
    public List<INode<V, E>> getNodes(){
        
        List<INode<V, E>> nodes = new LinkedList<>();
        for(INode<V, E> n : nodeList.values()) nodes.add(n);
        
        return nodes;
        
    }
    
    @Override
    public void addNode(V nodeValue) throws IllegalArgumentException {

        //se nodo já existir, da excessão
        if (nodeList.containsKey(nodeValue)) {
            throw new IllegalArgumentException("The node " + nodeValue + " already exists");
        }

        //adiciona nodo
        nodeList.put(nodeValue, new Node<>(nodeValue));

    }

    @Override
    public void addEdge(V nodeOrig, V nodeDest, E edgeValue) {

        INode<V, E> orig = getNode(nodeOrig);
        INode<V, E> dest = getNode(nodeDest);

        orig.addAdj(edgeValue, dest);

    }

    private INode<V, E> getNode(V nodeValue) throws IllegalArgumentException {

        INode<V, E> node = nodeList.get(nodeValue);

        if (node == null) {
            throw new IllegalArgumentException("The node " + nodeValue + " does not exist");
        }

        return nodeList.get(nodeValue);

    }

    @Override
    public void removeNode(V nodeValue) {

        INode<V, E> nodo = nodeList.get(nodeValue);

        //Remove as arestas que possuem o nodo como destino
        for (IEdge<V, E> incid : nodo.getIncid().values()) {

            incid.getOrigin().getAdjs().remove(nodeValue);

        }
        
        for (IEdge<V, E> adj : nodo.getAdjs().values()) {

            adj.getDest().getIncid().remove(nodeValue);

        }

        nodeList.remove(nodeValue);

    }

    @Override
    public void removeEdge(V origValue, V destValue) {

        nodeList.get(origValue).removeAdj(destValue);

    }

    //Utiliza o algoritmo de Dijkstra e a classe auxiliar DijkstraResult para retornar o menor caminho entre 2 Nodes
    @Override
    public AlgorithmReport pathFromTo(V orig, V dest) {
        try{
            AlgorithmReport algReport = new AlgorithmReport();
            Report state = new Report();

            //cria um objeto DijkstraResult x, para fins de auxilio na obtencao do caminho
            DijkstraResult<INode<V, E>> x = new DijkstraResult<>(nodeList.get(orig));

            //cria um map de inteiros mapeados por nodos
            HashMap<INode<V, E>, Double> d = new HashMap<>();

            //inicia o map com o nodo origem e o valor 0
            d.put(nodeList.get(orig), 0.0);

            //coloca o valor maximo em todos os nodos diferentes de orig
            for (V n : nodeList.keySet()) {
                if (!n.equals(orig)) {
                    d.put(nodeList.get(n), Double.MAX_VALUE);
                }
            }

            //inicia a fila prioritaria com nodos e adiciona todos os nodos  da nodeList
            //a fila prioritaria se guia pela propriedade dnumber do Node que eh setada usando os valores de d, de acordo com o compareTo de Node
            PriorityQueue<INode<V, E>> q = new PriorityQueue<>();

            for (V v : nodeList.keySet()) {

                INode<V, E> aux = nodeList.get(v);

                //pra cada valor adicionado na fila, eh definido o dnumber com os valores de d.
                aux.setDNumber(d.get(aux));
                q.add(aux);

            }

            while (q.size() > 0) {

                //remove o elemento com o menor dnumber
                INode<V, E> u = q.remove();

                //se o elemento removido é igual ao destino, caminho até o destino está pronto
                if (u.equals(dest)) {
                    break;
                }

                //pra cada Node de chave z nas adjacencias de u
                for (V z : u.getAdjs().keySet()) {

                    //auxiliar recebe o valor inteiro do mapa d com chave u.value somado da distancia de u at� o nodo de z
                    Double aux = d.get(u) + getValue(u.getValue(), z);

                    //aux2 recebe o nodo de valor z
                    INode<V, E> aux2 = nodeList.get(z);

                    //se aux2 esta em q, e aux � menor q o nodo de z
                    if (q.contains(aux2) && aux < d.get(aux2)) {

                        //atualiza valor de aux2 com aux
                        d.put(aux2, aux);

                        //remove e atualiza o valor de aux2 em q
                        q.remove(aux2);
                        aux2.setDNumber(aux);
                        q.add(aux2);

                        //grava o Node anterior para fins de caminho
                        x.setNode(aux2, u, aux);
                        x.addNode(aux2, u, aux);

                    }
                }
            }


            //relatório
            List<INode<V,E>> resultado =  x.getPath(nodeList.get(dest));
            for(int i=0; i < resultado.size(); i++){

                state.addNode(resultado.get(i));
                if(i != 0){
                    IEdge<V,E> edge = resultado.get(i).getIncid().get(resultado.get(i-1).getValue());

                    if(edge == null) continue;
                    
                    state.addEdge(edge.getOrigin().getValue(),edge.getDest().getValue(),edge.getLabel());

                }

                algReport.addState(state);

            }

            //retorna o menor caminho para o destino usando o objeto auxiliar x
            algReport.setReturn(x.getPath(nodeList.get(dest))); // retorno do tipo List<INode<V, E>>

            return algReport;
        }catch(NullPointerException e){
            
            return null;
            
        }
    }

    //retorna a distancia entre orig e dest, caso sejam adjacentes, caso contrario retorna MAX_VALUE
    private Double getValue(V orig, V dest) {
        Node<V, E> aux = (Node) nodeList.get(orig);
        if (aux.adjs.containsKey(dest)) {
            return Double.parseDouble(aux.adjs.get(dest).getLabel().toString());
        } else {
            return Double.MAX_VALUE;
        }
    }

    /*
	 * requer label das edges do tipo inteiro. Considera grafo como não-direcionado. Retorna um conjunto de arestas (representando a árvore)
     */
    public AlgorithmReport getMSTKruskal() {

        AlgorithmReport relatorio = new AlgorithmReport();
        relatorio.setAlgorithmName("MST Kruskal");
        Report<V,E> state = new Report<>();
        
        Grafo<V, E> mst = new Grafo<>();
        Set<IEdge<V, E>> A = new HashSet<>();

        HashMap<INode, Set<INode<V, E>>> setsNodes = new HashMap<>();
        List<IEdge> orderedEdges = new ArrayList<>();

        //Cria a floresta e a lista de edges desordenada (linha 2-3)

        for (INode<V, E> n : nodeList.values()) {
            
            setsNodes.put(n, makeSet(n));
            
            //adiciona edges adjacentes de n na lista de edges

            for (IEdge<V, E> e : n.getAdjs().values()) {

                //adiciona desordenado
                orderedEdges.add(e);

            }

        }
        
        Collections.sort(orderedEdges, new Comparator<IEdge>() {

            @Override
            public int compare(IEdge o1, IEdge o2) {

                return o1.compare(o1, o2);

            }

        });

        for (IEdge<V, E> e : orderedEdges) {

            Set<INode<V, E>> setOrig = setsNodes.get(e.getOrigin());
            Set<INode<V, E>> setDest = setsNodes.get(e.getDest());
            
            if (setOrig != setDest) {
                //uniao entre A e edge (linha 7)
                
                state.addEdge(e.getOrigin().getValue(), e.getDest().getValue(), e.getLabel());
                state.addNode(e.getOrigin().getValue());
                state.addNode(e.getDest().getValue());
                
                A.add(e);
                
                relatorio.addState(state);
                
                //uniao entre os sets (setOrig add setDest, setDest aponta para setOrig) (linha 8)
                setOrig.addAll(setDest);
                setDest.addAll(setOrig);

                for (INode<V, E> n : setOrig) {
                    setsNodes.put(n, setOrig);
                }
                for (INode<V, E> n : setDest) {
                    setsNodes.put(n, setOrig);
                }

            }

        }
        String result = "";
        for (IEdge e : A) {
            result += "\n        " + e.getOrigin() + "-[" + e.getLabel() + "]->" + e.getDest();
        }
        
        relatorio.setReturn(A);
        
        return relatorio;

    }

    /*
	 * Metodo auxiliar para getMSTKruskall();
     */
    private Set<INode<V, E>> makeSet(INode<V, E> n) {

        Set<INode<V, E>> u = new HashSet<>();
        u.add(n);
        return u;

    }

    @Override
    public String toString() {

        StringBuilder graph = new StringBuilder("Grafo:");
        graph.append("\n");

        //StringBuilder nodesAdjs = new StringBuilder("Adjs:");
        for (INode<V, E> node : nodeList.values()) {

            graph.append("(");
            graph.append(node.getValue());
            graph.append(",[");

            for (IEdge<V, E> edge : node.getAdjs().values()) {
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

    public void setCaminhamento(TipoCamin tipo) {

        this.tipo = tipo;

    }

    public List<V> getCaminhoAtom(V nodeOrig, TipoCamin tipo) {

        if (!(tipo == TipoCamin.LARGURA) && !(tipo == TipoCamin.PROFUNDIDADE)) {
            return null;
        }

        List<V> caminhamento = new ArrayList<V>();
        caminhamento.add(nodeOrig);

        if (tipo == TipoCamin.LARGURA) {

            int i = 0;

            while (i < caminhamento.size()) {

                INode atual = getNode(caminhamento.get(i));
                Collection<Edge<V, E>> adjs = atual.getAdjs().values();

                for (Edge<V, E> edge : adjs) {

                    if (caminhamento.contains(edge.getDest().getValue())) {
                        continue;
                    }
                    caminhamento.add(edge.getDest().getValue());

                }

                i++;

            }

            return caminhamento;

        } else {

            INode fst = getNode(caminhamento.get(0));
            Collection<Edge<V, E>> adjs = fst.getAdjs().values();
            List<V> nodes = new ArrayList<V>();
            nodes.add((V) fst.getValue());

            for (IEdge<V, E> edge : adjs) {

                List<V> lista = new ArrayList<V>();
                nodes.addAll(getCamAtomAux(nodes, edge.getDest(), lista));

            }

            return nodes;

        }

    }

    private List<V> getCamAtomAux(List<V> nodesSoFar, INode orig, List<V> listaRetorno) {

        Collection<Edge<V, E>> adjs = orig.getAdjs().values();
        List<Node<V, E>> nodes = new ArrayList<Node<V, E>>();
        nodesSoFar.add((V) orig.getValue());

        for (Edge<V, E> edge : adjs) {

            if (nodesSoFar.contains(edge.getDest().getValue())) {
                continue;
            }
            listaRetorno.addAll(getCamAtomAux(nodesSoFar, edge.getDest(), listaRetorno));

        }

        return listaRetorno;

    }

    /**
     * Encapsula o processo de iteração da operação de caminhamento Este
     * processo pode ser feita diretamente pelo programador, através de um loop
     * de repetição. Porém, para usar um loop diretamente, o programador deve
     * primeiro setar o valor originCaminha usando o método setOrigem(V origem).
     *
     * @param origem
     * @param tipo
     * @return
     */
    @Override
    public List<V> getCaminhoIter(V origem, TipoCamin tipo) {

        //determina a origem do caminhamento e a lista do caminhamento
        setCaminhamento(tipo);
        setOrigem(origem);
        List<V> trav = new ArrayList<V>();
        Iterator it = this.iterator();

        while (it.hasNext()) {

            trav.add((V) it.next());

        }

        return trav;

    }

    public void setOrigem(V origem) {

        originCaminha = nodeList.get(origem);

    }

    @Override
    public Iterator<V> iterator() {

        if (tipo == TipoCamin.LARGURA) {
            return new CaminLargIterator();
        }
        return new CaminProfIterator();

    }

}
