package Modelo;

import java.util.Iterator;
import java.util.List;

public interface IGrafo<V,E> {

	enum TipoCamin {LARGURA, PROFUNDIDADE;}
	
	void addNode(V nodeValue) throws IllegalArgumentException;
	
	void addEdge(V nodeOrig, V nodeDest, E edgeValue);

	void removeNode(V nodeValue);
	
	void removeEdge(V origValue, V destValue);
	
	AlgorithmReport pathFromTo(V orig, V dest);
	
	void setCaminhamento(TipoCamin tipo);
	
	List<V> getCaminhoAtom(V nodeOrig, TipoCamin tipo);
	
	List<V> getCaminhoIter(V origem, TipoCamin tipo);
	
	void setOrigem(V origem);
        
}
