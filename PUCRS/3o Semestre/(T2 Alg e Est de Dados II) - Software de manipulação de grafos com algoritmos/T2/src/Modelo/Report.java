/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package Modelo;

import Modelo.IEdge;
import Modelo.INode;
import java.util.ArrayList;
import java.util.List;

/**
 *
 * @author victor
 */
public class Report<V,E> {
    
    
    private List<NodeDTO<V,E>> nodes; // diferenciar nodos pintados
    private List<EdgeDTO<V,E>> edges; // diferenciar arestas pintadas
    
    public class NodeDTO<V,E>{
        
        V value;
        
        public NodeDTO(V value){
            
            this.value = value;
            
        }
        
    }
    
    public class EdgeDTO<V,E>{
        
        V origValue, destValue;
        E label;
        
        public EdgeDTO(V origValue, V destValue, E label){
         
            this.origValue = origValue;
            this.destValue = destValue;
            this.label = label;
            
        }
        
    }
    
    public Report(){
        
        nodes = new ArrayList<>();
        edges = new ArrayList<>();
        
    }
    
    public void addNode(V nodeValue){
        
        nodes.add(new NodeDTO(nodeValue));
        
    }
    
    public void addEdge(V origValue, V destValue, E edgeLabel){
        
        edges.add(new EdgeDTO(origValue, destValue, edgeLabel));
        
    }
    
    public Report clone(){
        
        Report stateReturn = new Report();
        
        for(EdgeDTO e : edges) stateReturn.addEdge(e.origValue, e.destValue, e.label);
        for(NodeDTO n : nodes) stateReturn.addNode(n.value);
        
        return stateReturn;
        
    }
    
    public List<V> getNodesVal(){
        
        List<V> returnList = new ArrayList<>();
        
        for(NodeDTO<V,E> n : nodes) returnList.add(n.value); 
        return returnList;
        
    }
    
    public List<String> getEdges(){
        
        List<String> returnList = new ArrayList<>();
        
        for(EdgeDTO<V,E> e : edges) returnList.add(e.origValue.toString()+e.label+e.destValue.toString()); 
        return returnList;
        
    }
    
}
