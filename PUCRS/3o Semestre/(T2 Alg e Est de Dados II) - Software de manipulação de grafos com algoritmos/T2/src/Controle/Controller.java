/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package Controle;

import Interface.CreatingType;
import Interface.Edge;
import Interface.InsertValue;
import Interface.screen.GraphFrame;
import Interface.Node;
import Interface.SimpleGraph;
import Interface.screen.InsertValueFrame;
import Modelo.AlgorithmReport;
import Modelo.Algorithms;
import Modelo.TypeChange;
import Modelo.Grafo;
import Modelo.IEdge;
import Modelo.INode;
import Modelo.Report;
import Modelo.Terminal;
import java.util.List;
import java.util.Observable;
import javax.swing.JFrame;
import java.util.Observer;
import java.util.Set;
import javax.swing.WindowConstants;

/**
 *
 * @author victor
 */
public class Controller implements Observer{
    
    Grafo<String,Integer> grafo;
    GraphFrame graphFrame;
    Integer v1,v2;
    
    public Controller(){
     
      graphFrame = new GraphFrame(new SimpleGraph());
      grafo = new Grafo<>();
      graphFrame.getGraphPanel().addObserverToGraph(this);
      
    }

    @Override
    //Controller observa grafo, mas utiliza valores de GraphPanel para definir sua operacao. GraphPanel eh quem chama as operacoes
    //da classe Grafo. Este eh um problema de encapsulamento. Porem, sem ele, seria necessario percorrer os nodos do grafo para
    //saber qual operacao foi executada, perdendo em desempenho. Por isso mantivemos este problema (ateh aparecer uma solucao melhor).
    public void update(Observable o, Object arg) {
        
        TypeChange change = null;
        CreatingType continueAlgorithm = null;
        Algorithms executeAlg = null;
        
        if(arg instanceof TypeChange) change = (TypeChange) arg;
        if(arg instanceof CreatingType) continueAlgorithm = (CreatingType) arg;
        else if(arg instanceof Algorithms) executeAlg = (Algorithms) arg;
        
        if(change != null){
            switch(change){

                case AddEdge:
                    
                    Edge edgeInterface = graphFrame.getGraphPanel().getEdgeChanged();
                    Node origInterface = edgeInterface.getStart();
                    Node destInterface = edgeInterface.getEnd();
                                        
                    grafo.addEdge(origInterface.getValue(), destInterface.getValue(), edgeInterface.getValue());
                    
                    break;

                case RemoveEdge:

                    edgeInterface = graphFrame.getGraphPanel().getEdgeChanged();
                    origInterface = edgeInterface.getStart();
                    destInterface = edgeInterface.getEnd();
                    grafo.removeEdge(origInterface.getValue(), destInterface.getValue());
                    break;

                case AddNode:

                    Node nodeInterface = graphFrame.getGraphPanel().getNodeChanged();
                    grafo.addNode(nodeInterface.getValue());
                    break;

                case RemoveNode:

                    nodeInterface = graphFrame.getGraphPanel().getNodeChanged();
                    grafo.removeNode(nodeInterface.getValue());
                    break;
            }
            
        }else if(executeAlg != null){
            AlgorithmReport report;
            InsertValueFrame insertValue;
            switch(executeAlg){
                case DijkstraAlgoritmo:
                    
                    insertValue = new InsertValueFrame("Insira o nodo origem", "Insira o nodo destino");
                    insertValue.setCreatingType(CreatingType.NodesDijkstra);
                    insertValue.addObserver(this);
                    insertValue.setVisible(true);
                    
                    break;

                case KruskalAlgoritmo:

                    report = grafo.getMSTKruskal();
                    Set<IEdge<String,Integer>> s = (Set<IEdge<String,Integer>>)report.getReturn();
                    Terminal.println("Algoritmo de Kruskal executado com sucesso");
//                    Terminal.println("Resultado:\n{");
//                    for(IEdge<String,Integer> e : s){
//                        
//                        Terminal.println("  "+e.getOrigin()+"-["+e.getLabel()+"]->"+e.getDest());
//                        
//                    }
//                    
//                    Terminal.println("}");
                    graphFrame.showStates(report);
                    
                    break;            

                case CaminhoCriticoAlgoritmo:
                    
                    insertValue = new InsertValueFrame("Insira o nodo origem", "Insira o nodo destino");
                    insertValue.setCreatingType(CreatingType.NodesCriticalPath);
                    insertValue.addObserver(this);
                    insertValue.setVisible(true);
                    
                    break;
                    
                case OrdenacaoTopologicaAlgoritmo:
                    
                    report = null;
                    
                    try{
                        
                        report = grafo.ordTopologica();
                        Terminal.println("Algoritmo de ordenação topológica executado com sucesso");
                        
                    }catch(Exception e){
                        Terminal.println("Erro: Não foi possível executar o algoritmo de ordenação topológica: "+e.getMessage());
                    }
                    
                    if(report != null) graphFrame.showStates(report);
                    
                    break;
            }   
            
        }else if(continueAlgorithm != null){
            
            InsertValue values = (InsertValue) o;
            AlgorithmReport report;
            
            switch(continueAlgorithm){
                
                case NodesDijkstra:
                
                    report = grafo.pathFromTo(values.getV1(), values.getV2());
                    if(report != null){
                        
                        Terminal.println("Algoritmo de Dijkstra executado com sucesso");
                        graphFrame.showStates(report);
                    
                    }else{
                        
                        Terminal.println("Erro: Não foi possível executar algoritmo de Dijkstra\n(há um caminho entre os nodos escolhidos?)");
                        
                    }
                    
                    break;
                    
                case NodesCriticalPath:
                    
                    //troca pathFromTo para o nome do método de caminho crítico
                    report = grafo.caminhoCritico(values.getV1(), values.getV2());
                    if(report != null){
                        
                        Terminal.println("Algoritmo de Caminho Crítico executado com sucesso");
                        graphFrame.showStates(report);
                    
                    }else{
                        
                        Terminal.println("Erro: Não foi possível executar algoritmo de Caminho Crítico\n(há um caminho entre os nodos escolhidos?)");
                        
                    }
                   
                    break;
                    
                default:
                    
                    break;
            
            }
        }
        
    }
    
}
