package Interface.screen;

import Interface.Graph;
import Interface.Node;
import Interface.ToolBar;
import Modelo.AlgorithmReport;
import Modelo.Algorithms;
import Modelo.Report;
import Modelo.Report.NodeDTO;
import Modelo.TypeChange;
import java.awt.*;
import java.awt.event.*;
import java.io.*;
import java.util.LinkedList;
import java.util.Observable;
import java.util.Observer;
import java.util.List;
import javax.swing.JFileChooser;
import javax.swing.JFrame;
import javax.swing.JMenu;
import javax.swing.JMenuBar;
import javax.swing.JMenuItem;
import javax.swing.JOptionPane;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;

/**
   This frame shows the toolbar and the graph.
*/
public class GraphFrame extends JFrame implements Observer
{
   /**
      Constructs a graph frame that displays a given graph.
      @param graph the graph to display
   */
   public GraphFrame(final Graph graph)
   {
      setSize(FRAME_WIDTH, FRAME_HEIGHT);
      setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);

      this.graph = graph;

      constructFrameComponents();
      // Set up menus

      JMenuBar menuBar = new JMenuBar();
      setJMenuBar(menuBar);
      JMenu fileMenu = new JMenu("File");
      menuBar.add(fileMenu);

      JMenuItem exitItem = new JMenuItem("Exit");
      exitItem.addActionListener(new
         ActionListener()
         {
            public void actionPerformed(ActionEvent event)
            {
               System.exit(0);
            }
         });
      fileMenu.add(exitItem);

      JMenuItem deleteItem = new JMenuItem("Delete");
      deleteItem.addActionListener(new
         ActionListener()
         {
            public void actionPerformed(ActionEvent event)
            {
               panel.removeSelected();
               
            }
         });

      JMenu editMenu = new JMenu("Edit");
      editMenu.add(deleteItem);
      menuBar.add(editMenu);
      
      
      JMenu algorithmsMenu = new JMenu("Algoritmos");
      
      JMenuItem dijkstraItem = new JMenuItem("Dijkstra");
      dijkstraItem.addActionListener(new
         ActionListener()
         {
            public void actionPerformed(ActionEvent event)
            {
                executaAlgoritmo(Algorithms.DijkstraAlgoritmo);
            }
         });
      algorithmsMenu.add(dijkstraItem);
      
      JMenuItem caminhoCriticoItem = new JMenuItem("Caminho Crítico");
      caminhoCriticoItem.addActionListener(new
         ActionListener()
         {
            public void actionPerformed(ActionEvent event)
            {
                
                executaAlgoritmo(Algorithms.CaminhoCriticoAlgoritmo);
                
            }
         });
      algorithmsMenu.add(caminhoCriticoItem);
      
      JMenuItem kruskalMstItem = new JMenuItem("MST (Kruskal)");
      kruskalMstItem.addActionListener(new
         ActionListener()
         {
            public void actionPerformed(ActionEvent event)
            {
                
                executaAlgoritmo(Algorithms.KruskalAlgoritmo);
           
            }
         });
      algorithmsMenu.add(kruskalMstItem);
      
      JMenuItem ordTopologicaItem = new JMenuItem("Ordenação Topológica");
      ordTopologicaItem.addActionListener(new
         ActionListener()
         {
            public void actionPerformed(ActionEvent event)
            {
                
                executaAlgoritmo(Algorithms.OrdenacaoTopologicaAlgoritmo);
                
            }
         });
      algorithmsMenu.add(ordTopologicaItem);
      
      menuBar.add(algorithmsMenu);
      
   }
   
   private void executaAlgoritmo(Algorithms algoritmo){
       
       //panel.setTypeChange(algoritmo);
       graph.notifyAlgorithmExecutation(algoritmo);
   }

   /**
      Constructs the tool bar and graph panel.
   */
   private void constructFrameComponents()
   {
      toolBar = new ToolBar(graph);
      panel = new GraphPanel(toolBar, graph);
      terminal = new JTextArea();
      terminalPanel = new TerminalPanel(terminal);
      scrollPane = new JScrollPane(panel);
      stateControlPanel = new StateControlPanel();
      stateControlPanel.setVisible(false);
      this.add(toolBar, BorderLayout.NORTH);
      this.add(scrollPane, BorderLayout.CENTER);
      this.add(stateControlPanel,BorderLayout.EAST);
      this.add(terminalPanel, BorderLayout.SOUTH);
   }
   
   public GraphPanel getGraphPanel(){
       
       return panel;
       
   }

   public void showStates(AlgorithmReport algReport){
       
       stateControlPanel.setVisible(true);

       //adicionar algReport ao stateControl
       algReport.addObserver(this);
       stateControlPanel.addStates(algReport);
       //stateControl possui uma maneira de setar as arestas e os nodos a serem destacados
       //GraphFrame observa stateControl. Quando stateControl muda os nodos e arestas destacados, GraphFrame muda em graphPanel
       
   }
   
   @Override
    public void update(Observable o, Object arg) {
        //se observavel for AlgorithmReport, mudou o estado. Necessario pintar os algoritmos corretos
        
        if(o instanceof AlgorithmReport){
            
            //arg é o estado (Report). Contem nodos e arestas a serem destacadas
            Report state = (Report) arg;
            
            //armazena valores dos nodos em uma lista como string
            
            List<String> nodesHighlight = new LinkedList<>();
            
            //armazena labels das arestas em uma lista como string
            
            List<String> edgesHighlight = new LinkedList<>();
            
            
//            for(Edge e : graph.getEdges()) e.unHighLight();
            
            for(Object v : state.getNodesVal()){
                
                nodesHighlight.add(""+v);
                
            }
            
            for(Object e : state.getEdges()){
                
                edgesHighlight.add(""+e);
                
            }
            
            graph.highLightNodesAndEdges(nodesHighlight, edgesHighlight, (Graphics2D) panel.getGraphics());
            
        }

    }
   
   
   private Graph graph;
   private GraphPanel panel;
   private JScrollPane scrollPane;
   private TerminalPanel terminalPanel;
   private ToolBar toolBar;
   private JTextArea terminal;
   private StateControlPanel stateControlPanel;

   public static final int FRAME_WIDTH = 600;
   public static final int FRAME_HEIGHT = 600;

}
