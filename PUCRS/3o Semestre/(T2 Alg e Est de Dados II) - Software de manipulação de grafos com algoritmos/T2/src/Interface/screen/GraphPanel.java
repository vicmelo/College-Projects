package Interface.screen;

import Interface.CreatingType;
import Interface.Edge;
import Interface.Graph;
import Interface.InsertValue;
import Interface.Node;
import Interface.ToolBar;
import Modelo.Terminal;
import Modelo.TypeChange;
import java.awt.*;
import java.awt.geom.*;
import java.awt.event.*;
import java.util.ArrayList;
import javax.swing.*;
import javax.swing.event.*;
import java.util.List;
import java.util.Observable;
import java.util.Observer;

/**
   A panel to draw a graph
*/
public class GraphPanel extends JComponent implements Observer
{
    
   private List<Observer> observers = new ArrayList<>();
   private Graph graph;
   private ToolBar toolBar;
   private Point2D lastMousePoint;
   private Point2D rubberBandStart;
   private Point2D dragStartPoint;
   private Rectangle2D dragStartBounds;
   private InsertValueFrame insertValue;
   private Object selected;
   private static final Color PURPLE = new Color(0.7f, 0.4f, 0.7f);
 
   //observer do controller (atributos que indicam qual operacao controller deve fazer)
   //Importante: typeChange deve ser setado antes de executar operacoes no grafo. Isto se dá pois é o grafo quem notifica os observers ao executar
   //a operação em si. Logo, typeChange deve estar setado corretamente antes que os observers sejam notificados da mudança.
   //public TypeChange typeChange; //usado para adicao e remocao de nodos e execucao dos algoritmos
   public Edge edgeChanged;
   public Node nodeChanged;
   
   //Uteis como atributos para adição de nodo (para método createNode) e arestas
   private Object tool;
   private Point2D mousePoint;
   private Node n;
   
   /**
      Constructs a graph panel.
      @param aToolBar the tool bar with the node and edge tools
      @param aGraph the graph to be displayed and edited
   */
   public GraphPanel(ToolBar aToolBar, Graph aGraph)
   {
      insertValue = new InsertValueFrame();
      insertValue.addObserver(this); //adiciona observer
      toolBar = aToolBar;
      graph = aGraph;
      graph.addObserver(this);
      setBackground(Color.WHITE);

      addMouseListener(new
         MouseAdapter()
         {
            public void mousePressed(MouseEvent event)
            {
               mousePoint = event.getPoint();
               n = graph.findNode(mousePoint);
               Edge e = graph.findEdge(mousePoint);
               tool = toolBar.getSelectedTool();
               
               selected = null;
               repaint();
               
               if (tool == null)
               {
                  if (e != null)
                  {
                     selected = e;
                  }
                  else if (n != null)
                  {
                     selected = n;
                     dragStartPoint = mousePoint;
                     dragStartBounds = n.getBounds();
                  }
                  else
                  {
                     selected = null;
                  }
               }
               else if (tool instanceof Node) //adiciona nodo
               {
                  
                  //nodo é criado com o padrão observer usado com InsertValue 
                  insertValue.setCreatingType(CreatingType.Node);
                  insertValue.setCustomText("Insira o nome do nodo");
                  insertValue.setVisible(true);
                  
               }
               else if (tool instanceof Edge)
               {
                  
                  if (n != null) rubberBandStart = mousePoint;
               }
               
               lastMousePoint = mousePoint;
               repaint();
            }

            public void mouseReleased(MouseEvent event)
            {
               Object tool = toolBar.getSelectedTool();
               if (rubberBandStart != null) //adiciona edge
               {
                  if(graph.findNode(event.getPoint()) != null){ //se soltou o mouse em um nodo
                    
                    //edge é criada com padrão observer usado com InsertValue
                    
                    insertValue.setCreatingType(CreatingType.Edge);
                    insertValue.setCustomText("Insira um número inteiro como valor da aresta");
                    mousePoint = event.getPoint();
                    insertValue.setVisible(true); 
                    
                  }else{//caso tenha soltado o mouse em um espaço vazio
                      
                    lastMousePoint = null;
                    dragStartBounds = null;
                    rubberBandStart = null;
                    revalidate();
                    repaint();
                      
                  }

               }

            }
         });

      addMouseMotionListener(new
         MouseMotionAdapter()
         {
            public void mouseDragged(MouseEvent event)
            {
               Point2D mousePoint = event.getPoint();
               if (dragStartBounds != null)
               {
                  if (selected instanceof Node)
                  {

                     Node n = (Node) selected;
                     Rectangle2D bounds = n.getBounds();
                     n.translate(
                        dragStartBounds.getX() - bounds.getX()
                        + mousePoint.getX() - dragStartPoint.getX(),
                        dragStartBounds.getY() - bounds.getY()
                        + mousePoint.getY() - dragStartPoint.getY());
                  }
               }
               lastMousePoint = mousePoint;
               repaint();
            }
         });
   }
   
//   public void setTypeChange(TypeChange type){
//       
//       this.typeChange = type;
//       
//   }
   
   public void addObserverToGraph(Observer obs){
       
       graph.addObserver(obs);
       
   }
   
   public void paintComponent(Graphics g)
   {
      Graphics2D g2 = (Graphics2D) g;
      Rectangle2D bounds = getBounds();
      Rectangle2D graphBounds = graph.getBounds(g2);
      graph.draw(g2);

      if (selected instanceof Node)
      {
         Rectangle2D grabberBounds = ((Node) selected).getBounds();
         drawGrabber(g2, grabberBounds.getMinX(), grabberBounds.getMinY());
         drawGrabber(g2, grabberBounds.getMinX(), grabberBounds.getMaxY());
         drawGrabber(g2, grabberBounds.getMaxX(), grabberBounds.getMinY());
         drawGrabber(g2, grabberBounds.getMaxX(), grabberBounds.getMaxY());
      }

      if (selected instanceof Edge)
      {
         Line2D line = ((Edge) selected).getConnectionPoints();
         drawGrabber(g2, line.getX1(), line.getY1());
         drawGrabber(g2, line.getX2(), line.getY2());
      }

      if (rubberBandStart != null)
      {
         Color oldColor = g2.getColor();
         g2.setColor(PURPLE);
         g2.draw(new Line2D.Double(rubberBandStart, lastMousePoint));
         g2.setColor(oldColor);
      }
   }


   /**
      Removes the selected node or edge.
   */
   public void removeSelected()
   {
       
      if (selected instanceof Node)
      {
          
         //typeChange = TypeChange.RemoveNode;
         nodeChanged = (Node) selected;
         
         graph.removeNode((Node) selected);
      
      }
      
      else if (selected instanceof Edge)
      {
          
         //typeChange = TypeChange.RemoveEdge;
         edgeChanged = (Edge) selected;
         
         graph.removeEdge((Edge) selected);
         
      }
      
      //if(selected instanceof Edge || selected instanceof Node) notifyObservers();
      
      selected = null;
      repaint();
      
   }

   /**
      Draws a single "grabber", a filled square
      @param g2 the graphics context
      @param x the x coordinate of the center of the grabber
      @param y the y coordinate of the center of the grabber
   */
   public static void drawGrabber(Graphics2D g2, double x, double y)
   {
      final int SIZE = 5;
      Color oldColor = g2.getColor();
      g2.setColor(PURPLE);
      g2.fill(new Rectangle2D.Double(x - SIZE / 2,
         y - SIZE / 2, SIZE, SIZE));
      g2.setColor(oldColor);
   }

   public Dimension getPreferredSize()
   {
      Rectangle2D bounds
         = graph.getBounds((Graphics2D) getGraphics());
      return new Dimension(
         (int) bounds.getMaxX(),
         (int) bounds.getMaxY());
   }
   
  
    private void createNode(String value) throws IllegalArgumentException {
        
        if(value.isEmpty()) throw new IllegalArgumentException("Necessário definir um valor para o nodo");
        
        Node prototype = (Node) tool;
        Node newNode = (Node) prototype.clone();
        newNode.setValue(value);
        
        
        //typeChange = TypeChange.AddNode;
        nodeChanged = newNode;
        
        boolean added = graph.add(newNode, mousePoint);
        if (added)
        {
           selected = newNode;
           dragStartPoint = mousePoint;
           dragStartBounds = newNode.getBounds();
        }
        else if (n != null)
        {
           selected = n;
           dragStartPoint = mousePoint;
           dragStartBounds = n.getBounds();
        }
        
        validate();
        repaint();

        lastMousePoint = null;
        dragStartBounds = null;
        rubberBandStart = null;
        
        //notifyObservers();
        
    }
    
    private void createEdge(Integer value){
        
        Edge prototype = (Edge) tool;
        Edge newEdge = (Edge) prototype.clone();
        newEdge.setValue(value);
        
        //typeChange = TypeChange.AddEdge;
        edgeChanged = newEdge;
        
        if (graph.connect(newEdge,rubberBandStart, mousePoint))
           selected = newEdge;
        
        validate();
        repaint();

        lastMousePoint = null;
        dragStartBounds = null;
        rubberBandStart = null;
        
        //notifyObservers();
        
    }
    
//    public TypeChange getTypeChange(){
//       
//       return typeChange;
//       
//   }
   
   public Edge getEdgeChanged(){
       
       return edgeChanged;
       
   }
   
   public Node getNodeChanged(){
       
       return nodeChanged;
       
   }
    
    //Observer pattern
    public void attach(Observer obs){
        
        observers.add(obs);
        
    }

   @Override
    public void update(Observable o, Object arg) {

        if(o instanceof InsertValue){
        
            insertValue.setVisible(false);
            if(insertValue.getCreatingType() == CreatingType.Node){
                try{
                    
                    createNode(insertValue.getValue());
                    
                }catch(IllegalArgumentException e){
                    
                    Terminal.println("Erro: Não foi possível criar o nodo com o valor solicitado: "+e.getMessage());
                    
                }
            }
            
            if(insertValue.getCreatingType() == CreatingType.Edge){
                try{
                    
                    createEdge(Integer.parseInt(insertValue.getValue()));
                    
                }catch (NumberFormatException e) {
                    
                    Terminal.println("Erro: Valor de aresta deve ser um número inteiro");
                    insertValue.clearText();
                    insertValue.focusTextArea();
                    
                    edgeChanged = null;
                    selected = null;
                    lastMousePoint = null;
                    dragStartBounds = null;
                    rubberBandStart = null;
                    revalidate();
                    repaint();
                    
                }catch (IllegalArgumentException e){
                    
                    Terminal.println("Erro: Não foi possível criar a aresta: "+e.getMessage());
                    
                    edgeChanged = null;
                    selected = null;
                    lastMousePoint = null;
                    dragStartBounds = null;
                    rubberBandStart = null;
                    revalidate();
                    repaint();
                    
                }
            }
        
        }else if(o instanceof Graph){
            if(arg instanceof TypeChange){
                
//                TypeChange change = (TypeChange) arg; 
                
                revalidate();
                repaint();

            }
            
               
        }
    }
    
}
