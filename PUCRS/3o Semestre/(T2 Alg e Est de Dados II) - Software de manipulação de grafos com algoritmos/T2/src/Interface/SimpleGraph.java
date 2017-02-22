package Interface;

import java.awt.*;
import java.util.*;

/**
   A simple graph with round nodes and straight edges.
*/
public class SimpleGraph extends Graph
{
   public Node[] getNodePrototypes()
   {
      Node[] nodeTypes =
         {
            new CircleNode("V")
         };
      return nodeTypes;
   }

   public Edge[] getEdgePrototypes()
   {
       
      Edge[] edgeTypes = 
         {
            new ArrowEdge(0)
         };
      return edgeTypes;
   }
}





