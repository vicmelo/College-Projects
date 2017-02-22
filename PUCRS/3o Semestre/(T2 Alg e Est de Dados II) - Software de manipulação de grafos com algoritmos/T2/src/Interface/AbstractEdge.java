package Interface;

import java.awt.*;
import java.awt.geom.*;

/**
   A class that supplies convenience implementations for 
   a number of methods in the Edge interface type.
*/
public abstract class AbstractEdge implements Edge
{  
   public Object clone()
   {
      try
      {
         return super.clone();
      }
      catch (CloneNotSupportedException exception)
      {
         return null;
      }
   }

   public void connect(Node s, Node e)
   {  
      start = s;
      end = e;
   }

   public Node getStart()
   {
      return start;
   }

   public Node getEnd()
   {
      return end;
   }

   public Rectangle2D getBounds(Graphics2D g2)
   {
      Line2D conn = getConnectionPoints();      
      Rectangle2D r = new Rectangle2D.Double();
      r.setFrameFromDiagonal(conn.getX1(), conn.getY1(),
            conn.getX2(), conn.getY2());
      return r;
   }

   public Line2D getConnectionPoints()
   {
      Rectangle2D startBounds = start.getBounds();
      Rectangle2D endBounds = end.getBounds();
      Point2D startCenter = new Point2D.Double(
            startBounds.getCenterX(), startBounds.getCenterY());
      Point2D endCenter = new Point2D.Double(
            endBounds.getCenterX(), endBounds.getCenterY());
      return new Line2D.Double(
            start.getConnectionPoint(endCenter),
            end.getConnectionPoint(startCenter));
   }
   
   public Integer getValue(){
    
       return value;
       
   }
   
   public void setValue(Integer value){
       
       this.value = value;
       
   }
   
   public Double getLineCenterX(Line2D line){
       
       Double x = (line.getX2()+(line.getX1()+line.getX2())/2)/2;
   
       if(line.getX2() >= line.getX1()) x-= 5;
       else x+=5;
       
       return x;
       
   }
   
   public Double getLineCenterY(Line2D line){
       
       Double y = (line.getY2()+(line.getY1()+line.getY2())/2)/2;

       if(line.getY2() >= line.getY1()) y-= 5;
       else y+=5;
       
       return y;
       
   }
   
   private Node start;
   private Node end;
   Integer value;
   Stroke stroke;
   static final Color DEFAULT_COLOR = new Color(0, 0, 0);
   static final Color HIGHLIGHT_COLOR = new Color(128, 170, 255);
   static final Stroke DEFAULT_STROKE = new BasicStroke(1);
   static final Stroke HIGHLIGHT_STROKE = new BasicStroke(2);
}
