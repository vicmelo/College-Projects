package Interface;

import java.awt.*;
import java.awt.geom.*;

/**
   A circular node that is filled with a color.
*/
public class CircleNode implements Node
{
    
   private double x;
   private double y;
   private double size;
   private String value;
   private Color color, oldColor;
   private static final int DEFAULT_SIZE = 35;
   private static final Color DEFAULT_COLOR = new Color(255, 255, 179);
   private static final Color HIGHLIGHT_COLOR = new Color(128, 170, 255);
   
   /**
      Construct a circle node with a given size and color.
      @param aColor the fill color
   */
   public CircleNode(String value)
   {
      color = DEFAULT_COLOR;
      size = DEFAULT_SIZE;
      x = 0;
      y = 0;
      this.value = value;
   }
   
   public String getValue(){
       
       return value;
       
   }
   
   @Override
   public void setValue(String value){
       
       this.value = value;
       
   }

   @Override
   public Object clone()
   {
      try
      {
         CircleNode n = (CircleNode) super.clone();
         n.setValue("B");
         return n;
      }
      catch (CloneNotSupportedException exception)
      {
         return null;
      }
   }

   @Override
   public void draw(Graphics2D g2)
   {
      Ellipse2D circle = new Ellipse2D.Double(
            x, y, size, size);
      Double centerX = x + size / 2;
      Double centerY = y + size / 2;
      
      Font font = new Font("Arial", Font.BOLD, 12);
      g2.setFont(font);
      FontMetrics fm = g2.getFontMetrics();
      int xx = (int) (circle.getCenterX() - fm.stringWidth(value)/2);
      int yy = (int) ((circle.getCenterY()- fm.getHeight()/ 2) + fm.getAscent());

      
      this.oldColor = g2.getColor();
      
      g2.setColor(color);
      g2.fill(circle);
      g2.setColor(oldColor);
      g2.drawString(value, xx, yy);
      
      //g2.setColor(color);
      //g2.fill(circle);
      //g2.setColor(oldColor);
      g2.draw(circle);
   }
   
   public void translate(double dx, double dy)
   {
      x += dx;
      y += dy;
   }

   public boolean contains(Point2D p)
   {
      Ellipse2D circle = new Ellipse2D.Double(
            x, y, size, size);
      return circle.contains(p);
   }

   public Rectangle2D getBounds()
   {
      return new Rectangle2D.Double(
            x, y, size, size);
   }

   public Point2D getConnectionPoint(Point2D other)
   {
      double centerX = x + size / 2;
      double centerY = y + size / 2;
      double dx = other.getX() - centerX;
      double dy = other.getY() - centerY;
      double distance = Math.sqrt(dx * dx + dy * dy);
      if (distance == 0) return other;
      else return new Point2D.Double(
            centerX + dx * (size / 2) / distance,
            centerY + dy * (size / 2) / distance);
   }

    @Override
    public void highLight() {
        
        this.color = HIGHLIGHT_COLOR;

    }
    
    @Override
    public void unHighLight(){
        
      color = DEFAULT_COLOR;
        
    }
   
}
