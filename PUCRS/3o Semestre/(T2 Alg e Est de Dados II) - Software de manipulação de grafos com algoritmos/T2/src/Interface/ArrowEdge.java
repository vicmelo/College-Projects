/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package Interface;

import com.sun.javafx.geom.transform.BaseTransform;
import java.awt.*;
import java.awt.geom.*;

/**
 *
 * @author victor
 */
public class ArrowEdge extends AbstractEdge{
    
    
    public ArrowEdge(Integer value){
        
        this.stroke = DEFAULT_STROKE;
        this.value = value;
        
    }
      
//     public void draw(Graphics2D g2)
//   {
//      Path2D line = getArrow(g2);
//
//      g2.draw(getArrow(g2));
//      
//   }
//    
//   public Path2D getArrow(Graphics2D g2)
//   {
//      Rectangle2D startBounds = super.getStart().getBounds();
//      Rectangle2D endBounds = super.getEnd().getBounds();
//      
//      Point2D startCenter = new Point2D.Double(
//            startBounds.getCenterX(), startBounds.getCenterY());
//      
//      Point2D endCenter = new Point2D.Double(
//            endBounds.getCenterX(), endBounds.getCenterY());
//      
//      Line2D line = new Line2D.Double(super.getStart().getConnectionPoint(endCenter),super.getEnd().getConnectionPoint(startCenter));
//      Path2D resultPath = new Path2D.Double();
//      resultPath.append(line, true);
//      
//      double angle = getAngle(line.getP1(), line.getP2());
//      
//      Path2D arrow = createArrowForLine(line.getP2(), angle, 10, 30, line);
//      resultPath.append(arrow, true);
//      
//      FontMetrics fm = g2.getFontMetrics();
//      
//      this.oldColor = g2.getColor();
//     
//      g2.setColor(color);
//      g2.fill(line);
//      g2.setColor(oldColor);
//      g2.setStroke(stroke);
//      g2.drawString(getValue().toString(), getLineCenterX(line).floatValue(), getLineCenterY(line).floatValue());
//      
//      return resultPath;
//   
//   }
    
    public void draw(Graphics2D g2)
   {
      Rectangle2D startBounds = super.getStart().getBounds();
      Rectangle2D endBounds = super.getEnd().getBounds();
      
      Point2D startCenter = new Point2D.Double(
            startBounds.getCenterX(), startBounds.getCenterY());
      
      Point2D endCenter = new Point2D.Double(
            endBounds.getCenterX(), endBounds.getCenterY());
      
      Line2D line = new Line2D.Double(super.getStart().getConnectionPoint(endCenter),super.getEnd().getConnectionPoint(startCenter));
      
      Path2D arrow = getArrow(g2, line);

      FontMetrics fm = g2.getFontMetrics();
      
      g2.setStroke(stroke);
      g2.drawString(getValue().toString(), getLineCenterX(line).floatValue(), getLineCenterY(line).floatValue());
      
      g2.draw(arrow);
      
   }
    
   public Path2D getArrow(Graphics2D g2, Line2D line)
   {
      Path2D resultPath = new Path2D.Double();
      resultPath.append(line, true);
      
      double angle = getAngle(line.getP1(), line.getP2());
      
      Path2D arrow = createArrowForLine(line.getP2(), angle, 10, 30, line);
      resultPath.append(arrow, true);
      
      return resultPath;
   
   }
   
   /**
    * retorna o angulo entre dois pontos
    * @param p1
    * @param p2
    * @return 
    */
   private double getAngle(Point2D p1, Point2D p2) {
       
      float angle = (float) Math.toDegrees(Math.atan2(p1.getY() - p2.getY(), p1.getX() - p2.getX()));

      if(angle < 0){
         angle += 360;
      }

      return angle;
      
   }
    
   /**
    * Cria a ponta da seta
    * @param fromPoint end of the arrow
    * @param rotationDeg rotation angle of line
    * @param length arrow length
    * @param wingsAngleDeg wingspan of arrow
    * @return Path2D arrow shape
    */
    public static Path2D createArrowForLine(Point2D fromPoint, double rotationDeg, double length, double wingsAngleDeg, Line2D line) {

        double ax = fromPoint.getX();
        double ay = fromPoint.getY();
        
        double radB = Math.toRadians(rotationDeg - wingsAngleDeg);
        double radC = Math.toRadians(rotationDeg + wingsAngleDeg);

        Path2D resultPath = new Path2D.Double();
        resultPath.moveTo(length * Math.cos(radB) + ax, length * Math.sin(radB) + ay);
        resultPath.lineTo(ax, ay);
        resultPath.lineTo(length * Math.cos(radC) + ax, length * Math.sin(radC) + ay);
        return resultPath;
        
    }
    

   public boolean contains(Point2D aPoint)
   {
      final double MAX_DIST = 2;
      return getConnectionPoints().ptSegDist(aPoint) 
         < MAX_DIST;
   }

    @Override
    public void highLight() {
    
        this.stroke = HIGHLIGHT_STROKE;
        
    }
    
    public void unHighLight(){
        
        this.stroke = DEFAULT_STROKE;
        
    }
    
}
