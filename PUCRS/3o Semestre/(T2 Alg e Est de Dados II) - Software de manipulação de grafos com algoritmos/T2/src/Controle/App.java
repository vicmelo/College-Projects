/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package Controle;

import Interface.screen.GraphFrame;
import Modelo.Terminal;
import javax.swing.JFrame;

/**
 *
 * @author victor
 */
public class App {
    
   public static void main(String[] args)
   {
       
       Controller c = new Controller();
      c.graphFrame.setVisible(true);
   
   }
    
}
