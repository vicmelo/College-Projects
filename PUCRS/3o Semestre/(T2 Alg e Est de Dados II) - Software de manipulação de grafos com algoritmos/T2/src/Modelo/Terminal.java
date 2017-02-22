/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package Modelo;

import java.util.Observable;
import java.util.Observer;

/**
 *
 * @author victor
 */
public class Terminal extends Observable{
    
   private static final Terminal INSTANCE = new Terminal();
   private String terminalText;
   
   
   private Terminal(){
       
      terminalText = "<<Exhibition algorithm terminal v0.1>>\nAqui são mostradas anotações dos algoritmos (caso haja)\ne mensagens de erros tratados.";
   
   }
   
   public static Terminal getTerminal(){
       
       return INSTANCE;
       
   }
   
   public static void println(String text){
       
       INSTANCE.terminalText+= "\n"+text;
       INSTANCE.setChanged();
       INSTANCE.notifyObservers();
       
   }
   
   public static void clear(){
       
       INSTANCE.terminalText = "";
       INSTANCE.setChanged();
       INSTANCE.notifyObservers();
       
   }
   
   public String getText(){
        
       return terminalText;
       
   }
   
   
}
