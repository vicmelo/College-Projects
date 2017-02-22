/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package Modelo;

import java.util.ArrayList;
import java.util.List;
import java.util.Observable;
import javafx.beans.InvalidationListener;

/**
 *
 * @author 15105199
 */
public class AlgorithmReport extends Observable{
    
    public final List<Report> states;
    private String algorithmName;
    private int actualState;
    
    //algorithmReturn armazena retorno do algoritmo, caso haja. Quem utiliza esta classe deve saber o tipo de retorno do algoritmo.
    
    private Object algorithmReturn;
    
    public AlgorithmReport(){
        
        states = new ArrayList<>();
        states.add(new Report()); //report 0 (mostra o grafo sem alteração)
        actualState = 0;
        
    }

    
    //adiciona como clone para que no algoritmo, utilize um mesmo report inicial e o modifique. Assim, cada state aqui é um caso separado,
    //e não múltiplas referências para o mesmo objeto.
    public void addState(Report state){
        
        states.add(state.clone());
        
    }
    
    public int getStep(){
        
        return actualState;
        
    }
    
    public void next(){
        
        if(actualState+1 >= states.size()) return;
        
        actualState++;
        setChanged();
        notifyObservers(states.get(actualState));
        
    }
    
    public void previous(){
     
        if(actualState-1 < 0) return;
        
        actualState--;
        setChanged();
        notifyObservers(states.get(actualState));
        
    }
    
    public Report getState(){
        
        return states.get(actualState);
        
    }
    
    public void setReturn(Object algReturn){
        
        algorithmReturn = algReturn;
        
    }
    
    public Object getReturn(){
        
        return algorithmReturn;
        
    }
    
    public void setAlgorithmName(String name){
        
        algorithmName = name;
        
    }
    
    public String getAlgorithmName(){
        
        return algorithmName;
        
    }
    
}
