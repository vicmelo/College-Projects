/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package Interface;

import Interface.CreatingType;
import java.util.*;

/**
 *
 * @author victor
 */
public class InsertValue extends Observable{
    
    protected String value;
    public String v1 = "",v2 = ""; //node values for algorithms
    protected CreatingType type;

    public String getValue() {
        
        return value;
    
    }

    public void setValue(String value) {
        
        this.value = value;
        setChanged();
        notifyObservers();
        
    }

    public CreatingType getCreatingType() {
        return type;
    }

    public void setCreatingType(CreatingType type) {
        this.type = type;
    }
    
    public void setV1Algorithm(String value) {
        
        this.v1 = value;
        
    }
    
    public void setV2Algorithm(String value) {
        System.out.println("t4");
        this.v2 = value;
        setChanged();
        notifyObservers(type);
        
    }
    
    public String getV1(){
        
        return v1;
        
    }
    
    public String getV2(){
        
        return v2;
        
    }
    
    
    
}
