/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package trabalhofinaltestes;

/**
 *
 * @author victor
 */
public interface IAresta<N,E> {
    
    public E getValue();
		
    public INodo<N> getDestino();
    
    public INodo<N> getOrigem(); 
    
    public int compare(Object o1, Object o2);    
}
