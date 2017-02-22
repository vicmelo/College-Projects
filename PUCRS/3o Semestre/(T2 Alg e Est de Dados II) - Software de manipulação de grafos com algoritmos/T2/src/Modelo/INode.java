package Modelo;

import java.util.List;
import java.util.Map;

public interface INode<V, E> extends Comparable<INode<V,E>>, Cloneable{

    
        enum Marca {BRANCO, CINZA, PRETO;}

        Marca getMark();
        
        void setMark(Marca m);
               
	void addAdj(E edgeValue, INode<V,E> dest);
	
	V getValue();
	
	Map<V,IEdge<V,E>> getAdjs();
	
	Map<V,IEdge<V,E>> getIncid();
	
	Double getDNumber();
	
	void setDNumber(Double dnumber);

        void removeAdj(V v);
        
        int compareTo(INode<V, E> n);
	
}
