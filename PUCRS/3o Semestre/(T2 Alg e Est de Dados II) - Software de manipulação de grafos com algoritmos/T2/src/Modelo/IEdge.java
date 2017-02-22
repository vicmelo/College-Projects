package Modelo;

public interface IEdge<V, E> extends Cloneable {
	
	E getLabel();
	
	INode<V,E> getOrigin();
	
	INode<V,E> getDest();

	int compare(Object o1, Object o2);	

}
