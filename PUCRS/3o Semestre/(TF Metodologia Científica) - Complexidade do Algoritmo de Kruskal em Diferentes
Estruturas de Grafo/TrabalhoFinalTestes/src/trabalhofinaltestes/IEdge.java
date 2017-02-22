package trabalhofinaltestes;

public interface IEdge<V, E> {
	
	E getLabel();
	
	INode<V,E> getOrigin();
	
	INode<V,E> getDest();

	int compare(Object o1, Object o2);
	

}
