package trabalhofinaltestes;

import java.util.Map;

interface INode<V, E> {
	
	void addAdj(E edgeValue, INode<V,E> dest);
	
	V getValue();
	
	Map<V,IEdge<V,E>> getAdjs();
	
	Map<V,IEdge<V,E>> getIncid();
	
	Double getDNumber();
	
	void setDNumber(Double dnumber);
	
}
