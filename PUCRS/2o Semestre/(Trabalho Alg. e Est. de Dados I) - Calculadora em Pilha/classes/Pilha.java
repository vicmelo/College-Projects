public class Pilha {

	// ReferÃªncia para o primeiro elemento
	protected Node first;
	private int tamMax = 0;
	private int tam = 0;

	/*
	 * Node A lista usa esta classe interna. Cada nodo contem uma informacao
	 * e referencia para o proximo nodo.
	 */
	protected static class Node {
		Node next;
		float data;

		Node(float newData) {
			data = newData;
			next = null;
		}

	}

	public Pilha() {
		first = null;
	}
	
	public void insert(float data) {
		tam++;
		if(tam > tamMax) tamMax = tam;
		
		Node p = new Node(data);
		p.next = first;
		first = p;
	}
	
	public float get() {
		if(isEmpty()) return -1;
		tam--;
		Node p = first;
		first = first.next;
		return p.data;
	}

	public void dup() {
		if (isEmpty()) return;
		insert(first.data);
	}

	public void swap() {
		if(isEmpty() || first.next == null) return;
		
		Node secondAux = first.next;
		first.next = first.next.next;
		secondAux.next = first;
		first = secondAux;
	}

	public void print() {
		System.out.print("[ ");
		Node p = first;
		while (p != null) {
			System.out.print(p.data + " ");
			p = p.next;
		}
		System.out.println("]");
	}
	
	public int getTamMax(){
		return tamMax;
	}
	
	public int getTam(){
		return tam;
	}

	public boolean isEmpty() {
		if (first == null) return true;
		return false;
	}

}
