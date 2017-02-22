
public class PilhaCalculadora extends Pilha{
	
	
	 public void soma(){
		if(this.isEmpty() || this.first.next == null) return;
		insert(Calculadora.soma(get(),get()));
	 }
	
	 public void mult(){
		if(isEmpty() || first.next == null) return;
	 	insert(Calculadora.mult(get(),get()));
	 }
	
	 public void sub(){
		if(isEmpty() || first.next == null) return;
		insert(Calculadora.sub(get(),get()));
	 }
	
	 public void div(){
		 if(isEmpty() || first.next == null) return;	 
		 insert(Calculadora.div(get(),get()));
	 }

	 public void sin(){
		 if(isEmpty()) return;
		 insert(Calculadora.sin(get()));
	 }	
	
	 public void cos(){
		 if(isEmpty()) return;
		 insert(Calculadora.cos(get()));
	 }
	
	 public void atan(){
		 if(isEmpty() || first.next == null) return;	
		 insert(Calculadora.atan(get(),get()));
	 }
}
