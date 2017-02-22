import java.util.Scanner;

public class App {
	
	
	public static void main(String[] args) {
	
		Scanner sc = new Scanner(System.in);
		PilhaCalculadora pilhaCalc = new PilhaCalculadora();
		while(sc.hasNext()){
			String line = sc.next();
			if(line.matches("[0-9]+")){
				pilhaCalc.insert(Integer.parseInt(line));
				//pilhaCalc.print();
				continue;
			}
			
			switch(line){
				case "pop":
					if(pilhaCalc.isEmpty()) break;
					pilhaCalc.get();
					break;
				case "dup":
					pilhaCalc.dup();
					break;
				case "swap":
					pilhaCalc.swap();
					break;
				case "+":
					pilhaCalc.soma();
					break;
				case "-":
					pilhaCalc.sub();
					break;
				case "*":
					pilhaCalc.mult();
					break;
				case "/":
					pilhaCalc.div();
					break;
				case "sin":
					pilhaCalc.sin();
					break;
				case "cos":
					pilhaCalc.cos();
					break;
				case "atan":
					pilhaCalc.atan();
					break;
			
			}
			
	
			//pilhaCalc.print();
		}
		pilhaCalc.print();
		System.out.println("Tamanho atual:"+pilhaCalc.getTam());
		System.out.println("Tamanho máximo:"+pilhaCalc.getTamMax());
		sc.close();
	
	}
}
