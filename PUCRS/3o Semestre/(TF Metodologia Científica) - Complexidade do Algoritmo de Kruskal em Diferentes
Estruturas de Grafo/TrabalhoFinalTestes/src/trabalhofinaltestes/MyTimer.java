package trabalhofinaltestes;

public class MyTimer {

	private long tempoIni, tempoFim;
	private double tempoSec;
	
	public void start(){
		
		tempoIni = System.nanoTime();
		
	}
	
	public void stop(){
		
		tempoFim = System.nanoTime();
		
		tempoSec = ((double)tempoFim - (double) tempoIni) / (double) 1000000000.0;
	
	}
	
	public double getTempo(){
		
		return tempoSec;
		
	}
	
}
