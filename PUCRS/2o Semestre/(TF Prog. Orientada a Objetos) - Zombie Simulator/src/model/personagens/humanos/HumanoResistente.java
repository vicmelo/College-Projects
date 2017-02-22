package model.personagens.humanos;

public class HumanoResistente extends Humano{
	
	
	public HumanoResistente(int x, int y, int mapSize) {
		super(x, y, mapSize);
	}
	
	public HumanoResistente(HumanoResistente humanoResistente) {
		
		super(humanoResistente);
		
	}

	protected int diferVigor(){ return 50;}
	protected int diferAgilidade(){ return 0;}
	
}
