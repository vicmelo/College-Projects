package model.personagens.humanos;

import model.personagens.Personagem;

public class HumanoComum extends Humano{
	
	public HumanoComum(int x, int y, int mapSize) {
		super(x, y, mapSize);
	}
	
	public HumanoComum(HumanoComum humanoComum) {
		
		super(humanoComum);
		
	}

	protected int diferVigor(){ return 0;}
	protected int diferAgilidade(){ return 0;}
	

}
