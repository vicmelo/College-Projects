package model.personagens.zumbis;

import model.personagens.Personagem;

public class ZumbiComum extends Zumbi{

	
	public ZumbiComum(int x, int y, int mapSize) {
		super(x, y, mapSize);
	}
	
	public ZumbiComum(ZumbiComum personagem) {
		super(personagem);
	}

	protected int diferVigor(){ return 0;}
	protected int diferAgilidade(){ return 0;}

}
