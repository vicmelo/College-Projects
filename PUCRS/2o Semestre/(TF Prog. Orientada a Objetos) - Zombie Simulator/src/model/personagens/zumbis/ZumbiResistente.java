package model.personagens.zumbis;

import java.util.Random;

public class ZumbiResistente extends Zumbi{

	
	public ZumbiResistente(int x, int y, int mapSize) {
		super(x, y, mapSize);
	}
	
	public ZumbiResistente(ZumbiResistente zumbiResistente) {
	
		super(zumbiResistente);
	
	}

	protected int diferVigor(){ return 50;}
	protected int diferAgilidade(){ return 0;}

	@Override
	protected int limiteFome(){
		
		Random r = new Random();
		return 400+r.nextInt(200);

		
	}
}
