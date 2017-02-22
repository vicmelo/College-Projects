package model.personagens.zumbis;

import java.util.Random;

public class ZumbiNemesis extends Zumbi{

	
	public ZumbiNemesis(int x, int y, int mapSize) {
		super(x, y, mapSize);
	}
	
	public ZumbiNemesis(ZumbiNemesis zumbiNemesis) {
		super(zumbiNemesis);
	}

	protected int diferVigor(){ return 100;}
	protected int diferAgilidade(){ return 100;}

	@Override
	protected int limiteFome(){
		
		Random r = new Random();
		return 700+r.nextInt(300);

	}
	
}
