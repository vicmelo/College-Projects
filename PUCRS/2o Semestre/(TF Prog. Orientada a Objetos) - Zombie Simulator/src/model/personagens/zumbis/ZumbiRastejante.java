package model.personagens.zumbis;

public class ZumbiRastejante extends Zumbi{

	
	public ZumbiRastejante(int x, int y, int mapSize) {
		super(x, y, mapSize);
	}
	
	public ZumbiRastejante(ZumbiRastejante zumbiRastejante) {
		super(zumbiRastejante);
	}

	protected int diferVigor(){ return 0;}
	protected int diferAgilidade(){ return -20;}

}
