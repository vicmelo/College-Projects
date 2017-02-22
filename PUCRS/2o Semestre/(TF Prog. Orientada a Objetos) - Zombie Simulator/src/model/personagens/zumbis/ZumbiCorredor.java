package model.personagens.zumbis;

public class ZumbiCorredor extends Zumbi{

	
	public ZumbiCorredor(int x, int y, int mapSize) {
		super(x, y, mapSize);
		movimentacoesRodada = 3;
	}
	
	public ZumbiCorredor(ZumbiCorredor zumbiCorredor) {
		super(zumbiCorredor);
	}

	protected int diferVigor(){ return 0;}
	protected int diferAgilidade(){ return 50;}

	@Override
	protected int limiteFome(){
		return 350;
	}
	
}
