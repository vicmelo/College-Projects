package model.personagens.humanos;

import model.personagens.Personagem;

public class HumanoCorredor extends Humano {

	
	public HumanoCorredor(int x, int y, int mapSize) {
		super(x, y, mapSize);
		movimentacoesRodada = 3;
	}
	
	public HumanoCorredor(HumanoCorredor humanoCorredor) {
	
		super(humanoCorredor);

	}

	protected int diferVigor(){ return 0;}
	protected int diferAgilidade(){ return 50;}


}
