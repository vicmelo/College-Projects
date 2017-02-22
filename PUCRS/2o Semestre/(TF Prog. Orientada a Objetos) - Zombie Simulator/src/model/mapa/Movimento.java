package model.mapa;

import model.personagens.Personagem;

//estrutura usada na hora da movimentacao dos personagens. Necessaria para criar uma lista
//de movimentacoes que serao realizadas na rodada. Caso fosse alterado diratamente na iteracao,
//um personagem poderia acabar movendo-se varias vezes numa rodada

public class Movimento{
	
	public Personagem personagem;
	public int x;
	public int y;
	public int novoX;
	public int novoY;
	
	public Movimento(Personagem per, int x, int y, int novoX, int novoY){
		
		this.personagem = per;
		this.x = x;
		this.y = y;
		this.novoX = novoX;
		this.novoY = novoY;
		
	}
}
