package model.personagens;


import model.mapa.Espaco;
import model.personagens.zumbis.Zumbi;
import model.personagens.humanos.Humano;

import java.util.*;

public abstract class Personagem implements IPersonagem {

	//@ public invariant getSaude() >= 0;
	//@ public invariant getFome() >= 0;
	
	protected /*@ spec_public @*/ static int vigor;
	protected /*@ spec_public @*/ static int agilidade;
	protected /*@ spec_public @*/ int saude;
	protected /*@ spec_public @*/ int fome;
	protected /*@ spec_public @*/ int[] posicao = new int[2]; //x, y
	protected Personagem[][] perceptArea;
	protected /*@ spec_public @*/ boolean morto; //se o personagem esta morto ou nao
	protected /*@ spec_public @*/ int perceptRadius;
	protected /*@ spec_public @*/ int movimentacoesRodada;
	protected /*@ spec_public @*/ int mapSize;
	protected List<Personagem> personagensPercebidos;
	
	/*@ requires x >= 0 && x < getMapSize() && y >= 0 && y < getMapSize();
	 	requires mapSize > 0;
	 	
	 	ensures saude == 100 && 
	 			fome == 0 && 
	 			movimentacoesRodada == 1 && 
	 			posicao[0] == x && 
	 			posicao[1] == y;
	@*/
	public Personagem(int x, int y,int mapSize){
		
		saude = 100;
		fome = 0;
		movimentacoesRodada = 1;
		this.setPos(x, y);
		this.mapSize = mapSize;
	}
	
	public void recuperaAtributosIniciais(){
		saude = 100;
		fome = 0;
		movimentacoesRodada = 1;
	}
	
	/*@ requires copia != null;
	 	
	 	ensures saude == copia.getSaude() &&
	 			fome == copia.getFome() &&
	 			movimentacoesRodada == copia.getMovimentacoesRodada() &&
	 			posicao[0] == copia.getPosX() && 
	 			posicao[1] == copia.getPosY() &&
	 			mapSize == copia.mapSize;
	 @*/
	public Personagem(Personagem copia){

		saude = copia.getSaude();
		fome = copia.getFome();
		movimentacoesRodada = copia.getMovimentacoesRodada();
		this.setPos(copia.getPosX(), copia.getPosY());
		this.mapSize = copia.mapSize;
		
	}
	
	//@ ensures \result == mapSize;
	/*@ pure @*/public int getMapSize(){
		return mapSize;
	}
	
	//@ ensures \result == morto
	public boolean getMorto(){
		return morto;
	}
	
	//@ requires saude > -1;
	//@ ensures this.saude == saude;
	public void setSaude(int saude){
	
		this.saude = saude;
	
	}
	
	//@ requires vigor > -1;
	//@ ensures this.vigor == vigor;
	public void setVigor(int vigor){
		
		this.vigor = vigor;
		
	}
	
	//@ requires movimentacoesRodada > -1;
	//@ ensures this.movimentacoesRodada == movimentacoesRodada;
	public void setMovimentacoesRodada(int movimentacoesRodada){
		
		this.movimentacoesRodada = movimentacoesRodada;
		
	}
	
	//@ requires perceptRadius > -1;
	//@ ensures this.perceptRadius == perceptRadius;
	public void setPerceptRadius(int perceptRadius){
		
		this.perceptRadius = perceptRadius;
		
	}
	
	//@ ensures this.morto == morto;
	public void setMorto(boolean morto){
		
		this.morto = morto;
		
	}
	
	//@ requires mapSize > 0;
	//@ ensures this.mapSize = mapSize;
	public void setMapSize(int mapSize){
		
		this.mapSize = mapSize;
		
	}
	
	public void setAgilidade(int agilidade){
		
		this.agilidade = agilidade;
	
	}
	
	public int getMovimentacoesRodada(){
		
		return this.movimentacoesRodada;
		
	}
	
	public abstract void setAmigavel(boolean b);

	@Override
	public abstract void agir(Espaco tipoEspacoPersonagem, Personagem[][] areaAoRedor);
	
	protected void andar() {
		
		Random local = new Random();
		
		 //moverPara é um valor entre 0 e 7. Decide pra qual lado o personagem vai se mover dentre os 8 quadrados ao seu redor
		
		int moverPara = local.nextInt(8);
		int x,y;
		x = this.getPerceptRadius();
		y = this.getPerceptRadius();
		
		//se o personagem esta cercado, fica parado
		
		boolean estaCercado = this.cercado();
		if(estaCercado) return;
		
		int xDest = 0,yDest = 0,xDestMapa = 0,yDestMapa = 0;
		do{
			
			switch (moverPara){
				case 0:
					
					xDest = x-1;
					yDest = y-1;					
					xDestMapa = this.getPosX()-1;
					yDestMapa = this.getPosY()-1;
					break;
					
				case 1:
					xDest = x-1;
					yDest = y;
					xDestMapa = this.getPosX()-1;
					yDestMapa = this.getPosY();
					break;
					
				case 2:
					
					xDest = x-1;
					yDest = y+1;
					xDestMapa = this.getPosX()-1;
					yDestMapa = this.getPosY()+1;
					break;
					
				case 3:
					
					xDest = x;
					yDest = y+1;
					xDestMapa = this.getPosX();
					yDestMapa = this.getPosY()+1;
					break;
					
				case 4:
					
					xDest = x+1;
					yDest = y+1;
					xDestMapa = this.getPosX()+1;
					yDestMapa = this.getPosY()+1;
					break;
					
				case 5:
					
					xDest = x+1;
					yDest = y;
					xDestMapa = this.getPosX()+1;
					yDestMapa = this.getPosY();
					break;
					
				case 6:
					
					xDest = x+1;
					yDest = y-1;
					xDestMapa = this.getPosX()+1;
					yDestMapa = this.getPosY()-1;
					break;
					
				case 7:
					
					xDest = x;
					yDest = y-1;			
					xDestMapa = this.getPosX();
					yDestMapa = this.getPosY()-1;
					
			}
			
			if(perceptArea[xDest][yDest] != null){
				
				moverPara += 1;
				moverPara %= 8;
				
			}
			
		}while(perceptArea[xDest][yDest] != null);
		
		if(xDestMapa < 0 || yDestMapa < 0 || xDestMapa >= mapSize || yDestMapa >= mapSize) return;
		
		this.setPos(xDestMapa, yDestMapa);
		
	}
	
	protected boolean tentaAtacarAoRedor(Personagem[][] areaAoRedor){
		
		int xPersonagem = this.perceptRadius;
		int yPersonagem = this.perceptRadius;
		
		boolean atacou = false;
		
		//verifica se ha algum personagem ao redor(8 quadrados da volta) e ataca-o caso precise
		
		for(int x=xPersonagem-1;x<=xPersonagem+1;x++){
			for(int y = yPersonagem-1; y <= yPersonagem+1;y++){
				
				if( x == xPersonagem && y == yPersonagem) continue;
				if(areaAoRedor[x][y] != null) return atacar(areaAoRedor[x][y]);
				
			}
		}
		return false;
	}

	/*@ 
	  	
	  	ensures getFome() <= \old(getFome());
	 @*/
	protected abstract void comer(Espaco local);
	
	/*@ requires alvo != null; 
	 	ensures alvo.getSaude() <= \old(alvo.getSaude());
	 @*/
	protected abstract boolean atacar(Personagem alvo);

	protected abstract void atualizaAtributos(Personagem[][] areaPercebida);
	
	@Override
	public abstract int getVigor();
	
	//retorna o quanto de fome o personagem aguenta sem morrer
	
	protected abstract int limiteFome();
	
	public int getPerceptRadius(){
		
		return this.perceptRadius;
	
	}
	
	/*@ 
 	requires perceptArea[this.getPerceptRadius()-1][this.getPerceptRadius()-1] == null||
  			 perceptArea[this.getPerceptRadius()-1][this.getPerceptRadius()] == null ||
  			 perceptArea[this.getPerceptRadius()-1][this.getPerceptRadius()+1] == null ||
  			 perceptArea[this.getPerceptRadius()][this.getPerceptRadius()-1] == null ||
  			 perceptArea[this.getPerceptRadius()][this.getPerceptRadius()+1] == null ||
  			 perceptArea[this.getPerceptRadius()+1][this.getPerceptRadius()-1] == null ||
  			 perceptArea[this.getPerceptRadius()+1][this.getPerceptRadius()] == null ||
  			 perceptArea[this.getPerceptRadius()+1][this.getPerceptRadius()+1] == null;
  	
  	ensures \return == false;
  	
	also

	requires perceptArea[this.getPerceptRadius()-1][this.getPerceptRadius()-1] != null &&
  			 perceptArea[this.getPerceptRadius()-1][this.getPerceptRadius()] != null &&
  			 perceptArea[this.getPerceptRadius()-1][this.getPerceptRadius()+1] != null &&
  			 perceptArea[this.getPerceptRadius()][this.getPerceptRadius()-1] != null &&
  			 perceptArea[this.getPerceptRadius()][this.getPerceptRadius()+1] != null &&
  			 perceptArea[this.getPerceptRadius()+1][this.getPerceptRadius()-1] != null &&
  			 perceptArea[this.getPerceptRadius()+1][this.getPerceptRadius()] != null &&
  			 perceptArea[this.getPerceptRadius()+1][this.getPerceptRadius()+1] != null;
  	ensures \return == true;
	 @*/
	public boolean cercado(){
		
		int posPersonagemX = this.getPerceptRadius();
		int posPersonagemY = this.getPerceptRadius();
		
		for(int x=posPersonagemX-1;x<=posPersonagemX+1;x++){
			for(int y = posPersonagemY-1; y<= posPersonagemY+1; y++){
			
				if(x == posPersonagemX && y == posPersonagemY) continue;
				if(perceptArea[x][y] == null) return false;
		
			}
		}
	
		return true;
	
	}
	
	@Override
	public /*@ pure helper @*/ int getSaude() {
		
		return this.saude;
	
	}
	
	@Override
	public /*@ pure helper @*/ int getFome() {
		
		return this.fome;
		
	}
	

	//@ requires novaFome >= 0;
	//@ ensures this.fome == novaFome;
	public void setFome(int novaFome){
		
		this.fome = novaFome;
		
	}
	
	//@ requires x >= 0 && x < mapSize && y >= 0 && y < mapSize
	//@ ensures posicao[0] == x && posicao[1] == y
	public void setPos(int x, int y){
		
		posicao[0] = x;
		posicao[1] = y;
		
	}
	
	public int getPosX(){
		
		return posicao[0];
		
	}

	public int getPosY(){
		
		return posicao[1];
		
	}
	
	/*@
 		requires atacante != null;
 		ensures \old(saude) > saude;
 	@*/
	public void serAtacado(Humano atacante){
		
		saude-=(90/vigor)*(atacante.getAgilidade()/10)*(100-atacante.getExaustao())/50;

	}
	
	/*@
	 	requires atacante != null;
	 	ensures \old(saude) > saude;
	 @*/
	public void serAtacado(Zumbi atacante){
	
		saude-=(90/vigor)*(atacante.getAgilidade()/8);

	}
	
	protected /*@ pure @*/ boolean aoLado(Personagem alvo)
	{
		
		int diffx=Math.abs(getPosX()-alvo.getPosX()),diffy=Math.abs(getPosY()-alvo.getPosY());
		if((diffx==1&&diffy==0)||(diffx==0&&diffy==1)) return true;
		return false;
	
	}
}
