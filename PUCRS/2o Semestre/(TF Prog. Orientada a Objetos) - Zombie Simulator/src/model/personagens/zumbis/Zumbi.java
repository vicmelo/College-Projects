package model.personagens.zumbis;

import java.util.*;
import model.personagens.Personagem;
import model.personagens.humanos.Humano;
import model.mapa.Espaco;
import model.mapa.TipoDeEspacos;

import java.lang.Math;

//INCOMPLETO
public abstract class Zumbi extends Personagem {

	Personagem /*@ spec_public @*/ perseguido;
	
	public Zumbi(int x, int y, int mapSize){
		super(x,y, mapSize);
		inicializaAtributos();
	}
	
	public Zumbi(Zumbi copia){
		super(copia);
		inicializaAtributos(copia);
	}
	
	protected void inicializaAtributos(Zumbi copia){
		morto = copia.getMorto();
		perceptRadius = copia.getPerceptRadius();
		this.vigor = copia.getVigor();
		this.agilidade = copia.getAgilidade();
	}
	
	protected void inicializaAtributos(){
		morto = false;
		perceptRadius = 3;
		Random r = new Random();
		//vigor varia de 60 a 80
		//agilidade varia de 95 a 115
		this.vigor = 60 + r.nextInt(21);
		this.agilidade = 95 + r.nextInt(21);
	}
	
	@Override
	public void recuperaAtributosIniciais(){
		
		super.recuperaAtributosIniciais();
		morto = false;
	}
	
	protected void atualizaAtributos(Personagem[][] areaPercebida){
		
		if(getMorto()) return;
		
		if(saude <= 0) {
			morto = true;
			return;
		}
		
		perceptArea = areaPercebida;
		this.perceptArea = areaPercebida;
		fome+=5;
		if(fome > limiteFome()){
			morto = true;
		}
	}
	
	public void agir(Espaco localDoPersonagem, Personagem[][] areaAoRedor){
		
		atualizaAtributos(areaAoRedor);
		
		//getMorto é chamado depois do atualizaAtributos pois, no atualizaAtributos, o personagem pode já ter morrido pela fome ter chegado no limite.
		
		if(getMorto()) return;

		boolean atacou = tentaAtacarAoRedor(areaAoRedor);
		
		if(!atacou){
			for(int i=0; i < movimentacoesRodada; i++){
				
				boolean emPerseguicao = emPerseguicao(areaAoRedor);
				
				if(emPerseguicao){
					
					andar(perseguido, areaAoRedor);
				
				}else{
					perseguido = getHumanoAoRedor(areaAoRedor);
					
					if(perseguido != null) andar(perseguido, areaAoRedor);
					else andar();
					
				}
			
			}
		}
		
	}
	
	protected Personagem getHumanoAoRedor(Personagem[][] areaAoRedor){
		
		for(Personagem[] pLinha: areaAoRedor){
			for(Personagem p: pLinha){
				if (p != null){
					if(p instanceof Humano) return p;
				}
			}
		}
		
		return null;
	}
	
	protected boolean emPerseguicao(Personagem[][] areaAoRedor){
		
		//nao esta perseguindo ninguem
		
		if(perseguido == null) return false;
		
		if(perseguido.getMorto()){
			perseguido = null;
			return false;
		}
		
		boolean perseguidoNaArea = false;
		
		//verificar se o perseguido fugiu da areaAoRedor
		
		if(perseguindo()){
			for(Personagem[] pLinha: areaAoRedor){
				for(Personagem p: pLinha){
					if (p == perseguido && p != null){
						
						perseguidoNaArea = true;
						break;
						
					}
				}
			}
		}
		
		if(!perseguidoNaArea){//perseguido fugiu
			encerraPerseguicao();
			return false;
			
		}else{
			return true;
		}
		
	}
	/*@
	  	requires alvo != null;
	  	ensures (\old(this.getPosX()) != this.getPosX()) || (\old(this.getPosY()) != this.getPosY());
	 @*/
	protected void andar(Personagem alvo, Personagem[][] areaAoRedor){
		
		int x = 0, y = 0;
		boolean esquerda = false;
		boolean acima = false;
		
		if(alvo.getPosX() < this.getPosX()){
			x--;
			acima = true;
		}else if(alvo.getPosX() > this.getPosX()){
			x++;
		}
		
		if(alvo.getPosY() < this.getPosY()){
			y--;
			esquerda = true;
		}else if(alvo.getPosY() > this.getPosY()){
			y++;
		}
		int novoX = this.getPerceptRadius()+x;
		int novoY = this.getPerceptRadius()+y;
		
		if(areaAoRedor[novoX][novoY] == null){
			
			int xDestMapa = this.getPosX()+x;
			int yDestMapa = this.getPosY()+y;
			
			if(xDestMapa < 0 || yDestMapa < 0 || xDestMapa >= mapSize || yDestMapa >= mapSize) return;

			this.setPos(xDestMapa, yDestMapa);
			
		}
		
		
	}
	
	//@ ensures perseguido == null;
	protected void encerraPerseguicao(){
		perseguido = null;
	}
	
	/*@ requires perseguido != null;
	 	ensures \result == true;
		
		also
		
		requires perseguido == null;
		ensures \result == false;
	
	@*/
	protected boolean perseguindo(){
		if (perseguido != null) return true;
		return false;
	}
	
	//@ requires local != null;
	//@ ensures fome < \old(fome);
	protected void comer(Espaco local){
		fome -= local.getProbComida() * 30;
	}
	
	protected void comer(){
		fome-=20;
	}

	@Override
	protected int limiteFome(){
		
		Random r = new Random();
		return 250+r.nextInt(200);
	
	}
	
	//Metodo criado apenas porque setAmigavel é herdado, ainda que zumbis não sejam amigaveis
	
	@Override
	public void setAmigavel(boolean b){}
	
	/*@
	  	requires alvo != null && (alvo instanceof Humano);
	  	ensures alvo.getSaude() < \old(alvo.getSaude()) && fome < \old(fome) && \result == true;
	  	
	  	also
	  	
	  	requires (alvo instanceof Humano) == false;
	  	ensures \result == false;
	  @*/
	@Override
	protected boolean atacar(Personagem alvo) {
		if(alvo instanceof Humano){
			alvo.serAtacado(this);
			comer();
			return true;
		}
		return false;
		
	}
	
	public int getAgilidade() {
		int agiTotal = agilidade+diferAgilidade();
		return  agiTotal;
	}

	public int getVigor() {
		int vigorTotal = vigor+diferVigor();
		return vigorTotal;
	}
	
	private boolean aoLado(Humano alvo)
	{
		int diffx=Math.abs(getPosX()-alvo.getPosX()),diffy=Math.abs(getPosY()-alvo.getPosY());
		if((diffx==1&&diffy==0)||(diffx==0&&diffy==1)) return true;
		return false;
	}
		
	protected abstract int diferVigor();
	protected abstract int diferAgilidade();

	
}
