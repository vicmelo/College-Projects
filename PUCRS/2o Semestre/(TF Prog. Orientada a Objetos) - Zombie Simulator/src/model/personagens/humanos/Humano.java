package model.personagens.humanos;

import java.util.Collection;
import java.util.Random;

import model.mapa.Espaco;
import model.mapa.TipoDeEspacos;
import model.personagens.Personagem;
import model.personagens.zumbis.Zumbi;
import model.personagens.zumbis.ZumbiComum;

//INCOMPLETO
public abstract class Humano extends Personagem {
	

	
	protected /*@ spec_public @*/ boolean amigavel;
	protected boolean dormindo;

	protected boolean faminto;
	protected boolean exausto;
	protected int exaustao;
	protected int rodadaAtualizaExaustao = RODADAS_EXAUSTAO; //exaustao aumenta a cada RODADAS_EXAUSTAO rodadas
	
	private static final int RODADAS_EXAUSTAO = 3;

	// quantos pontos de exaustão o personagem ganha cada rodada dormida

	private static final int RECUPERA_EXAUSTAO = 20;

	public Humano(int x, int y, int mapSize) {
		super(x, y, mapSize);
		inicializaAtributos();
	}
	
	public Humano(Humano copia){
		super(copia);
		inicializaAtributos(copia);
	}
	
	protected void inicializaAtributos(Humano copia) {
		
		amigavel = copia.getAmigavel();
		dormindo = copia.getDormindo();
		morto = copia.getMorto();
		exaustao = copia.getExaustao();
		perceptRadius = copia.getPerceptRadius();
		agilidade = copia.getAgilidade();
		vigor = copia.getVigor();
		
	}
	
	public boolean getAmigavel(){
		return amigavel;
	}
	
	public boolean getDormindo(){
		return dormindo;
	}
	
	public void setDormindo(boolean b){
		dormindo = b;
	}
	
	protected void inicializaAtributos() {
		
		amigavel = true;
		dormindo = false;
		morto = false;
		exaustao = 0;
		perceptRadius = 3;
		
		// agilidade e vigor variam de 90 a 110
		
		Random r = new Random();
		agilidade = 90 + r.nextInt(21);
		vigor = 90 + r.nextInt(21);
	}
	
	@Override
	public void recuperaAtributosIniciais() {
		
		super.recuperaAtributosIniciais();
		dormindo = false;
		morto = false;
		exaustao = 0;
		perceptRadius = 3;
	}

	//@ requires localDoPersonagem != null;
	public void agir(Espaco localDoPersonagem, Personagem[][] areaAoRedor) {
		
		atualizaAtributos(areaAoRedor);
		
		//getMorto é chamado depois do atualizaAtributos pois, no atualizaAtributos, o personagem pode já ter morrido pela fome ter chegado no limite.
		
		if(getMorto()) return;
		
		if (!dormindo) {
			
			boolean atacou = tentaAtacarAoRedor(areaAoRedor);
			
			if(!atacou){
				
				if (faminto() && localDoPersonagem.getTipo() != TipoDeEspacos.destrocos){
				
					comer(localDoPersonagem);
							
				}else {
					
					for(int i=0; i< movimentacoesRodada;i++){
						
						andar();
					
					}
					
				}
				
				if(exausto()){
					if(areaSegura(areaAoRedor)){
						dormir();
					}
				}
			}
		}
		
	}
	
	protected /*@ pure @*/ boolean areaSegura(Personagem[][] areaAoRedor){
		for(Personagem[] pLinha : areaAoRedor){
			for(Personagem p: pLinha){
				if(p != null){
					return false;
				}
			}
		}
		return true;
	}
	
	
	@Override
	//@ ensures this.amigavel == b;
	public void setAmigavel(boolean b){
		this.amigavel = b;
	}

	/*@
	  requires local != null;
	  ensures \old(fome) > fome;
	@*/
	protected void comer(Espaco local) {
		int novaFome = (int) Math.floor(fome - local.getProbComida()*100);
		if(novaFome < 0) novaFome = 0;
		fome = novaFome;
	}

	/*@
	 	requires inimigo != null && amigavel && (inimigo instanceof Humano);
	 	ensures \result == false;
	 	
	 	also
	 	
	 	requires inimigo == null && (!amigavel || (inimigo instanceof Zumbi)) && requires aoLado(inimigo);
	 	ensures \result == true;
	 
	 @*/
	protected boolean atacar(Personagem inimigo) {
		if (amigavel && (inimigo instanceof Humano)) {
			return false;
		} else if (aoLado(inimigo)) {
			inimigo.serAtacado(this);
			return true;
		}
		
		return false;
	}

	@Override
	protected int limiteFome() {
		return 100;
	}

	protected /*@ pure @*/ boolean faminto() {
		if (fome > limiteFome() * 70 / 100)
			return true;
		return false;
	}

	protected boolean exausto() {
		if (exaustao >= 70)
			return true;
		return false;
	}
	
	protected void dormir(){
		this.dormindo = true;
	}
	
	protected void acordar(){
		this.dormindo = false;
	}

	@Override
	protected void atualizaAtributos(Personagem[][] areaPercebida) {
		
		if(getMorto()) return;
		
		perceptArea = areaPercebida;
		
		if(saude <= 0) {
			morto = true;
			return;
		}
		
		// logica: atualização da exaustao
		
		if (dormindo) {
			if (exaustao > 0)
				exaustao -= RECUPERA_EXAUSTAO;
			else
				dormindo = false;

			if (exaustao <= RECUPERA_EXAUSTAO)
				acordar();

		} else {
			
			// se não for a rodada para aumentar exaustão, apenas diminui o verificador
			
			if (rodadaAtualizaExaustao > 0){
				rodadaAtualizaExaustao--; 
				
			}// se for a rodada que aumenta exaustão.
			else { 
				exaustao += 5;
				rodadaAtualizaExaustao = RODADAS_EXAUSTAO;
			}
			
			if (exaustao >= 100) {
				
				dormir();
				
			}
		}

		fome += 5;
		if (fome >= limiteFome()) {
			morto = true;
		}

	}
	
	public int getRodadaAtualizaExaustao(){
		return rodadaAtualizaExaustao;
	}

	public int getAgilidade() {
		int agiTotal = agilidade + diferAgilidade();
		int agiPerdida = agiTotal * exaustao / 100;
		return agiTotal - agiPerdida;
	}

	public int getVigor() {
		int vigorTotal = vigor + diferVigor();
		int vigorPerdido = vigorTotal * exaustao / 100;
		return vigorTotal - vigorPerdido;
	}

	protected abstract int diferVigor();

	protected abstract int diferAgilidade();

	public int getExaustao() {
		return exaustao;
	}

	public void setExaustao(int novaExaustao) {
		exaustao = novaExaustao;
	}
	
	public void setRodadaAtualizaExaustao(int rodadaAtualizaExaustaoAtual){
		rodadaAtualizaExaustao = rodadaAtualizaExaustaoAtual;
	}

}
