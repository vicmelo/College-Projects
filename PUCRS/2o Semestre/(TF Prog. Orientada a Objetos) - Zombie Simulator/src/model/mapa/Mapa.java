package model.mapa;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.Observable;
import java.util.Random;

import model.personagens.Personagem;
import model.personagens.humanos.Humano;
import model.personagens.humanos.HumanoComum;
import model.personagens.humanos.HumanoCorredor;
import model.personagens.humanos.HumanoResistente;
import model.personagens.zumbis.Zumbi;
import model.personagens.zumbis.ZumbiComum;
import model.personagens.zumbis.ZumbiCorredor;
import model.personagens.zumbis.ZumbiNemesis;
import model.personagens.zumbis.ZumbiRastejante;
import model.personagens.zumbis.ZumbiResistente;
import view.ui.App;

public class Mapa extends Observable{

	private static Mapa instance = null;
	private static int mapSize = App.TAMANHO; //tamanho definido na classe App
	private int qtdHumanos = 10,qtdZumbis = 10;
	private int porcentagemAmigavel;
	private Espaco[][] tabuleiro;
	private Personagem[][] radar;
	private List<Movimento> movimentosIniciais;
	
	private Mapa(int mapSize) {
		
		Random dimensoes = new Random();
		tabuleiro = new Espaco[mapSize][mapSize];
		setNull(tabuleiro);
		//O *9/10 la embaixo ja garante que nao fica na borda inferior nem na direita
		gerarCidade(tabuleiro,dimensoes.nextInt(2*tabuleiro.length/3),dimensoes.nextInt(2*tabuleiro[0].length/3));
		gerarEspacos(tabuleiro);
		
	}
	
	public void setDefinicoes(int qtdHumanos, int qtdZumbis, int pctHumanosAmigaveis){

		setPctAmigavel(pctHumanosAmigaveis);
		setPersonagens(qtdHumanos, qtdZumbis);
		
	}
	
	public void setPersonagens(int qtdHumanos, int qtdZumbis){
		
		if(Mapa.instance == null) return;
		this.qtdHumanos = qtdHumanos;
		this.qtdZumbis = qtdZumbis;
		getInstance().radar = new Personagem[mapSize][mapSize];
		//getInstance().criarPersonagens(qtdHumanos, qtdZumbis);
		
	}
	
	public void setPctAmigavel(int porcentagemAmigaveis){
		
		porcentagemAmigavel = porcentagemAmigaveis;
		
	}

	public static Mapa getInstance() { //Singleton
		
		if (instance == null) Mapa.instance = new Mapa(mapSize);
		return (instance);
		
	}
	
	public Espaco[][] getTabuleiro(){
		return tabuleiro;
	}
	
	public void criarPersonagens(){
		
			try {
				movimentosIniciais = new ArrayList<Movimento>();
				addHumanos(qtdHumanos);
				addZumbis(qtdZumbis);
				
			} catch (Exception e) {

				e.printStackTrace();
			}
			
	}
	
	private void addHumanos(int qtdHumanos) throws Exception{
		
		Random sorteia = new Random();
		
		for(int i=0;i<qtdHumanos;i++){
			
			if(this.isFull()) break; // se o mapa esta cheio, retorna
			int posicaoX = 0, posicaoY = 0;
			posicaoX = sorteia.nextInt(mapSize);
			posicaoY = sorteia.nextInt(mapSize);
			addPersonagem(posicaoX, posicaoY, "humano");
			
		}
	}
		
	private void addZumbis(int qtdZumbis) throws Exception{
		
		Random sorteia = new Random();
		
		for(int i=0;i<qtdZumbis;i++){	

			if(this.isFull()) break; // se o mapa esta cheio, retorna
			int posicaoX = sorteia.nextInt(mapSize);
			int posicaoY = sorteia.nextInt(mapSize);
			addPersonagem(posicaoX,posicaoY, "zumbi");
		
		}
	}
	
	private void addPersonagem(int x, int y, String tipo) throws Exception{
		
		if(this.isFull()) return;

		int count=x*mapSize + y;
		int countMax = mapSize*mapSize;
		Movimento m = null;
		
		while(radar[x][y] != null){//caso a posicao esteja ocupada, adiciona na proxima. Caso chegue no final, comeca do inicio do mapa
			
			x = count/mapSize;
			y = count % mapSize;
			count++;
			if(count >= countMax){
				count %= countMax;
			}
			
		}
		
		if(tipo.equals("humano")){

			radar[x][y] = FactoryPersonagem.getPersonagem("humano", x, y, mapSize, porcentagemAmigavel);
			
			if(radar[x][y] instanceof HumanoComum) m = new Movimento(new HumanoComum((HumanoComum)radar[x][y]), -1, -1, x, y);
			if(radar[x][y] instanceof HumanoCorredor) m = new Movimento(new HumanoCorredor((HumanoCorredor)radar[x][y]), -1, -1, x, y);
			if(radar[x][y] instanceof HumanoResistente) m = new Movimento(new HumanoResistente((HumanoResistente)radar[x][y]), -1, -1, x, y);
			
			movimentosIniciais.add(m);
			
		}else if(tipo.equals("zumbi")){
			
			radar[x][y] = FactoryPersonagem.getPersonagem("zumbi",x, y,mapSize, porcentagemAmigavel);
			
			if(radar[x][y] instanceof ZumbiComum) m = new Movimento(new ZumbiComum((ZumbiComum)radar[x][y]), -1, -1, x, y);
			if(radar[x][y] instanceof ZumbiCorredor) m = new Movimento(new ZumbiCorredor((ZumbiCorredor)radar[x][y]), -1, -1, x, y);
			if(radar[x][y] instanceof ZumbiResistente) m = new Movimento(new ZumbiResistente((ZumbiResistente)radar[x][y]), -1, -1, x, y);
			if(radar[x][y] instanceof ZumbiRastejante) m = new Movimento(new ZumbiRastejante((ZumbiRastejante)radar[x][y]), -1, -1, x, y);
			if(radar[x][y] instanceof ZumbiNemesis) m = new Movimento(new ZumbiNemesis((ZumbiNemesis)radar[x][y]), -1, -1, x, y);
		
			movimentosIniciais.add(m);
			
		}
		
		this.setChanged();
		this.notifyObservers(m);

	}

	public Espaco criarEspacoCidade(int n)// Factory method
	{	
		
		/*
		 * A ideia eh passar um valor aleatorio de 0 a 9 aqui - 80% de chance de criar um espaco urbano,
		 * 10% de criar destrocos e 10% de criar um mercado
		 */
		if(n<7) return new Espaco(TipoDeEspacos.urbano);
		else if (n<8) return new Espaco(TipoDeEspacos.destrocos);
		return new Espaco(TipoDeEspacos.mercado);
		
	}
	
	public Espaco criarEspacoRural(int n)
	{
		/*
		 * Cria um espaco rural aleatorio - 85% de chance de ser rural, 10% de destroco, 5% de celeiro
		 */
		
		if(n<17) return new Espaco(TipoDeEspacos.rural);
		else if(n<19) return new Espaco(TipoDeEspacos.destrocos);
		return new Espaco(TipoDeEspacos.celeiro);
	}

	public void setNull(Espaco[][] tab) {
		for (int i = 0; i < tab.length; i++)
			for (int j = 0; j < tab[i].length; j++)
				tab[i][j] = null;
	}

	private void gerarEspacos(Espaco[][] target) {
		Random geraEspacos = new Random();
		for (int i = 0; i < target.length; i++) {
			for (int j = 0; j < target[i].length; j++) {
				try {
					if (target[i][j] == null)
						target[i][j] = criarEspacoRural(geraEspacos.nextInt(20));
				} catch (NullPointerException e) {
					System.out.println("O elemento (" + i + "," + j + ") nao foi inicializado.");
					target[i][j] = null;
				}
				/*
				 * Cria um espaco 
				 */
			}
			// System.out.println();
		}
	}

	private void gerarCidade(Espaco[][] tab, int altura, int largura)
	{
		Random pontosDePartida = new Random();
		int x0=pontosDePartida.nextInt(tab.length-altura)*9/10+(tab.length)/20;
		int y0=pontosDePartida.nextInt(tab[0].length-largura)*9/10+(tab[0].length)/20;
		for(int x=x0;x<x0+altura;x++)
			for(int y=y0; y<y0+largura;y++)
				tab[x][y]=criarEspacoCidade(pontosDePartida.nextInt(10));
	}
	
	private void gerarCidadeComPontos(Espaco[][] tab,int altura, int largura, int x0, int y0)
	{
		Random pontosDePartida = new Random();
		for(int x=x0;x<x0+largura;x++)
			for(int y=y0; y<y0+altura;y++)
				tab[x][y]=criarEspacoCidade(pontosDePartida.nextInt(10));
	}
	
	private boolean isFull(){
		for(int x=0;x<mapSize;x++){
			for(int y=0;y<mapSize;y++){
				if(radar[x][y] == null){
					
					return false;
					
				}
			}
		}
		return true;
	}
	
	public void avancaRodada(int rodadas) throws GameOverException{	
		
		//caso a quantidade de rodadas seja zero ou negativo, não faz nada
		
		if(rodadas < 1) return;
		
		for(int i=0; i<rodadas;i++){
			
			int contZumbis = contPersonagens("zumbis");
			int contHumanos = contPersonagens("humanos");

			if(contZumbis == 0 && contHumanos > 0){
			
				throw new GameOverException("Humanos");
				
			}else if(contZumbis > 0 && contHumanos == 0){

				throw new GameOverException("Zumbis");
				
			}else if(contZumbis == 0 && contHumanos == 0){
				
				throw new GameOverException("Nenhum");
				
			}
			
			List<Movimento> movimentacoes = new ArrayList<Movimento>();
			
			for(int x=0;x<mapSize;x++){
				for(int y=0; y<mapSize;y++){
					
					if(radar[x][y] != null){
						
						//adiciona personagens que estao no raio de visao do personagem da posicao x y em uma matriz, para passar como parametro no metodo agir();
						
						Personagem p = radar[x][y];
						
						if(p.getMorto()){
							radar[x][y] = null;
							continue;
						}
						
						int percepcao = p.getPerceptRadius();
						
						//armazena a regiao do mapa percebida em uma matriz
						
						Personagem[][] areaAoRedor = new Personagem[percepcao*2+1][percepcao*2+1];
						
						//os pontos <xi,yi> sao os pontos dentro da area de percepcao do personagem
						
						for(int xi = x-percepcao; xi <= x+percepcao;xi++){
							
							if(xi < 0) continue;
							if(xi >= mapSize) continue;
							
							for(int yi = y-percepcao; yi<= y+percepcao;yi++){

								if(yi < 0) continue;
								if(yi >= mapSize) continue;
								areaAoRedor[xi-(x-percepcao)][yi-(y-percepcao)] = radar[xi][yi];
							
							}
							
						}
						p.agir(tabuleiro[x][y], areaAoRedor);
						
						int novoX = p.getPosX();
						int novoY = p.getPosY();
						
						if(novoX != x || novoY != y){
							
							movimentacoes.add(new Movimento(p, x,y,novoX,novoY));
						
						}
					}
				}
			}
			removeMortos(movimentacoes);
			
			//precisa ser separado, pois se fossem alterados na iteracoes, um personagem poderia acabar movendo-se duas vezes
			
			realizaMovimentacoes(movimentacoes); 
		}
	}
	
	private void removeMortos(List<Movimento> movimentos){
		
		for(int x=0;x<mapSize;x++){
			for(int y=0; y<mapSize;y++){
				
				if(radar[x][y] != null){
					Personagem p = radar[x][y];
					if (p.getMorto()) {
						
						for(int i=0;i<movimentos.size();i++){
							if(movimentos.get(i).personagem == p){
								movimentos.remove(i);
								i--;
							}
						}
						
						radar[x][y] = null;
						
						this.setChanged();
						this.notifyObservers(new Movimento(p,x,y,-1,-1));
						
					}
				}
			}
		}
	}
	
	private void realizaMovimentacoes(List<Movimento> movimentacoes){
		
		for(Movimento m : movimentacoes){
			
			if(m.novoX >= mapSize || m.novoX < 0 || m.novoY >= mapSize || m.novoY < 0) continue;
			
			//Se outro personagem foi para o destino nesta mesma rodada, nao faz o movimento
			
			if(radar[m.novoX][m.novoY] != null) continue;
			
			//Personagem p = radar[m.x][m.y];
			radar[m.novoX][m.novoY] = m.personagem;
			
			if(m.x > -1 && m.x < mapSize && m.y > -1 && m.y < mapSize){
							
				radar[m.x][m.y] = null;
			}

			this.setChanged();
			this.notifyObservers(m);
			
		}
		
	}
	
	public void reiniciar(){
				
		//Atualiza cada posicao na interface
		
		limpaMapa();

		realizaMovimentacoes(movimentosIniciais);
		
		//Adiciona os novos personagens no radar.
		
		for(int i=0; i< movimentosIniciais.size();i++){
			
			this.radar[movimentosIniciais.get(i).novoX][movimentosIniciais.get(i).novoY] = movimentosIniciais.get(i).personagem;
			
			//Atualiza posicao nos objetos personagens
			
			movimentosIniciais.get(i).personagem.setPos(movimentosIniciais.get(i).novoX, movimentosIniciais.get(i).novoY);
			movimentosIniciais.get(i).personagem.recuperaAtributosIniciais();
			
		}	
		//movimentosIniciais = movimentosAux
	}
	
	
	
	public void limpaMapa(){
		List<Movimento> movimMatar = new ArrayList<Movimento>();

		if(radar == null) {
		
			radar = new Personagem[mapSize][mapSize];
			return;
			
		}
		
		for(int i=0;i<mapSize;i++){
			for(int j=0;j<mapSize;j++){
				
				if(radar[i][j] != null){
					
					Personagem p = radar[i][j];
					radar[i][j].setMorto(true);
					
					//movimento ira remover mortos da interface
					
					movimMatar.add(new Movimento(p,p.getPosX(),p.getPosY(),-1,-1));

				}
			}
		}

		removeMortos(movimMatar);
	}
	
	public void novaSimulacao(int qtdHumanos, int qtdZumbis, int pctHumanosAmigaveis){

		limpaMapa();
		setDefinicoes(qtdHumanos, qtdZumbis, pctHumanosAmigaveis);
		criarPersonagens();
		
	}
	
	public void setRadar(Personagem[][] radarNovo){
		limpaMapa();
		
		List<Movimento> movimPopular = new ArrayList<Movimento>();
		
		for(int i=0;i<mapSize;i++){
			for(int j=0;j<mapSize;j++){
		
				if(radarNovo[i][j] != null){
					
					Personagem p = radarNovo[i][j];
					movimPopular.add(new Movimento(p, -1, -1, p.getPosX(), p.getPosY()));
					
				}
				
			}
		}
		realizaMovimentacoes(movimPopular);
		radar = radarNovo;
	}
	
	public int contPersonagens(String tipo){
		int cont = 0;
		
		if(tipo.equals("humanos")){
			
			for(int i=0;i<mapSize;i++){
				for(int j=0; j<mapSize;j++){
					if(radar[i][j] != null){
						if(radar[i][j] instanceof Humano) cont++;
					}
				}
			}
		}
		
		if(tipo.equals("zumbis")){
			
			for(int i=0;i<mapSize;i++){
				for(int j=0; j<mapSize;j++){
					if(radar[i][j] != null){
						if(radar[i][j] instanceof Zumbi) cont++;
					}
				}
			}
		}
		
		return cont;
	}
	
	public Personagem[][] getRadar(){
		return radar;
	}
	
	public void print() {
		for (int i = 0; i < tabuleiro.length; i++) {
			for (int j = 0; j < tabuleiro[i].length; j++)
				System.out.print(tabuleiro[i][j].toString().toUpperCase().charAt(0));
			
			System.out.println();
		}
		
	}

	
}
