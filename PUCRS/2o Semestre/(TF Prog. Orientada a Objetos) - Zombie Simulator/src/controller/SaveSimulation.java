package controller;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;

import model.personagens.Personagem;
import model.personagens.humanos.Humano;
import model.personagens.humanos.HumanoComum;
import model.personagens.humanos.HumanoCorredor;
import model.personagens.humanos.HumanoResistente;
import model.personagens.zumbis.ZumbiComum;
import model.personagens.zumbis.ZumbiCorredor;
import model.personagens.zumbis.ZumbiNemesis;
import model.personagens.zumbis.ZumbiRastejante;
import model.personagens.zumbis.ZumbiResistente;
import view.ui.App;

public class SaveSimulation {
	
	String personagensString;
	private static SaveSimulation instance;
	public final String NOME_ARQUIVO = "save.txt";
	
	
	
	private SaveSimulation(){}
	
	public static SaveSimulation getInstance(){
		if(instance == null) instance = new SaveSimulation();
		return instance;
	}

	public String salvar(Personagem[][] matrizPersonagens){
		personagensString = "";
		for(Personagem[] pLinha: matrizPersonagens){
			for(Personagem p : pLinha){
				if(p != null){
					
					int tipo = getTipo(p);
					
					//Se for humano
	
					personagensString += getTipo(p)+" "+
										p.getPosX()+" "+
										p.getPosY()+" "+
										p.getSaude()+" "+
										p.getAgilidade()+" "+
										p.getVigor()+" "+
										p.getFome()+" "+
										p.getMovimentacoesRodada()+" "+
										p.getMapSize()+" "+
										p.getPerceptRadius()+" "+
										p.getMorto()+" ";
	
					
					if(tipo > 0 && tipo <= 3 ){
						
						personagensString += ((Humano) p).getAmigavel()+" "+
											 ((Humano) p).getDormindo()+" "+
											 ((Humano) p).getExaustao()+" "+
											 ((Humano) p).getRodadaAtualizaExaustao();
				
					}
					
					personagensString +="\n";
				}
			}
		}
				
		try {
			
			BufferedWriter writer = new BufferedWriter(new FileWriter(NOME_ARQUIVO));
			writer.write(personagensString);
			
			writer.close();
		
		}
		catch(IOException e) {
			
			System.out.println("IOException");
			
		}
			
		return personagensString;
	
	}
	
	public Personagem[][] carregar(){
		
		Personagem[][] radar = new Personagem[App.TAMANHO][App.TAMANHO];
		
		try {
			
			BufferedReader reader = new BufferedReader(new FileReader(NOME_ARQUIVO));
			String linhaAtual;
			
			while((linhaAtual = reader.readLine()) != null){
				
				String[] vetorStr = linhaAtual.split(" ");
				Personagem p = getTipo(Integer.parseInt(vetorStr[0]));
				p.setPos(Integer.parseInt(vetorStr[1]), Integer.parseInt(vetorStr[2]));
				p.setSaude(Integer.parseInt(vetorStr[3]));
				p.setAgilidade(Integer.parseInt(vetorStr[4]));
				p.setVigor(Integer.parseInt(vetorStr[5]));
				p.setFome(Integer.parseInt(vetorStr[6]));
				p.setMovimentacoesRodada(Integer.parseInt(vetorStr[7]));
				p.setMapSize(Integer.parseInt(vetorStr[8]));
				p.setPerceptRadius(Integer.parseInt(vetorStr[9]));
				p.setMorto(Boolean.parseBoolean(vetorStr[10]));
				
				if(p instanceof Humano){
					
					((Humano) p).setAmigavel(Boolean.parseBoolean(vetorStr[11]));
					((Humano) p).setDormindo(Boolean.parseBoolean(vetorStr[12]));
					((Humano) p).setExaustao(Integer.parseInt(vetorStr[13]));
					((Humano) p).setRodadaAtualizaExaustao(Integer.parseInt(vetorStr[14]));
					
				}
				

				radar[p.getPosX()][p.getPosY()] = p;
			}
			
			reader.close();
		
		}
		catch(IOException e) {
			
			System.out.println("IOException");
			
		}
		
		for(int i=0;i < App.TAMANHO;i++){
			for(int j=0;j < App.TAMANHO;j++){
				if(radar[i][j] != null) System.out.println("Carregado <"+radar[i][j].getPosX()+", "+radar[i][j].getPosY()+">");
			}
		}
		return radar;
		
	}
	
	public int getTipo(Personagem p){
	
		if(p instanceof HumanoComum) return 1;
		if(p instanceof HumanoCorredor) return 2;
		if(p instanceof HumanoResistente) return 3;
	
		if(p instanceof ZumbiComum) return 4;
		if(p instanceof ZumbiCorredor) return 5;
		if(p instanceof ZumbiResistente) return 6;
		if(p instanceof ZumbiRastejante) return 7;
		if(p instanceof ZumbiNemesis) return 8;
		
		return -1;

	}
	
	public Personagem getTipo(int p){
		
		if(p == 1) return new HumanoComum(-1, -1, -1);
		if(p == 2) return new HumanoCorredor(-1, -1, -1);
		if(p == 3) return new HumanoResistente(-1, -1, -1);
		
		if(p == 4) return new ZumbiComum(-1, -1, -1);
		if(p == 5) return new ZumbiCorredor(-1, -1, -1);
		if(p == 6) return new ZumbiResistente(-1, -1, -1);
		if(p == 7) return new ZumbiRastejante(-1, -1, -1);
		if(p == 8) return new ZumbiNemesis(-1, -1, -1);
		
		return null;

	}
}
