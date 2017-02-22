package model.mapa;

import java.util.Random;

import model.personagens.*;
import model.personagens.humanos.*;
import model.personagens.zumbis.*;

public class FactoryPersonagem {
	
	/**
	 * classe: "humano" ou "zumbi"
	 * @param tipo
	 * @param classe
	 * @return
	 * @throws Exception 
	 */
	public static Personagem getPersonagem(String classe, int x, int y, int mapSize, int prctAmigavel) throws Exception{
		
		Random sorteia = new Random();
		int tipo = sorteia.nextInt(1000);// 0% a 999%
		Personagem per = null;
		
		if(classe.equals("humano")){ //Humano
			if(tipo < 600) per = new HumanoComum(x,y,mapSize);
			else if(tipo >= 600 && tipo <= 800) per = new HumanoCorredor(x,y,mapSize);
			else if(tipo > 800) per = new HumanoResistente(x,y,mapSize);
			
			int sorteiaPctAmigavel = sorteia.nextInt(101);
			
			if(sorteiaPctAmigavel > prctAmigavel){
				
				per.setAmigavel(false);
			
			}
			
		}else if(classe.equals("zumbi")){
			if(tipo < 600) return new ZumbiComum(x,y,mapSize); 
			else if(tipo >= 600 && tipo < 750) per = new ZumbiCorredor(x,y,mapSize);
			else if(tipo >= 750 && tipo < 900 ) per = new ZumbiResistente(x,y,mapSize);
			else if(tipo >= 900 && tipo < 998 ) per = new ZumbiRastejante(x,y,mapSize);
			else per = new ZumbiNemesis(x,y,mapSize);
			
		}else{
			
			throw new Exception("Erro FactoryPersonagem: classe de personagem do parametro nao existe");
		
		}
		
		return per;
	}
}
