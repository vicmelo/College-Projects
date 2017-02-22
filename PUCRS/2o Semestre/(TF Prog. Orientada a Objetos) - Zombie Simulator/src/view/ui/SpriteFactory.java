package view.ui;

import java.util.Random;

import javax.swing.ImageIcon;

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

public class SpriteFactory {
	
	private final int QTD_HUMANO_COMUM = 8;
	private final int QTD_HUMANO_CORREDOR = 4;
	private final int QTD_HUMANO_RESISTENTE = 5;
	
	private final int QTD_ZUMBI_COMUM = 4;
	private final int QTD_ZUMBI_CORREDOR = 1;
	private final int QTD_ZUMBI_NEMESIS = 3;
	private final int QTD_ZUMBI_RASTEJANTE = 2;
	private final int QTD_ZUMBI_RESISTENTE = 1;
	
	private static SpriteFactory sprite;
	
	private SpriteFactory(){}
	
	public static SpriteFactory getInstance(){
		
		if(sprite == null) sprite = new SpriteFactory();
		return sprite;
	
	}
	
	public ImageIcon getSprite(Personagem tipo){

		Random sorteiaSprite = new Random();
		
		String local = "/imagens/";
		int numSprite = 0;
		
		if(tipo instanceof Humano){
		
			local+="humano";
			
			//Escolhe o sprite de acordo com o tipo de humano.
			
			if(tipo instanceof HumanoComum){ numSprite = sorteiaSprite.nextInt(QTD_HUMANO_COMUM)+1; local+="Comum"+numSprite;}
			if(tipo instanceof HumanoCorredor){ numSprite = sorteiaSprite.nextInt(QTD_HUMANO_CORREDOR)+1; local+="Corredor"+numSprite; }
			if(tipo instanceof HumanoResistente){ numSprite = sorteiaSprite.nextInt(QTD_HUMANO_RESISTENTE)+1; local+="Resistente"+numSprite; }
			
			return new ImageIcon(this.getClass().getResource(local+".gif"));
			
		}
		if(tipo instanceof Zumbi) {
			
			local+="zumbi";
			
			if(tipo instanceof ZumbiComum){ numSprite = sorteiaSprite.nextInt(QTD_ZUMBI_COMUM)+1; local+="Comum"+numSprite; }
			if(tipo instanceof ZumbiCorredor){ numSprite = sorteiaSprite.nextInt(QTD_ZUMBI_CORREDOR)+1; local+="Corredor"+numSprite; }
			if(tipo instanceof ZumbiResistente){ numSprite = sorteiaSprite.nextInt(QTD_ZUMBI_RESISTENTE)+1; local+="Resistente"+numSprite; }
			if(tipo instanceof ZumbiRastejante){ numSprite = sorteiaSprite.nextInt(QTD_ZUMBI_RASTEJANTE)+1; local+="Rastejante"+numSprite; }
			if(tipo instanceof ZumbiNemesis){ numSprite = sorteiaSprite.nextInt(QTD_ZUMBI_NEMESIS)+1; local+="Nemesis"+numSprite; }
			
			return new ImageIcon(this.getClass().getResource(local+".gif"));
		}
		
		return null;
	
	}
	
}
