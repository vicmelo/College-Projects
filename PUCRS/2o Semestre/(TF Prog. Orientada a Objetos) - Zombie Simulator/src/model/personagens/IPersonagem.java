package model.personagens;

import java.util.ArrayList;

import model.mapa.Espaco;

public interface IPersonagem {
	
	
	void agir(Espaco tipoEspacoPersonagem, Personagem[][] areaAoRedor);
	int getSaude();
	int getVigor();
	int getAgilidade();
	int getFome();
}
