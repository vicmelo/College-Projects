package model.mapa;

public enum TipoDeEspacos {
	destrocos(0), urbano (0.25), rural (0.5), assentamento (0.6), mercado (0.7), celeiro (0.9), debug(-1);
	
	private final double probComida;
	
	TipoDeEspacos(double prob)
	{
		probComida = prob;
	}
	
	public double getProb()
	{
		return probComida;
	}
}
