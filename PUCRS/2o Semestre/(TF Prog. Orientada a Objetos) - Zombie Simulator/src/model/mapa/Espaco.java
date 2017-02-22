package model.mapa;

public class Espaco {
	private TipoDeEspacos tipoDoEspaco; //Placeholder
	/*A ideia ï¿½ que a probabilidade seja um valor de 0 a 1 que mapeia, quase que diretamente,
	a chance de achar comida (o que pode ser afetado pelo tipo de humano)
	Sobre a comida: acho que pode ser uma boa tb só garantir que a probabilidade de achar comida
	represente quanto de fome o personagem mata naquele lugar
	*/
	
	public Espaco(TipoDeEspacos tipo)
	{
		tipoDoEspaco = tipo;
	}
	
	public double getProbComida()
	{
		return tipoDoEspaco.getProb();
	}
	
	public TipoDeEspacos getTipo()
	{
		return tipoDoEspaco;
	}
	
	@Override
	public String toString()
	{
		return tipoDoEspaco.toString();
	}
}
