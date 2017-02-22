package view.ui;

import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Dimension;
import java.awt.GridLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.Observable;
import java.util.Observer;

import javax.swing.BoxLayout;
import javax.swing.JButton;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JSpinner;
import javax.swing.SwingUtilities;

import model.mapa.Espaco;
import model.mapa.GameOverException;
import model.mapa.Mapa;
import model.mapa.Movimento;
import model.mapa.TipoDeEspacos;

import org.jfree.chart.ChartFactory;
import org.jfree.chart.ChartPanel;
import org.jfree.chart.JFreeChart;
import org.jfree.chart.plot.PlotOrientation;
import org.jfree.data.category.DefaultCategoryDataset;

import controller.SaveSimulation;

public class App extends JFrame implements Observer{
	
	public static final int TAMANHO = 100;
	public int qtdHumanos;
	public int qtdZumbis;
	public int pctHumanosAmigaveis;

	public App janela = this;
	
	//Variaveis do Grafico
	
	private ChartPanel chart_panel;
	private JFreeChart entity_chart;
	private DefaultCategoryDataset category_dataset;
	
	private int rodada = 0;
	
	JPanel[][] mapa = new JPanel[TAMANHO][TAMANHO];
	
	public static void main(String[] args) {
		SwingUtilities.invokeLater(new Runnable() {
			public void run() {
				new App();
			}
		});
	}

	public App(){
		
		// Configuracoes iniciais
		
		setTitle("Simulador Zumbis");
		setSize(800,600);
		setDefaultCloseOperation(EXIT_ON_CLOSE);
		setVisible(true);
		
		// Campo
		
		criarCampo();

		// Se adicionar como observador
		
		Mapa.getInstance().addObserver(this);
		
		// Adicionar painel de botões
		
		JPanel panel = new JPanel();
		panel.setLayout(new BoxLayout(panel, BoxLayout.PAGE_AXIS));
		
		JButton button = new JButton("Avançar");
		
		final JSpinner spinner = new JSpinner();
		spinner.setMaximumSize(new Dimension(200,20));
		
		JButton buttonReiniciar = new JButton("Reiniciar");
		JButton buttonNovo = new JButton("Novo");
		JButton buttonCarregar = new JButton("Carregar");
		JButton buttonSalvar = new JButton("Salvar");
		JButton buttonContexto = new JButton("Contexto");
		
		buttonReiniciar.addActionListener(new ActionListener(){
			
			public void actionPerformed(ActionEvent e){
				
				rodada = 0;

				janela.resetar();
				Mapa.getInstance().reiniciar();
				
				//Talvez tenha que mudar pra resetar o grafico
				
				category_dataset.clear();
				
				//category_dataset.addValue((Number)Mapa.getInstance().contHumanos, "Humanos", rodada);
				//category_dataset.addValue((Number)Mapa.getInstance().contZumbis, "Zumbis", rodada);	
				
			}
			
			
			
		});
		
		buttonContexto.addActionListener(new ActionListener() {
			
			@Override
			public void actionPerformed(ActionEvent arg0) {
				
				String historia = "Em um pequeno e subdesenvolvido vilarejo português, com pouco mais de mil habitantes, um surto de uma mutação\n"+
							      "de um letal parasita foi responsável pela transformação em zumbis de maior parte da populaçao local. Os péssimos\n"+
							      "hábitos de higiene e a falta de saneamento básico do pobre vilarejo permitiram que o parasita se espalhasse facilmente\n"+
							      "e contaminasse quase toda a população – no entanto, sendo um parasita, ele não é capaz de se espalhar pelo ar ou por\n"+
							      "ataques dos infectados, o que garante um pouco de esperança aos remanescentes saudáveis. Os zumbis e os humanos se movem\n"+
							      "aleatoriamente pelo mapa, e quando um zumbi percebe um humano ao seu redor, move-se até ele para atacá-lo. Humanos podem\n"+
							      "ser amigáveis ou não, sendo que caso não sejam, ao encostarem em outro humano, o atacam. Humanos ficam exaustos com o tempo,\n"+
							      "sendo necessário dormir. Porém, estes só dormem quando não há nenhum outro personagem ao seu redor ou quando está tão exausto\n"+
							      "que dorme automaticamente. O dano do ataque de um humano é relacionado com sua agilidade e sua exaustão, enquanto o dano de\n"+
							      "um zumbi é relativo apenas à sua agilidade. Humanos podem ser do tipo comum, corredor (mais ágil e caminha mais vezes por\n"+
							      "rodada) e resistente (possuem mais resistência a ataques). Por outro lados, zumbis podem ser do tipo comum, corredor, resistente,\n"+
							      "rastejante (seu ataque é mais fraco) e nemesis (raros, mas super fortes). Zumbis percebem seres humanos em um raio de visão e\n"+
							      "o perseguem, até que o alcancem ou que o ser humano saia do raio de visão do zumbi.";
				JOptionPane.showMessageDialog(janela, historia);
				
			}
		});
		
		buttonNovo.addActionListener(new ActionListener() {
			
			@Override
			public void actionPerformed(ActionEvent e) {
				ConfigQuantidades config = new ConfigQuantidades(janela);
				category_dataset.clear();				
			}
		});
		
		buttonSalvar.addActionListener(new ActionListener() {
			
			@Override
			public void actionPerformed(ActionEvent arg0) {
				
				SaveSimulation.getInstance().salvar(Mapa.getInstance().getRadar());
				
			}
		});
		
		buttonCarregar.addActionListener(new ActionListener() {
			
			@Override
			public void actionPerformed(ActionEvent arg0) {
				
				Mapa.getInstance().setRadar(SaveSimulation.getInstance().carregar());
				category_dataset.clear();
			}
		});
		
		button.addActionListener(new ActionListener() {
						
			@Override
			public void actionPerformed(ActionEvent e) {
			
				rodada += (Integer)spinner.getValue();
				
				try {
					
					Mapa.getInstance().avancaRodada((Integer)spinner.getValue());
					
				} catch (GameOverException e1) {
					
					JOptionPane.showMessageDialog(janela, "O jogo acabou. Vencedor é: "+ e1.getMessage());
				
				}
				
				category_dataset.addValue((Number)Mapa.getInstance().contPersonagens("humanos"), "Humanos", rodada);
				category_dataset.addValue((Number)Mapa.getInstance().contPersonagens("zumbis"), "Zumbis", rodada);			
				
				
			}
			
		});
		
		panel.add(button);
		panel.add(spinner);
		panel.add(buttonReiniciar);
		panel.add(buttonNovo);
		panel.add(buttonCarregar);
		panel.add(buttonSalvar);
		panel.add(buttonContexto);
		
		add(panel, BorderLayout.WEST);
		
		// Adicionar Gráfico
		
		category_dataset = new DefaultCategoryDataset();
		entity_chart = ChartFactory.createLineChart("Personagens", "Passo de Simulação", "Quantidade de Personagens", category_dataset, PlotOrientation.VERTICAL, true, true, true);
		entity_chart.getCategoryPlot().getDomainAxis().setTickLabelsVisible(false);
		chart_panel = new ChartPanel(entity_chart);
		chart_panel.setPreferredSize(new Dimension(300,600));
		add(chart_panel, BorderLayout.EAST);
		
	}
	
	public void setaPersonagens(int qtdHumanos, int qtdZumbis, int pctAmigaveis){
		Mapa.getInstance().setDefinicoes(qtdHumanos, qtdZumbis, pctAmigaveis);
	}
	
	protected void resetar(){
		
		for(int i=0; i < TAMANHO;i++){
			for(int j=0; j < TAMANHO; j++){
			
				if(mapa[i][j].getComponentCount() > 0){
					JLabel personagem = (JLabel) mapa[i][j].getComponent(0);
					mapa[i][j].remove(personagem);
					mapa[i][j].validate();
					mapa[i][j].repaint();
				}
				
			}	
		}
		
	}
	
	private void criarCampo(){
		
		JPanel campo = new JPanel();
		campo.setLayout(new GridLayout(TAMANHO, TAMANHO));
		
		for(int i=0; i < TAMANHO;i++){
			for(int j=0; j < TAMANHO; j++){
				JPanel bloco = new JPanel();
				Espaco espacoAtual = Mapa.getInstance().getTabuleiro()[i][j];
				
				if(espacoAtual.getTipo() == TipoDeEspacos.destrocos) bloco.setBackground(new Color(80, 80, 80));
				if(espacoAtual.getTipo() == TipoDeEspacos.urbano) bloco.setBackground(new Color(135, 135, 135));
				if(espacoAtual.getTipo() == TipoDeEspacos.rural) bloco.setBackground(new Color(97, 168, 88));
				if(espacoAtual.getTipo() == TipoDeEspacos.mercado) bloco.setBackground(new Color(180, 180, 180));
				if(espacoAtual.getTipo() == TipoDeEspacos.celeiro) bloco.setBackground(new Color(87, 55, 29));
				
				bloco.setPreferredSize(new Dimension(48, 48));
				
				mapa[j][i] = bloco;
				campo.add(bloco);
				
			}
		}
		
		JScrollPane pane = new JScrollPane(campo);
		pane.setMinimumSize(new Dimension(800,600));
		pane.setPreferredSize(new Dimension(800,600));
		
		add(pane, BorderLayout.CENTER);
		
	}

	@Override
	public void update(Observable o, Object arg) {
		
		if(o instanceof Mapa){
			
			if(arg instanceof Movimento){
			
				if(arg instanceof Movimento){
					
					JLabel personagem = null;
					Movimento m = (Movimento) arg;
					
					// Personagem não existe
					
					if(m.x == -1){
						
						personagem = new JLabel(SpriteFactory.getInstance().getSprite(m.personagem));
								
					}
					
					// Personagem já existe
					
					else{
						
						if( mapa[m.y][m.x].getComponentCount() > 0){
							personagem = (JLabel) mapa[m.y][m.x].getComponent(0);
							
							mapa[m.y][m.x].remove(personagem);
							mapa[m.y][m.x].validate();
							mapa[m.y][m.x].repaint();
						}
						
					}
					
					// Personagem não morreu
					
					if (m.novoX != -1) {

						mapa[m.novoY][m.novoX].add(personagem);
						mapa[m.novoY][m.novoX].validate();
						mapa[m.novoY][m.novoX].repaint();
		
						
					}
				}
			}

		}
		
	}
	
}
