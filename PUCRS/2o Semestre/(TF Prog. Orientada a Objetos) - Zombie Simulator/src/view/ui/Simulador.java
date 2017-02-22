package view.ui;
import javax.swing.*;

import model.mapa.Mapa;

import java.awt.*;

public class Simulador extends JFrame {

	public static void main(String[] args) {
		SwingUtilities.invokeLater(new Runnable() {
			public void run() {
				new Simulador();
			}
		});
	}
	
	public Simulador() {
		//inicializarInterfaceGrafica();
		Mapa tabuleiro = Mapa.getInstance();
	}

	public final void inicializarInterfaceGrafica() {
		JPanel comecoExecucao = new JPanel();
		comecoExecucao.setLayout(null);
		setSize(600, 400); // TODO remover esse setSize depois que adicionar
							// todos os componentes desejados
		// e meter um pack l� no fim. acho que � o caso de botar o setResizable
		// como false tb
		setResizable(true);
		setContentPane(comecoExecucao);
		setDefaultCloseOperation(EXIT_ON_CLOSE);
		setTitle("Simulador de zumbis generico versao alpha");
		setVisible(true);
		setLocationRelativeTo(null);
		
		JButton inicio = new JButton("Iniciar simulacao");
		inicio.setBounds(225,300,150,50);
		comecoExecucao.add(inicio);
		
		
		}

}
