package view.ui;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.BoxLayout;
import javax.swing.JButton;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JSpinner;
import javax.swing.SwingUtilities;

import model.mapa.Mapa;

public class ConfigQuantidades extends JFrame{
	
	public ConfigQuantidades janelaConfig = this;
	
	public ConfigQuantidades(final App janela){
		
		setTitle("Simulador Zumbis");
		setSize(800,600);
		setDefaultCloseOperation(EXIT_ON_CLOSE);
		setVisible(true);
		
		JPanel jp = new JPanel();
		jp.setLayout(new BoxLayout(jp, BoxLayout.PAGE_AXIS));
		setDefaultCloseOperation(DISPOSE_ON_CLOSE);
		
		final JSpinner spinnerQtdHumanos = new JSpinner();
		final JSpinner spinnerPctHumanosAmigaveis = new JSpinner();
		final JSpinner spinnerQtdZumbis = new JSpinner();
		JButton ok = new JButton("Ok");
		
		
		ok.addActionListener(new ActionListener() {
			
			@Override
			public void actionPerformed(ActionEvent arg0) {
			
				Mapa.getInstance().novaSimulacao((int) spinnerQtdHumanos.getValue(), (int) spinnerQtdZumbis.getValue(), (int) spinnerPctHumanosAmigaveis.getValue());
				janelaConfig.dispose();
			}
			
		});
		
		jp.add(new JLabel("Quantidade Humanos"));
		jp.add(spinnerQtdHumanos);
		jp.add(new JLabel("Humanos Amigaveis (%)"));
		jp.add(spinnerPctHumanosAmigaveis);
		jp.add(new JLabel("Quantidade Zumbis"));
		jp.add(spinnerQtdZumbis);
		jp.add(ok);
		
		add(jp);
		
		pack();
		setVisible(true);
		
	}
	
}
