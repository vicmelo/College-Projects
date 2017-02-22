library IEEE;
package definicoesTransmissaoAssincrona is
	type ESTADO_TRANSMISSAO_ENVIA is (esperaDados, esperaAck, esperaFimAck, esperaDadosPeriferico, enviaDadosCPU);
	type ESTADO_TRANSMISSAO_RECEBE is (esperaDadoPer, enviaDadoCPU);
end definicoesTransmissaoAssincrona;

library IEEE;
use IEEE.STD_LOGIC_1164.all;
use work.definicoesTransmissaoAssincrona.all;

entity InterfaceCPU is
	port
	(
		clock: in STD_LOGIC;
		reset: in STD_LOGIC;
		-- Interface de comunicacao assincrona
		sendCPU: out STD_LOGIC;
		sendPeriferico: in STD_LOGIC;
		ackPeriferico: in STD_LOGIC;
		ackCPU: out STD_LOGIC;
		dadoCPU2Periferico : out STD_LOGIC_VECTOR(15 downto 0); -- Valor recebido da CPU e enviado para InterfacePeriferico
		dadoPeriferico2CPU : in STD_LOGIC_VECTOR(15 downto 0); -- Valor recebido da InterfacePeriferico e enviado para CPU
		-- Interface com a maquina local
		dadoCPU2Interface : in STD_LOGIC_VECTOR(15 downto 0); -- Valor recebido pela InterfaceCPU da CPU
		dadoInterface2CPU : out STD_LOGIC_VECTOR(15 downto 0); -- Valor enviado da InterfaceCPU para a CPU
		prontoParaProximoDado: out STD_LOGIC;		-- InterfaceCPU sinaliza para CPU que pode receber outro dado
		transmitirDado: in STD_LOGIC;			-- Sinal que CPU envia para InterfaceCPU sinalizando que os dados foram enviados
		dadoRecebidoCPU: out STD_LOGIC -- Sinal que InterfaceCPU recebeu dado

	);
end InterfaceCPU;

architecture InterfaceCPU of InterfaceCPU is
	signal estadoTxRecebe: ESTADO_TRANSMISSAO_RECEBE;
	signal estadoTxEnvia: ESTADO_TRANSMISSAO_ENVIA;
	signal dadoPer2CPU: STD_LOGIC_VECTOR(15 downto 0); -- Valor que recebe do periferico
	signal dadoCPU2Per: STD_LOGIC_VECTOR(15 downto 0); -- Valor que manda para o periferico
begin
	dadoCPU2Periferico <= dadoCPU2Per;
	dadoPer2CPU <= dadoPeriferico2CPU;

	process(clock, reset)
	begin
		if reset = '1' then
			estadoTxEnvia <= esperaDados;
			estadoTxRecebe <= esperaDadoPer;
			prontoParaProximoDado <= '0';
   	 	sendCPU <= '0';
			ackCPU <= '0';

		-- Quando sobe o ciclo de clock, a InterfaceCPU transfere os dados para a InterfacePeriferico
		elsif clock'event and clock = '1' then

			case estadoTxEnvia is
				when esperaDados =>

					if transmitirDado = '1' then

						dadoCPU2Per <= dadoCPU2Interface;
						sendCPU <= '1';
						prontoParaProximoDado <= '1';
						dadoRecebidoCPU <= '1';
						estadoTxEnvia <= esperaAck;

					end if;

				when esperaAck =>

					prontoParaProximoDado <= '0';
					dadoRecebidoCPU <= '0';

					if ackPeriferico = '1' then

						sendCPU <= '0';
						estadoTxEnvia <= esperaFimAck;

					end if;

				when esperaFimAck =>

					if ackPeriferico = '0' then

							prontoParaProximoDado <= '1';
							estadoTxEnvia <= esperaDados;

					end if;

				when others => null;

			end case;

		-- Quando baixa o ciclo de clock, a InterfaceCPU recebe os dados da InterfacePeriferico e salva no sinal dadoPer2CPU, que irá para a CPU
		elsif clock'event and clock = '0' then
			case estadoTxRecebe is
				when esperaDadoPer =>

					if sendPeriferico = '1' then

						dadoInterface2CPU <= dadoPer2CPU;
						dadoRecebidoCPU <= '1';
						ackCPU <= '1';
						estadoTxRecebe <= enviaDadoCPU;

					end if;

				when enviaDadoCPU =>

					ackCPU <= '0';
					estadoTxRecebe <= esperaDadoPer;

				when others => null;
			end case;
		end if;
	end process;
end InterfaceCPU;
