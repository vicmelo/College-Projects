library IEEE;
use IEEE.STD_LOGIC_1164.all;

package definicoesTransmissaoSemiSincrona is

	type ESTADO_TRANSMISSAO_RECEBE is (esperaDadoCPU, enviaDadoPerif);
	type ESTADO_TRANSMISSAO_ENVIA is (esperaDados, esperaAck, esperaFimAck, esperaDadosPeriferico, enviaDadosCPU);

end definicoesTransmissaoSemiSincrona;

library IEEE;
use IEEE.STD_LOGIC_1164.all;
use work.definicoesTransmissaoSemiSincrona.all;


entity InterfacePeriferico is
	port
	(
		clock: in STD_LOGIC;
		reset: in STD_LOGIC;
		-- Interface de comunicacao assincrona CPU <-> Per
		sendCPU: in STD_LOGIC;
		sendPer: out STD_LOGIC;
		ackPer: out STD_LOGIC;
		ackCPU: in STD_LOGIC;
		dadoCPU2Periferico: in STD_LOGIC_VECTOR(15 downto 0);
		dadoPeriferico2CPU: out STD_LOGIC_VECTOR(15 downto 0);

		-- Interface com a maquina local Interf <-> Perif
		dadoInt2Periferico: out STD_LOGIC_VECTOR(15 downto 0);
		dadoPeriferico2Interface: in STD_LOGIC_VECTOR(15 downto 0);
		dadoRecebido: out STD_LOGIC;
		prontoParaProximoDado: out STD_LOGIC;
		transmitirDadoPer: in STD_LOGIC

	);
end InterfacePeriferico;

architecture InterfacePeriferico of InterfacePeriferico is
	signal estadoTxRecebe: ESTADO_TRANSMISSAO_RECEBE;
	signal estadoTxEnvia: ESTADO_TRANSMISSAO_ENVIA;
	signal dadoCPU2Per: STD_LOGIC_VECTOR(15 downto 0);
	signal dadoInt2CPU: STD_LOGIC_VECTOR(15 downto 0);
	signal dadoInt2Per: STD_LOGIC_VECTOR(15 downto 0);
	signal dadoPer2CPU: STD_LOGIC_VECTOR(15 downto 0); -- Valor que envia para CPU

begin

	dadoCPU2Per <= dadoCPU2Periferico;
  dadoPeriferico2CPU <= dadoPer2CPU;
	dadoInt2Periferico <= dadoInt2Per;

	Recepcao: process(clock, reset)
	begin
		if reset = '1' then
			dadoRecebido <= '0';
			ackPer <= '0';
			sendPer <= '0';
			prontoParaProximoDado <= '0';
			estadoTxRecebe <= esperaDadoCPU;
			estadoTxEnvia <= esperaDados;

		elsif clock'event and clock = '0' then

			case estadoTxRecebe is
				when esperaDadoCPU =>

					if sendCPU = '1' then

						dadoInt2Per <= dadoCPU2Per;
						dadoRecebido <= '1';
						ackPer <= '1';
						estadoTxRecebe <= enviaDadoPerif;

					end if;

				when enviaDadoPerif =>

					ackPer <= '0';
					estadoTxRecebe <= esperaDadoCPU;

				when others => null;
			end case;

		elsif clock'event and clock = '1' then

			case estadoTxEnvia is
				when esperaDados =>

					if transmitirDadoPer = '1' then

						dadoPer2CPU <= dadoPeriferico2Interface;
						sendPer <= '1';
						prontoParaProximoDado <= '1';
						estadoTxEnvia <= esperaAck;

					end if;

				when esperaAck =>

					prontoParaProximoDado <= '0';

					if ackCPU = '1' then

						sendPer <= '0';
						estadoTxEnvia <= esperaFimAck;

					end if;

				when esperaFimAck =>

					if ackCPU = '0' then

							prontoParaProximoDado <= '1';
							estadoTxEnvia <= esperaDados;

					end if;

				when others => null;

			end case;

		end if;
  end process;
end InterfacePeriferico;
