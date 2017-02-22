library IEEE;
use IEEE.STD_LOGIC_1164.all;

package definicoesTransmissaoAssincronaPeriferico is
	type ESTADO_TRANSMISSAO is (esperaDadoCPU, enviaDadoPerif);
end definicoesTransmissaoAssincronaPeriferico;


library IEEE;
use IEEE.STD_LOGIC_1164.all;
use work.definicoesTransmissaoAssincronaPeriferico.all;

entity InterfacePeriferico is
	port
	(
		clock: in STD_LOGIC;
		reset: in STD_LOGIC;
		-- Interface de comunicacao assincrona
		receive: in STD_LOGIC;
		accept: out STD_LOGIC;
		dataIn: in STD_LOGIC_VECTOR(15 downto 0);
		-- Interface com a maquina local
		dadoParaMaq: out STD_LOGIC_VECTOR(15 downto 0);
		dadoRecebido: out STD_LOGIC
	);
end InterfacePeriferico;

architecture InterfacePeriferico of InterfacePeriferico is
	signal estadoTx: ESTADO_TRANSMISSAO;
	signal regDataIn: STD_LOGIC_VECTOR(15 downto 0);
begin
	dadoParaMaq <= regDataIn;
	Recepcao: process(clock, reset)
	begin
		if reset = '1' then
			dadoRecebido <= '0';
			accept <= '0';
		elsif clock'event and clock = '0' then

			case estadoTx is
				when esperaDadoCPU =>

					if receive = '1' then

						dadoRecebido <= '1';
						accept <= '1';
						estadoTx <= enviaDadoPerif;

					end if;

				when enviaDadoPerif =>

					accept <= '0';
					regDataIn <= dataIn;
					estadoTx <= esperaDadoCPU;
					dadoRecebido <= '0';

				when others => null;
		end case;
		end if;
  end process;
end InterfacePeriferico;
