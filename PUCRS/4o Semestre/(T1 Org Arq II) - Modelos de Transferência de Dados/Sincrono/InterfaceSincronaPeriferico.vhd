library IEEE;
use IEEE.STD_LOGIC_1164.all;

entity InterfacePeriferico is
	port
	(
		clock: in STD_LOGIC;
		reset: in STD_LOGIC;
		-- Interface de comunicacao assincrona
		receive: in STD_LOGIC;
		dataIn: in STD_LOGIC_VECTOR(15 downto 0);
		-- Interface com a maquina local
		dadoParaMaq: out STD_LOGIC_VECTOR(15 downto 0);
		dadoRecebido: out STD_LOGIC
	);
end InterfacePeriferico;

architecture InterfacePeriferico of InterfacePeriferico is

	signal regDataIn: STD_LOGIC_VECTOR(15 downto 0);
begin
	Recepcao: process(clock, reset)
	begin
		if reset = '1' then
			dadoRecebido <= '0';
		elsif clock'event and clock = '0' then

					if receive = '1' then

						dadoRecebido <= '1';
						regDataIn <= dataIn;

					else

						dadoRecebido <= '0';

					end if;

		end if;

		dadoParaMaq <= regDataIn;

  end process;

end InterfacePeriferico;
