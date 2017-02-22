library IEEE;
use IEEE.STD_LOGIC_1164.all;
use IEEE.STD_LOGIC_unsigned.all;

entity Periferico is
	port
	(
		clock: in STD_LOGIC;
		reset: in STD_LOGIC;
		-- Envio e recebimento de dados para a interface do Periférico
		dadoPer2Int: out STD_LOGIC_VECTOR(15 downto 0);
		dadoInt2Per: in STD_LOGIC_VECTOR(15 downto 0);
		prontoParaProximoDado: in STD_LOGIC; -- Sinal que a interface manda para o periférico dizendo que está pronta para receber mais dados
		transmitirDado: out STD_LOGIC;
		dadoRecebido: in STD_LOGIC
	);
end Periferico;

architecture Periferico of Periferico is
	signal dadoEnviado: STD_LOGIC_VECTOR(15 downto 0);
	signal dadoInt2Periferico: STD_LOGIC_VECTOR(15 downto 0);
	signal contador: STD_LOGIC_VECTOR(15 downto 0);
begin
	dadoPer2Int <= dadoEnviado;
	Transmissao: process(clock, reset)
	begin
		if reset = '1' then
			dadoEnviado <= x"0000";
			transmitirDado <= '1';
			contador <= (others=>'0');
		elsif clock'event and clock = '1' then

			if prontoParaProximoDado = '1' and contador < 20 then

				dadoEnviado <= dadoEnviado + 1;
				contador <= contador + 1;
				transmitirDado <= '1';

			else

				transmitirDado <= '0';

			end if;

		elsif clock'event and clock = '0'  then -- TODO receber dados na descida e enviar na subida de clock (?)
-- OBS.: O sinal dadoRecebido deve ficar apenas um ciclo em '1'
			if dadoRecebido = '1' then
				dadoInt2Periferico <= dadoInt2Per;
				contador <= contador + 1;
			end if;
		end if;
	end process;
end Periferico;
