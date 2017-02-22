library IEEE;
use IEEE.STD_LOGIC_1164.all;
use IEEE.STD_LOGIC_unsigned.all;

entity CPU is
	port
	(
		clock: in STD_LOGIC;
		reset: in STD_LOGIC;
		-- Envio de dados de e para a interface da CPU
		dadoCPU2Int: out STD_LOGIC_VECTOR(15 downto 0);	-- Dados enviados pela CPU para a InterfaceCPU
		dadoInterface2CPU: in STD_LOGIC_VECTOR(15 downto 0); -- Dados recebidos da Interface para CPU

		prontoParaProximoDado: in STD_LOGIC; -- Sinal que a interface manda para a CPU dizendo que está pronta para receber mais dados
		transmitirDado: out STD_LOGIC;		-- Sinal que a CPU envia para a InterfaceCPU sinalizando que os dados foram enviados

		-- Recebimento de dados da Interface (dados enviados pelo periférico para CPU)
		dadoRecebidoCPU: in STD_LOGIC		-- Sinal da InterfaceCPU que diz se possui dados para enviar

	);
end CPU;

architecture CPU of CPU is

	signal dadoCPU2Interface: STD_LOGIC_VECTOR(15 downto 0);
	signal dadoInt2CPU: STD_LOGIC_VECTOR(15 downto 0);
	signal contador: STD_LOGIC_VECTOR(15 downto 0);

begin
	dadoCPU2Int <= dadoCPU2Interface;
	process(clock, reset)
	begin

		if reset = '1' then
			dadoCPU2Interface <= x"0000";
			transmitirDado <= '1';
			contador <= (others=>'0');
		elsif clock'event and clock = '1' then

			if prontoParaProximoDado = '1' and contador < 20 then
				dadoCPU2Interface <= dadoCPU2Interface + 1;
				contador <= contador + 1;
				transmitirDado <= '1';
			end if;

		elsif clock'event and clock = '0' then
			if dadoRecebidoCPU = '1' then
				dadoInt2CPU <= dadoInterface2CPU;
				contador <= contador + 1;
			end if;
		end if;
	end process;
end CPU;
