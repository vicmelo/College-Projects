library ieee;
use ieee.std_logic_1164.all;

entity tbSincrono is
end tbSincrono;

architecture tbSincrono of tbSincrono is
-- Sinais da CPU e interface local
	signal resetCPU: std_logic;
-- Sinais entre CPU e interface local
	signal prontoParaProximoDadoCPU: std_logic;
	signal dadoCPU: std_logic_vector(15 downto 0);
	signal transmitirDadoCPU: std_logic;
-- Sinais do Periferico e interface local
	--signal clockPeriferico: std_logic;
	signal resetPeriferico: std_logic;
-- Sinais entre Periferico e interface local
	signal dadoRecebidoPeriferico: std_logic;
	signal dadoDaInterfacePeriferico: std_logic_vector(15 downto 0);
-- Sinais entre interfaces
	signal clock: std_logic;
 	signal send: std_logic;
	signal dado: std_logic_vector(15 downto 0);

begin

	resetCPU <= '1', '0' after 100 ns;
	resetPeriferico <= '1', '0' after 100 ns;

	process
	begin
		clock <= '0', '1' after 20 ns;
		wait for 40 ns;
	end process;

	MaquinaCPU: entity work.CPU port map
	(
		clock => clock,
		reset => resetCPU,
		dadoParaInterface => dadoCPU,
		prontoParaProximoDado => prontoParaProximoDadoCPU,
		transmitirDado => transmitirDadoCPU
	);


	InterfaceCPU: entity work.InterfaceCPU port map
	(
		clock => clock,
		reset => resetCPU,
		send => send,
		dataOut => dado,
		dadoDaMaq => dadoCPU,
		prontoParaProximoDado => prontoParaProximoDadoCPU,
		transmitirDado => transmitirDadoCPU
	);

	MaquinaPeriferico: entity work.Periferico port map
	(
		clock => clock,
		reset => resetPeriferico,
		dadoDaInterface => dadoDaInterfacePeriferico,
		dadoRecebido => dadoRecebidoPeriferico
	);
	InterfacePeriferico: entity work.InterfacePeriferico port map
	(
		clock => clock,
		reset => resetPeriferico,
		receive => send,
		dataIn => dado,
		dadoParaMaq => dadoDaInterfacePeriferico,
		dadoRecebido => dadoRecebidoPeriferico
	);
end tbSincrono;
