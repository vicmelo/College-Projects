library ieee;
use ieee.std_logic_1164.all;

entity tbSemiSincrono is
end tbSemiSincrono;

architecture tbSemiSincrono of tbSemiSincrono is

-- Sinais da CPU e interface local
	signal clock: std_logic;
	signal resetClock: std_logic;
-- Sinais entre CPU e interface local
	signal dadoCPU2Int: std_logic_vector(15 downto 0);
	signal dadoInt2CPU: std_logic_vector(15 downto 0);
	signal transmitirDadoCPU: std_logic;
	signal prontoParaProximoDadoCPU: std_logic;
	signal dadoRecebidoCPU: std_logic;
-- Sinais entre Periferico e interface local
	signal dadoPer2Int: std_logic_vector(15 downto 0);
	signal dadoInt2Per: std_logic_vector(15 downto 0);
	signal transmitirDadoPeriferico: std_logic;
	signal prontoParaProximoDadoPeriferico: std_logic;
	signal dadoRecebidoPeriferico: std_logic;
-- Sinais entre interfaces
	signal dadoCPU2Per: std_logic_vector(15 downto 0);
	signal dadoPer2CPU: std_logic_vector(15 downto 0);
 	signal sendCPU: std_logic;
	signal sendPer: std_logic;
	signal ackCPU: std_logic;
	signal ackPer: std_logic;

begin

	resetClock <= '1', '0' after 100 ns;

	process
	begin
		clock <= '0', '1' after 5 ns;
		wait for 10 ns;
	end process;

	MaquinaCPU: entity work.CPU port map
	(
		clock => clock,
		reset => resetClock,
		dadoCPU2Int => dadoCPU2Int,
		dadoInterface2CPU => dadoInt2CPU,
		transmitirDado => transmitirDadoCPU,
		prontoParaProximoDado => prontoParaProximoDadoCPU,
		dadoRecebidoCPU => dadoRecebidoCPU

	);

	InterfaceCPU: entity work.InterfaceCPU port map
	(
		clock => clock,
		reset => resetClock,
		sendCPU => sendCPU,
		ackCPU => ackCPU,
		ackPeriferico => ackPer,
		dadoRecebidoCPU => dadoRecebidoCPU,
		dadoCPU2Periferico => dadoCPU2Per,
		dadoCPU2Interface => dadoCPU2Int,
		dadoInterface2CPU => dadoInt2CPU,
		prontoParaProximoDado => prontoParaProximoDadoCPU,
		transmitirDado => transmitirDadoCPU,
		dadoPeriferico2CPU => dadoPer2CPU,
		sendPeriferico => sendPer
	);

	MaquinaPeriferico: entity work.Periferico port map
	(
		clock => clock,
		reset => resetClock,
		dadoPer2Int => dadoPer2Int,
		dadoInt2Per => dadoInt2Per,
		transmitirDado => transmitirDadoPeriferico,
		prontoParaProximoDado => prontoParaProximoDadoPeriferico,
		dadoRecebido => dadoRecebidoPeriferico
	);
	InterfacePeriferico: entity work.InterfacePeriferico port map
	(
		clock => clock,
		reset => resetClock,
		sendCPU => sendCPU,
		sendPer => sendPer,
		ackPer => ackPer,
		ackCPU => ackCPU,
		dadoRecebido => dadoRecebidoPeriferico,
		prontoParaProximoDado => prontoParaProximoDadoPeriferico,
		dadoCPU2Periferico => dadoCPU2Per,
		dadoInt2Periferico => dadoInt2Per,
		dadoPeriferico2Interface => dadoPer2Int,
		dadoPeriferico2CPU => dadoPer2CPU,
		transmitirDadoPer => transmitirDadoPeriferico
	);
end tbSemiSincrono;
