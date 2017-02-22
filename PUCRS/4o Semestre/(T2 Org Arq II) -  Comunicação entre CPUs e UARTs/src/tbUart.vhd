library ieee;
use ieee.std_logic_1164.all;

entity tbUart is
end tbUart;

architecture tbUart of tbUart is

-- Sinais da CPU e interface local
	signal clock: std_logic;
	signal resetClock: std_logic;
-- Sinais entre CPU e Uart
	signal CpuToUart: STD_LOGIC_VECTOR(7 downto 0);
	signal UartToCpu: STD_LOGIC_VECTOR(7 downto 0);
	signal inta : STD_LOGIC;
	signal intr : std_logic;
	signal ceTb : std_logic;
	signal TipoInterrupcao: std_logic;
	signal CPUEscreveuRW : std_logic;
-- Sinais entre Uarts
	signal rx: std_logic;
	signal tx: std_logic;
	signal send : std_logic;
	signal sendUart : std_logic;
	signal ack : std_logic;
	signal ackUart: std_logic;

begin

	resetClock <= '1', '0' after 100 ns;

	process
	begin
		clock <= '0', '1' after 5 ns;
		wait for 10 ns;
	end process;

	process
	begin
		ceTb <= '0', '1' after 5 ns;
		wait for 15 ns;
	end process;

	process
	begin
		rx <= '0', '1' after 10 ns;
		wait for 20 ns;
	end process;

	UART: entity work.UART port map
	(
		ck => clock,
		rst => resetClock,
		ce => '1',
		rx => rx,
		sendUart => '1',
		ackUart => '1',
		inta => '1',
		address => x"FFE00004",
		dataIn => x"000000"&"01101001",
		row => '1'

	);
end tbUart;
