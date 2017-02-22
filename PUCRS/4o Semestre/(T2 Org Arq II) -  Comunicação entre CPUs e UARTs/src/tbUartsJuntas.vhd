library ieee;
use ieee.std_logic_1164.all;

entity tbUartsJuntas is
end tbUartsJuntas;

architecture tbUartsJuntas of tbUartsJuntas is

-- Sinais da CPU e interface local
	signal clock1: std_logic;
	signal clock2: std_logic;
	signal resetClock: std_logic;
-- Sinais entre CPU e Uart
	signal ceTb1 : std_logic;
	signal ceTb2 : std_logic;
-- Sinais entre Uarts
	signal rx1: std_logic;
	signal tx1: std_logic;
	signal tx2: std_logic;
	signal sendUart1 : std_logic;
	signal ackUart1: std_logic;
	signal rx2: std_logic;
	signal sendUart2 : std_logic;
	signal ackUart2: std_logic;
	signal send1 : std_logic;
	signal send2 : std_logic;
	signal ack1 : std_logic;
	signal ack2 : std_logic;
	signal addressProc : std_logic_vector(31 downto 0);

begin

	resetClock <= '1', '0' after 100 ns;

	process
	begin
		clock1 <= '0', '1' after 5 ns;
		wait for 10 ns;
	end process;

	process
	begin
		clock2 <= '1', '0' after 15 ns;
		wait for 20 ns;
	end process;

	addressProc <= x"FFE00004",x"FFE00008" after 700 ns;

	UART1: entity work.UART port map
	(
		ck => clock1,
		rst => resetClock,
		ce => '1',
		rx => tx2,
		tx => tx1,
		send => send1,
		ack => ack1,
		sendUart => send2,
		ackUart => ack2,
		inta => '1',
		address => addressProc,
		dataIn => x"000000"&"01101001",
		row => '1'


	);

	UART2: entity work.UART port map
	(
		ck => clock2,
		rst => resetClock,
		ce => '1',
		rx => tx1,
		tx => tx2,
		send => send2,
		ack => ack2,
		sendUart => send1,
		ackUart => ack1,
		inta => '1',
		address => addressProc,
		dataIn => x"000000"&"10010110",
		row => '1'


	);
end tbUartsJuntas;
