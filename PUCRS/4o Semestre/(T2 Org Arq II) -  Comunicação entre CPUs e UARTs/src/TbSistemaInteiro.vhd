library ieee;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use work.aux_functions.all;

ENTITY TbTop IS
END TbTop;

ARCHITECTURE behavior OF TbTop IS
   signal tx1 : std_logic;
	 signal tx2 : std_logic;
   signal send1 : std_logic;
	signal send2 : std_logic;
	signal accept1: std_logic;
	signal accept2: std_logic;
BEGIN


   M1:entity work.CPU_tb1 PORT MAP (
          txCPU => tx1,
          rxCPU => tx2,
          ackUART=>accept1,
			    sendUART=>send2,
			    ack=>accept2,
			    send=>send1
        );

	M2:entity work.CPU_tb2 PORT MAP (
          txCPU => tx2,
          rxCPU => tx1,
          ackUART=>accept2,
		 	    sendUART=>send1,
		 	    ack=>accept1,
			    send=>send2
        );

END;
