library IEEE;
use IEEE.std_logic_1164.all;
use ieee.std_logic_UNSIGNED.all;

entity teste is
	
	port
	(
		vetor: out std_logic_vector(3 downto 0)

	);
end teste;

architecture teste of teste is

signal vetorAux: std_logic_vector(3 downto 0);
signal get0,get3: std_logic;
begin

	vetorAux <= "0011";
	vetor <= vetorAux;
	get0 <= vetorAux(0);
	get3 <= vetorAux(3);

end teste;



entity teste_tb is

end teste_tb;

architecture teste_tb of teste_tb is
begin

end teste_tb;