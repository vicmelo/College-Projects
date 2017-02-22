library IEEE;
use IEEE.std_logic_1164.all;

package aux_functions_l2 is

	constant TAM_CACHEL2: integer:= 8;
	constant TAM_LINHA: integer:= 156;
	subtype reg32 is std_logic_vector(31 downto 0);
	subtype reg2 is std_logic_vector(1 downto 0);
--	subtype reg32 is std_logic_vector(31 downto 0);
--	subtype reg16 is std_logic_vector(15 downto 0);
	subtype reg8 is std_logic_vector(7 downto 0);
	subtype reg4 is std_logic_vector(3 downto 0);
	subtype reg_linhal2 is std_logic_vector(282 downto 0);
--	subtype reg2 is std_logic_vector(1 downto 0);

--	subtype word is reg32;

--	-- defini��o do tipo 'memory', que ser� utilizado para as mem�rias de dados/instru��es
--	constant CACHE_SIZE: integer:= 282;
	type memoryl2 is array (0 to TAM_CACHEL2) of reg_linhal2;
	function CONV_VECTOR(letra: string(1 to TAM_LINHA); pos: integer) return std_logic_vector;

	type DATA_ACCESS is array (0 to 3, 1 to 4) of integer range 0 to 1000000;

end aux_functions_l2;

package body aux_functions_l2 is

	--
	-- converte um caracter de uma dada linha em um std_logic_vector
	--
	function CONV_VECTOR(letra:string(1 to TAM_LINHA);  pos: integer) return std_logic_vector is
		variable bin: reg4;
	begin
		case (letra(pos)) is
				when '0' => bin:= "0000";
				when '1' => bin:= "0001";
				when '2' => bin:= "0010";
				when '3' => bin:= "0011";
				when '4' => bin:= "0100";
				when '5' => bin:= "0101";
				when '6' => bin:= "0110";
				when '7' => bin:= "0111";
				when '8' => bin:= "1000";
				when '9' => bin:= "1001";
				when 'A' | 'a' => bin:= "1010";
				when 'B' | 'b' => bin:= "1011";
				when 'C' | 'c' => bin:= "1100";
				when 'D' | 'd' => bin:= "1101";
				when 'E' | 'e' => bin:= "1110";
				when 'F' | 'f' => bin:= "1111";
				when others =>  bin:= "0000";
		end case;
	return bin;
	end CONV_VECTOR;

end aux_functions_l2;

--------------------------------------------------------------------------
-- Module implementing a behavioral model of an ASYNCHRONOUS INTERFACE RAM
--------------------------------------------------------------------------
library IEEE;
use ieee.std_logic_1164.all;
use ieee.std_logic_UNSIGNED.all;
use work.aux_functions_l2.all;

entity L2_mem is

	port
	(
		
		ce_nL1L2, we_nL1L2, oe_nL1L2, bwL1L2: in std_logic;
		ce_nL2RAM, we_nL2RAM, oe_nL2RAM, bwL2RAM: out std_logic;
		addressL1L2: in reg32;
		dataL1L2: inout reg32;
		dataL2RAM: inout reg32;
		rstCPU: in std_logic;
		ck: in std_logic;
		ackL2L1: out std_logic;
		sendL1toL2: in std_logic;
		START_ADDRESS: in reg32

	);
end L2_mem;

architecture L2_mem of L2_mem is
	
	signal CACHE: memoryl2;
	--signal tag_address,tag_cache: std_logic_vector(27 downto 0);
	--signal linha_cache,p: reg2;
	signal miss: std_logic;
	--signal dado_4,dado_3,dado_2,dado_1: std_logic_vector(31 downto 0);
	signal ackRAMtoL2, sendL2toRAM,ackL2toL1: std_logic;
	signal pGetFromRAM: std_logic_vector(2 downto 0) := "000"; -- utilizado em caso de miss (para pegar valores e popular linha da cache)
	--signal linha_cache_aux: std_logic_vector(2 downto 0);
	signal p: std_logic_vector(2 downto 0);
	signal waitingData: integer range 0 to 8 := 0; --não está esperando (0), está esperando de RAM o dado 1 (1), dado 2 (2), dado 3 (3), dado 4 (4), dado 5 (5), dado 6 (6), dado 7 (7) ou dado 8 (8).
	--signal dataL1L2Aux: reg32;
	signal cont: Integer := 0;
	signal addressL2RAM : reg32;
--	signal dataAux: reg32;

begin

	process(ck)
	begin
		if ck'event and ck = '0' then

			if cont >= 1 then
				cont <= 0;
			else
				cont <= cont + 1;
			end if;

		end if;
	end process;

	--process(rstCPU,cont)
	--begin
	--	if rstCPU='0' and cont >= 8 then
	--		data <= dataAux;
	--	elsif rstCPU='1' then
	--		data <= (others => 'Z');
	--	end if;
	--end process;

	-- DISPOSIÇÃO ENDEREÇO (addressL1L2):
	--  _________________________
	-- |    TAG    | LINHA |  P  | -- obs: P é o signal p
	--  ‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾
	--  31        6 5     3 2   0


	-- DISPOSIÇÃO LINHA DA CACHE (são 8 linhas):
	--  ________________________________________________________________________________________________________________________________________
	-- |    DADO 8    |    DADO 7    |    DADO 6    |    DADO 5    |    DADO 4    |    DADO 3    |    DADO 2    |    DADO 1    |    TAG    | BV |
	--  ‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾
	--  282        251 250        219 218        187 186        155 154        123 122         91 90          59 58          27 26        1   0           


	ackL2L1 <= ackL2toL1;
	p <= addressL1L2(2 downto 0);

	process(addressL1L2,sendL1toL2,rstCPU,ackRAMtoL2,ck)
	begin
		-- Se está em reset, não popula nem altera cache. Mantém BV de todas linhas como zero.
		if rstCPU ='1' then

			waitingData <= 0;

			--transmite valores para próximo nível de cache
			dataL1L2 <= (others => 'Z');
			dataL2RAM <= dataL1L2;
			addressL2RAM <= addressL1L2;

			--seta BVs para zero
			for i in 0 to TAM_CACHEL2 loop
				CACHE(i)(0) <= '0';
			end loop;

		-- Se não está em reset
		elsif ck'event and ck = '1' then

			ackL2toL1 <= '0';


			-- se não está esperando dado da RAM
			if waitingData = 0 then
				
				-- se o BV é 1, analisa linha da CACHE
				if CACHE(CONV_INTEGER(addressL1L2(5 downto 3)))(0) = '1' then

					-- se a tag do address é igual a tag da cache, o dado está na cache.
					if addressL1L2(31 downto 6) = CACHE(CONV_INTEGER(addressL1L2(5 downto 3)))(26 downto 1) then
						-- seta miss para zero (encontrou dado)
						--miss <= '0';

						-- coloca dado no barramento (case p)
						case p is
							when "000" =>
								-- dado 1
								dataL1L2 <= CACHE(CONV_INTEGER(addressL1L2(5 downto 3)))(58 downto 27);

							when "001" =>
								-- dado 2
								dataL1L2 <= CACHE(CONV_INTEGER(addressL1L2(5 downto 3)))(90 downto 59);

							when "010" =>
								-- dado 3
								dataL1L2 <= CACHE(CONV_INTEGER(addressL1L2(5 downto 3)))(122 downto 91);

							when "011" =>
								-- dado 4
								dataL1L2 <= CACHE(CONV_INTEGER(addressL1L2(5 downto 3)))(154 downto 123);

							when "100" =>
								-- dado 5
								dataL1L2 <= CACHE(CONV_INTEGER(addressL1L2(5 downto 3)))(186 downto 155);

							when "101" =>
								-- dado 6
								dataL1L2 <= CACHE(CONV_INTEGER(addressL1L2(5 downto 3)))(218 downto 187);

							when "110" =>
								-- dado 7
								dataL1L2 <= CACHE(CONV_INTEGER(addressL1L2(5 downto 3)))(250 downto 219);

							when "111" =>
								-- dado 8
								dataL1L2 <= CACHE(CONV_INTEGER(addressL1L2(5 downto 3)))(282 downto 251);

							when others =>

						end case;	

						--dataL1L2 <= dataL1L2Aux;
						ackL2toL1 <= '1';	

					else -- se o dado não está na CACHE, seta miss para 1
						--report "entrou miss. Deve alterar tag : " & std_logic'image(addressL1L2(5)) & std_logic'image(addressL1L2(4)) & std_logic'image(addressL1L2(3));
						miss <= '1';
						waitingData <= 1;

						pGetFromRAM <= "000";

						addressL2RAM <= addressL1L2(31 downto 3) & pGetFromRAM;

						sendL2toRAM <= '1';

						dataL2RAM <= (others => 'Z');

					end if;

				else
					-- se BV = 0, então o dado não está na cache. Seta a linha da cache para a tag do address e miss para 1.
					--report "entrou miss. Deve alterar tag : " & std_logic'image(addressL1L2(5)) & std_logic'image(addressL1L2(4)) & std_logic'image(addressL1L2(3));
					miss <= '1';
					waitingData <= 1;

					pGetFromRAM <= "000";

					addressL2RAM <= addressL1L2(31 downto 3) & pGetFromRAM;

					sendL2toRAM <= '1';

					dataL2RAM <= (others => 'Z');

				end if;

			elsif waitingData > 0 then -- se está esperando dado de L2
	
				-- se já recebeu dado de L2
				if ackRAMtoL2 = '1' then

					if waitingData >= 8 then
						
						-- se todos dados já foram recebidos, sai do estado de espera
						waitingData <= 0;

					else

						-- espera próximo dado
						waitingData <= waitingData + 1;

					end if;
					
					-- popula dado recebido
					case pGetFromRAM is

						when "000" =>
							CACHE(CONV_INTEGER(addressL1L2(5 downto 3)))(26 downto 1) <= addressL1L2(31 downto 6);
							CACHE(CONV_INTEGER(addressL1L2(5 downto 3)))(58 downto 27) <= dataL2RAM;
							pGetFromRAM <= "001";
							addressL2RAM <= addressL1L2(31 downto 3) & pGetFromRAM;
							--sendL2toRAM	<= '1';

						when "001" =>
							CACHE(CONV_INTEGER(addressL1L2(5 downto 3)))(90 downto 59) <= dataL2RAM;
							pGetFromRAM <= "010";
							addressL2RAM <= addressL1L2(31 downto 3) & pGetFromRAM;
							--sendL2toRAM	<= '1';

						when "010" =>
							CACHE(CONV_INTEGER(addressL1L2(5 downto 3)))(122 downto 91) <= dataL2RAM;
							pGetFromRAM <= "011";
							addressL2RAM <= addressL1L2(31 downto 3) & pGetFromRAM;
							--sendL2toRAM	<= '1';

						when "011" =>
							CACHE(CONV_INTEGER(addressL1L2(5 downto 3)))(154 downto 123) <=dataL2RAM;
							pGetFromRAM <= "100";
							addressL2RAM <= addressL1L2(31 downto 3) & pGetFromRAM;
							--sendL2toRAM	<= '1';

						when "100" =>
							CACHE(CONV_INTEGER(addressL1L2(5 downto 3)))(186 downto 155) <= dataL2RAM;
							pGetFromRAM <= "101";
							addressL2RAM <= addressL1L2(31 downto 3) & pGetFromRAM;
							--sendL2toRAM	<= '1';

						when "101" =>
							CACHE(CONV_INTEGER(addressL1L2(5 downto 3)))(218 downto 187) <= dataL2RAM;
							pGetFromRAM <= "110";
							addressL2RAM <= addressL1L2(31 downto 3) & pGetFromRAM;
							--sendL2toRAM	<= '1';

						when "110" =>
							CACHE(CONV_INTEGER(addressL1L2(5 downto 3)))(250 downto 219) <= dataL2RAM;
							pGetFromRAM <= "111";
							addressL2RAM <= addressL1L2(31 downto 3) & pGetFromRAM;
							--sendL2toRAM	<= '1';

						when "111" =>
							CACHE(CONV_INTEGER(addressL1L2(5 downto 3)))(282 downto 251) <=dataL2RAM;
							pGetFromRAM <= "000";
							addressL2RAM <= addressL1L2(31 downto 3) & pGetFromRAM;
							-- atualiza bit de validade da linha

						when others =>

					end case;


					if pGetFromRAM = "111" then
						
						miss <= '0';
						sendL2toRAM	<= '0'; -- recebeu último dado já.
						CACHE(CONV_INTEGER(addressL1L2(5 downto 3)))(0) <= '1'; 

						--report "Entrou e setou sendL2toRAM para " & std_logic'image(sendL2toRAM);

					end if;

				end if;

				-- se já recebeu toda a linha (não está mais pedindo dado de L2)
				if sendL2toRAM = '0' and miss = '0' then
					
					-- Coloca dado buscado no barramento para CPU (case p)ack2Cpu
					case p is
						when "000" =>

							dataL1L2 <= CACHE(CONV_INTEGER(addressL1L2(5 downto 3)))(58 downto 27);

						when "001" =>

							dataL1L2 <= CACHE(CONV_INTEGER(addressL1L2(5 downto 3)))(90 downto 59);

						when "010" =>

							dataL1L2 <= CACHE(CONV_INTEGER(addressL1L2(5 downto 3)))(122 downto 91);

						when "011" =>

							dataL1L2 <= CACHE(CONV_INTEGER(addressL1L2(5 downto 3)))(154 downto 123);

						when "100" =>

							dataL1L2 <= CACHE(CONV_INTEGER(addressL1L2(5 downto 3)))(186 downto 155);

						when "101" =>

							dataL1L2 <= CACHE(CONV_INTEGER(addressL1L2(5 downto 3)))(218 downto 187);

						when "110" =>

							dataL1L2 <= CACHE(CONV_INTEGER(addressL1L2(5 downto 3)))(250 downto 219);

						when "111" =>

							dataL1L2 <= CACHE(CONV_INTEGER(addressL1L2(5 downto 3)))(282 downto 251);

						when others =>

					end case;

					-- avisa L1 que dado está no barramento
					--if cont = 1 then
					ackL2toL1 <= '1';

				end if;

			end if;

		end if;

	end process;

	Instr_mem: entity work.IRAM_mem generic map(START_ADDRESS => x"00400000") port map(ce_n => ce_nL1L2, we_n => we_nL1L2, oe_n => oe_nL1L2, bw => bwL1L2, address => addressL2RAM, data => dataL2RAM, send2Late => sendL2toRAM, ack2Cpu => ackRAMtoL2, rstCPU => rstCPU, ck => ck, START_ADDRESS => START_ADDRESS);

end L2_mem;
