library IEEE;
use IEEE.std_logic_1164.all;

package aux_functions_l1 is

	constant TAM_CACHE: integer:= 4;
	constant TAM_LINHA: integer:= 156;
	subtype reg32 is std_logic_vector(31 downto 0);
	subtype reg2 is std_logic_vector(1 downto 0);
--	subtype reg32 is std_logic_vector(31 downto 0);
--	subtype reg16 is std_logic_vector(15 downto 0);
	subtype reg8 is std_logic_vector(7 downto 0);
	subtype reg4 is std_logic_vector(3 downto 0);
	subtype reg_linha is std_logic_vector(156 downto 0);
--	subtype reg2 is std_logic_vector(1 downto 0);

--	subtype word is reg32;

--	-- defini��o do tipo 'memory', que ser� utilizado para as mem�rias de dados/instru��es
--	constant CACHE_SIZE: integer:= 156;
	type memory is array (0 to TAM_CACHE) of reg_linha;
	function CONV_VECTOR(letra: string(1 to TAM_LINHA); pos: integer) return std_logic_vector;

	type DATA_ACCESS is array (0 to 3, 1 to 4) of integer range 0 to 1000000;

end aux_functions_l1;

package body aux_functions_l1 is

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

end aux_functions_l1;

--------------------------------------------------------------------------
-- Module implementing a behavioral model of an ASYNCHRONOUS INTERFACE RAM
--------------------------------------------------------------------------
library IEEE;
use ieee.std_logic_1164.all;
use ieee.std_logic_UNSIGNED.all;
use work.aux_functions_l1.all;

entity L1_mem is
	port
	(
		
		ce_nCPUL1, we_nCPUL1, oe_nCPUL1, bwCPUL1: in std_logic;
		ce_nL1L2, we_nL1L2, oe_nL1L2, bwL1L2: out std_logic;
		addressCPUL1: in reg32;
		dataCPUL1: inout reg32;
		dataL1L2: inout reg32;
		rstCPU: in std_logic;
		ck: in std_logic;
		ackL1CPU: out std_logic;
		sendCPU2L1: in std_logic;
		START_ADDRESS: in reg32

	);
end L1_mem;

architecture L1_mem of L1_mem is
	
	signal CACHE: memory;
	--signal tag_address,tag_cache: std_logic_vector(27 downto 0);
	--signal linha_cache,p: reg2;
	signal miss: std_logic;
	--signal dado_4,dado_3,dado_2,dado_1: std_logic_vector(31 downto 0);
	signal ackL2toL1, sendL1toL2,ackL12CPU: std_logic;

	signal pGetFromL2: std_logic_vector(1 downto 0) := "00"; -- utilizado em caso de miss (para pegar valores e popular linha da cache)
	--signal linha_cache_aux: reg2;
	-- é modificado de acordo com o valor de p
	signal addressL1L2: reg32;

	signal p: reg2 := "00";
	--signal addressAuxGetFromL2: reg32;
	signal waitingData: integer range 0 to 4 := 0; --não está esperando (0), está esperando de L2 o dado 1 (1), dado 2 (2), dado 3 (3) ou dado 4 (4).

begin

	-- DISPOSIÇÃO ENDEREÇO (addressCPUL1):
	--  _________________________
	-- |    TAG    | LINHA |  P  | -- obs: P é o signal p
	--  ‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾
	--  31        4 3     2 1   0


	-- DISPOSIÇÃO LINHA DA CACHE (são 4 linhas):
	--  ____________________________________________________________________________
	-- |    DADO 4    |    DADO 3    |    DADO 2    |    DADO 1    |    TAG    | BV |
	--  ‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾
	--  156        125 124         93 92          61 60          29 28        1   0

	-- signals auxiliares para melhorar compreensão do código
	ackL1CPU <= ackL12CPU;
	p <= addressCPUL1(1 downto 0);

	process(ck,addressCPUL1,sendCPU2L1,rstCPU,ackL2toL1)
	begin
		-- Se está em reset, não popula nem altera cache. Mantém BV de todas linhas como zero.
		if rstCPU ='1' then

			waitingData <= 0;
			addressL1L2 <= addressCPUL1;

			--transmite valores para próximo nível de cache
			dataCPUL1 <= (others => 'Z');
			dataL1L2 <= dataCPUL1;

			--seta BVs para zero
			for i in 0 to TAM_CACHE loop
				CACHE(i)(0) <= '0';
			end loop;

		-- Se não está em reset
		--elsif addressCPUL1'event and rstCPU = '0' then -- neste caso, precisa imediatamente setar ackL12CPU pra 0.

		--	ackL12CPU <= '0';

		elsif ck'event and ck = '1' then

			ackL12CPU <= '0';

			-- se não está esperando dado de L2
			if waitingData = 0 then

				sendL1toL2 <= '0';
				
				-- se o BV é 1, analisa linha da CACHE
				if CACHE(CONV_INTEGER(addressCPUL1(3 downto 2)))(0) = '1' then

					-- se a tag do address é igual a tag da cache, o dado está na cache.
					if addressCPUL1(31 downto 4) = CACHE(CONV_INTEGER(addressCPUL1(3 downto 2)))(28 downto 1) then
						-- seta miss para zero (encontrou dado)
						--miss <= '0';

						report "encontrou tag.";

						-- coloca dado no barramento (case p)
						case p is
							when "00" =>
								-- dado 1
								dataCPUL1 <= CACHE(CONV_INTEGER(addressCPUL1(3 downto 2)))(60 downto 29);

							when "01" =>
								-- dado 2
								dataCPUL1 <= CACHE(CONV_INTEGER(addressCPUL1(3 downto 2)))(92 downto 61);

							when "10" =>
								-- dado 3
								dataCPUL1 <= CACHE(CONV_INTEGER(addressCPUL1(3 downto 2)))(124 downto 93);

							when "11" =>
								-- dado 4
								dataCPUL1 <= CACHE(CONV_INTEGER(addressCPUL1(3 downto 2)))(156 downto 125);

							when others =>

						end case;

						-- avisa CPU que o dado está no barramento
						ackL12CPU <= '1';

					else -- se o dado não está na CACHE, seta miss para 1
						--report "Deu miss (tag diferente). Setou miss para 1";

						miss <= '1';
						waitingData <= 1;

						-- Seta pGetFromL2 para 00 (irá variar de 00 a 11)
						pGetFromL2 <= "00";
						
						-- Seta addressL1L2 para addressCPUL1 e bloco 00.
						addressL1L2 <= addressCPUL1(31 downto 2) & pGetFromL2;
						
						--avisa L2 que precisa de valor
						sendL1toL2 <= '1';

						-- libera barramento entre L1 e L2 para poder receber dado de L2
						dataL1L2 <= (others => 'Z');

					end if;

				else
					-- se BV = 0, então o dado não está na cache. Seta a linha da cache para a tag do address e miss para 1.
					--report "Deu miss (bit de validade 0). Setou miss para 1";
					
					miss <= '1';
					waitingData <= 1;

					-- Seta pGetFromL2 para 00 (irá variar de 00 a 11)
					pGetFromL2 <= "00";
					
					-- Seta addressL1L2 para addressCPUL1 e bloco 00.
					addressL1L2 <= addressCPUL1(31 downto 2) & pGetFromL2;
					
					--avisa L2 que precisa de valor
					sendL1toL2 <= '1';

					-- libera barramento entre L1 e L2 para poder receber dado de L2
					dataL1L2 <= (others => 'Z');

				end if;

			elsif waitingData > 0 then -- se está esperando dado de L2
				
				-- se já recebeu dado de L2
				if ackL2toL1 = '1' then

					if waitingData >= 4 then
						
						-- se todos dados já foram recebidos, sai do estado de espera
						waitingData <= 0;

					else

						-- espera próximo dado
						waitingData <= waitingData + 1;

					end if;
					
					-- popula dado recebido

					case pGetFromL2 is

						when "00" => -- dado 1
							CACHE(CONV_INTEGER(addressCPUL1(3 downto 2)))(28 downto 1) <= addressCPUL1(31 downto 4); -- seta tag
							CACHE(CONV_INTEGER(addressCPUL1(3 downto 2)))(60 downto 29) <= dataL1L2;
							pGetFromL2 <= "01";
							addressL1L2 <= addressCPUL1(31 downto 2) & pGetFromL2; -- atualiza valor buscado em L2
							--sendL1toL2	<= '1';

						when "01" => -- dado 2
							CACHE(CONV_INTEGER(addressCPUL1(3 downto 2)))(92 downto 61) <= dataL1L2;
							pGetFromL2 <= "10";
							addressL1L2 <= addressCPUL1(31 downto 2) & pGetFromL2;
							--sendL1toL2	<= '1';

						when "10" => -- dado 3
							CACHE(CONV_INTEGER(addressCPUL1(3 downto 2)))(124 downto 93) <= dataL1L2;
							pGetFromL2 <= "11";
							addressL1L2 <= addressCPUL1(31 downto 2) & pGetFromL2;
							--sendL1toL2	<= '1';

						when "11" => -- dado 4
							CACHE(CONV_INTEGER(addressCPUL1(3 downto 2)))(156 downto 125) <=dataL1L2;
							pGetFromL2 <= "00";
							addressL1L2 <= addressCPUL1(31 downto 2) & pGetFromL2;

						when others =>

					end case;

					if pGetFromL2 = "11" then
						miss <= '0';
						sendL1toL2 <= '0';
						CACHE(CONV_INTEGER(addressCPUL1(3 downto 2)))(0) <= '1'; -- atualiza bit de validade da linha
					end if;

				end if;

				-- se já recebeu toda a linha (não está mais pedindo dado de L2)
				if sendL1toL2 = '0' and miss = '0' then

					-- Coloca dado buscado no barramento para CPU (case p)
					case p is
						when "00" =>

							dataCPUL1 <= CACHE(CONV_INTEGER(addressCPUL1(3 downto 2)))(60 downto 29);

						when "01" =>

							dataCPUL1 <= CACHE(CONV_INTEGER(addressCPUL1(3 downto 2)))(92 downto 61);

						when "10" =>

							dataCPUL1 <= CACHE(CONV_INTEGER(addressCPUL1(3 downto 2)))(124 downto 93);

						when "11" =>

							dataCPUL1 <= CACHE(CONV_INTEGER(addressCPUL1(3 downto 2)))(156 downto 125);

						when others =>

					end case;

					-- avisa CPU que dado está no barramento
					ackL12CPU <= '1';
					--waitingData <= 0;

				end if;


			end if;

		end if;
	end process;

--	Caso queira testar sem L2, comente a primeira linha e descomente a segunda:
	L2: entity work.L2_mem port map(ce_nL1L2 => ce_nCPUL1, we_nL1L2 => we_nCPUL1, oe_nL1L2 => oe_nCPUL1, bwL1L2 => bwCPUL1, addressL1L2 => addressL1L2, dataL1L2 => dataL1L2, sendL1toL2 => sendL1toL2, ackL2L1 => ackL2toL1, rstCPU => rstCPU, ck => ck, START_ADDRESS => START_ADDRESS);
--	Instr_mem: entity work.IRAM_mem port map(ce_n => ce_nCPUL1, we_n => we_nCPUL1, oe_n => oe_nCPUL1, bw => bwCPUL1, address => addressL1L2, data => dataL1L2, send2Late => sendL1toL2, ack2Cpu => ackL2toL1, rstCPU => rstCPU, ck => ck,START_ADDRESS => START_ADDRESS);

end L1_mem;
