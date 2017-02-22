library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

package definicaouart is

	type ESTADO_TRANSMISSAO_RECEBE is (esperaPrimeiroBitUART, esperaBitUART, recebeBitUart, esperaFimSend, verificaValidade, rdiToRR, solicitaInterrupcaoCPU,  esperaCPUAceitarInterrupcao, esperaCPULerDado);
	type ESTADO_TRANSMISSAO_ENVIA is (PedeDadoCPU,esperaCPUAceitarInterrupcao,esperaRDOEsvaziar,transformaDadoP82,enviaDadoUart,esperaAckUart);

end definicaouart;

library IEEE;
use IEEE.STD_LOGIC_1164.all;
use IEEE.STD_LOGIC_UNSIGNED.all;
use IEEE.numeric_std.all;
use work.definicaouart.all;
use work.aux_functions.all;

entity UART is
	port
	(
		ck,rst,ce,row: in std_logic;
		-- Barramentos
		address: in reg32;
	  dataIn: in reg32;
		dataOut: out reg32;
		-- Sinais de Interrupcao
		inta: in std_logic;
		intr: out std_logic;
		-- Interfacde de comunicação entre UARTS --
		rx: in std_logic; -- Entrada de dados
		tx: out std_logic; -- Saida de dados
		send : out std_logic;
		ackUart : in std_logic;
		sendUart : in std_logic;
		ack : out std_logic

	);
end UART;

architecture UART of UART is

	signal estadoTxRecebe: ESTADO_TRANSMISSAO_RECEBE;
	signal estadoTxEnvia: ESTADO_TRANSMISSAO_ENVIA;
	signal InUartToUart: STD_LOGIC;
	signal OutUartToUart: STD_LOGIC;
	signal RDOBits: std_logic_vector(11 downto 0);
	signal RDIBits : std_logic_vector(11 downto 0) := "000000000000";
	signal signalRR : std_logic_vector(7 downto 0);
	signal signalRW : std_logic_vector(7 downto 0);
	signal EnderecoUART: std_logic_vector(31 downto 0) := x"FFE00000";
	signal dadoEnderecoUART: std_logic;
	signal vetorDeInterrupcoes : std_logic_vector(7 downto 0);
	signal interrupcaoAtiva : std_logic := '0';

	signal rwPodeReceberDados : std_logic := '1';
	signal RDOOcupado : std_logic := '0';
	signal RROcupado : std_logic := '0';

	begin

			InUartToUart <= rx;
			tx <= OutUartToUart;

			process(ck, rst)
			variable contSubida: Integer := 0;
			variable contDescida: Integer := 0;
			begin
				if rst = '1' then
					send <= '0';
					ack <= '0';
					intr <= '0';
					estadoTxRecebe <= esperaPrimeiroBitUART;
					estadoTxEnvia <= PedeDadoCPU;

			elsif ck'event and ck = '1' then -- Na subida do clock a uart recebe o dado se estiver ativada

			case estadoTxRecebe is
				when esperaPrimeiroBitUART =>
					RDIBits <= "000000000000";
					ack <= '0';
					if sendUart = '1' and InUartToUart = '0' then -- Uart enviou um bit (0 é o startbit)
						contSubida := 0;
						estadoTxRecebe <= recebeBitUart;

					end if;
				when esperaBitUART =>

					if sendUart = '1' then -- Uart enviou um bit

						estadoTxRecebe <= recebeBitUart;

					end if;

				when recebeBitUart =>

						RDIBits <= RDIBits(10 downto 0) & InUartToUart; -- Recebe o bit vindo da outra UART
						contSubida := contSubida + 1;
						ack <= '1'; -- Avisa a outra Uart que recebeu o bit
						if contSubida = 12 then -- Já recebeu todos os bits
							estadoTxRecebe <= verificaValidade;
						else
							estadoTxRecebe <= esperaFimSend; -- Espera o próximo dado
						end if;

				when esperaFimSend =>

					if sendUart = '0' then
						ack <= '0';
						estadoTxRecebe <= esperaBitUART;
					end if;

				when verificaValidade => -- Verifica se a informação é valida através do bit de paridade

					contSubida := 0;
					for i in RDIBits'range loop
						if RDIBits(i) = '1' then contSubida := contSubida + 1;
						end if;
					end loop;

					if((RDIBits(2) = '1') and (contSubida mod 2 = 0)) then
						report "O Bit de paridade não confere com a informação do dado (1)";
							estadoTxRecebe <= esperaPrimeiroBitUART;
					elsif((RDIBits(2) = '0') and (contSubida mod 2 /= 0)) then
						report "O Bit de paridade não confere com a informação do dado (2)";
						estadoTxRecebe <= esperaPrimeiroBitUART;
					else
						estadoTxRecebe <= rdiToRR;
					end if;

				when rdiToRR =>
					if RROcupado = '0' then
						-- Passa os 12 bits de dado em RDI para 8 bits em RR
						signalRR <= RDIBits(10 downto 3);
						-- Zera o RDIBits para pode receber novos dados
						RROcupado <= '1'; -- RR tem um dado (segurança para não reescrever)
						estadoTxRecebe <= solicitaInterrupcaoCPU; -- Espera cpu aceitar interrupcao e ler o dado
					end if;

				when solicitaInterrupcaoCPU =>
					if ce = '1' then
						if interrupcaoAtiva = '1' then
							-- Já existe uma interrupcao sendo atendida, logo esperar
						else
							dataOut <= x"0000000" & "0001"; -- Seta o tipo de interrupcao para chegada de um dado
							intr <= '1';		-- Requisita a interrupcao para a CPU
							interrupcaoAtiva <= '1';
							estadoTxRecebe <= esperaCPUAceitarInterrupcao;
						end if;
					end if;

				when esperaCPUAceitarInterrupcao =>

					if inta = '1' then	-- Se CPU aceitou a interrupcao da Uart
						if address = x"FFE00008" then	-- Se CPU endereçou a uart para ler o dado em RR
							dataOut <= x"000000"&signalRR;		-- Coloca no barramento de dados a data contida em RR
							intr <= '0';
							RROcupado <= '0';
							interrupcaoAtiva <= '0';
							estadoTxRecebe <= esperaCPULerDado;
						end if;
					end if;

				when esperaCPULerDado =>

					-- OBS: Não tratamos o caso em que a CPU não leia o dado a tempo!!
					if ackUart = '1' then -- Se UART respondeu o ACK
						estadoTxRecebe <= esperaPrimeiroBitUART;
					end if;

				when others => null;
			end case;

		elsif ck'event and ck = '0' then -- Na descida de clock, envia um dado

			case estadoTxEnvia is

				when PedeDadoCPU =>

					if rwPodeReceberDados = '1' and ce = '1' then
						if interrupcaoAtiva = '1' then
							-- Já existe uma interrupcao sendo atendida, logo, esperar
						else
							dataOut <= x"00000000"; -- Seta o campo de data para receber o dado da CPU
							intr <= '1';						-- Requisita a interrupcao para a CPU
							interrupcaoAtiva <= '1';
							estadoTxEnvia <= esperaCPUAceitarInterrupcao;
						end if;
					end if;

				when esperaCPUAceitarInterrupcao =>

					if inta = '1' then	-- Se CPU aceitou a interrupcao da Uart
						if address = x"FFE00004" then	-- Se CPU endereçou a uart para escrever no RW
							signalRW <= dataIn(7 downto 0);		-- Pega o dado posto no barramento pela CPU
							rwPodeReceberDados <= '0';
							intr <= '0';
							interrupcaoAtiva <= '0';
							estadoTxEnvia <= esperaRDOEsvaziar;
						end if;
					end if;

				when esperaRDOEsvaziar =>

					if RDOOcupado = '0' then
						estadoTxEnvia <= transformaDadoP82;
					end if;

				when transformaDadoP82 =>

				RDOOcupado <= '1';
				contDescida := 0;
				for i in signalRW'range loop
					if signalRW(i) = '1' then contDescida := contDescida + 1;
					end if;
				end loop;

				if (contDescida mod 2) = 0 then
					-- Passa os 8bits de dados em RW para o protocolo P82 em RD0
        				RDOBits <= "0" & signalRW & "011";
				else
					-- Passa os 8bits de dados em RW para o protocolo P82 em RD0
        				RDOBits <= "0" & signalRW & "111";
				end if;

					contDescida := 0;
					estadoTxEnvia <= enviaDadoUart;

				when enviaDadoUart =>

					rwPodeReceberDados <= '1';	-- Tudo já foi transmitido para RDO, logo, RW esta livre para receber mais um dado
					if contDescida = 12 then -- Todos dados ja foram enviados
						RDOOcupado <= '0';
						estadoTxEnvia <= PedeDadoCPU;
					else
						contDescida := contDescida+1;
						OutUartToUart <= RDOBits((RDOBits'length-1)); -- Envia o dado serializado para a uart
						-- ATENÇÃO: O Vector le ao contrário! portanto o valor "001000101111" deve ser lido a partir da posicao 11 até a 0 do vetor!!!!!!
						RDOBits <= std_logic_vector(unsigned(RDOBits) sll 1); -- Retira do vetor o bit enviado
						send <= '1';	-- Liga o sinal de send
						estadoTxEnvia <= esperaAckUart; -- Espera a uart avisar que captou o dado
					end if;

				when esperaAckUart =>

					if ackUart = '1' then
						send <= '0';
						estadoTxEnvia <= enviaDadoUart;
					end if;

				when others => null;

			end case;

		end if;
  end process;

end UART;
