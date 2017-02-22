# T3-Org-Arq-2

Anotações importantes (para falar no relatório)
Sistema SEND e ACK entre CPU e RAM

Send aparenta nunca descer (sempre está em 1 a partir do momento em que reset baixa), mas na verdade, quando o Iaddress muda, o need2Send2Late sobe (indicando que precisa mandar algo no futuro). Assim, quando o send vai baixar, o need2Send2Late ta em 1, então ao invés de baixar, Send permanece em um, porém para o address novo.


Metodologia de substituição de dados na cache:

Contador de acesso aos dados da cache. Cada vez que um dado é acessado, soma um.
Quando o resultado é miss, substitui o dado menos acessado na cache pelo dado novo e zera os contadores (para não acontecer de um dado ser muito acessado no início, depois nunca mais ser acessado mas continuar na cache por tempo indefinido). Por fim, soma um acesso ao dado novo inserido.