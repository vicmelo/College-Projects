# AlgEstDadosI

Este projeto trata-se da implementação do código de uma calculadora que lê um arquivo com números e operações e executa estas operações, utilizando uma estrutura de pilha. Os arquivos estão na pasta "Casos de Teste". As operações contidas no arquivo e que devem ser tratadas são:

- inteiro: neste caso o inteiro deve ser inserido na calculadora e torna-se disponível;
- +,*: as operações de soma e multiplicação são executadas com os dois últimos números disponíveis;
- -, /: as operações de subtração e divisão são realizadas com os dois últimos números disponíveis. A ordem é importante:

2
3
/

deve resultar em 1.5
- pop: descarta o último resultado da calculadora;
- dup: repete o último resultado;
- swap: troca de ordem os dois últimos resultados;
- sin, cos: calculam o seno e cosseno respectivamente do último resultado;
- atan: calcula o arco-tangente, mas usa **dois** números da pilha. O arquivo

2
3
atan

produz o resultado 0.982794...

##Resultado:

Como resultado, devem ser mostrados:

-Resultado das operações
-Tamanho máximo da pilha
-Tamanho atual da pilha
