
import java.util.ArrayList;


public class CoinRepo implements ICoinRepo {

    final int LIMITE = 10;
    
    int[] coinBase;
    
    public CoinRepo() {
        
        coinBase = new int[CoinTypes.values().length];
        
    }
    
    @Override
    //@ ensures \result == LIMITE;
    public int getLimit() {
        
        return LIMITE;
        
    }

    @Override
    //@ requires getCoinNumber() < LIMITE;
    //@ ensures getTotalValue() == \old(getTotalValue()) + coin.valor;
    public void add(CoinTypes coin) throws LimitOverflowException {
    
        if (getCoinNumber()+1 > LIMITE) throw new LimitOverflowException();
        
        int index = -1;
        for (int i = 0; i < coinBase.length && index == -1; i++) if (CoinTypes.values()[i] == coin) index = i;
        
        coinBase[index]++;
    
    }

    @Override
    //@ ensures \result == (\sum int j; 0 <= j < coinBase.length; coinBase[j]);
    public int getCoinNumber() {
    
        int qtd = 0;
        for (int i = 0; i < coinBase.length; i++) qtd += coinBase[i];
        
        return qtd;
    
    }

    @Override
    //@ ensures \result == (\sum int j; 0 <= j < coinBase.length; coinBase[j] * CoinTypes.getValues()[j]);
    public int getTotalValue() {
    
        int value = 0;
        for (int i = 0; i < coinBase.length; i++) value += CoinTypes.values()[i].valor * coinBase[i];
        
        return value;
    
    }

    @Override
    //@ ensures (\sum int j; 0 <= j < coinBase.length; coinBase[j] * CoinTypes.getValues()[j]) <= \old(getTotalValue()) - value;
    public CoinTypes[] getChange(int value) {
    
        int troco = getTotalValue() - value;
        if (troco <= 0) return new CoinTypes[0];
        
        ArrayList<CoinTypes> moedas = new ArrayList<>();
        
        for (int i = coinBase.length - 1; i >= 0; i--) {
            while (coinBase[i] > 0 && troco >= CoinTypes.values()[i].valor) {
                
                moedas.add(CoinTypes.values()[i]);
                troco -= CoinTypes.values()[i].valor;
                coinBase[i]--;
                
            }
        }
        
        CoinTypes[] retorno = new CoinTypes[moedas.size()];
        return (CoinTypes[]) moedas.toArray(retorno);
    
    }

    @Override
    //@ ensures getTotalValue() == 0;
    //@ ensures getCoinNumber() == 0;
    public void reset() {
    
        for (int i = 0; i < coinBase.length; i++) coinBase[i] = 0;
    
    }
    
}
