
public interface ICoinRepo {
    
    public /*@ pure */ int getLimit();
    
    public /*@ pure */ int getCoinNumber();
    
    public /*@ pure */ int getTotalValue();
    
    //@ ensures getCoinNumber() == \old(getCoinNumber()) + 1 || getCoinNumber() == getLimit();
    //@ ensures \old(getCoinNumber()) < getLimit() <==> getTotalValue() == \old(getTotalValue()) + coin.valor;
    public void add(CoinTypes coin) throws LimitOverflowException;
    
    //@ requires value >= 0;
    //@ ensures CoinTypes.sum(\result) <= \old(getTotalValue()) - value;
    public CoinTypes[] getChange(int value);
    
    //@ ensures getCoinNumber() == 0;
    //@ ensures getTotalValue() == 0;
    public void reset();
    
}
