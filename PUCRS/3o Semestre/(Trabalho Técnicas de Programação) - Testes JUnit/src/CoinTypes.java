
public enum CoinTypes {
    
    UM(1),
    CINCO(5),
    DEZ(10),
    VINTE_E_CINCO(25),
    CINQUENTA(50),
    CEM(100);
    
    public int valor;
    CoinTypes(int valor) {

        this.valor = valor;
        
    }
    
    //@ ensures \result == (\sum int j; 0 <= j < coins.length; coins[j].valor);
    static int sum(CoinTypes[] coins) {
        
        int i = 0;
        for (CoinTypes c : coins) i += c.valor;
        return i;
        
    }
    
}
