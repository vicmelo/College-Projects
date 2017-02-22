import static org.junit.Assert.*;

import org.junit.Test;
import java.util.Arrays;
import org.junit.Before;
import java.util.Collection;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

@RunWith(value = Parameterized.class)
public class Driver_CoinRepo {
    
    private ICoinRepo repo;
    private final CoinTypes[] coins;
    
    @Parameters
    public static Collection data() {
        
        return Arrays.asList(new Object[][]{
        
            { new CoinTypes[] { CoinTypes.DEZ, CoinTypes.VINTE_E_CINCO, CoinTypes.VINTE_E_CINCO }},
            { new CoinTypes[] { CoinTypes.CEM, CoinTypes.CEM,           CoinTypes.CEM }}
        
        });
        
    }
    
    public Driver_CoinRepo(CoinTypes[] coins) {
        
        this.coins = coins;
        
    }
    
    @Before
    public void setup() {

        repo = new CoinRepo();
        
    }
    
    @Test
    public void getLimitTest() {
        
        assertEquals(repo.getLimit(), 10);
        
    }
    
    @Test
    public void addTest() {

        try {
        
            for (int i = 0; i < 3; i++) {
                for (int j = 0; j < coins.length; j++) {
                
                    repo.add(coins[j]);
                    
                }
            }
            repo.reset();
        
        }
        catch (LimitOverflowException e) {
            
            fail("1. Limite não foi estourado ainda, 9 itens");
            
        }
        
        try {
        
            for (int i = 0; i < 3; i++) {
                for (int j = 0; j < coins.length; j++) {
                
                    repo.add(coins[j]);
                    
                }
            }
            repo.add(CoinTypes.VINTE_E_CINCO);
            repo.reset();
        
        }
        catch (LimitOverflowException e) {
            
            fail("2. Limite não foi estourado ainda, 10");
            
        }
        
        try {
        
            for (int i = 0; i < 4; i++) {
                for (int j = 0; j < coins.length; j++) {
                
                    repo.add(coins[j]);
                    
                }
            }
            repo.reset();
            
            fail("Limite estourado");
        
        }
        catch (LimitOverflowException e) {}
        
    }
    
    @Test
    public void getCoinNumberTest() {
        
        try {
            
            for (int j = 0; j < coins.length; j++) {
                
                repo.add(coins[j]);
                    
            }
        
        } catch (LimitOverflowException e) { fail(); }
        
        assertEquals(repo.getCoinNumber(), coins.length);

    }
    
    @Test
    public void getTotalValueTest() {
        
        try {
            
            for (int j = 0; j < coins.length; j++) {
                
                repo.add(coins[j]);
                    
            }
        
        } catch (LimitOverflowException e) { fail(); }
        
        assertEquals(repo.getTotalValue(), CoinTypes.sum(coins));
        
    }
    
    @Test
    public void getChangeTest() {
        
        try {
            
            for (int j = 0; j < coins.length; j++) {
                
                repo.add(coins[j]);
                    
            }
        
        } catch (LimitOverflowException e) { fail(); }
        
        int total = repo.getTotalValue();
        int sum = CoinTypes.sum(repo.getChange(50));
        assertTrue(sum <= (total-50));
        
        try {
            
            for (int j = 0; j < coins.length; j++) {
                
                repo.add(coins[j]);
                    
            }
        
        } catch (LimitOverflowException e) { fail(); }
        
        total = repo.getTotalValue();
        sum = CoinTypes.sum(repo.getChange(55));
        assertTrue(sum <= (total - 55));
        
    }
    
    @Test
    public void resetTest() {
        
        try {
            
            for (int j = 0; j < coins.length; j++) {
                
                repo.add(coins[j]);
                    
            }
        
        } catch (LimitOverflowException e) { fail(); }
        
        repo.reset();
        
        assertEquals(repo.getCoinNumber(), 0);
        assertEquals(repo.getTotalValue(), 0);
        
    }
    
}
