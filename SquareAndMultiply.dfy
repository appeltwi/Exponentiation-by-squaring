opaque function pow(x: int, n: int): int
    requires n >= 0
{
    if n == 0 then 
        1
    else 
        x * pow(x, n-1)
}

opaque function isEven(a: int): bool
    requires a >= 0
{
    a % 2 == 0
}

type EvenInt = x: nat | x % 2 == 0 witness 2
type OddInt = x: nat | x % 2 != 0 witness 3

method NormalExp(x: int, n: int) returns (r: int)
requires P: n > 0
ensures r == pow(x, n)
{
    r := x;
    var tmp := n - 1;
    assert(tmp > -1) by { reveal P; }
    calc
    { 
        pow(x, n - tmp);        
        pow(x, n - n + 1);
        { reveal pow(); }
        r;
    }    
    while(tmp > 0)
        invariant tmp >= 0
        invariant r == pow(x, n - tmp)
        decreases tmp
    {       
        reveal pow();    
        r := r * x;
        tmp := tmp - 1;
    }
    assert(r == pow(x, n)) by { reveal P; }
}

lemma AssociativityLaw(x: int, n: int, m: int)
  requires npos: n >= 0
  requires mpos: m >= 0
  ensures pow(x, n + m) == pow(x, n) * pow(x, m)
{	  
    if (m == 0)
    {
        reveal npos;
        assert(pow(x, n + 0) == pow(x,n) * pow(x, 0)) by 
        {
            reveal pow();
        }
    } 
    else
    {
        reveal npos; 
        reveal mpos;        
        calc 
        {                                
            pow(x, n + m);                
            pow(x, n + m - 1 + 1);            
            { reveal pow(); }
            pow(x, n + m - 1) * x;  
            { AssociativityLaw(x, n, m - 1);}
            pow(x, n) * pow(x, m - 1) * x;   
            { reveal pow(); }
            pow(x, n) * pow(x, m);                   
        }
    }
}

lemma AssociativityLaw2(x: int, n: int, m: int)
  requires npos: n > 0
  requires mpos: m >= 0
  ensures pow(x, n * m) == pow(pow(x, n), m)
{
    if (m == 0)
    {
        reveal npos;    
        calc {
        pow(x, n * m);
        { reveal pow(); }
        1;
        { reveal pow(); }
        pow(pow(x, n), 0);
        }
    }
    else
    {
        reveal npos; 
        reveal mpos;          
        calc 
        {
            pow(x, n * m);
            pow(x, n * (m-1) + n);
                { AssociativityLaw(x, n, (m-1) * n);} 
            pow(x, n * (m-1)) * pow(x, n);
                { AssociativityLaw2(x, n, m - 1);} 
            pow(pow(x, n), m -1) * pow(x, n);  
            { reveal pow(); }
            pow(pow(x, n), m - 1) * pow(pow(x, n), 1);        
                { AssociativityLaw(pow(x, n), m - 1, 1);} 
            pow(pow(x, n), m);                
        }
    }
}

method FastExpr(x2: int, n2: int) returns (r: int)
requires npos: n2 > 0
ensures r == pow(x2, n2)
{
    var x := x2;
    var n := n2;
    assert(n > 0) by {reveal npos;}
    var y := 1; 		
    while (n > 1)
        decreases n
        invariant n > 0
        invariant y * pow(x, n) == pow(x2, n2) 	
    {	
      reveal isEven();  		    
      if (!isEven(n))
      {
        calc
        {
            y * pow(x, n); 
           { reveal pow(); }                    
            y * pow(x, n - 1)*x; 
           { AssociativityLaw2(x, 2, (n-1)/2);}             
            y * pow(pow(x, 2), (n - 1)/2) * x;   
        }       
        y, x, n := x * y, pow(x, 2), (n-1) / 2;	
      }
      else
      {            	
        calc
        {
            y * pow(x, n);  
           { AssociativityLaw2(x, 2, n / 2);}             
            y * pow(pow(x, 2), n / 2);   
        }     
        y, x, n := y, pow(x, 2), n / 2; 
      }	   
    }   
    calc
    {
        y * pow(x, n) == pow(x2, n2); 	 
            { reveal pow(); }     
        y * x == pow(x2, n2);        
    }
    r:= x * y; 	
}