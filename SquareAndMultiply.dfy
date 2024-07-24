function exp(x: int, n: int): int
    requires n >= 0
{
    if n == 0 then 
        1
    else 
        x * exp(x, n-1)
}

function isEven(a: int): bool
    requires a >= 0
{
    a % 2 == 0
}

method NormalExp(x: int, n: int) returns (r: int)
requires n > 0
ensures r == exp(x, n)
{
    r := x;
    var tmp := n - 1;
    while(tmp > 0)
        invariant r == exp(x, n - tmp)
    {
        r := r * x;
        tmp := tmp - 1;
    }
}

lemma AssociativityLaw(x: int, n: int, m: int)
  requires n > 0
  requires m >= 0
  ensures exp(x, n + m) == exp(x, n) * exp(x, m)
{	
    if (m == 0)
    {
        assert(exp(x, n + 0) == exp(x,n));
    }
    else
    {
        AssociativityLaw(x, n, m - 1);
    }
}

lemma AssociativityLaw2(x: int, n: int, m: int)
  requires n > 0
  requires m >= 0
  ensures exp(x, n * m) == exp(exp(x, n), m)
{
    if (m == 0)
    {
        assert(exp(x, 0) == 1);
    }
    else
    {
        assert(exp(x, n * m) == exp(x, n * (m-1) + n));		
        AssociativityLaw(x, n, (m-1) * n); // exp(x, m*n) = exp(x, n * (m-1)) * exp(x, n)		
        AssociativityLaw2(x, n, m - 1);	 // exp(x, n * (m-1)) = exp(exp(x, n), m - 1) 
    }
}

method FastExpr(x2: int, n2: int) returns (r: int)
requires n2 > 0
ensures r == exp(x2, n2)
{
    var x := x2;
    var n := n2;
    var y := 1;		
    assert(y * exp(x, n) == exp(x2, n2));
    while (n > 1)
        decreases n
        invariant n > 0
        invariant y * exp(x, n) == exp(x2, n2) 	
    {			
      if (!isEven(n))
      {
        AssociativityLaw2(x, 2, (n-1)/2);  // exp(x,n-1) == exp(exp(x, 2), (n-1)/2)     
        y, x, n := x * y, exp(x, 2), (n-1)/2;	
        // y * exp(x , n) == y' * exp(x', (n - 1)/2)    
        // y' = x * y
        // x' = x * x
        // zz  	exp(x , n) = x * exp(exp(x, 2), (n-1)/2)
      }
      else
      {    
        AssociativityLaw2(x, 2, n / 2); // exp(x, n) == exp(exp(x, 2), n/2)		
        y, x, n := y, exp(x, 2), n / 2; 
        // y * exp(x , n) -> y' * exp(x', n/2)           
        // y' = y
        // x' = x * x  
        // zz  	exp(x , n) = exp(x*x, n/2)
      }	   
    }
    assert(n == 1);
    r:= x * y; 	
}

