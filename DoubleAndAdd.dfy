function sum(x: int, n: int): int
    requires n >= 0
{
    if n == 0 then 
        0
    else 
        x + sum(x, n-1)
}

function isEven(a: int): bool
    requires a >= 0
{
    a % 2 == 0
}

lemma AssociativityLaw(x: int, n: int, m: int)
  requires n > 0
  requires m >= 0
  ensures sum(x, n + m) == sum(x, n) + sum(x, m)
{	
    if (m == 0)
    {
        assert(sum(x, n + 0) == sum(x,n));
    }
    else
    {
        AssociativityLaw(x, n, m - 1);
    }
}

lemma AssociativityLaw2(x: int, n: int, m: int)
  requires n > 0
  requires m >= 0
  ensures sum(x, n * m) == sum(sum(x, n), m)
{
    if (m == 0)
    {
        assert(sum(x, 0) == 0);
    }
    else
    {
        assert(sum(x, n * m) == sum(x, n * (m-1) + n));		
        AssociativityLaw(x, n, (m-1) * n); // sum(x, m*n) = sum(x, n * (m-1)) * sum(x, n)		
        AssociativityLaw2(x, n, m - 1);	 // sum(x, n * (m-1)) = sum(sum(x, n), m - 1) 
    }
}

lemma sumtest(x: int, n: int)
    requires n >= 0
    ensures  x * n == sum(x,n)
{

}


method NormalSum(x: int, n: int) returns (r: int)
requires n > 0
ensures r == x * n
{
    r := x;
    var tmp := n - 1;
    while(tmp > 0)
        invariant r == sum(x, n - tmp)
    {
        r := r + x;
        tmp := tmp - 1;
    }
    sumtest(x, n);
}

method FastSum(x2: int, n2: int) returns (r: int)
requires n2 > 0
ensures r ==  x2 * n2
{
    var x := x2;
    var n := n2;
    var y := 0;		
    assert(y + sum(x, n) == sum(x2, n2));
    while (n > 1)
        decreases n
        invariant n > 0
        invariant y + sum(x, n) == sum(x2, n2) 	
    {			
      if (!isEven(n))
      {
        AssociativityLaw2(x, 2, (n-1)/2);  // sum(x,n-1) == sum(sum(x, 2), (n-1)/2)     
        y, x, n := x + y, sum(x, 2), (n-1)/2;	
        // y * sum(x , n) == y' * sum(x', (n - 1)/2)    
        // y' = x * y
        // x' = x * x
        // zz  	sum(x , n) = x * sum(sum(x, 2), (n-1)/2)
      }
      else
      {    
        AssociativityLaw2(x, 2, n / 2); // sum(x, n) == sum(sum(x, 2), n/2)		
        y, x, n := y, sum(x, 2), n / 2; 
        // y * sum(x , n) -> y' * sum(x', n/2)           
        // y' = y
        // x' = x * x  
        // zz  	sum(x , n) = sum(x*x, n/2)
      }	   
    }
    assert(n == 1);
    sumtest(x2, n2);
    r:= x + y; 	
}

