function exp(x: int, n: int): int
    requires n >= 0
{
    if n == 0 then 
        1
	else if n == 1 then
		x
     else 
        x * exp(x, n-1)
}

function isEven(a: int): bool
    requires a >= 0
{
    a % 2 == 0
}


function exp_by_squaring2(y: int, x: int, n :int): (r :  int)
    requires n >= 0
	decreases n	
  {
    if n == 0 then y
    else if isEven(n) then exp_by_squaring2(y, x * x, n / 2)
    else exp_by_squaring2(x * y, x * x, (n - 1) / 2)
  }

function exp_by_squaring(x: int, n :int): (r :  int)
    requires n >= 0
  {
		exp_by_squaring2(1, x , n)
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

lemma factor(x: int, n: int, m: int)
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
		factor(x, n, m - 1);
	}
}

lemma factor2(x: int, n: int, m: int)
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
		//factor(x, (m-1) * n, n); // exp(x, m*n) = exp(x, n * (m-1)) * exp(x, n)
		factor(x, n, (m-1) * n); // exp(x, m*n) = exp(x, n * (m-1)) * exp(x, n)		
		factor2(x, n, m - 1);	 // exp(x, n * (m-1)) = exp(exp(x, n), m - 1) -> 
		assert(exp(exp(x, n), m - 1) * exp(x, n) == exp(exp(x, n), m));	//	exp(exp(x, n), m - 1) * exp(x, n) = exp(exp(x, n), m)
	}
}

method IndexComp(n2: int, i2: int, j2 : int) returns (n: int, i: int, j : int)
requires n2 > 1 
requires i2 >= 1
requires j2 >= 0  
ensures n >= 1 
ensures i >= 1
ensures j >= 0 
ensures isEven(n2) ==> j == j2 && n ==  n2 /2
ensures !isEven(n2) ==> j == j2 + i2 && n ==  (n2 - 1) /2
ensures i == i2 *2
ensures i2*n2 +j2  == i*n +j   
{
	n := n2;
	i := i2;
	j := j2;
    assert(i2*n2 +j2  == i*n +j);			  	
	if (!isEven(n))
	{
		n := n - 1;
		assert(j == j2);		
		j := j + i;		
		assert(j == j2 + i);
    	assert(i2*n2 +j2  == i*n +j);		
	}
	n := n / 2;
	i := i * 2;	 
	assert(i2*n2 +j2  == i*n +j);			  	      
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
		factor2(x, 2, (n-1)/2);
		assert(exp(x , n) == x * exp(x*x, (n-1)/2));
		assert(y * exp(x , n) == y * x * exp(exp(x, 2), (n-1)/2));
        y, x, n := x * y, x * x, (n-1)/2;	// y * exp(x , n) == y' * exp(x', (n - 1)/2)
		// y' = x * y
		// x' = x * x
		// zz  	exp(x , n) = x * exp(x*x, (n-1)/2)
	  }
	  else
	  {    
	    factor2(x, 2, n/2);
		assert(exp(x , n) == exp(x*x, n/2));	
		assert(y * exp(x , n) == y * exp(exp(x, 2), n/2));			
      	y, x, n := y, x * x, n / 2;  // y * exp(x , n) -> y' * exp(x', n/2)
		// y' = y
		// x' = x * x  
		// zz  	exp(x , n) = exp(x*x, n/2)
	  }	   
	}
	assert(n == 1);
    r:= x * y; 	
}

