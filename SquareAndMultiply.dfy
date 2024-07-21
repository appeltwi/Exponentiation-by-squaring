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
  requires m > 0
  ensures exp(x, n + m) == exp(x, n) * exp(x, m)
{
	if (m == 1)
	{
		assert(exp(x, n + 1) == exp(x,n)*x);
	}
	else
	{
		factor(x, n, m - 1);
	}
}

lemma factor2(x: int, n: int, m: int)
  requires n > 0
  requires m > 0
  ensures exp(x, n * m) == exp(exp(x, n), m)
{
	if (m == 1)
	{
		assert(exp(x, n * 1) == exp(x,n));
	}
	else
	{
		assert(exp(x, n * m) == exp(x, n * (m-1) + n));		
		factor(x, (m-1) * n, n); // exp(x, m*n) = exp(x, n * (m-1)) * exp(x, n)
		factor2(x, n, m - 1);	 // exp(x, n * (m-1)) = exp(exp(x, n), m - 1) -> 
		assert(exp(exp(x, n), m - 1) * exp(x, n) == exp(exp(x, n), m));	//	exp(exp(x, n), m - 1) * exp(x, n) = exp(exp(x, n), m)
	}
}

method FastExpr(x2: int, n2: int) returns (r: int)
requires n2 > 0
ensures r == exp(x2, n2)
{
    var x := x2;
	var n := n2;
	var nrest := 0;	
    var y := 1;
	var r2 := x * y;
	var i := 1;
    while (n > 1)
		invariant n >= 1
		invariant i >= 1
		decreases n
		invariant nrest + n == n2	
		invariant exp(x2, nrest) * exp(x2, n) == exp(x2, n2)
		invariant x == exp(x2, i)
		invariant exp(x2, i * n) == exp(exp(x2, i), n)
		invariant exp(x, n) == exp(x2, i * n)
		//invariant y * exp(x, n) == exp(x2, n2) 	
	{
	  assert(exp(x2, i * n) == exp(exp(x2, i), n));		
      if (!isEven(n))
	  {
        y := x * y;
        nrest, n := nrest + 1, n - 1;
	  }
      x := x * x;
      nrest, n := nrest + n / 2, n - n / 2;
	  factor(x2, nrest, n); // exp(x2, nrest + n) = exp(x2, nrest) * exp(x2, n)
	  factor(x2, i, i);// exp(x2, 2*i) = exp(x2, i) * exp(x2, i)
	  factor2(x2, i, n);// exp(x2, i * n) == exp(exp(x2, i), n)
	  assert(exp(x2, i * n) == exp(exp(x2, i), n));
	  i := i * 2;
	  factor2(x2, i, n);// exp(x2, i * n) == exp(exp(x2, i), n)	    
	}
	assert(nrest + n == n2);
	//assert(x * y == exp(x2, n2));
    r:= x * y; 	
}
