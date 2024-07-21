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

method FastExpr(x2: int, n2: int) returns (r: int)
requires n2 > 0
ensures r == exp(x2, n2)
{
    var x :=  x2;
	var n := n2;
	var nrest := 0;	
    var y := 1;
    while (n > 1)
		invariant n >= 1
		decreases n
		invariant nrest + n == n2	
		invariant exp(x2, nrest) * exp(x2, n) == exp(x2, n2)		
		invariant y * exp(x, n) == exp(x2, n2) // schlägt fehl
	{
      if (!isEven(n))
	  {
        y := x * y;
        nrest, n := nrest + 1, n - 1;
	  }
      x := x * x;
      nrest, n := nrest + n / 2, n - n / 2;
	  factor(x2, nrest, n);
	}
	assert(nrest + n == n2);
	assert(x * y == exp(x2, n2));
    r:= x * y; 	
}