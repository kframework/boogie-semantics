method Main(n: int)
{
    var sumTo: int;
    var sum: int;
    var iter: int;
    sumTo:=20;
    sum:=0;
    iter:=0;

    while (iter != sumTo) 
      invariant sum * 2 == iter * (iter + 1); 
      invariant sumTo - iter >= 0;
      decreases sumTo - iter;
    {
        iter := iter + 1;
        sum := sum + iter;
    }

    assert  sum == 210;
}