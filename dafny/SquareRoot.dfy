method SquareRoot (x : int) returns (z : int) 
  requires x > 0
  ensures z*z<=x && x<(z+1)*(z+1)
  ensures forall j:int :: j > 0
{
      z := 0;
      while (z+1)*(z+1) <= x 
        invariant z * z <= x
      {
        z := z+1;
      }
}