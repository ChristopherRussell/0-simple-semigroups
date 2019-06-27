InstallMethod(NrMatricesAllRowsAndColsUnique,
"for an int and an int", [IsInt, IsInt],
function(m, n)
  local sum, iter_comps, comps, iter_labels, labels, size, parity;
  if m < 1 then
    ErrorNoReturn("OtherSmallSemi: NrMatricesAllRowsAndColsUnique: the ",
                  "first arugment should be a positive integer,");
  elif n < 1 then
    ErrorNoReturn("OtherSmallSemi: NrMatricesAllRowsAndColsUnique: the ",
                  "second arugment should be a positive integer,");
  elif list[1] < list[2] then
    return NrMatricesAllRowsAndColsUnique([list[2], list[1]]);
  elif list[1] > 2 ^ list[2] then
    return 0;
  fi;
  sum        := 0;
  iter_comps := IteratorOfConnectedComponents(m, n, rho, sig)
  while not IsDoneIterator(iter_comps) do
    comps       := NextIterator(iter_comps);
    iter_labels := IteratorOfLabelGCDs(comps);
    while not IsDoneIterator(iter_labels) do
      labels := NextIterator(iter_labels);
      size   := CardinalityOfMatrixSetsIntersection(comps, labels);
      parity := ParityOfMatrixSetsCollection(comps, labels);
      sum    := sum + size * parity;
    od;
  od;
  return sum;
end);

InstallMethod(IteratorOfConnectedComponents,
"for an int, an int, a perm and a perm",
[IsInt, IsInt, IsPerm, IsPerm],
function(m, n, rho, sig)
  local R;
  IteratorOfCC := function(m, rho)
    local lens, comps, i;
    lens  := CycleLengths(rho);
    comps := EmptyPlist(m);
    for i in [1 .. m] do
      comps[i] := Partitions(Number(lens, l -> l = i));
    od;
    return IteratorOfCartesianProduct(comps);
  end;
  R          := rec();
  R!.iter1   := IteratorOfConnectedComponents(m, rho);
  R!.iter2   := IteratorOfConnectedComponents(n, sig);
  R!.temp    := NextIterator(R!.iter1);

  R!.NextIterator := function(iter)
    if IsDoneIterator(R!.iter2) then
      R!.temp    := NextIterator(R!.iter1);
      R!.iter2   := IteratorOfConnectedComponents(n, sig);
    fi;
    return Concatenation(R!.temp, NextIterator(R!.iter2));
  end;

  R!.IsDoneIterator := function(iter)
    return IsDoneIterator(R!.iter1) and IsDoneIterator(R!.iter2);
  end;

  R!.ShallowCopy   := function(iter)

    return rec(iter1   := iter!.iter1,
               iter2   := iter!.iter2,
               temp    := iter!.temp);
  end;

  return IteratorByFunctions(R);
end);

InstallMethod(IteratorOfLabelsGCDs,
"for an int, an int and a list",
[IsInt, IsInt, IsList],
function(m, n, comps)
  local divs, i;
  for i in [1 .. m] do
    divs      := ShallowCopy(DivisorsInt(i));
    Remove(divs);  # Remove i from divs
    labels[i] := ListWithIdenticalEntries(Length(comps[i]), divs);
  od;
  for i in [1 .. n] do
    divs      := ShallowCopy(DivisorsInt(i));
    Remove(divs);  # Remove i from divs
    labels[m + i] := ListWithIdenticalEntries(Length(comps[m + i]), divs);
  od;
  return IteratorOfCartesianProduct(labels);
end);

InstallMethod(CardinalityOfMatrixSets,
"for an int, an int, a list and a list",
[IsInt, IsInt, IsList, IsList],
function(m, n, comps, labels)
  local prod, out, x, i, y, j;
  prod := 1;
  for x in [1 .. m] do
    for i in [1 .. Length(comps[x])] do
      for y in [1 .. n] do
        for j in [1 .. Length(comps[m + y])] do
          out := out * Omega(Gcd(labels[x][i], labels[m + y][j]),
                             comps[x][i],
                             comps[m + y][j]);
        od;
      od;
    od;
  od;
  return prod;
end);

InstallMethod(Omega,
"for an int, an int and an int",
[IsInt, IsInt, IsInt],
function(k, x, y)
  return Sum(DivisorsInt(k), d -> omega(d) * d ^ (x + y - 2));
end);

# TODO: THIS SHOULD BE AN ATTRIBUTE
InstallMethod(omega,
"for an int", [IsInt],
function(p)
  if p = 1 then
    return 2;
  fi;
  divs := ShallowCopy(DivisorsInt(p));
  Remove(divs);  # Remove p from divs
  return 2 ^ p - Sum(divs, q -> omega(q));
end);

InstallMethod(ParityOfGraphTupleClass,
"for an int, an int, a list and a list",
[IsInt, IsInt, IsList, IsList],
function(m, n, comps, labels)
  return Psi(comps) * Omega(m, n, comps, labels);
end);

InstallMethod(Psi,
"for a list", [IsList],
function(comps)
  return Product([1 .. Length(comps)], x -> psi(Sum(comps[x]), List([1 ..
  Sum(comps[x])], i -> Number(comps[x], j -> j = i))));
end);

InstallMethod(psi,
"for an int and a list", [IsInt, IsList],
function(degree, comp)
  return Factorial(degree) *
         Product([1 .. degree],
                 j -> ((-1) ^ (j - 1) * Factorial(j - 1)) ^ comp[j]) /
         Product([1 .. degree], i -> Factorial(comp[i]) * i ^ comp[i]) /
         Product([1 .. degree], i -> Factorial(i - 1) ^ comp[i]);
end);

InstallMethod(Omega,
"for an int, an int, a list and a list",
[IsInt, IsInt, IsList, IsList],
function(m, n, comps, labels)
  local prod, x, d;
  prod := 1;
  for x in [1 .. m + n] do
    for d in divs[x] do
      if x > m then
        prod := prod * omega(x - m, d);
      else
        prod := prod * omega(x, d);
      fi;
    od;
  od;
  return prod;
end);

InstallMethod(omega,
"for a int and a int", [IsInt, IsInt],
function(x, k)
  p := PrimePowersInt(x / k);
  if ForAll([2, 4 .. Length(p)], i -> p[i] = 1) then
    return (-1) ^ (Length(p) / 2);
  fi;
  return 0;
end);
