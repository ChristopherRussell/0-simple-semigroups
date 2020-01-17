InstallMethod(NrMatricesAllRowsAndColsUniqueUpToRowAndColPermutation,
"for an int and an int", [IsInt, IsInt],
function(m, n)
  local sum, G1, G2, class1, class2;
  if m < 1 then
    ErrorNoReturn("OtherSmallSemi: NrMatricesAllRowsAndColsUniqueUpToRowAndColPermutation: the ",
                  "first arugment should be a strictly positive integer,");
  elif n < 1 then
    ErrorNoReturn("OtherSmallSemi: NrMatricesAllRowsAndColsUniqueUpToRowAndColPermutation: the ",
                  "second arugment should be a strictly positive integer,");
  elif m < n then
    return NrMatricesAllRowsAndColsUniqueUpToRowAndColPermutation(n, m);
  elif m > 2 ^ n then
    return 0;
  fi;
  sum    := 0;
  G1     := SymmetricGroup(m);
  G2     := SymmetricGroup(n);
  for class1 in ConjugacyClasses(G1) do
    for class2 in ConjugacyClasses(G2) do
      sum := sum + Size(class1) * Size(class2) *
             NrMatricesAllRowsAndColsUnique(m, n, Representative(class1),
             Representative(class2));
    od;
  od;
  return (sum / Factorial(m)) / Factorial(n);
end);

InstallMethod(NrMatricesAllRowsAndColsUnique,
"for an int, an int, a perm and a perm", [IsInt, IsInt, IsPerm, IsPerm],
function(m, n, rho, sig)
  local sum, iter_comps, comps, iter_labels, labels, size, parity;
  if m < 1 then
    ErrorNoReturn("OtherSmallSemi: NrMatricesAllRowsAndColsUnique: the ",
                  "first arugment should be a positive integer,");
  elif n < 1 then
    ErrorNoReturn("OtherSmallSemi: NrMatricesAllRowsAndColsUnique: the ",
                  "second arugment should be a positive integer,");
  elif m < n then
    return NrMatricesAllRowsAndColsUnique(n, m, sig, rho);
  elif m > 2 ^ n then
    return 0;
  elif Order(rho) <> Order(sig) then
    return 0;
  fi;
  sum        := 0;
  iter_comps := IteratorOfConnectedComponents(m, n, rho, sig);
  while not IsDoneIterator(iter_comps) do
    comps       := NextIterator(iter_comps);
    iter_labels := IteratorOfLabelGCDs(m, n, comps);
    while not IsDoneIterator(iter_labels) do
      labels := NextIterator(iter_labels);
      size   := __OmegaSum(m, n, comps, labels);
##        if CountByCompsAndLabels(m, n, comps, labels) <> size then
##          Print(comps, "\n", labels, "\n\n");
##        fi;
      parity := ParityOfMatrixSetsCollection(m, n, comps, labels);
      sum    := sum + size * parity;
    od;
  od;
  return sum;
end);

InstallMethod(IteratorOfConnectedComponents,
"for an int, an int, a perm and a perm",
[IsInt, IsInt, IsPerm, IsPerm],
function(m, n, rho, sig)
  local IteratorOfCC, R;
  IteratorOfCC := function(m, rho)
    local lens, comps, i;
    lens  := CycleLengths(rho, [1 .. m]);
    comps := EmptyPlist(m);
    for i in [1 .. m] do
      comps[i] := Partitions(Number(lens, l -> l = i));
    od;
    return IteratorOfCartesianProduct(comps);
  end;
  R          := rec();
  R!.iter1   := IteratorOfCC(m, rho);
  R!.iter2   := IteratorOfCC(n, sig);
  R!.temp    := NextIterator(R!.iter1);

  R!.NextIterator := function(iter)
    if IsDoneIterator(R!.iter2) then
      R!.temp    := NextIterator(R!.iter1);
      R!.iter2   := IteratorOfCC(n, sig);
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

# TODO: need to give special consideration to the case where some cycle lengths
# are equal to 1.
InstallMethod(IteratorOfLabelGCDs,
"for an int, an int and a list",
[IsInt, IsInt, IsList],
function(m, n, comps)
  local labels, divs, x;
  labels := EmptyPlist(m + n);
  for x in [1 .. m + n] do
    if IsEmpty(comps[x]) then
      labels[x] := [[]];
##      elif x = 1 or x = m + 1 then
##        labels[x] := [ListWithIdenticalEntries(Length(comps[x]), 1)];
    else
      if x > m then
        divs := ShallowCopy(DivisorsInt(x - m));
      else
        divs := ShallowCopy(DivisorsInt(x));
      fi;
##      Remove(divs);  # Remove i from divs
      labels[x] := Cartesian(ListWithIdenticalEntries(Length(comps[x]), divs));
    fi;
  od;
  return IteratorOfCartesianProduct(labels);
end);

InstallMethod(CardinalityOfMatrixSetsIntersection,
"for an int, an int, a list and a list",
[IsInt, IsInt, IsList, IsList],
function(m, n, comps, labels)
  local prod, x, i, y, j;
  prod := 1;
  for x in [1 .. m] do
    for i in [1 .. Length(comps[x])] do
      for y in [1 .. n] do
        for j in [1 .. Length(comps[m + y])] do
          prod := prod *_Omega(Gcd(labels[x][i], labels[m + y][j]),
                               comps[x][i],
                               comps[m + y][j]);
        od;
      od;
    od;
  od;
  return prod;
end);

InstallMethod(_Omega,
"for an int, an int and an int",
[IsInt, IsInt, IsInt],
function(k, x, y)
  return Sum(DivisorsInt(k), d -> omega(d) * d ^ (x + y - 2));
end);

# TODO: THIS SHOULD BE AN ATTRIBUTE BUT DOESN'T WORK AS AN INT ATTRIBUTE
InstallMethod(omega,
"for an int", [IsInt],
function(p)
  local divs;
  if p = 1 then
    return 2;
  fi;
  divs := ShallowCopy(DivisorsInt(p));
  Remove(divs);  # Remove p from divs
  return 2 ^ p - Sum(divs, q -> omega(q));
end);

#  TODO: Shouldn't this return the negative of what it currently returns?
InstallMethod(ParityOfMatrixSetsCollection,
"for an int, an int, a list and a list",
[IsInt, IsInt, IsList, IsList],
function(m, n, comps, labels)
  return Psi(comps) * Theta(m, n, comps, labels);
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

InstallMethod(Theta,
"for an int, an int, a list and a list",
[IsInt, IsInt, IsList, IsList],
function(m, n, comps, labels)
  local prod, x, i;
  prod := 1;
  for x in [1 .. m + n] do
    for i in [1 .. Length(comps[x])] do
      if x > m then
        prod := prod * theta(x - m, labels[x][i]);
      else
        prod := prod * theta(x, labels[x][i]);
      fi;
    od;
  od;
  return prod;
end);

InstallMethod(theta,
"for a int and a int", [IsInt, IsInt],
function(x, k)
  local p;
  p := PrimePowersInt(x / k);
  if ForAll([2, 4 .. Length(p)], i -> p[i] = 1) then
    return (-1) ^ (Length(p) / 2);
  fi;
  return 0;
end);


MatsFixedBy := function(m, n, p, q)
  local a, b, G, o, f, mat, out, i, x;

  a := OSS.ApplyPermWholeDimension([m, n, 1], 1, p);
  b := OSS.ApplyPermWholeDimension([m, n, 1], 2, q);
  G := Group(a * b);
  o := Orbits(G, [1 .. Product([m, n, 1])]);
  f := function(x)
    local t, u;
    t := (x - 1) mod n + 1;
    u := (x - t) / n + 1;
    return [u, t];
  end;
  o := List(o, x -> List(x, i -> f(i)));
  mat := List([1 .. m], i -> EmptyPlist(n));
  for i in [1 .. Length(o)] do
    for x in o[i] do
      mat[x[1]][x[2]] := i;
    od;
  od;
    
  out :=[];
  cart := Cartesian(List([1 .. Length(o)], i -> [0,1])); 
  for x in cart do
    Add(out, List(mat, row -> List(row, y -> x[y])));
  od;

  return out;
end;

DuplicateFreeMats := function(mats)
  return Filtered(mats, m -> IsDuplicateFreeList(m) and
                             IsDuplicateFreeList(TransposedMat(m)));
end;

FixedAndDupeFree := function(m, n, p, q)
  local a, b, G, o, f, mat, out, i, x, M;

  a := OSS.ApplyPermWholeDimension([m, n, 1], 1, p);
  b := OSS.ApplyPermWholeDimension([m, n, 1], 2, q);
  G := Group(a * b);
  o := Orbits(G, [1 .. Product([m, n, 1])]);
  f := function(x)
    local t, u;
    t := (x - 1) mod n + 1;
    u := (x - t) / n + 1;
    return [u, t];
  end;
  o := List(o, x -> List(x, i -> f(i)));
  mat := List([1 .. m], i -> EmptyPlist(n));
  for i in [1 .. Length(o)] do
    for x in o[i] do
      mat[x[1]][x[2]] := i;
    od;
  od;
    
  out :=[];
  cart := Cartesian(List([1 .. Length(o)], i -> [0,1])); 
  for x in cart do
    M := List(mat, row -> List(row, y -> x[y]));
    if IsDuplicateFreeList(M) and IsDuplicateFreeList(TransposedMat(M)) then
      Add(out, M);
    fi;
  od;
  
  if Length(out) > 0 then
    Print("Checked ", 2 ^ Length(o), " matrices and found ", Length(out), 
    " fixed by [", p, ", ", q, "]\n");
  fi;
  #Print("Checked ", 2 ^ Length(o), " matrices and found ", Length(out), 
  #" with no duplicates.\n");
  return out;
end;

FixedAndDupeFreeUpToPerm := function(m, n)
  local G, act, dupefree;
  G   := DirectProduct(SymmetricGroup(m), SymmetricGroup(n));
  act := function(x, g)
    local out;
    out := Permuted(x, Image(Projection(G, 1), g));
    out := TransposedMatMutable(out);
    out := Permuted(out, Image(Projection(G, 2), g));
    return TransposedMatMutable(out);
  end;
  dupefree := DuplicateFreeMats(Cartesian(List([1 .. m], i -> Cartesian(List([1 ..
              n], j -> [0, 1])))));
  return List(Orbits(G, dupefree, act), Representative); 
end;

CountByCompsAndLabels := function(m, n, comps, labels)
  local comp_to_perm, comp_to_comp, labels_to_labels, p, q, pp, qq, comps_p,
  comps_q, labels_p, labels_q, mats, g;

  comp_to_perm := function(comps)
    local p, x, c, i, j;
      p := [];
      for x in [1 .. Length(comps)] do
        for c in comps[x] do
          for i in [1 .. c] do
            Append(p, Concatenation([Length(p) + 2 .. Length(p) + x], [Length(p) +
            1]));
          od;
        od;
      od;
      return PermList(p);
    end;

    comp_to_comp := function(comps)
      local out, seen, x, c;
      out  := [];
      seen := 0;
      for x in [1 .. Length(comps)] do
        for c in comps[x] do
          Add(out, [1 .. c] + seen);
          seen := seen + c;
        od;
      od;
      return out;
    end;

    labels_to_labels := function(labels)
      return Concatenation(labels);
    end;
    p        := comp_to_perm(comps{[1 .. m]});
    q        := comp_to_perm(comps{[m + 1 .. m + n]});
    pp       := Orbits(Group(p), [1 .. m]);
    qq       := Orbits(Group(q), [1 .. n]);
    comps_p  := comp_to_comp(comps{[1 .. n]});
    comps_q  := comp_to_comp(comps{[m + 1 .. m + n]});
    labels_p := Concatenation(labels{[1 .. m]});
    labels_q := Concatenation(labels{[m + 1 .. m + n]});


    mats := MatsFixedBy(m, n, p, q);
    
    # FILTER BY ROW & COLUMN EQUALITIES
    mats := Filtered(mats, mat -> ForAll(comps_p, comp -> ForAll(comp, i ->
    ForAny(pp[i], j -> mat[j] = mat[pp[comp[1]][1]]))));
    mats := Filtered(mats, mat -> ForAll(comps_q, comp -> ForAll(comp, i ->
    ForAny(qq[i], j -> ForAll([1 .. m], k -> mat[k][j] = mat[k][qq[comp[1]][1]])))));
  
    # FILTER BY ROW AND COLUMN PERIODS
    mats := Filtered(mats, mat -> ForAll([1 .. Length(labels_p)], i -> ForAll([1
            .. n], j -> mat[pp[comps_p[i][1]][1]][j] =
            mat[pp[comps_p[i][1]][1] ^ (p ^ labels_p[i])][j])));
  
    mats := Filtered(mats, mat -> ForAll([1 .. Length(labels_q)], i -> ForAll([1
            .. m], j -> mat[j][qq[comps_q[i][1]][1]] =
            mat[j][qq[comps_q[i][1]][1] ^ (q ^ labels_q[i])])));

  return Length(mats);
end;

# pp and qq are p and q written as lists of lists (replace '(' and ')' in
# cycles with '[' and ']' and surround by '[ ]', comps denotes which lists in pp
# and qq are such that the two lists contain indices of equal rows or columns.
MatsFixedByPermsAndRCPartitioned := function(m, n, p, q, comps_p, comps_q,
labels_p, labels_q)
  local mats, pp, qq;
  mats := MatsFixedBy(m, n, p, q);
  pp   := Orbits(Group(p), [1 .. m]);
  qq   := Orbits(Group(q), [1 .. n]);
  mats := Filtered(mats, mat -> ForAll(comps_p, comp -> ForAll(comp, i ->
  ForAny(pp[i], j -> mat[j] = mat[pp[comp[1]][1]]))));
  mats := Filtered(mats, mat -> ForAll(comps_q, comp -> ForAll(comp, i ->
  ForAny(qq[i], j -> ForAll([1 .. m], k -> mat[k][j] = mat[k][qq[comp[1]][1]])))));
  return Length(mats);
end;

# Replacement for _Omega, in a sesnse, since the theory is wrong behind _Omega.
# Delta is assummed to be a 4 dimensional array with delta[x][y][i][j] referring
# to the divisor of the intersection of the i'th row block of size x and the
# j'th column block of size y.
__Omega := function(m, n, delta, comps)
  local prod, count, x, i, y, j;
  prod  := Product(Flat(delta), omega);
  count := 1;
  for x in [1 .. m] do
    for i in [1 .. Length(comps[x])] do
      prod  := prod * Lcm(delta[count]) ^ (comps[x][i] - 1);
      count := count + 1;
    od;
  od;
  count := 1;
  for y in [1 .. n] do
    for j in [1 .. Length(comps[y + m])] do
      prod := prod * Lcm(List([1 .. Length(delta)], i -> delta[i][count])) ^
              (comps[y + m][j] - 1);
      count := count + 1;
    od;
  od;
  return prod;
end;

__OmegaSum := function(m, n, comps, labels)
  local d1, d2, iter, sum, delta;
  d1   := Concatenation(labels{[1 .. m]});
  d2   := Concatenation(labels{[m + 1 .. m + n]});
  iter := IteratorOfCartesianProduct(List([1 .. Length(d1)], i ->
          Cartesian(List([1 .. Length(d2)], j -> DivisorsInt(Gcd(d1[i],
          d2[j]))))));

  sum := 0;
  while not IsDoneIterator(iter) do
    delta := NextIterator(iter);
    sum   := sum + __Omega(m, n, delta, comps);
  od;
  return sum;
end;
