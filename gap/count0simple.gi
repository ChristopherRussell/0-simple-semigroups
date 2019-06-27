# TODO: check that multiplication actions are correct (row on left inverse and
# column on right). Factor out inner automorphisms from automorphism group
# action.
# TODO: Elements -> Enumerator

OSS.FlattenRow := function(row, nr_cols, size_grp)
  return Sum([1 .. nr_cols], i -> (size_grp + 1) ^ (i - 1) * (row[i] - 1)) + 1;
end;

OSS.UnflattenRow := function(value, nr_cols, size_grp)
  local ret, i;
  ret   := [];
  value := value - 1;
  for i in [1 .. nr_cols - 1] do
    ret[i] := value mod (size_grp + 1) + 1;
    value  := value - (ret[i] - 1);
    value  := value / (size_grp + 1);
  od;
  ret[nr_cols] := value mod (size_grp + 1) + 1;
  return ret;
end;

OSS.GroupLeftMultActRep := function(G)
  local act;
  act := function(x, g)
    if x = 1 then
      return 1;
    else
      return Position(Elements(G), OnLeftInverse(Elements(G)[x - 1], g)) + 1;
    fi;
  end;
  return Image(ActionHomomorphism(G, [1 .. Size(G) + 1], act));
end;

OSS.GroupRightMultActRep := function(G)
  local act;
  act := function(x, g)
    if x = 1 then
      return 1;
    else
      return Position(Elements(G), OnRight(Elements(G)[x - 1], g)) + 1;
    fi;
  end;
  return Image(ActionHomomorphism(G, [1 .. Size(G) + 1], act));
end;

OSS.RowMultActRep := function(nr_cols, G)
  local H, out_gens, map, point, h, i;

  if Size(G) = 1 then
    return Group(());
  fi;

  H        := OSS.GroupLeftMultActRep(G);
  out_gens := [];
  for h in Generators(H) do
    map := [];
    for i in [1 .. (Size(G) + 1) ^ nr_cols] do
      point  := OSS.UnflattenRow(i, nr_cols, Size(G));
      point  := OnTuples(point, h);
      map[i] := OSS.FlattenRow(point, nr_cols, Size(G));
    od;
    Add(out_gens, ShallowCopy(map));
  od;

  if IsEmpty(out_gens) then
    return Group(());
  fi;

  return Group(List(out_gens, PermList));
end;

OSS.SymmetricGroupActRep := function(nr_rows, nr_cols, G, row_group)
  local points, out_gens, map, point, g, i;

  points   := List(Orbits(row_group, [2 .. (Size(G) + 1) ^ nr_cols]),
                   Representative);
  out_gens := [];
  for g in Generators(SymmetricGroup(nr_cols)) do
    map := [1 .. Maximum(points)];
    for i in points do
      point  := OSS.UnflattenRow(i, nr_cols, Size(G));
      point  := Permuted(point, g);
      map[i] := CanonicalImage(row_group,
                          OSS.FlattenRow(point, nr_cols, Size(G)));
    od;
    Add(out_gens, ShallowCopy(map));
  od;

  if IsEmpty(out_gens) then
    return Group(());
  fi;

  return Group(List(out_gens, PermList));
end;

OSS.PowerGroupActRep := function(nr_rows, nr_cols, G, row_group)
  local points, out_gens, H, map, point, g, col, i;

  if Size(G) = 1 then
    return Group(());
  fi;

  points   := List(Orbits(row_group, [2 .. (Size(G) + 1) ^ nr_cols]),
                   Representative);
  out_gens := [];
  H        := OSS.GroupRightMultActRep(G);
  # TODO: can we do this with just nr_cols - 1 factors since doing things up to
  # row classes is equivalant to removing a factor? (every row class has |G|
  # many elements, which are essentially removed from the |G|^nr_cols many
  # elements of G^nr_cols).
  # TODO: can quotient one factor of power group by Z(G) the center.
  for g in Generators(H) do
    for col in [1 .. nr_cols] do
      map := [1 .. Maximum(points)];
      for i in points do
        point      := OSS.UnflattenRow(i, nr_cols, Size(G));
        point[col] := point[col] ^ g;
        map[i]     := CanonicalImage(row_group,
                                    OSS.FlattenRow(point, nr_cols, Size(G)));
      od;
      Add(out_gens, ShallowCopy(map));
    od;
  od;
  if IsEmpty(out_gens) then
    return Group(());
  fi;
  return Group(List(out_gens, PermList));
end;

# TODO: Remove inner automorphisms from this
OSS.AutomorphismGroupActRep := function(nr_rows, nr_cols, G, row_group)
  local points, out_gens, A, AA, map, point, g, i;

  if Size(G) = 1 then
    return Group(());
  fi;

  points   := List(Orbits(row_group, [2 .. (Size(G) + 1) ^ nr_cols]),
                   Representative);
  out_gens := [];

  A  := AutomorphismGroup(G);
  if Size(A) = 1 then
    AA := [()];
  else
    AA := Generators(A);
    AA := List(AA, a -> PermList(Concatenation([1], 1 + List(Elements(G),
                                 g -> Position(Elements(G), g ^ a)))));
  fi;
  A  := Group(AA);

  for g in Generators(A) do
    map := [1 .. Maximum(points)];
    for i in points do
      point  := OSS.UnflattenRow(i, nr_cols, Size(G));
      point  := OnTuples(point, g);
      map[i] := CanonicalImage(row_group,
                               OSS.FlattenRow(point, nr_cols, Size(G)));
    od;
    Add(out_gens, ShallowCopy(map));
  od;
  if IsEmpty(out_gens) then
    return Group(());
  fi;

  return Group(List(out_gens, PermList));
end;

OSS.FullRowActRep := function(nr_rows, nr_cols, G)
  local row_group, sym_group, pow_group, aut_group;
  row_group := OSS.RowMultActRep(nr_cols, G);
  sym_group := OSS.SymmetricGroupActRep(nr_rows, nr_cols, G, row_group);
  pow_group := OSS.PowerGroupActRep(nr_rows, nr_cols, G, row_group);
  aut_group := OSS.AutomorphismGroupActRep(nr_rows, nr_cols, G, row_group);
  return Group(Union(List([sym_group, pow_group, aut_group], Generators)));
end;

OSS.CountMatrixRowSets := function(nr_rows, nr_cols, G)
  local row_group, grp, pnts, indices, appearing, val, coeff, i;
  row_group := OSS.RowMultActRep(nr_cols, G);
  grp       := OSS.FullRowActRep(nr_rows, nr_cols, G);
  pnts      := List(Orbits(row_group, [1 .. (Size(G) + 1) ^ nr_cols]),
                    Representative);

  indices   := CycleIndex(grp, pnts);
  appearing := ExtRepPolynomialRatFun(indices);
  appearing := Union(appearing{[1, 3 .. Length(appearing) - 1]});

  val := Value(indices,
               List(appearing, i -> Indeterminate(Rationals, i)),
               List(appearing, i -> Sum([0 .. nr_rows], j ->
                                      Indeterminate(Rationals, 1) ^ (i * j))));

  coeff := CoefficientsOfLaurentPolynomial(val)[1]{[2 .. nr_rows + 1]};
  for i in [1 .. nr_rows - 1] do
    if not Tester(NrMatrixRowSets)([i, nr_cols, G]) then
      Setter(NrMatrixRowSets)([i, nr_cols, G], coeff[i]);
    fi;
  od;
  return coeff[nr_rows];
end;

OSS.PartitionsBySize := function(m)
  local out, func, i;

  out := [];

  func := function(max, list)
    local sum, new, i;
    sum := Sum(list);
    if sum = max then
      Add(out, list);
      return;
    fi;
    for i in [1 .. Minimum(max - sum, Minimum(list))] do
      new := ShallowCopy(list);
      Add(new, i);
      func(max, new);
    od;
  end;

  for i in [1 .. m] do
    func(m, [i]);
  od;

  return out;
end;

OSS.NrBinaryMatricesUpToPerm := function(m, n)
  local index, denom, indet, p, q;
  denom := function(part)
    return Product(Collected(part), x -> x[1] ^ x[2] * Factorial(x[2]));
  end;

  index := 0;
  for p in OSS.PartitionsBySize(m) do
    for q in OSS.PartitionsBySize(n) do
      indet := Product([1 .. m], i -> Product([1 .. n], j -> 2 ^ (Gcd(i, j) *
               Length(Positions(p, i)) * Length(Positions(q, j)))));
      index := index + 1 / (denom(p) * denom(q)) * indet;
    od;
  od;
  return index;
end;

OSS.NrBinaryMatricesUpToPermNoZeroRows := function(m, n)
  local f;
  if m = 1 or n = 1 then
    return 1;
  fi;
  f := OSS.NrBinaryMatricesUpToPerm;
  return f(m, n) - f(m, n - 1) - f(m - 1, n) + f(m - 1, n - 1);
end;

OSS.NrMatrixRowSetsStorage := [];

InstallMethod(NrMatrixRowSets,
"for a list", [IsList],
function(list)
  local out;
  if Length(list) <> 3 then
    ErrorNoReturn("OtherSmallSemi: NrMatrixRowSets: there should be three ",
                  "arguments,");
  elif not IsInt(list[1]) and list[1] > 0 then
    ErrorNoReturn("OtherSmallSemi: NrMatrixRowSets: the first arugment should ",
                  "be a positive integer,");
  elif not IsInt(list[2]) and list[2] > 0 then
    ErrorNoReturn("OtherSmallSemi: NrMatrixRowSets: the second arugment ",
                  "should be a positive integer,");
  elif not IsGroup(list[3]) then
    ErrorNoReturn("OtherSmallSemi: NrMatrixRowSets: the third arugment should ",
                  "be a group,");
  elif list[1] < list[2] then
    return NrMatrixRowSets([list[2], list[1], list[3]]);
  elif list[1] = 1 or list[2] = 1 then
    return Maximum(list[1], list[2]) + 1;
  fi;  # TODO: use better calculations for case where list[3] is trivial

  if not IsBound(OSS.NrMatrixRowSetsStorage[list[1]]) then
    OSS.NrMatrixRowSetsStorage[list[1]] := [];
  fi;
  if not IsBound(OSS.NrMatrixRowSetsStorage[list[1]][list[2]]) then
    OSS.NrMatrixRowSetsStorage[list[1]][list[2]] := [];
  fi;
  if not IsBound(OSS.NrMatrixRowSetsStorage[list[1]][list[2]]
      [IdSmallGroup(list[3])[1]]) then
    OSS.NrMatrixRowSetsStorage[list[1]][list[2]]
      [IdSmallGroup(list[3])[1]] := [];
  fi;
  if IsBound(OSS.NrMatrixRowSetsStorage[list[1]][list[2]]
      [IdSmallGroup(list[3])[1]][IdSmallGroup(list[3])[2]]) then
    return OSS.NrMatrixRowSetsStorage[list[1]][list[2]]
      [IdSmallGroup(list[3])[1]][IdSmallGroup(list[3])[2]];
  fi;

  out := OSS.CountMatrixRowSets(list[1], list[2], list[3]);
  OSS.NrMatrixRowSetsStorage[list[1]][list[2]][IdSmallGroup(list[3])[1]]
    [IdSmallGroup(list[3])[2]] := out;
  return out;
end);

InstallMethod(NrZeroSimpleSemigroups,
"for a list", [IsList],
function(list)
  if Length(list) <> 3 then
    ErrorNoReturn("OtherSmallSemi: NrZeroSimpleSemigroups: there should be ",
                  "three arguments,");
  elif not IsInt(list[1]) and list[1] > 0 then
    ErrorNoReturn("OtherSmallSemi: NrZeroSimpleSemigroups: the first arugment ",
                  "should be a positive integer,");
  elif not IsInt(list[2]) and list[2] > 0 then
    ErrorNoReturn("OtherSmallSemi: NrZeroSimpleSemigroups: the second arugment",
                  " should be a positive integer,");
  elif not IsGroup(list[3]) then
    ErrorNoReturn("OtherSmallSemi: NrZeroSimpleSemigroups: the third arugment ",
                  "should be a group,");
  elif list[1] = 1 or list[2] = 1 then
    return 1;
  elif list[1] > list[2] then
    return NrZeroSimpleSemigroups([list[2], list[1], list[3]]);
  fi;

  return NrMatrixRowSets([list[1], list[2], list[3]]) -
    NrMatrixRowSets([list[1] - 1, list[2], list[3]]) -
    NrMatrixRowSets([list[1], list[2] - 1, list[3]]) +
    NrMatrixRowSets([list[1] - 1, list[2] - 1, list[3]]);
end);

InstallMethod(NrZeroSimpleSemigroups,
"for an int", [IsInt],
function(n)
  local parameters, out, p, G;
  if n = 1 then
    return 0;
  elif n = 2 then
    return 1;
  elif n < 1 then
    ErrorNoReturn("OtherSmallSemi: NrZeroSimpleSemigroups: the argument ",
                  "should be a positive integer,");
  fi;
  parameters := OSS.RZMSParametersByOrder(n, false);
  out        := 0;
  for p in parameters do
    for G in AllSmallGroups(p[3]) do
      out := out + NrZeroSimpleSemigroups([p[1], p[2], G]);
    od;
  od;
  return out;
end);

###############################################################################
# Count 0-simple semigroups over groups with no outer automorphisms
###############################################################################



###############################################################################
# Count 0-simple semigroups over groups with no outer automorphisms (abandoned)
# Approach based on paper of Palmer on enumeration under wreath product but
# which doesn't work due to working with row orbits rather than rows
###############################################################################

MobiusFunction := function(x)
  if x = 1 then
    return 1;
  elif not IsDuplicateFreeList(FactorsInt(x)) then
    return 0;
  fi;
  return (-1) ^ Length(FactorsInt(x));
end;

# The multiplication defined in Section 3 equation (1)
xProd := function(x, y)
  local func, ext1, ext2;

  func := function(x, y)
    return Product([1, 3 .. Length(x) - 1], s -> Product([1, 3 .. Length(y) - 1],
          t -> Indeterminate(Rationals, Lcm(x[s], y[t])) ^
            (Gcd(x[s], y[t]) * x[s + 1] * y[t + 1])));
  end;

  ext1 := ExtRepPolynomialRatFun(x);
  ext2 := ExtRepPolynomialRatFun(y);

  return Sum([1, 3 .. Length(ext1) - 1], i -> Sum([1, 3 .. Length(ext2) - 1],
  j -> ext1[i + 1] * ext2[j + 1] * func(ext1[i], ext2[j])));
end;

# The function defined in Section 3 equation (6)
iv := function(v, r, j)
  local func;

  func := function(k)
    local pos;
    pos := Position(j{[1, 3 .. Length(j) - 1]}, k);
    if pos = fail then
      return 0;
    fi;
    return j[pos + 1];
  end;

  # some easy cases
  if Gcd(r, v) = 1 then
    return func(v);
  elif IsPrimeInt(v) and Gcd(r, v) = v then
    return (func(1) ^ v - func(1)) / v;
  fi;

  return Sum(DivisorsInt(v), w -> MobiusFunction(v / w) * Sum(DivisorsInt(w /
             Gcd(w, r)), k -> k * func(k)) ^ Gcd(w, r)) / v;
end;

# The function defined in Section 3 equation (5)
Ir := function(x, r)
  local ext, out, j, a;
  ext := ExtRepPolynomialRatFun(x);

  out := 0;

  n := Maximum(Union(List(ext{[1, 3 .. Length(ext) - 1]}, t -> t{[1, 3 ..
       Length(t) - 1]})));

  for a in [1, 3 .. Length(ext) - 1] do
    j   := ext[a];
    out := out + ext[a + 1] * Product([1 .. n ^ r], v ->
           Indeterminate(Rationals, v) ^ iv(v, r, j));
  od;
  return out;
end;

CycleIndexOfWreathProduct := function(G, H)
  local ZG, ZH, ext, num, Irs, out, lis, tmp, i, j;
  ZG := CycleIndex(G);  # This is the group which acts
  ZH := CycleIndex(H);  # This is the group which has multiple factors

  ext := ExtRepPolynomialRatFun(ZG);
  num := Union(List([1, 3 .. Length(ext) - 1], i -> ext[i]{[1, 3 ..
         Length(ext[i]) - 1]}));

  Irs := List(num, r -> Ir(ZH, r));

  out := 0;
  for i in [1, 3 .. Length(ext) - 1] do
    lis := Concatenation(List([1, 3 .. Length(ext[i]) - 1], j ->
           ListWithIdenticalEntries(ext[i][j + 1], ext[i][j])));
    tmp := ext[i + 1] * Irs[lis[1]];
    for j in lis{[2 .. Length(lis)]} do
      tmp := xProd(tmp, Irs[j]);
    od;
    out := out + tmp;
  od;
  return out;
end;
