OSS.SimpleFlattenRow := function(row, nr_cols, size_grp)
  return Sum([1 .. nr_cols], i -> (size_grp) ^ (i - 1) * (row[i] - 1)) + 1;
end;

OSS.SimpleUnflattenRow := function(value, nr_cols, size_grp)
  local ret, i;

  ret   := [];
  value := value - 1;
  for i in [1 .. nr_cols - 1] do
    ret[i] := value mod (size_grp) + 1;
    value  := value - (ret[i] - 1);
    value  := value / (size_grp);
  od;
  ret[nr_cols] := value mod (size_grp) + 1;
  return ret;
end;

OSS.SimpleGroupLeftMultActRep := function(G)
  local act;
  act := function(x, g)
    return Position(Elements(G), OnLeftInverse(Elements(G)[x], g));
  end;
  return Image(ActionHomomorphism(G, [1 .. Size(G)], act));
end;

OSS.SimpleGroupRightMultActRep := function(G)
  local act;
  act := function(x, g)
    return Position(Elements(G), OnRight(Elements(G)[x], g));
  end;
  return Image(ActionHomomorphism(G, [1 .. Size(G)], act));
end;

OSS.SimpleRowMultActRep := function(nr_cols, G)
  local H, out_gens, map, point, h, i;

  if Size(G) = 1 then
    return Group(());
  fi;

  H        := OSS.SimpleGroupLeftMultActRep(G);
  out_gens := [];
  for h in Generators(H) do
    map := [];
    for i in [1 .. Size(G) ^ nr_cols] do
      point  := OSS.SimpleUnflattenRow(i, nr_cols, Size(G));
      point  := OnTuples(point, h);
      map[i] := OSS.SimpleFlattenRow(point, nr_cols, Size(G));
    od;
    Add(out_gens, ShallowCopy(map));
  od;

  if IsEmpty(out_gens) then
    return Group(());
  fi;

  return Group(List(out_gens, PermList));
end;

OSS.SimpleSymmetricGroupActRep := function(nr_rows, nr_cols, G, row_group)
  local points, out_gens, map, point, g, i;

  points   := List(Orbits(row_group, [1 .. Size(G) ^ nr_cols]),
                   Representative);
  out_gens := [];
  for g in Generators(SymmetricGroup(nr_cols)) do
    map := [1 .. Maximum(points)];
    for i in points do
      point  := OSS.SimpleUnflattenRow(i, nr_cols, Size(G));
      point  := Permuted(point, g);
      map[i] := CanonicalImage(row_group,
                          OSS.SimpleFlattenRow(point, nr_cols, Size(G)));
    od;
    Add(out_gens, ShallowCopy(map));
  od;

  if IsEmpty(out_gens) then
    return Group(());
  fi;

  return Group(List(out_gens, PermList));
end;

OSS.SimplePowerGroupActRep := function(nr_rows, nr_cols, G, row_group)
  local points, out_gens, H, map, point, g, col, i;

  if Size(G) = 1 then
    return Group(());
  fi;

  points   := List(Orbits(row_group, [1 .. Size(G) ^ nr_cols]),
                   Representative);
  out_gens := [];
  H        := OSS.SimpleGroupRightMultActRep(G);
  # TODO: can we do this with just nr_cols - 1 factors since doing things up to
  # row classes is equivalant to removing a factor? (every row class has |G|
  # many elements, which are essentially removed from the |G|^nr_cols many
  # elements of G^nr_cols).
  for g in Generators(H) do
    for col in [1 .. nr_cols] do
      map := [1 .. Maximum(points)];
      for i in points do
        point      := OSS.SimpleUnflattenRow(i, nr_cols, Size(G));
        point[col] := point[col] ^ g;
        map[i]     := CanonicalImage(row_group,
                                     OSS.SimpleFlattenRow(point, nr_cols, Size(G)));
      od;
      Add(out_gens, ShallowCopy(map));
    od;
  od;
  if IsEmpty(out_gens) then
    return Group(());
  fi;
  return Group(List(out_gens, PermList));
end;

OSS.SimpleAutomorphismGroupActRep := function(nr_rows, nr_cols, G, row_group)
  local points, out_gens, A, AA, map, point, g, i;

  if Size(G) = 1 then
    return Group(());
  fi;

  points   := List(Orbits(row_group, [1 .. Size(G) ^ nr_cols]),
                   Representative);
  out_gens := [];

  A  := AutomorphismGroup(G);
  if Size(A) = 1 then
    AA := [()];
  else
    AA := Generators(A);
    AA := List(AA, a -> PermList(List(Elements(G),
                                      g -> Position(Elements(G), g ^ a))));
  fi;
  A  := Group(AA);

  for g in Generators(A) do
    map := [1 .. Maximum(points)];
    for i in points do
      point  := OSS.SimpleUnflattenRow(i, nr_cols, Size(G));
      point  := OnTuples(point, g);
      map[i] := CanonicalImage(row_group,
                               OSS.SimpleFlattenRow(point, nr_cols, Size(G)));
    od;
    Add(out_gens, ShallowCopy(map));
  od;
  if IsEmpty(out_gens) then
    return Group(());
  fi;

  return Group(List(out_gens, PermList));
end;

OSS.SimpleFullRowActRep := function(nr_rows, nr_cols, G)
  local row_group, sym_group, pow_group, aut_group;
  row_group := OSS.SimpleRowMultActRep(nr_cols, G);
  sym_group := OSS.SimpleSymmetricGroupActRep(nr_rows, nr_cols, G, row_group);
  pow_group := OSS.SimplePowerGroupActRep(nr_rows, nr_cols, G, row_group);
  aut_group := OSS.SimpleAutomorphismGroupActRep(nr_rows, nr_cols, G, row_group);
  return Group(Union(List([sym_group, pow_group, aut_group], Generators)));
end;

OSS.NrSimpleSemigroupsStorage := [];

OSS.SimpleCountMatrixRowSets := function(nr_rows, nr_cols, G)
  local row_group, grp, pnts, indices, appearing, val, coeff, i;
  row_group := OSS.SimpleRowMultActRep(nr_cols, G);
  grp       := OSS.SimpleFullRowActRep(nr_rows, nr_cols, G);
  pnts      := List(Orbits(row_group, [1 .. Size(G) ^ nr_cols]),
                    Representative);

  indices   := CycleIndex(grp, pnts);
  appearing := ExtRepPolynomialRatFun(indices);
  appearing := Union(appearing{[1, 3 .. Length(appearing) - 1]});

  val := Value(indices,
               List(appearing, i -> Indeterminate(Rationals, i)),
               List(appearing, i -> Sum([0 .. nr_rows], j ->
                                      Indeterminate(Rationals, 1) ^ (i * j))));

  coeff := CoefficientsOfLaurentPolynomial(val)[1]{[2 .. nr_rows + 1]};
  return coeff[nr_rows];
end;

InstallMethod(NrSimpleSemigroups,
"for a list", [IsList],
function(list)
  local out;
  if Length(list) <> 3 then
    ErrorNoReturn("OtherSmallSemi: NrSimpleSemigroups: there should be three ",
                  "arguments,");
  elif not IsInt(list[1]) and list[1] > 0 then
    ErrorNoReturn("OtherSmallSemi: NrSimpleSemigroups: the first arugment ",
                  "should be a positive integer,");
  elif not IsInt(list[2]) and list[2] > 0 then
    ErrorNoReturn("OtherSmallSemi: NrSimpleSemigroups: the second arugment ",
                  "should be a positive integer,");
  elif not IsGroup(list[3]) then
    ErrorNoReturn("OtherSmallSemi: NrSimpleSemigroups: the third arugment ",
                  "should be a group,");
  elif list[1] < list[2] then
    return NrSimpleSemigroups([list[2], list[1], list[3]]);
  elif list[1] = 1 or list[2] = 1 then
    return 1;
  fi;

  if not IsBound(OSS.NrSimpleSemigroupsStorage[list[1]]) then
    OSS.NrSimpleSemigroupsStorage[list[1]] := [];
  fi;
  if not IsBound(OSS.NrSimpleSemigroupsStorage[list[1]][list[2]]) then
    OSS.NrSimpleSemigroupsStorage[list[1]][list[2]] := [];
  fi;
  if not IsBound(OSS.NrSimpleSemigroupsStorage[list[1]][list[2]]
      [IdSmallGroup(list[3])[1]]) then
    OSS.NrSimpleSemigroupsStorage[list[1]][list[2]]
      [IdSmallGroup(list[3])[1]] := [];
  fi;
  if IsBound(OSS.NrSimpleSemigroupsStorage[list[1]][list[2]]
      [IdSmallGroup(list[3])[1]][IdSmallGroup(list[3])[2]]) then
    return OSS.NrSimpleSemigroupsStorage[list[1]][list[2]]
      [IdSmallGroup(list[3])[1]][IdSmallGroup(list[3])[2]];
  fi;

  out := OSS.SimpleCountMatrixRowSets(list[1], list[2], list[3]);
  OSS.NrSimpleSemigroupsStorage[list[1]][list[2]][IdSmallGroup(list[3])[1]]
    [IdSmallGroup(list[3])[2]] := out;
  return out;
end);

InstallMethod(NrSimpleSemigroups,
"for an int", [IsInt],
function(n)
  local parameters, out, p, G;
  if n = 1 then
    return 1;
  elif n < 1 then
    ErrorNoReturn("OtherSmallSemi: NrZeroSimpleSemigroups: the argument ",
                  "should be a positive integer,");
  fi;
  parameters := OSS.RZMSParametersByOrder(n + 1, false);
  out        := 0;
  for p in parameters do
    for G in AllSmallGroups(p[3]) do
      out := out + NrSimpleSemigroups([p[1], p[2], G]);
    od;
  od;
  return out;
end);
