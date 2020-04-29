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

# TODO: Remove inner automorphisms from this, when possible, for efficiency.
#       i.e. 'quotient' the part of the kernel of the action.
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
# Started coding this part on 15/04/20
###############################################################################

OSS.NrZeroSimpleSemigroupsNoOuterAut := function(m, n, G)
  if m = 1 or n = 1 then
    return 1;
  elif m > n then
    return OSS.NrZeroSimpleSemigroupsNoOuterAut(n, m, G);
  fi;

  return OSS.NrMatrixRowSetsNoOuterAut(m, n, G) -
    OSS.NrMatrixRowSetsNoOuterAut(m - 1, n, G) -
    OSS.NrMatrixRowSetsNoOuterAut(m, n - 1, G) +
    OSS.NrMatrixRowSetsNoOuterAut(m - 1, n - 1, G);
end;

OSS.NrMatrixRowSetsNoOuterAut := function(m, n, G)
  local out;
  if m < n then
    return OSS.NrMatrixRowSetsNoOuterAut(n, m, G);
  elif m = 1 or n = 1 then
    return Maximum(m, n) + 1;
  fi;
  out := OSS.CountMatrixRowSetsNoOuterAut(m, n, G);
  return out;
end;

OSS.CountMatrixRowSetsNoOuterAut := function(nr_rows, nr_cols, G)
  local indices, appearing, val, coeff, i;
  indices   := OSS.CycleIndexNoOuterAut(G, nr_cols);
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

OSS.CycleIndexNoOuterAut := function(G, n)
  local G_classes, G_reps, G_cc_sizes, CG_sizes, S, S_classes, S_reps, max_ord,
  powers, roots, reps, sizes, fixes, x, lens, common_factor, iter, g, perm, ci,
  nr_i_cycles, xx, gg, ci_rep, exp, l, d, xxx, pos, divs, i, j, k, list;

  G_classes  := ConjugacyClasses(G);
  G_reps     := List(G_classes, Representative);
  G_cc_sizes := List(G_classes, Size);

  # Sizes of the centralizers of elements of the resepctive conjugacy classes,
  # which are equal to the size of G divided by the size of the conj class.
  CG_sizes  := List(G_cc_sizes, i -> Size(G) / i);

  S         := SymmetricGroup(n);
  S_classes := ConjugacyClasses(S);
  S_reps    := List(S_classes, Representative);

  # max order of element of S_n
  max_ord   := Maximum(List(S_reps, Order));

  # powers[i][j] is such that G_reps[i]^j is an element of the conjugacy class
  # G_classes[powers[i][j]].
  powers    := NthPowers(G, G_reps, G_classes);

  # roots[i][j] is a list L of ints such that k is in L if G_reps[k]^j is an
  # element of the conjugacy class G_classes[i].
  roots     := NthRoots(powers, max_ord);

  # For G wr S_n, we will find the conjugacy class reps, the class sizes, and
  # the number of elements fixed by an element in each class. With this
  # informations we can later determine the cycle indices of these elements and
  # finally apply polya enumeration to count orbits.
  reps  := [];
  sizes := [];
  fixes := [];
  for i in [1 .. Size(S_classes)] do
    x    := S_reps[i];
    lens := Collected(CycleLengths(x, [1 .. n]));

    # When determining the size of the CC class of (x, g) the following
    # is a common factor so we only want to calculate it once, now.
    common_factor := Size(ConjugacyClass(SymmetricGroup(n), x))
                     * Product(lens, l -> Size(G) ^ ((l[1] - 1) * l[2]));

    iter := IteratorOfCartesianProduct(List(lens, j -> UnorderedTuples([1 ..
            Size(G_cc_sizes)], j[2])));
    while not IsDoneIterator(iter) do
      g := NextIterator(iter);
      Add(reps, [x, g]);
      Add(sizes, common_factor
                 * Product(g, NrPermutationsList)
                 * Product(g, j -> Product(j, k -> G_cc_sizes[k])));
      Add(fixes, FixSizeOfCCRep(G, x, g, n, roots, G_cc_sizes, CG_sizes, lens));
    od;
  od;
  perm  := Sortex(reps);
  sizes := Permuted(sizes, perm);  # Sorts sizes in paralell with reps
  fixes := Permuted(fixes, perm);  # Sorts fixes in paralell with reps

  ci := 0;
  for i in [1 .. Length(reps)] do
    nr_i_cycles := [fixes[i]];
    x           := reps[i][1];
    lens        := Collected(CycleLengths(x, [2 .. n]));
    g           := reps[i][2];
    xx          := x;
    gg          := reps[i][2];
    ci_rep      := Indeterminate(Rationals, 1) ^ fixes[i];
    exp         := 2;
    while xx <> () or ForAny(gg, j -> ForAny(j, k -> k <> 1)) do
      # find xx, gg such that (xx, gg) is in the conjugacy class of the
      # the expo'th power of (x, g)
      xx     := xx * x;
      gg     := [];
      for j in [1 .. Length(g)] do
        l := lens[j][1];
        d := Gcd(l, exp);
        if not IsBound(gg[l / d]) then
          gg[l / d] := [];
        fi;
        for k in [1 .. Length(g[j])] do
          Append(gg[l / d],
          ListWithIdenticalEntries(d, nthpower(powers[g[j][k]], exp / d)));
        od;
      od;
      gg := Compacted(gg);
      for list in gg do
        Sort(list);
      od;
      # conjugate to change to form of gg so that (xx, gg) is of equal to one of
      # our conjugacy class reps, since we only know reps and don't have another
      # way of checking membership of a conjugacy class of G wr S_n.
      xxx := S_reps[Position(S_classes, ConjugacyClass(S, xx))];
      pos := Position(reps, [xxx, gg]);
      # Fix this line, use lemma from thesis... nr_i_cycles = fix(x^i) - \sum_{d
      # dividing i} nr_d_cycles * d
      divs := DivisorsInt(exp);
      divs := divs{[1 .. Length(divs) - 1]};  # Remove i from divs
      nr_i_cycles[exp]
             := (fixes[pos] - Sum(divs, d -> d * nr_i_cycles[d])) / exp;
      ci_rep := ci_rep * Indeterminate(Rationals, exp) ^ (nr_i_cycles[exp]);
      exp    := exp + 1;
    od;
    ci := ci + sizes[i] * ci_rep;
  od;
  return ci / (Size(G) ^ n * Factorial(n));
end;

# g is a list of ints so that g[i] gives the index of the cc class which the
# element (x, g) has in the i'th spot of the g factor.
FixSizeOfCCRep := function(G, x, g, n, roots, G_cc_sizes, centralizer_sizes,
                           cycle_lens)
  local sum, prod, i, j, k;
  sum    := 0;
  for i in [1 .. Length(roots)] do  # length of roots is nr cc classes of G
    prod := 1;
    for j in [1 .. Length(cycle_lens)] do  # for each different length of cycle
      for k in [1 .. cycle_lens[j][2]] do  # for each cycle of that length
        # if an element of the i'th cc class of G has any j'th roots
        if IsBound(roots[g[j][k]][cycle_lens[j][1]]) then
          if i in roots[g[j][k]][cycle_lens[j][1]] then
            prod := prod * (centralizer_sizes[g[j][k]] + 1);
          fi;
        fi;
      od;
    od;
    prod := prod * G_cc_sizes[i];  # multiply by size of i'th cc class
    sum  := sum + prod;
  od;
  return sum / Size(G);
end;

# Return a list of lists. If g_1, g_2, ... are the CC reps of G then
# the i'th list is the sequence i, i_1, i_2, ... such that i_j is in the
# conjugacy class of g_{i_j}. cc_reps and cc_classes should be such that the
# i'th entry of cc_reps is from the i'th entry of cc_classes.
NthPowers := function(G, cc_reps, cc_classes)
  local out, g, pos, divs, i, j;
  out := List([1 .. Length(cc_reps)], i -> [i]);
  for i in [1 .. Length(cc_reps)] do
    if out[i] = [i] then
      g := cc_reps[i];
      while g <> () do
        g   := g * cc_reps[i];
        pos := Position(cc_classes, ConjugacyClass(G, g));
        Add(out[i], pos);
      od;

      divs := DivisorsInt(Length(out[i]));
      for j in divs{[2 .. Length(divs) - 1]} do
        if out[j] = [j] then
          out[j] := List([1 .. Length(out[i]) / j], k -> out[i][j * k]);
        fi;
      od;
    fi;
  od;
  return out;
end;

nthpower := function(powers, n)
  return powers[(n - 1) mod Length(powers) + 1];
end;

NthRoots := function(powers, max)
  local roots, i, j;
  roots := List([1 .. Length(powers)], i -> []);
  for i in [1 .. Length(powers)] do
    for j in [1 .. max] do
      if IsBound(roots[nthpower(powers[i], j)][j]) then
        AddSet(roots[nthpower(powers[i], j)][j], i);
      else
        roots[nthpower(powers[i], j)][j] := [i];
      fi;
    od;
  od;
  return roots;
end;

# NthPowers for each CC of G and each power up to the degree of S_n we want to
# know which conjugacy class the n'th power goes to. We also need to know the
# size of the centralizer of each CC class. We should work the out only once per
# CC.
