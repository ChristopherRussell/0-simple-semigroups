###############################################################################
###############################################################################
## Enumerating matrices over 0-groups up to row and column permutations
###############################################################################
###############################################################################
# This code requires the images package and the ferret package.
#
###############################################################################
# Functions here rely on some functinos defined in 0simple.gi
###############################################################################
# Go between 1D and 3D repesentations of matrices over groups
###############################################################################
OSS.SetToGroupMatrix := function(set, nr_rows, nr_cols, G)
  local els, mat, dim, point, x;
  els := Elements(G);
  mat := List([1 .. nr_rows], a -> EmptyPlist(nr_cols));
  dim := [nr_rows, nr_cols, Size(G)];
  for x in set do
    point                   := OSS.Unflatten3DPoint(dim, x);
    mat[point[1]][point[2]] := els[point[3]];
  od;
  return mat;
end;

###############################################################################
# This function uses ApplyPermWholeDimension and ApplyPermSingleAssignDimension
# to construct the group which has orbits corresponding to distinct isomorphism
# classes of RMS.
OSS.RMSMatrixIsomorphismGroup := function(nr_rows, nr_cols, G, anti_iso)
  local dim, S, rows, cols, gens, elms, rmlt, grswaps, lmlt, gcswaps, auto;

  dim := [nr_rows, nr_cols, Size(G)];
  # Row Swaps
  S    := SymmetricGroup(nr_rows);
  rows := List(GeneratorsOfGroup(S),
               x -> OSS.ApplyPermWholeDimension(dim, 1, x));

  # Col swaps
  S    := SymmetricGroup(nr_cols);
  cols := List(GeneratorsOfGroup(S),
               x -> OSS.ApplyPermWholeDimension(dim, 2, x));

  gens := GeneratorsOfGroup(G);
  elms := ShallowCopy(Elements(G));

  # Apply g to each row (right multiplication):
  rmlt    := List(gens, g -> PermList(List(elms, e -> Position(elms, e * g))));
  grswaps := List([1 .. dim[1]], r -> List(rmlt, g ->
                  OSS.ApplyPermSingleAssignDimension(dim, 3, g, 1, r)));

  # Apply g to each col (left multiplication by inverse):
  lmlt := List(gens,
               g -> PermList(List(elms, e -> Position(elms, g ^ -1 * e))));
  gcswaps := List([1 .. dim[2]], r -> List(lmlt, g ->
  OSS.ApplyPermSingleAssignDimension(dim, 3, g, 2, r)));

  # Automorphisms of G
  S    := AutomorphismGroup(G);
  auto := List(GeneratorsOfGroup(S), x -> List(Elements(G), a ->
          Position(Elements(G), a ^ x)));
  Apply(auto, PermList);
  auto := List(auto, x -> OSS.ApplyPermWholeDimension(dim, 3, x));

  # Add transposition perm if searching up to anti-isomorphism in square case
  if anti_iso and nr_rows = nr_cols then
    Append(auto, OSS.TranspositionPerm(dim));
  fi;

  # The RMS matrix isomorphism group
  return Group(Flat([rows, cols, grswaps, gcswaps, auto]));
end;

###############################################################################
# This function finds the possible dimensions of matrices which define
# RMS of order k. If anti_iso = true then we search up to anti-isomorphism.
###############################################################################
OSS.RMSParametersByOrder := function(k, anti_iso)
  return OSS.RMSParametersByOrder(k + 1, anti_iso);
end;

###############################################################################
# Methods for enumerating matrices over groups
###############################################################################
OSS.RMSMatricesByParameters := function(nr_rows, nr_cols, G, anti_iso)
  local pos, out, i, R, dim, space, pos_one, j;

  if nr_cols = 1 then
    pos := Position(Elements(G), One(G));
    return [List([1 .. nr_rows], i -> pos + (i - 1) * Size(G))];
  fi;

  # The m x n case is deduced from the n x m case.
  if nr_rows < nr_cols then
    out := OSS.RMSMatricesByParameters(nr_cols, nr_rows, G, anti_iso);
    Apply(out, a -> OSS.Unflatten3DPoint([nr_rows, nr_cols, Size(G)], a));
    for i in out do
      i := [i[2], i[1], i[3]];
    od;
    Apply(out, a -> OSS.Flatten3DPoint([nr_rows, nr_cols, Size(G)], a));
    return out;
  fi;

  R := rec();

  R!.IG       := OSS.RMSMatrixIsomorphismGroup(nr_rows, nr_cols, G, anti_iso);
  dim         := [nr_rows, nr_cols, Size(G)];
  space       := [];
  pos_one     := Position(G, One(G));
  for i in [1 .. dim[1]] do
    for j in [1 .. dim[2]] do
      if i = 1 or j = 1 then
        Add(space, [OSS.Flatten3DPoint(dim, [i, j, pos_one])]);
      else
        Add(space, List([1 .. Size(G)],
                        g -> OSS.Flatten3DPoint(dim, [i, j, g])));
      fi;
    od;
  od;

  R!.cart    := IteratorOfCartesianProduct(space);
  R!.current := CanonicalImage(R!.IG, NextIterator(R!.cart), OnSets);
  R!.found   := [];
  R!.done    := false;

  # TODO: this still returns something (the last value) even once IsDoneIterator
  # is true. Is this bad?
  R.NextIterator := function(iter)
    local next;
    next := R!.current;
    AddSet(R!.found, next);
    while not IsDoneIterator(R!.cart) and R!.current in R!.found do
      R!.current := CanonicalImage(R!.IG, NextIterator(R!.cart), OnSets);
    od;
    return next;
  end;

  R.IsDoneIterator := function(iter)
    return IsDoneIterator(R!.cart) and R!.current in R!.found;
  end;

  R.ShallowCopy   := function(iter)

    return rec(IG      := iter!.IG,
               cart    := iter!.cart,
               current := iter!.current,
               done    := iter!.done,
               found   := iter!.found);
  end;

  return IteratorByFunctions(R);
end;

###############################################################################
# Just for interest (have better method elsewhere) returns just the rees matrix
# semigroups. They correspond to the RMS which have no zeros in the defining
# matrix and are obtained by removing the zero element from these.
OSS.RMSMatrices := function(nr_rows, nr_cols, group, anti_iso)
  return List(OSS.RMSMatricesByParameters(nr_rows, nr_cols, group, anti_iso),
              mat -> OSS.SetToZeroGroupMatrix(mat, nr_rows, nr_cols, group));
end;

OSS.RMS := function(nr_rows, nr_cols, group, anti_iso)
  return List(OSS.RMSMatrices(nr_rows, nr_cols, group, anti_iso),
              mat -> ReesZeroMatrixSemigroup(group, mat));
end;

OSS.RMSByOrder := function(order, anti_iso)
  local out, parameters, groups, p, group;
  out        := [];
  parameters := OSS.RMSParameters(order, anti_iso);
  for p in parameters do
    groups := List(AllSmallGroups(p[3]), G -> Image(IsomorphismPermGroup(G)));
    for group in groups do
      Append(out, OSS.RMS(p[1], p[2], group, anti_iso);
    od;
  od;
  return out;
end;

###############################################################################
# User Methods
###############################################################################
AllSimpleSemigroups := function(nr_rows, nr_cols, group, anti_iso)

end;

AllSimpleSemigroups := function(order)

end;

IteratorOfSimpleSemigroups := function(nr_rows, nr_cols, group, anti_iso)

end;

IteratorOfSimpleSemigroups := function(order)

end;
