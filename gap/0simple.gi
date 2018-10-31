###############################################################################
###############################################################################
## Enumerating binary matrices up to row and column permutations
###############################################################################
###############################################################################
# This code requires the images package and the ferret package.
#
###############################################################################
# All functions without user documentation are stored in the following record.
###############################################################################
OSS := rec();
###############################################################################
# Permutations and operations on sets represenating (regular) binary matrices
###############################################################################
# Calculates the perm group which acts on these sets (via OnSets) by
# row permutations and column permutations. This is isomorphism to S_m x S_n. If
# the third argument is true then construct the group which also contains the
# permutation which transposes matrices.
OSS.ActingBinaryMatrixGroup := function(nr_rows, nr_cols, anti_iso)
  local out, temp, a, i;

  if nr_rows = 1 and nr_cols = 1 then
    return Group(PermList([1]));
  fi;

  out := [];
  if nr_rows = nr_cols and anti_iso then  # Add matrix transposition perm
    temp := [];
    for i in [1 .. nr_rows] do
      Append(temp, List([1 .. nr_cols], j -> i + (j - 1) * nr_cols));
    od;
    Add(out, PermList(temp));
  fi;

  # Add generators of Symmetric group acting on rows
  if nr_rows > 1 then  # Add row transposition
    Add(out, PermList(
      Concatenation([nr_cols + 1 .. 2 * nr_cols], [1 .. nr_cols])));
    if nr_rows > 2 then  # Add cyclic row permutation of length nr_rows
      Add(out, PermList(
        Concatenation([(nr_rows - 1) * nr_cols + 1 .. nr_rows * nr_cols],
                      [1 .. (nr_rows - 1) * nr_cols])));
    fi;
  fi;

  # Add generators of Symmetric group acting on columns
  if nr_cols > 1 then  # Add column transposition
    temp := Concatenation([2, 1], [3 .. nr_cols]);
    Add(out, PermList(
      Concatenation(List([1 .. nr_rows], a -> temp + nr_cols * (a - 1)))));
    if nr_cols > 2 then  # Add cyclic column permutation of length nr_cols
      temp := Concatenation([2 .. nr_cols], [1]);
      Add(out, PermList(
        Concatenation(List([1 .. nr_rows], a -> temp + nr_cols * (a - 1)))));
    fi;
  fi;

  return Group(out);
end;

###############################################################################
# This permutation sends (via OnSets) a set representing an m x n matrix to its
# transpose as a set representing a n x m matrix.
OSS.TranspositionPermutation := function(nr_rows, nr_cols)
  return PermList(Concatenation(
           List([1 .. nr_rows], i ->
             List([1 .. nr_cols], j -> (j - 1) * nr_rows) + i)));
end;

# TODO: the following two functions aren't used anywhere
###############################################################################
# This returns the binary matrix represented by the set <set>. Note this
# depends on the dimensions.
OSS.SetToBinaryMat := function(set, nr_rows, nr_cols)
  local func, out, i, row;
  func := function(b)
    if b then
      return 1;
    fi;
    return 0;
  end;
  out := EmptyPlist(nr_rows);
  for i in [1 .. nr_rows] do
    row := List([(i - 1) * nr_cols + 1 .. i * nr_cols], a -> func(a in set));
    Add(out, ShallowCopy(row));
  od;
  return out;
end;

OSS.BinaryMatToSet := function(mat)
  local out, i, j;
  out := [];
  for i in [1 .. Length(mat)] do
    for j in [1 .. Length(mat[1])] do
      if mat[i][j] = 1 then
        AddSet(out, (i - 1) * Length(mat[1]) + j);
      fi;
    od;
  od;
  return out;
end;

###############################################################################
# This returns a transformation which relabels the elements of the set so that
# it represents the upper left corner of a matrix with more rows and/or columns
OSS.EmbedSetTransformation := function(nr_rows, nr_cols, new_rows,
                                                  new_cols)
  local trans;
  trans := Concatenation(List([1 .. nr_rows], i -> List([1 .. nr_cols], j ->
           j + (i - 1) * new_cols)));
  Append(trans, List([1 .. (new_cols - nr_cols) * (nr_rows - 1)], a -> 1));
  return TransformationList(trans);
end;

###############################################################################
# Returns the extensions for a n-1 x n-1 01matrix (as a set) to a n x n matrix.
OSS.SquareExtensions := function(n)
  local last_col, last_row, ext1, ext2, comb1, comb2, c;
  last_col := Set([1 .. n - 1], i -> i * n);
  last_row := Set([1 .. n - 1], i -> n * (n - 1) + i);

  ext1 := Combinations(Union(last_col, last_row));
  for c in ext1 do
    AddSet(c, n ^ 2);
  od;

  comb1 := Combinations(last_col);
  Remove(comb1, 1);
  comb2 := Combinations(last_row);
  Remove(comb2, 1);

  ext2 := Cartesian(comb1, comb2);
  Apply(ext2, Union);

  return Union(ext1, ext2);
end;

# Returns the extensions for a m-1 x n 01matirx (as a set) to a m x n matrix.
OSS.RowExtensions := function(nr_rows, nr_cols)
  local last_row, cmb;
  last_row := Set([1 .. nr_cols], i -> nr_cols * (nr_rows - 1) + i);

  cmb := Combinations(last_row);
  Remove(cmb, 1);  # Remove the empty row.

  return cmb;
end;

###############################################################################
# Finding the binary matrix shapes
###############################################################################
# Solution to two row case.
OSS.BinaryMatrixShapesWithTwoRows := function(nr_cols)
  local row1, row2, out, i, j, opp;
  out  := [];
  row1 := [1 .. nr_cols];
  for j in [1 .. nr_cols] do
    Add(out, Union(row1, [1 .. j] + nr_cols));
  od;

  i := nr_cols - 1;
  while 2 * i >= nr_cols do
    row1 := [1 .. i];
    opp  := [1 .. nr_cols];
    SubtractSet(opp, row1);
    opp := opp + nr_cols;
    for j in [0 .. 2 * i - nr_cols] do
      row2 := Union(opp, [1 .. j] + nr_cols);
      Add(out, Union(row1, row2));
    od;
    i := i - 1;
  od;
  return out;
end;

###############################################################################
# Wrapper for solved cases.
OSS.BinaryMatrixShapesSolvedCases := function(nr_rows, nr_cols)
  if nr_rows = 1 then
    return [[1 .. nr_cols]];
  elif nr_cols = 1 then
    return List([1 .. nr_rows], a -> [a]);
  elif nr_rows = 2 then
    return OSS.BinaryMatrixShapesWithTwoRows(nr_cols);
  fi;
end;

###############################################################################
# IO methods used whilst seraching as well as to save results.
###############################################################################
OSS.BinaryMatrixShapesReadFile := function(nr_rows, nr_cols, anti_iso)
  local dir, name, file, out;
  dir    := PackageInfo("othersmallsemi")[1].InstallationPath;
  name   := Concatenation(dir, "/data/", String(nr_rows),
                          "x", String(nr_cols));
  if anti_iso and nr_rows = nr_cols then
    Append(name, "anti");
  fi;
  file   := IO_File(name, "r");
  if file = fail then
    return fail;
  fi;
  out := IO_ReadLines(file);
  IO_Close(file);
  Apply(out, a -> EvalString(Chomp(a)));
  return out;
end;

OSS.BinaryMatrixShapesWriteFile := function(nr_rows, nr_cols, anti_iso, data)
  local dir, name, file;
  dir    := PackageInfo("othersmallsemi")[1].InstallationPath;
  name   := Concatenation(dir, "/data/", String(nr_rows),
                          "x", String(nr_cols));
  if anti_iso and nr_rows = nr_cols then
    Append(name, "anti");
  fi;
  file   := IO_File(name, "w");
  IO_WriteLines(file, data);
  IO_Close(file);
end;

###############################################################################
# Main method
###############################################################################
# This finds shapes by building up from lower dimension cases.
OSS.BinaryMatrixShapesByDim := function(nr_rows, nr_cols, anti_iso, RW)
  local data, out, trans, embed, G, extensions, temp, d, e;

  # If we have calculated this case before then return those results
  if RW then
    data := OSS.BinaryMatrixShapesReadFile(nr_rows, nr_cols, anti_iso);
    if data <> fail then
      return data;
    fi;
  fi;

  # These are cases which we can describe the solution to explicitly
  if nr_rows <= 2 or nr_cols = 1 then
    return OSS.BinaryMatrixShapesSolvedCases(nr_rows, nr_cols);
  fi;

  # The m x n case is deduced from the n x m case.
  if nr_rows < nr_cols then
    out   := OSS.BinaryMatrixShapesByDim(nr_cols, nr_rows, anti_iso, RW);
    trans := OSS.TranspositionPermutation(nr_rows, nr_cols);
    Apply(out, a -> OnSets(a, trans));

    # In square matrix case, build up from previous square case
  elif nr_rows = nr_cols then
    data  := OSS.BinaryMatrixShapesByDim(nr_rows - 1, nr_cols - 1,
                                         anti_iso, RW);
    embed := OSS.EmbedSetTransformation(nr_rows - 1, nr_cols - 1,
                                        nr_rows, nr_cols);
    Apply(data, d -> OnSets(d, embed));
    G          := OSS.ActingBinaryMatrixGroup(nr_rows, nr_cols, anti_iso);
    out        := [];
    extensions := OSS.SquareExtensions(nr_rows);
    for d in data do
      for e in extensions do
        temp := ShallowCopy(d);
        UniteSet(temp, e);
        AddSet(out, CanonicalImage(G, temp, OnSets));
      od;
    od;

    # If more rows than columns then build from a square matrix by adding rows.
  elif nr_rows > nr_cols then
    data       := OSS.BinaryMatrixShapesByDim(nr_rows - 1, nr_cols,
                                              anti_iso, RW);
    G          := OSS.ActingBinaryMatrixGroup(nr_rows, nr_cols, anti_iso);
    extensions := OSS.RowExtensions(nr_rows, nr_cols);
    Remove(extensions, nr_cols);  # this omits the extension of a full row of 1's
    out := EmptyPlist(Size(extensions) * Size(data));
    for d in data do
      for e in extensions do
        temp := ShallowCopy(d);
        UniteSet(temp, e);
        AddSet(out, CanonicalImage(G, temp, OnSets));
      od;
    od;
    AddSet(out, [1 .. nr_rows * nr_cols]);  # this is the only case we miss with
                                            # by ommitting the full row of 1's
  fi;

  if RW then
    OSS.BinaryMatrixShapesWriteFile(nr_rows, nr_cols, anti_iso, out);
  fi;
  return out;
end;

OSS.IteratorBinaryMatrixShapesByDim := function(nr_rows, nr_cols, anti_iso, RW)
  local data, R;

  # If we have calculated this case before then return those results
  if RW then
    data := OSS.BinaryMatrixShapesReadFile(nr_rows, nr_cols, anti_iso);
    if data <> fail then
      return Iterator(data);
    fi;
  fi;

  # These are cases which we can describe the solution to explicitly
  if nr_rows <= 2 or nr_cols = 1 then
    return Iterator(OSS.BinaryMatrixShapesSolvedCases(nr_rows, nr_cols));
  fi;

  R := rec();
  # The m x n case is deduced from the n x m case.
  if nr_rows < nr_cols then
    R!.iter  := OSS.IteratorBinaryMatrixShapesByDim(nr_cols, nr_rows,
                                                    anti_iso, RW);
    R!.trans := OSS.TranspositionPermutation(nr_rows, nr_cols);

    R!.NextIterator := function(iter)
      return OnSets(NextIterator(R!.iter), R!.trans);
    end;

    R!.IsDoneIterator := R!.iter!.IsDoneIterator;

    R!.ShallowCopy := function(iter)

      return rec(iter := iter!.iter, trans := iter!.trans);
    end;

    # In square matrix case, build up from previous square case
  elif nr_rows = nr_cols then

    R!.data       := OSS.IteratorBinaryMatrixShapesByDim(nr_rows - 1,
                                                         nr_cols - 1,
                                                         anti_iso, RW);
    R!.embed      := OSS.EmbedSetTransformation(nr_rows - 1, nr_cols - 1,
                                           nr_rows, nr_cols);
    R!.G          := OSS.ActingBinaryMatrixGroup(nr_rows, nr_cols, anti_iso);
    R!.extensions := Iterator(OSS.SquareExtensions(nr_rows));
    R!.currentext := ShallowCopy(R!.extensions);
    R!.found      := [];
    R!.d          := NextIterator(R!.data);
    R!.e          := NextIterator(R!.currentext);
    R!.done       := false;

    R!.current := ShallowCopy(R!.d);
    UniteSet(R!.current, R!.e);
    R!.current := CanonicalImage(R!.G, R!.current, OnSets);

    R!.NextIterator := function(iter)
      local next;
      AddSet(R!.found, R!.current);
      next       := R!.current;
      R!.e       := NextIterator(R!.currentext);
      R!.current := ShallowCopy(R!.d);

      UniteSet(R!.current, R!.e);
      R!.current := CanonicalImage(R!.G, R!.current, OnSets);
      if IsDoneIterator(R!.currentext) then
        R!.currentext := ShallowCopy(R!.extensions);
        R!.d          := NextIterator(R!.data);
        if IsDoneIterator(R!.data) then
          R!.done := true;
        else
          R!.d := NextIterator(R!.data);
        fi;
      fi;
      while R!.current in R!.found do
        R!.e       := NextIterator(R!.currentext);
        R!.current := ShallowCopy(R!.d);

        UniteSet(R!.current, R!.e);
        R!.current := CanonicalImage(R!.G, R!.current, OnSets);
        if IsDoneIterator(R!.currentext) then
          R!.currentext := ShallowCopy(R!.extensions);
          if IsDoneIterator(R!.data) then
            R!.done := true;
          else
            R!.d := NextIterator(R!.data);
          fi;
        fi;
      od;
      return next;
    end;

    R!.IsDoneIterator := function(iter)
      return R!.done;
    end;

    R!.ShallowCopy := function(iter)

      return rec(embed      := iter!.embed,
                 G          := iter!.G,
                 extensions := iter!.extensions,
                 currentext := iter!.currentext,
                 found      := iter!.found,
                 d          := iter!.d,
                 e          := iter!.e,
                 done       := iter!.done,
                 current    := iter!.current);
    end;

    # If more rows than columns then build from a square matrix by adding rows.
  elif nr_rows > nr_cols then
    R!.data       := OSS.IteratorBinaryMatrixShapesByDim(nr_rows - 1,
                                                         nr_cols - 1,
                                                         anti_iso, RW);
    R!.embed      := OSS.EmbedSetTransformation(nr_rows - 1, nr_cols - 1,
                                           nr_rows, nr_cols);
    R!.G          := OSS.ActingBinaryMatrixGroup(nr_rows, nr_cols, anti_iso);
    R!.extensions := OSS.RowExtensions(nr_rows, nr_cols);
    Remove(R!.extensions, nr_cols);
    R!.extensions := Iterator(R!.extensions);

    R!.currentext := ShallowCopy(R!.extensions);
    R!.found      := [];
    R!.d          := NextIterator(R!.data);
    R!.done       := false;

    # Start with this one-off
    R!.current := [1 .. nr_rows * nr_cols];

    R!.NextIterator := function(iter)
      local next;
      AddSet(R!.found, R!.current);
      next       := R!.current;
      R!.e       := NextIterator(R!.currentext);
      R!.current := ShallowCopy(R!.d);

      UniteSet(R!.current, R!.e);
      R!.current := CanonicalImage(R!.G, R!.current, OnSets);
      if IsDoneIterator(R!.currentext) then
        R!.currentext := ShallowCopy(R!.extensions);
        R!.d          := NextIterator(R!.data);
        if IsDoneIterator(R!.data) then
          R!.done := true;
        else
          R!.d := NextIterator(R!.data);
        fi;
      fi;
      while R!.current in R!.found do
        R!.e       := NextIterator(R!.currentext);
        R!.current := ShallowCopy(R!.d);

        UniteSet(R!.current, R!.e);
        R!.current := CanonicalImage(R!.G, R!.current, OnSets);
        if IsDoneIterator(R!.currentext) then
          R!.currentext := ShallowCopy(R!.extensions);
          if IsDoneIterator(R!.data) then
            R!.done := true;
          else
            R!.d := NextIterator(R!.data);
          fi;
        fi;
      od;
      return next;
    end;

    R!.IsDoneIterator := function(iter)
      return R!.done;
    end;

    R!.ShallowCopy := function(iter)

      return rec(embed      := iter!.embed,
                 G          := iter!.G,
                 extensions := iter!.extensions,
                 currentext := iter!.currentext,
                 found      := iter!.found,
                 d          := iter!.d,
                 e          := iter!.e,
                 done       := iter!.done,
                 current    := iter!.current);
    end;
  fi;

  return IteratorByFunctions(R);
end;

###############################################################################
###############################################################################
## Enumerating matrices over 0-groups up to row and column permutations
###############################################################################
###############################################################################
# This code requires the images package and the ferret package.
#
###############################################################################
# A matrix with entries from a 0-group is represented as a point in 3D space,
# Rows X Cols X G u {0}.
###############################################################################
# I assume points in 3D space are represented as [x,y,z], where x runs from
# [1..dimensions[1]], y runs from [1..dimensions[2]], and z runs from
# [1..dimensions[3]]. These points may be represented in 1D space
# [1..dimensions[1] * dimensions[2] * dimensions[3]]. The representation in 1D
# space will be the best for our calculations as it allows us to use efficient
# methods involving permutation groups.
###############################################################################
# The following two functions just map between 3D and 1D represenations of
# 0-group matrices, which is a little annoying as GAP counts from 1.
###############################################################################
OSS.Flatten3DPoint := function(dimensions, point)
  return (point[1] - 1) * dimensions[2] * dimensions[3] +
    (point[2] - 1) * dimensions[3] + (point[3] - 1) + 1;
end;

OSS.Unflatten3DPoint := function(dimensions, value)
   local ret;
   ret    := [];
   value  := value - 1;
   ret[3] := value mod dimensions[3] + 1;
   value  := value - (ret[3] - 1);
   value  := value / dimensions[3];
   ret[2] := value mod dimensions[2] + 1;
   value  := value - (ret[2] - 1);
   ret[1] := value / dimensions[2] + 1;
   return ret;
end;

###############################################################################
# Helpers for working between binary matrix 'shapes' and 0-group matrices (both
# in set representations)
###############################################################################
# Converts a 'flat' 2D point into the 3D point with the first two dimensions
# the same and 1 in the final dimension.
OSS.Unflatten2DPointIn3D := function(dimensions, value)
  local ret;
   ret    := [];
   value  := value - 1;
   ret[2] := value mod dimensions[2] + 1;
   value  := value - (ret[2] - 1);
   value  := value / dimensions[2];
   ret[1] := value mod dimensions[1] + 1;
   ret[3] := 1;
   return ret;
end;

###############################################################################
# Converts binary matrix to a group matrix over the group {0, 1}
OSS.BinaryMatrixToZeroGroupMatrix := function(shape, dimensions)
  local 3dshape, point, i;
  3dshape := [];
  for i in [1 .. dimensions[1] * dimensions[2]] do
    point := OSS.Unflatten2DPointIn3D(dimensions, i);
    if i in shape then
      point[3] := 2;
      Add(3dshape, point);
    else
      Add(3dshape, point);
    fi;
  od;
  Apply(3dshape, a -> OSS.Flatten3DPoint(dimensions, a));
  return 3dshape;
end;

###############################################################################
# Converts 3D matrix into a 'flat' 2D point
OSS.Flatten3DPointIn2D := function(dimensions, point)
  return (point[1] - 1) * dimensions[2] + point[2];
end;

###############################################################################
# Go between 1D and 3D repesentations of 0-groups matrices
###############################################################################
OSS.SetToZeroGroupMatrix := function(set, nr_rows, nr_cols, G)
  local 0G, mat, dim, point, x;
  0G  := Concatenation([0], Elements(G));
  mat := List([1 .. nr_rows], a -> EmptyPlist(nr_cols));
  dim := [nr_rows, nr_cols, Size(G) + 1];
  for x in set do
    point                   := OSS.Unflatten3DPoint(dim, x);
    mat[point[1]][point[2]] := 0G[point[3]];
  od;
  return mat;
end;

# TODO: This isn't used anywhere!
OSS.ZeroGroupMatrixToSet := function(mat, nr_rows, nr_cols, G)
  local set, dim, i, j;
  set := [];
  dim := [nr_rows, nr_cols, Size(G) + 1];
  for i in [1 .. nr_rows] do
    for j in [1 .. nr_cols] do
      if mat[i][j] = 0 then
        Add(set, OSS.Flatten3DPoint(dim, [i, j, 1]));
      else
        Add(set,
          OSS.Flatten3DPoint(dim, [i, j, 1 + Position(Elements(G),
                                              mat[i][j])]));
      fi;
    od;
  od;
  return set;
end;

###############################################################################
# The functions return permutations corresponding to actions on the space
# of 0-group matrices which have orbits corresponding to isomorphism classes
# of RZMS. In particular, these actions are: row and column permutations, and
# multiplication of rows and columns by non-zero group elements.
# The action which transposes matrices sends 0-group matrices to
# anti-isomorphic matrices.
###############################################################################
# Given a 3D cube, dimensions dimensions, apply permutation 'perm' to dimension
# 'dim'.
#
# With dim = 1 and dim = 2 this returns a permutation which acts on 1D 0-group
# matrices by permuting the rows and columns, respectively.
# With dim = 3 and perm corresponding to an automorphism of the 0-group this
# returns a permutation on 1D reps which applies an automorphism elementwise.
OSS.ApplyPermWholeDimension := function(dimensions, dim, perm)
  local map, point, i;
    map := [];
    for i in [1 .. Product(dimensions)] do
      point      := OSS.Unflatten3DPoint(dimensions, i);
      point[dim] := point[dim] ^ perm;
      map[i]     := OSS.Flatten3DPoint(dimensions, point);
    od;
  return PermList(map);
end;

###############################################################################
# Given a 3D cube, dimensions dimensions, apply permutation 'perm' to dimension
# 'dim' But only to elements which have value 'fixval' in dimension 'fixdim'.
#
# Returns a permutation of 1D 0-group matrices corresponding to multiplying a
# row (fixdim = 1) or column (fixdim = 2) when:
#
# (i)  dim = 3, and
# (ii) perm is a permutation of [1..dimensions[3]] corresponding to the action
# (by left or right multiplication) of a non-zero element of G_0.
#
# (That is to say, the elements of G_0 correspond to [1 .. Size(G_0)] and perm
# sends a -> a * b for all a in G_0 and some b in G_0.)
OSS.ApplyPermSingleAssignDimension  := function(dimensions, dim,
                                                           perm, fixdim, fixval)
  local map, point, i;
  map := [];
  for i in [1 .. Product(dimensions)] do
    point := OSS.Unflatten3DPoint(dimensions, i);
    if point[fixdim] = fixval then
      point[dim] := point[dim] ^ perm;
    fi;
    map[i] := OSS.Flatten3DPoint(dimensions, point);
  od;
  return PermList(map);
end;

###############################################################################
# Returns a permutation of 1D 0-group matrices with dimensions dimensions
# corresponding to transposition of matrices.
OSS.TranspositionPerm := function(dimensions)
  local map, point, i;
  map := [];
  for i in [1 .. Product(dimensions)] do
    point  := OSS.Unflatten3DPoint(dimensions, i);
    map[i] := OSS.Flatten3DPoint(dimensions, [point[2], point[1],
                                                         point[3]]);
  od;
  return PermList(map);
end;

###############################################################################
# This function uses ApplyPermWholeDimension and ApplyPermSingleAssignDimension
# to construct the group which has orbits corresponding to distinct isomorphism
# classes of RZMS with a certain 'shape'. Having the same 'shape' means that
# RZMS are created from matrices which have zeros in the same locations.
OSS.RZMSMatrixIsomorphismGroup := function(shape, nr_rows, nr_cols,
                                           G, anti_iso)
  local dim, S, rows, cols, 3dshape, H, gens, elms, rmlt, grswaps, lmlt,
        gcswaps, auto;

  dim := [nr_rows, nr_cols, Size(G) + 1];
  # Row Swaps
  S    := SymmetricGroup(nr_rows);
  rows := List(GeneratorsOfGroup(S),
               x -> OSS.ApplyPermWholeDimension(dim, 1, x));

  # Col swaps
  S    := SymmetricGroup(nr_cols);
  cols := List(GeneratorsOfGroup(S),
               x -> OSS.ApplyPermWholeDimension(dim, 2, x));

  # We only want swaps which fix the locations of the zeros.
  3dshape := OSS.BinaryMatrixToZeroGroupMatrix(shape, dim);
  H       := Stabilizer(Group(Flat([cols, rows])), 3dshape, OnSets);

  gens := GeneratorsOfGroup(G);
  elms := ShallowCopy(Elements(G));

  # Apply g to each row (left multiplication by inverse):
  rmlt := List(gens, g -> PermList(Concatenation([1],
          1 + List(elms, e -> Position(elms, (g ^ -1) * e)))));
  grswaps := List(rmlt,
                  g -> OSS.ApplyPermSingleAssignDimension(dim, 3, g, 1, 1));

  # Apply g to each col (right multiplication):
  lmlt := List(gens, g -> PermList(Concatenation([1],
          1 + List(elms, e -> Position(elms, e * g)))));
  gcswaps := List(lmlt, g ->
                  OSS.ApplyPermSingleAssignDimension(dim, 3, g, 2, r));

  # Automorphisms of G
  S    := AutomorphismGroup(G);
  auto := List(GeneratorsOfGroup(S), x -> List(Elements(G), a ->
          Position(Elements(G), a ^ x)));
  Apply(auto, a -> PermList(Concatenation([1], a + 1)));
  auto := List(auto, x -> OSS.ApplyPermWholeDimension(dim, 3, x));

  # Add transposition perm if searching up to anti-isomorphism in square case
  if anti_iso and nr_rows = nr_cols then
    # Check if shape corresponds to a symmetric matrix
    if ForAll([2 .. nr_rows],
              i -> ForAll([i + 1 .. nr_cols],
                          j -> (((i - 1) * nr_cols + j) in shape) =
                               (((j - 1) * nr_cols + i) in shape))) then
      Add(auto, OSS.TranspositionPerm(dim));
    fi;
  fi;

  # The RZMS matrix isomorphism group
  return Group(Flat([GeneratorsOfGroup(H), grswaps, gcswaps, auto]));
end;

###############################################################################
# This function finds some of the possible dimensions of matrices which define
# RZMS of order k. I will find [x, y, z] such that x * y * z + 1 = k,
# however if [x, y, z] and [y, x, z] are distinct then it will only return one
# of these because the isomorphism classes of RZMS with dimensions [x, y, z]
# will be in 1-1 correspondence (by anti-isomorphism) with the classes of RZMS
# which have dimensions [y, x, z]. It is easy to go between these classes as we
# only need to transpose the matrices so there is no point calculating both
# cases by finding orbit representatives of a potentially very large
# permutation group.
#
# If anti_iso = true then we look up to anti isomrophism, otherwise just up to
# isomorphism.
###############################################################################
OSS.RZMSParametersByOrder := function(k, anti_iso)
  local out, d, e;
  out := [];
  for d in DivisorsInt(k - 1) do
    # |I| * |J| = k/d
    for e in DivisorsInt((k - 1) / d) do
      # If anti = true then We only want one of (|I|,|J|) = (a,b), (b,a)
      if not anti_iso or e <= (k - 1) / d / e then
        Add(out, [(k - 1) / d / e, e, d]);
      fi;
    od;
  od;
  return out;
end;

###############################################################################
# Methods for enumerating matrices over 0-groups
###############################################################################
# Given dimensions and a group and a shape, returns a representative for each
# isomorphism class of RZMS defined by a matrix with these dimensions over the
# 0-group G u {0} with 0's precisely the locations specified by the shape.
# When nr_rows is not equal to nr_cols a representative of each
# anti-isomorphism class is returned instead.
#
# We reduce the number of matrices to apply CanonicalImage to by only applying
# to certain normal matrices, which will still cover every isomorphism class.
OSS.RZMSMatricesByShape := function(nr_rows, nr_cols, G, shape, anti_iso)
  local IG, dim, space, is_norm_row, is_norm_col, point, out, iter, mat, i;

  # This is slow when one of nr_rows or nr_cols is large (even if the other is
  # small) so we have RZMSMatricesByShapeEasyCase for some of these situations.
  IG := OSS.RZMSMatrixIsomorphismGroup(shape, nr_rows, nr_cols, G, anti_iso);

  dim         := [nr_rows, nr_cols, Size(G) + 1];
  space       := [];
  is_norm_row := List([1 .. nr_rows], a -> false);
  is_norm_col := List([1 .. nr_cols], a -> false);
  for i in [1 .. dim[1] * dim[2]] do
    point := OSS.Unflatten2DPointIn3D(dim, i);
    if i in shape then
      if not is_norm_row[point[1]] then
        Add(space,
            [OSS.Flatten3DPoint(dim, [point[1], point[2], 2])]);
        is_norm_row[point[1]] := true;
      elif not is_norm_col[point[2]] then
        Add(space,
            [OSS.Flatten3DPoint(dim, [point[1], point[2], 2])]);
        is_norm_col[point[2]] := true;
      else
        Add(space, List([1 .. Size(G)], g ->
          OSS.Flatten3DPoint(dim, [point[1], point[2], g + 1])));
      fi;
    else
      Add(space, [OSS.Flatten3DPoint(dim, [point[1], point[2], 1])]);
    fi;
  od;

  out  := Set([]);
  iter := IteratorOfCartesianProduct(space);
  while not IsDoneIterator(iter) do
    mat := NextIterator(iter);
    AddSet(out, CanonicalImage(IG, mat, OnSets));
  od;

  return out;
end;

OSS.IteratorRZMSMatricesByShape := function(nr_rows, nr_cols, G,
                                            shape, anti_iso)
  local R, dim, space, is_norm_row, is_norm_col, point, i;

  R := rec();

  # This is slow when one of nr_rows or nr_cols is large (even if the other is
  # small) so we have RZMSMatricesByShapeEasyCase for some of these situations.
  R!.IG := OSS.RZMSMatrixIsomorphismGroup(shape, nr_rows, nr_cols,
                                          G, anti_iso);

  dim         := [nr_rows, nr_cols, Size(G) + 1];
  space       := [];
  is_norm_row := List([1 .. nr_rows], a -> false);
  is_norm_col := List([1 .. nr_cols], a -> false);

  for i in [1 .. dim[1] * dim[2]] do
    point := OSS.Unflatten2DPointIn3D(dim, i);
    if i in shape then
      if not is_norm_row[point[1]] then
        Add(space,
            [OSS.Flatten3DPoint(dim, [point[1], point[2], 2])]);
        is_norm_row[point[1]] := true;
      elif not is_norm_col[point[2]] then
        Add(space,
            [OSS.Flatten3DPoint(dim, [point[1], point[2], 2])]);
        is_norm_col[point[2]] := true;
      else
        Add(space, List([1 .. Size(G)], g ->
          OSS.Flatten3DPoint(dim, [point[1], point[2], g + 1])));
      fi;
    else
      Add(space, [OSS.Flatten3DPoint(dim, [point[1], point[2], 1])]);
    fi;
  od;

  R!.cart    := IteratorOfCartesianProduct(space);
  R!.current := CanonicalImage(R!.IG, NextIterator(R!.cart), OnSets);
  R!.found   := [];
  R!.done    := false;

  # TODO: this still returns something (the last value) even once IsDoneIterator
  # is true. Is this bad?
  R!.NextIterator := function(iter)
    local next;
    next := R!.current;
    AddSet(R!.found, next);
    while not IsDoneIterator(R!.cart) and R!.current in R!.found do
      R!.current := CanonicalImage(R!.IG, NextIterator(R!.cart), OnSets);
    od;
    return next;
  end;

  R!.IsDoneIterator := function(iter)
    return IsDoneIterator(R!.cart) and R!.current in R!.found;
  end;

  R!.ShallowCopy   := function(iter)

    return rec(IG      := iter!.IG,
               cart    := iter!.cart,
               current := iter!.current,
               done    := iter!.done,
               found   := iter!.found);
  end;

  return IteratorByFunctions(R);
end;

###############################################################################
# Given a trivial case (nr_rows = 1 or nr_cols = 1 or Size(G) = 1) this returns
# the (anti-)isomorphism classes of RZMS with the given dimensions. The method
# RZMSMatricesByShape would be very ineffective for these cases.
OSS.RZMSMatricesByShapeEasyCase := function(nr_rows, nr_cols, G, shape)
  local out, dim, pos, point, i;

  out := [];
  dim := [nr_rows, nr_cols, Size(G) + 1];
  if dim[1] = 1 or dim[2] = 1 then
    pos := Position(Elements(G), One(G)) + 1;
    return [List([1 .. nr_rows], i -> pos + (i - 1) * (Size(G) + 1))];
  elif dim[3] = 2 then
    for i in [1 .. dim[1] * dim[2]] do
      point := OSS.Unflatten2DPointIn3D(dim, i);
      if i in shape then
        Add(out, OSS.Flatten3DPoint(dim, [point[1], point[2], 2]));
      else
        Add(out, OSS.Flatten3DPoint(dim, [point[1], point[2], 1]));
      fi;
    od;
    return [out];
  fi;
  ErrorNoReturn("RZMSMatricesByShapeEasyCase: only for cases with 1 row, 1 ",
                "column or trivial group");
end;

OSS.IteratorRZMSMatricesByShapeEasyCase := function(nr_rows, nr_cols,
                                                    G, shape, anti_iso)
  local out, dim, pos, point, i;

  out := [];
  dim := [nr_rows, nr_cols, Size(G) + 1];
  if dim[1] = 1 or dim[2] = 1 then
    pos := Position(Elements(G), One(G)) + 1;
    return [List([1 .. nr_rows], i -> pos + (i - 1) * (Size(G) + 1))];
  elif dim[3] = 2 then
    for i in [1 .. dim[1] * dim[2]] do
      point := OSS.Unflatten2DPointIn3D(dim, i);
      if i in shape then
        Add(out, OSS.Flatten3DPoint(dim, [point[1], point[2], 2]));
      else
        Add(out, OSS.Flatten3DPoint(dim, [point[1], point[2], 1]));
      fi;
    od;
    return Iterator([out]);
  fi;
  ErrorNoReturn("RZMSIteratorMatricesByShapeEasyCase: only for cases with 1 ",
                "row, 1 column or trivial group");
end;

###############################################################################
# Given dimensions and a group, returns a representative for each isomorphism
# class of RZMS defined by a matrix with these dimensions over the 0-group G u
# {0}. When nr_rows is not equal to nr_cols a representative of each
# anti-isomorphism class is returned instead
OSS.RZMSMatricesByParameters := function(nr_rows, nr_cols, G, anti_iso)
  local pos, out, i, shapes, shape;

  if nr_cols = 1 then
    pos := Position(Elements(G), One(G)) + 1;
    return [List([1 .. nr_rows], i -> pos + (i - 1) * (Size(G) + 1))];
  fi;

  # The m x n case is deduced from the n x m case.
  if nr_rows < nr_cols then
    out := OSS.RZMSMatricesByParameters(nr_cols, nr_rows, G, anti_iso);
    Apply(out, a -> OSS.Unflatten3DPoint([nr_rows, nr_cols, Size(G) + 1], a));
    for i in out do
      i := [i[2], i[1], i[3]];
    od;
    Apply(out, a -> OSS.Flatten3DPoint([nr_rows, nr_cols, Size(G) + 1], a));
    return out;
  fi;

  # Get shapes - if 4th parameter is true then using precalculated binary mats.
  shapes := OSS.BinaryMatrixShapesByDim(nr_rows, nr_cols, anti_iso, true);

  # Find by shape
  out := [];
  for shape in shapes do
    if Size(G) = 1 then
      Append(out, OSS.RZMSMatricesByShapeEasyCase(nr_rows, nr_cols, G, shape));
    else
      Append(out, OSS.RZMSMatricesByShape(nr_rows, nr_cols, G,
                                          shape, anti_iso));
    fi;
  od;

  return out;
end;

OSS.IteratorRZMSMatricesByParameters := function(nr_rows, nr_cols, G, anti_iso)
  local pos, out, i, shapes, R, shape, func;

  if nr_cols = 1 then
    pos := Position(Elements(G), One(G)) + 1;
    return Iterator([List([1 .. nr_rows],
                          i -> pos + (i - 1) * (Size(G) + 1))]);
  fi;

  # The m x n case is deduced from the n x m case.
  if nr_rows < nr_cols then
    out := OSS.RZMSMatricesByParameters(nr_cols, nr_rows, G, anti_iso);
    Apply(out, a -> OSS.Unflatten3DPoint([nr_rows, nr_cols, Size(G) + 1], a));
    for i in out do
      i := [i[2], i[1], i[3]];
    od;
    Apply(out, a -> OSS.Flatten3DPoint([nr_rows, nr_cols, Size(G) + 1], a));
    return out;
  fi;

  # Get shapes - if 4th parameter is true then using precalculated binary mats.
  shapes := OSS.IteratorBinaryMatrixShapesByDim(nr_rows, nr_cols,
                                                anti_iso, true);

  # Find by shape
  R := rec(shapes_iter := shapes);

  shape := NextIterator(shapes);
  if Size(G) = 1 then
    func := OSS.IteratorRZMSMatricesByShapeEasyCase;
  else
    func := OSS.IteratorRZMSMatricesByShape;
  fi;
  R!.mat_iter := func(nr_rows, nr_cols, G, shape, anti_iso);

  R!.NextIterator := function(iter)
    if IsDoneIterator(R!.mat_iter) then
      R!.mat_iter := func(nr_rows, nr_cols, G, NextIterator(R!.shapes_iter),
                          anti_iso);
    fi;
    return NextIterator(R!.mat_iter);
  end;

  R!.IsDoneIterator := function(iter)
    return IsDoneIterator(R!.shapes_iter) and IsDoneIterator(R!.mat_iter);
  end;

  R!.ShallowCopy := function(iter)

    return rec(shapes_iter := iter!.shapes_iter, mat_iter := iter!.mat_iter);
  end;

  return IteratorByFunctions(R);
end;

###############################################################################
# Just for interest (have better method elsewhere) returns just the rees matrix
# semigroups. They correspond to the RZMS which have no zeros in the defining
# matrix and are obtained by removing the zero element from these.
OSS.RZMSMatrices := function(nr_rows, nr_cols, group, anti_iso)
  return List(OSS.RZMSMatricesByParameters(nr_rows, nr_cols, group, anti_iso),
              mat -> OSS.SetToZeroGroupMatrix(mat, nr_rows, nr_cols, group));
end;

OSS.RZMS := function(nr_rows, nr_cols, group, anti_iso)
  return List(OSS.RZMSMatrices(nr_rows, nr_cols, group, anti_iso),
              mat -> ReesZeroMatrixSemigroup(group, mat));
end;

OSS.RZMSByOrder := function(order, anti_iso)
  local out, parameters, groups, p, group;
  out        := [];
  parameters := OSS.RZMSParametersByOrder(order, anti_iso);
  for p in parameters do
    groups := List(AllSmallGroups(p[3]), G -> Image(IsomorphismPermGroup(G)));
    for group in groups do
      Append(out, OSS.RZMS(p[1], p[2], group, anti_iso));
    od;
  od;
  return out;
end;

OSS.IteratorRZMSMatrices := function(nr_rows, nr_cols, group, anti_iso)
  local R, f;
  R := OSS.IteratorRZMSMatricesByParameters(nr_rows, nr_cols, group,
                                               anti_iso);
  f := R!.NextIterator;

  R!.NextIterator := function(iter)
    return OSS.SetToZeroGroupMatrix(f(R), nr_rows, nr_cols, group);
  end;
  return R;
end;

OSS.IteratorRZMS := function(nr_rows, nr_cols, group, anti_iso)
  local R, f;
  R := OSS.IteratorRZMSMatrices(nr_rows, nr_cols, group, anti_iso);
  f := R!.NextIterator;

  R!.NextIterator := function(iter)
    return ReesZeroMatrixSemigroup(group, f(R));
  end;
  return R;
end;

OSS.IteratorRZMSByOrder := function(order, anti_iso)
  local parameters, R;
  parameters := OSS.RZMSParametersByOrder(order, anti_iso);
  parameters := List(parameters, p -> List(AllSmallGroups(p[3]), G -> [p[1],
                p[2], Image(IsomorphismPermGroup(G))]));
  parameters := Iterator(Concatenation(parameters));

  R           := rec(paramIter := parameters);
  R!.p        := NextIterator(R!.paramIter);
  R!.RZMSiter := OSS.IteratorRZMS(R!.p[1], R!.p[2], R!.p[3], anti_iso);

  R!.NextIterator := function(iter)
    if IsDoneIterator(R!.RZMSiter) then
      R!.p        := NextIterator(R!.paramIter);
      R!.RZMSiter := OSS.IteratorRZMS(R!.p[1], R!.p[2], R!.p[3], anti_iso);
    fi;
    return NextIterator(R!.RZMSiter);
  end;

  R!.IsDoneIterator := function(iter)
    return IsDoneIterator(R!.paramIter) and IsDoneIterator(R!.RZMSiter);
  end;

  R!.ShallowCopy := function(iter)

    return rec(paramIter := iter!.paramIter,
               RZMSiter  := R!.RZMSiter,
               p         := R!.p);
  end;

  return IteratorByFunctions(R);
end;

###############################################################################
# User Methods
###############################################################################
InstallMethod(AllZeroSimpleSemigroups,
"for an int, an int, a group and a bool",
[IsInt, IsInt, IsGroup, IsBool],
function(nr_rows, nr_cols, group, anti_iso)
  if 1 > nr_rows then
    ErrorNoReturn("OSS: AllZeroSimpleSemigroups: usage,\n ",
                  "the first argument should be a strictly positive integer,");
  elif 1 > nr_cols then
    ErrorNoReturn("OSS: AllZeroSimpleSemigroups: usage,\n ",
                  "the second argument should be a strictly positive integer,");
  fi;
  return OSS.RZMS(nr_rows, nr_cols, group, anti_iso);
end);

InstallMethod(AllZeroSimpleSemigroups,
"for an int and a bool",
[IsInt, IsBool],
function(order, anti_iso)
  if 1 > order then
    ErrorNoReturn("OSS: AllZeroSimpleSemigroups: usage,\n ",
                  "the first argument should be a strictly positive integer,");
  fi;
  return OSS.RZMSByOrder(order, anti_iso);
end);

InstallMethod(IteratorOfZeroSimpleSemigroups,
"for an int, an int, a group and a bool",
[IsInt, IsInt, IsGroup, IsBool],
function(nr_rows, nr_cols, group, anti_iso)
  if 1 > nr_rows then
    ErrorNoReturn("OSS: IteratorOfZeroSimpleSemigroups: usage,\n ",
                  "the first argument should be a strictly positive integer,");
  elif 1 > nr_cols then
    ErrorNoReturn("OSS: IteratorOfZeroSimpleSemigroups: usage,\n ",
                  "the second argument should be a strictly positive integer,");
  fi;
  return OSS.IteratorRZMS(nr_rows, nr_cols, group, anti_iso);
end);

InstallMethod(IteratorOfZeroSimpleSemigroups,
"for an int and a bool",
[IsInt, IsBool],
function(order, anti_iso)
  if 1 > order then
    ErrorNoReturn("OSS: IteratorOfZeroSimpleSemigroups: usage,\n ",
                  "the first argument should be a strictly positive integer,");
  fi;
  return OSS.IteratorRZMSByOrder(order, anti_iso);
end);
