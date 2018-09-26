#############################################################################
##
#W  tst/0_simple_semigroups.tst
#Y  Copyright (C) 2018                                    Christopher Russell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##
gap> START_TEST("OtherSmallSemi package: 0_simple_semigroups.tst");
gap> LoadPackage("images");
gap> LoadPackage("0_simple_semigroups", false);;

#T# AllZeroSimpleSemigroups helpers
gap> BadIsomorphismCheck := function(coll)
> local n, out, S;
>   n := Length(coll);
>   out := [];
>   for S in coll do
>     if not ForAny(out, T -> IsIsomorphicSemigroup(S, T)) then
>       Add(out, S);
>     fi;
>   od;
> end;;
gap> CompareFuncs := function(nr_cols, nr_rows, G)
> local x, y;
>   x := NrZeroSimpleSemigroups([nr_cols, nr_rows, G]);
>   y := AllZeroSimpleSemigroups(nr_cols * nr_rows * Size(G) + 1, nr_rows,
>                                nr_cols, G, false);
>   return x = y;
> end;;

#T# Check output of counting vs database functions
gap> parameters := Concatenation(List([2 .. 16], 
>                    i -> OSS.RZMSParameters(i, 0, 0, 0, false)));;
gap> ForAll(parameters, p -> ForAll(AllSmallGroups(p[3], g ->
      CompareFuncs(p[1], p[2], Image(IsomorphismPermGroup(g))))));
true

#T# UnbindVariables
gap> Unbind(A);

#E#
gap> STOP_TEST("OtherSmallSemi package: 0_simple_semigroups.tst");
