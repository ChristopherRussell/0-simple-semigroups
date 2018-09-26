#############################################################################
##
#W  tst/0simple.tst
#Y  Copyright (C) 2018                                    Christopher Russell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##
gap> START_TEST("othersmallsemi package: 0simple.tst");
gap> LoadPackage("images", false);;
gap> LoadPackage("othersmallsemi", false);;

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
gap> CompareFuncs := function(nr_cols, nr_rows, G, f1, f2)
> local x, y;
>   x := f1([nr_cols, nr_rows, G]);
>   y := Length(f2(nr_rows, nr_cols, G, false));
>   return x = y;
> end;;

#T# Check output of counting vs database functions
gap> parameters := Concatenation(List([2 .. 16], 
>                    i -> OSS.RZMSParametersByOrder(i, false)));;
gap> ForAll(parameters, p -> ForAll(AllSmallGroups(p[3]), g ->
>      CompareFuncs(p[1], p[2], Image(IsomorphismPermGroup(g)),
>      NrZeroSimpleSemigroups, AllZeroSimpleSemigroups)));
true
gap> parameters := Concatenation(List([2 .. 16], 
>                    i -> OSS.RMSParametersByOrder(i, false)));;
gap> ForAll(parameters, p -> ForAll(AllSmallGroups(p[3]), g ->
>      CompareFuncs(p[1], p[2], Image(IsomorphismPermGroup(g)),
>      NrSimpleSemigroups, AllSimpleSemigroups)));
true

#T# UnbindVariables
gap> Unbind(A);

#E#
gap> STOP_TEST("OtherSmallSemi package: 0simple.tst");
