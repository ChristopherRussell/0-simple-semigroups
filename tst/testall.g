#
# 0_simple_semigroups: This package contains a database of 0-simple semigroups of low order.
#
# This file runs package tests. It is also referenced in the package
# metadata in PackageInfo.g.
#
LoadPackage( "0_simple_semigroups" );

TestDirectory(DirectoriesPackageLibrary( "0_simple_semigroups", "tst" ),
  rec(exitGAP := true));

FORCE_QUIT_GAP(1); # if we ever get here, there was an error
