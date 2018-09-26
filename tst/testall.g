#
# othersmallsemi: This package contains various databases of semigroups
# of low order.
#
# This file runs package tests. It is also referenced in the package
# metadata in PackageInfo.g.
#
LoadPackage( "images" );
LoadPackage( "othersmallsemi" );

TestDirectory(DirectoriesPackageLibrary( "othersmallsemi", "tst" ),
  rec(exitGAP := true));

FORCE_QUIT_GAP(1); # if we ever get here, there was an error
