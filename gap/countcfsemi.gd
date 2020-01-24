DeclareOperation("NrMatricesAllRowsAndColsUniqueUpToRowAndColPermutation",
                 [IsInt, IsInt]);
DeclareOperation("NrMatricesAllRowsAndColsUnique",
                 [IsInt, IsInt, IsPerm, IsPerm]);
DeclareOperation("IteratorOfConnectedComponents",
                 [IsInt, IsInt, IsPerm, IsPerm]);
DeclareOperation("IteratorOfLabelGCDs", [IsInt, IsInt, IsList]);
DeclareOperation("CardinalityOfMatrixSetsIntersection",
                 [IsInt, IsInt, IsList, IsList]);
DeclareOperation("_Omega", [IsList, IsList, IsList]);
DeclareAttribute("omega", IsInt);
DeclareOperation("ParityOfMatrixSetsCollection",
                 [IsInt, IsInt, IsPerm, IsPerm, IsList, IsList]);
DeclareOperation("gamma",
                 [IsInt, IsInt, IsPerm, IsPerm, IsList, IsList]);
DeclareOperation("Psi", [IsList]);
DeclareAttribute("psi", IsInt);
DeclareOperation("Theta", [IsInt, IsInt, IsList, IsList]);
DeclareOperation("theta", [IsInt, IsInt]);
