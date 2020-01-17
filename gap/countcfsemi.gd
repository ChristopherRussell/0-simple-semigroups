DeclareOperation("NrMatricesAllRowsAndColsUniqueUpToRowAndColPermutation",
                 [IsInt, IsInt]);
DeclareOperation("NrMatricesAllRowsAndColsUnique",
                 [IsInt, IsInt, IsPerm, IsPerm]);
DeclareOperation("IteratorOfConnectedComponents",
                 [IsInt, IsInt, IsPerm, IsPerm]);
DeclareOperation("IteratorOfLabelGCDs", [IsInt, IsInt, IsList]);
DeclareOperation("CardinalityOfMatrixSetsIntersection",
                 [IsInt, IsInt, IsList, IsList]);
DeclareOperation("_Omega", [IsInt, IsInt, IsInt]);
DeclareAttribute("omega", IsInt);
DeclareOperation("ParityOfMatrixSetsCollection",
                 [IsInt, IsInt, IsList, IsList]);
DeclareOperation("Psi", [IsList]);
DeclareOperation("psi", [IsInt, IsList]);
DeclareOperation("Theta", [IsInt, IsInt, IsList, IsList]);
DeclareOperation("theta", [IsInt, IsInt]);
