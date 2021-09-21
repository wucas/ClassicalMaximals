gap> m := 3;; t := 2;; q := 5;;
gap> G := TensorInducedDecompositionStabilizerInSL(m, t, q);;
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> m := 2;; t := 2;; q := 7;;
gap> G := TensorInducedDecompositionStabilizerInSL(m, t, q);;
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> m := 2;; t := 2;; q := 5;;
gap> G := TensorInducedDecompositionStabilizerInSL(m, t, q);;
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
gap> m := 3;; t := 3;; q := 3;;
gap> G := TensorInducedDecompositionStabilizerInSL(m, t, q);;
gap> Size(Group(GeneratorsOfGroup(G))) = Size(G);
true
