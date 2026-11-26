/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.Exactness
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Product.Split
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Construction

/-!
# Semidirect decompositions over the unipotent radical

Let `G` be a geometrically reduced affine group of finite type over a field `k`, with unipotent
radical `R_u(G)`, and let `T ⊆ G` be a closed subgroup. If the composite `T → G → G ⧸ R_u(G)`
with the affine quotient is an isomorphism, then multiplication is an isomorphism

```text
R_u(G) ⋊ T ≅ G.
```

For a smooth connected solvable group over an algebraically closed field, whose quotient
`G ⧸ G_u` is a torus (`TauCeti.FiniteTypeCommHopfAlgCat.torus_coinvariants_unipotentRadical`),
this criterion yields the decomposition `G = G_u ⋊ T` of Milne, Theorem 16.33(d), for every
maximal torus `T` that maps isomorphically onto `G ⧸ G_u`.

The proof applies the split-extension criterion
`TauCeti.CommHopfAlgCat.isIso_productMapOfNormal_of_isIso` to the quotient map, whose kernel is
`R_u(G)` by exactness of the affine quotient for geometrically reduced groups
(`TauCeti.CommHopfAlgCat.kernelHopfIdeal_coinvariantsι_eq`).

## Main declarations

* `TauCeti.FiniteTypeCommHopfAlgCat.isIso_productMapOfNormal_unipotentRadical_of_isIso`: if
  `T → G ⧸ R_u(G)` is an isomorphism, then multiplication `R_u(G) ⋊ T → G` is an isomorphism.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 16.33(d).
* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), Theorem 10.6(4).
-/

public section

open CategoryTheory
open _root_.CommHopfAlgCat

namespace TauCeti.FiniteTypeCommHopfAlgCat

universe u

variable {k : Type u} [Field k]

/-- **A closed subgroup mapping isomorphically onto `G ⧸ R_u(G)` is a complement to the unipotent
radical.** For a geometrically reduced affine group `G` of finite type over a field and a closed
subgroup `T` cut out by `J`, if the composite `T → G → G ⧸ R_u(G)` is an isomorphism, then
multiplication `R_u(G) ⋊ T → G` is an isomorphism of affine groups. -/
theorem isIso_productMapOfNormal_unipotentRadical_of_isIso
    (G : FiniteTypeCommHopfAlgCat.{u, u} k) [Algebra.IsGeometricallyReduced k G]
    (J : HopfIdeal k G)
    [IsIso (CommHopfAlgCat.coinvariantsι (isNormal_unipotentRadicalDefiningIdeal G) ≫
      CommHopfAlgCat.mkQuotient G.obj J)] :
    IsIso (CommHopfAlgCat.productMapOfNormal G.obj (unipotentRadicalDefiningIdeal G) J
      (isNormal_unipotentRadicalDefiningIdeal G)) :=
  CommHopfAlgCat.isIso_productMapOfNormal_of_isIso _ J _ _
    (CommHopfAlgCat.kernelHopfIdeal_coinvariantsι_eq _)

end TauCeti.FiniteTypeCommHopfAlgCat
