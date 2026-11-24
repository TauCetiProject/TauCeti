/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.ClosedImmersion
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Construction

/-!
# Subgroups mapping by a closed immersion to the quotient by the unipotent radical

Let `G` be a geometrically reduced affine group of finite type over a field `k`, and let `T` be a
geometrically reduced closed subgroup of `G`, cut out by a Hopf ideal `J`. This file records that
if the composite `T → G → G ⧸ R_u(G)` has trivial scheme-theoretic kernel, then it is a closed
immersion: the case `N = R_u(G)` of `coinvariantsι_comp_mkQuotient_surjective`.

The main application is to a torus `T` of a smooth connected solvable group `G` over an
algebraically closed field, where `G ⧸ R_u(G)` is a torus (`torus_coinvariants_unipotentRadical`).
Combined with a dimension equality between `T` and `G ⧸ R_u(G)`, the isomorphism criterion
`isIso_coinvariantsι_comp_mkQuotient` then gives `T ≅ G ⧸ R_u(G)`, the input to the decomposition
`G = R_u(G) ⋊ T` for a maximal torus `T` (Milne, Theorem 16.33(d)).

## Main declarations

* `TauCeti.FiniteTypeCommHopfAlgCat.coinvariantsι_unipotentRadical_comp_mkQuotient_surjective`:
  a geometrically reduced subgroup meeting the unipotent radical trivially maps to `G ⧸ R_u(G)`
  by a closed immersion.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorems 5.34 and 16.33(d).
* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), Theorem 10.6.
-/

public section

open CategoryTheory

namespace TauCeti.FiniteTypeCommHopfAlgCat

universe u

variable {k : Type u} [Field k] (G : FiniteTypeCommHopfAlgCat.{u, u} k)

/-- The case `N = R_u(G)` of `coinvariantsι_comp_mkQuotient_surjective`: a geometrically
reduced subgroup meeting the unipotent radical trivially maps to `G ⧸ R_u(G)` by a closed
immersion. -/
theorem coinvariantsι_unipotentRadical_comp_mkQuotient_surjective
    [Algebra.IsGeometricallyReduced k G] {J : HopfIdeal k G}
    [Algebra.IsGeometricallyReduced k (quotient G J)]
    (hker : CommHopfAlgCat.kernelHopfIdeal
        (CommHopfAlgCat.coinvariantsι (isNormal_unipotentRadicalDefiningIdeal G) ≫
          CommHopfAlgCat.mkQuotient G.obj J) =
      HopfIdeal.augmentation k (CommHopfAlgCat.quotient G.obj J)) :
    Function.Surjective
      (CommHopfAlgCat.coinvariantsι (isNormal_unipotentRadicalDefiningIdeal G) ≫
        CommHopfAlgCat.mkQuotient G.obj J).hom :=
  coinvariantsι_comp_mkQuotient_surjective G _ hker

end TauCeti.FiniteTypeCommHopfAlgCat
