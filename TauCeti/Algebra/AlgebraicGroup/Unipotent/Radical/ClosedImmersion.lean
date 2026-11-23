/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.FiniteType
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.ClosedImmersion
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Construction

/-!
# Subgroups mapping isomorphically onto the quotient by the unipotent radical

Let `G` be an affine group of finite type over a field `k`, and let `T` be a closed subgroup of
`G`, cut out by a Hopf ideal `J`. This file proves that if `G` and `T` are geometrically reduced
and the composite `T → G → G ⧸ R_u(G)` has trivial scheme-theoretic kernel, then it is a closed
immersion. If moreover `G` is smooth and geometrically connected, `T` is smooth and connected,
and the Lie algebra of `T` has dimension at least that of `G ⧸ R_u(G)`, then the composite is an
isomorphism.

The main application is to a torus `T` of a smooth connected solvable group `G` over an
algebraically closed field, where `G ⧸ R_u(G)` is a torus (`torus_coinvariants_unipotentRadical`).
This is the closed-immersion step of the decomposition `G = R_u(G) ⋊ T` for a maximal torus `T`
(Milne, Theorem 16.33(d)). It leaves the dimension count: that a maximal torus has the same
dimension as `G ⧸ R_u(G)`.

Coordinate rings reverse arrows: `O(G ⧸ R_u(G))` is the Hopf subalgebra of right coinvariants,
and the composite is the coordinate map `coinvariantsι ≫ mkQuotient G J`.

## Main declarations

* `TauCeti.FiniteTypeCommHopfAlgCat.surjective_coinvariantsι_unipotentRadical_comp_mkQuotient`:
  a geometrically reduced subgroup meeting `R_u(G)` trivially maps to `G ⧸ R_u(G)` by a closed
  immersion.
* `TauCeti.FiniteTypeCommHopfAlgCat.isIso_coinvariantsι_unipotentRadical_comp_mkQuotient`:
  if moreover `G` and the subgroup are smooth and connected and the Lie dimension of the subgroup
  is at least that of `G ⧸ R_u(G)`, it maps isomorphically onto `G ⧸ R_u(G)`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorems 5.34 and 16.33(d).
* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), Theorem 10.6.
-/

public section

open CategoryTheory

namespace TauCeti.FiniteTypeCommHopfAlgCat

universe u

variable {k : Type u} [Field k] (G : FiniteTypeCommHopfAlgCat.{u, u} k)

/-- **A geometrically reduced subgroup meeting the unipotent radical trivially maps to
`G ⧸ R_u(G)` by a closed immersion**, for a geometrically reduced `G` over any field. If the
Hopf ideal `J` cuts out a
geometrically reduced subgroup `T` and the composite `T → G → G ⧸ R_u(G)` has trivial kernel,
then its coordinate map `coinvariantsι ≫ mkQuotient G J` is surjective. -/
theorem surjective_coinvariantsι_unipotentRadical_comp_mkQuotient
    [Algebra.IsGeometricallyReduced k G] {J : HopfIdeal k G}
    [Algebra.IsGeometricallyReduced k (quotient G J)]
    (hker : CommHopfAlgCat.kernelHopfIdeal
        (CommHopfAlgCat.coinvariantsι (isNormal_unipotentRadicalDefiningIdeal G) ≫
          CommHopfAlgCat.mkQuotient G.obj J) =
      HopfIdeal.augmentation k (CommHopfAlgCat.quotient G.obj J)) :
    Function.Surjective
      (CommHopfAlgCat.coinvariantsι (isNormal_unipotentRadicalDefiningIdeal G) ≫
        CommHopfAlgCat.mkQuotient G.obj J).hom := by
  let hR := isNormal_unipotentRadicalDefiningIdeal G
  let _ := hR.isHopfSubalgebra_coinvariants.hopfAlgebra
  have : Algebra.FiniteType k (CommHopfAlgCat.coinvariants hR) := hR.finiteType_coinvariants
  exact CommHopfAlgCat.surjective_of_kernelHopfIdeal_eq_augmentation _ hker

/-- **A smooth connected subgroup meeting the unipotent radical trivially, of Lie dimension at
least that of `G ⧸ R_u(G)`, maps isomorphically onto `G ⧸ R_u(G)`**, for a smooth geometrically
connected `G` over any field. If the Hopf ideal `J` cuts out a smooth connected subgroup `T`, the
composite `T → G → G ⧸ R_u(G)` has trivial kernel, and the Lie algebra of `T` has dimension at
least that of `G ⧸ R_u(G)`, then the composite is an isomorphism. -/
theorem isIso_coinvariantsι_unipotentRadical_comp_mkQuotient [Algebra.Smooth k G]
    (hG : geometricallyConnectedCommHopfAlgProperty k G.obj) {J : HopfIdeal k G}
    (hJ_smooth : smoothCommHopfAlgProperty k (CommHopfAlgCat.quotient G.obj J))
    (hJ_connected : ConnectedSpace (PrimeSpectrum (CommHopfAlgCat.quotient G.obj J)))
    (hker : CommHopfAlgCat.kernelHopfIdeal
        (CommHopfAlgCat.coinvariantsι (isNormal_unipotentRadicalDefiningIdeal G) ≫
          CommHopfAlgCat.mkQuotient G.obj J) =
      HopfIdeal.augmentation k (CommHopfAlgCat.quotient G.obj J))
    (hfinrank :
      letI := (isNormal_unipotentRadicalDefiningIdeal G).isHopfSubalgebra_coinvariants.hopfAlgebra
      Module.finrank k
          (Derivation k (CommHopfAlgCat.coinvariants (isNormal_unipotentRadicalDefiningIdeal G))
            (Bialgebra.CounitAlgebra k
              (CommHopfAlgCat.coinvariants (isNormal_unipotentRadicalDefiningIdeal G)) k)) ≤
        Module.finrank k
          (Derivation k (CommHopfAlgCat.quotient G.obj J)
            (Bialgebra.CounitAlgebra k (CommHopfAlgCat.quotient G.obj J) k))) :
    IsIso (CommHopfAlgCat.coinvariantsι (isNormal_unipotentRadicalDefiningIdeal G) ≫
      CommHopfAlgCat.mkQuotient G.obj J) := by
  have hG_red := geometricallyReducedCommHopfAlgProperty_of_smooth k G.obj
    ((smoothCommHopfAlgProperty_iff _).mpr inferInstance)
  have : Algebra.IsGeometricallyReduced k G := hG_red.isGeometricallyReduced
  let hR := isNormal_unipotentRadicalDefiningIdeal G
  let _ := hR.isHopfSubalgebra_coinvariants.hopfAlgebra
  have : Algebra.FiniteType k (CommHopfAlgCat.coinvariants hR) := hR.finiteType_coinvariants
  -- `O(G ⧸ R_u(G))` is a Hopf subalgebra of `O(G)`, so it inherits geometric reducedness
  -- (hence smoothness) and geometric connectedness from `G`.
  have hinj : Function.Injective (CommHopfAlgCat.coinvariantsι hR).hom.toAlgHom :=
    CommHopfAlgCat.hopfSubalgebraι_injective hR.isHopfSubalgebra_coinvariants
  have hQ_smooth : smoothCommHopfAlgProperty k (CommHopfAlgCat.coinvariants hR) :=
    smoothCommHopfAlgProperty_of_geometricallyReduced k _
      (geometricallyReducedCommHopfAlgProperty.of_injective _ hinj hG_red)
  exact CommHopfAlgCat.isIso_of_kernelHopfIdeal_eq_augmentation_of_finrank_le _
    hQ_smooth
    (geometricallyConnectedCommHopfAlgProperty.of_injective _ hinj hG).connectedSpace
    hJ_smooth hJ_connected hker hfinrank

end TauCeti.FiniteTypeCommHopfAlgCat
