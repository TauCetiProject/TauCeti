/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.FiniteType
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.ClosedImmersion

/-!
# Subgroups mapping isomorphically onto a quotient by a normal subgroup

Let `G` be an affine group of finite type over a field `k`, let `N` be a normal closed subgroup,
cut out by a normal Hopf ideal `I`, and let `T` be a closed subgroup of `G`, cut out by a Hopf
ideal `J`. This file proves that if `G` and `T` are geometrically reduced and the composite
`T → G → G ⧸ N` has trivial scheme-theoretic kernel, then it is a closed immersion. If moreover
`G` is smooth and geometrically connected, `T` is smooth and connected, and the Lie algebra of
`T` has dimension at least that of `G ⧸ N`, then the composite is an isomorphism.

Coordinate rings reverse arrows: `O(G ⧸ N)` is the Hopf subalgebra of right coinvariants, and
the composite is the coordinate map `coinvariantsι ≫ mkQuotient G J`. The main case is
`N = R_u(G)`, taking `I := unipotentRadicalDefiningIdeal G` and
`hI := isNormal_unipotentRadicalDefiningIdeal G`.

## Main declarations

* `TauCeti.FiniteTypeCommHopfAlgCat.coinvariantsι_comp_mkQuotient_surjective`: a geometrically
  reduced subgroup meeting `N` trivially maps to `G ⧸ N` by a closed immersion.
* `TauCeti.FiniteTypeCommHopfAlgCat.isIso_coinvariantsι_comp_mkQuotient`: if moreover `G` and the
  subgroup are smooth and connected and the Lie dimension of the subgroup is at least that of
  `G ⧸ N`, it maps isomorphically onto `G ⧸ N`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 5.34.
-/

public section

open CategoryTheory

namespace TauCeti.FiniteTypeCommHopfAlgCat

universe u

variable {k : Type u} [Field k] (G : FiniteTypeCommHopfAlgCat.{u, u} k)

/-- **A geometrically reduced subgroup meeting a normal subgroup `N` trivially maps to `G ⧸ N`
by a closed immersion**, for a geometrically reduced `G` over any field. If the Hopf ideal `J`
cuts out a geometrically reduced subgroup `T`, the normal Hopf ideal `I` cuts out `N`, and the
composite `T → G → G ⧸ N` has trivial kernel,
then its coordinate map `coinvariantsι ≫ mkQuotient G J` is surjective. -/
theorem coinvariantsι_comp_mkQuotient_surjective
    [Algebra.IsGeometricallyReduced k G] {I : HopfIdeal k G} (hI : I.IsNormal)
    {J : HopfIdeal k G}
    [Algebra.IsGeometricallyReduced k (quotient G J)]
    (hker : CommHopfAlgCat.kernelHopfIdeal
        (CommHopfAlgCat.coinvariantsι hI ≫
          CommHopfAlgCat.mkQuotient G.obj J) =
      HopfIdeal.augmentation k (CommHopfAlgCat.quotient G.obj J)) :
    Function.Surjective
      (CommHopfAlgCat.coinvariantsι hI ≫
        CommHopfAlgCat.mkQuotient G.obj J).hom := by
  let _ := hI.isHopfSubalgebra_coinvariants.hopfAlgebra
  have : Algebra.FiniteType k (CommHopfAlgCat.coinvariants hI) := hI.finiteType_coinvariants
  exact CommHopfAlgCat.surjective_of_kernelHopfIdeal_eq_augmentation _ hker

/-- **A smooth connected subgroup meeting a normal subgroup `N` trivially, of Lie dimension at
least that of `G ⧸ N`, maps isomorphically onto `G ⧸ N`**, for a smooth geometrically connected
`G` over any field. If the Hopf ideal `J` cuts out a smooth connected subgroup `T`, the normal
Hopf ideal `I` cuts out `N`, the composite `T → G → G ⧸ N` has trivial kernel, and the Lie
algebra of `T` has dimension at least that of `G ⧸ N`, then the composite is an isomorphism. -/
theorem isIso_coinvariantsι_comp_mkQuotient [Algebra.Smooth k G]
    (hG : geometricallyConnectedCommHopfAlgProperty k G.obj) {I : HopfIdeal k G}
    (hI : I.IsNormal) {J : HopfIdeal k G}
    (hJ_smooth : smoothCommHopfAlgProperty k (CommHopfAlgCat.quotient G.obj J))
    (hJ_connected : ConnectedSpace (PrimeSpectrum (CommHopfAlgCat.quotient G.obj J)))
    (hker : CommHopfAlgCat.kernelHopfIdeal
        (CommHopfAlgCat.coinvariantsι hI ≫
          CommHopfAlgCat.mkQuotient G.obj J) =
      HopfIdeal.augmentation k (CommHopfAlgCat.quotient G.obj J))
    (hfinrank :
      letI := hI.isHopfSubalgebra_coinvariants.hopfAlgebra
      Module.finrank k
          (Derivation k (CommHopfAlgCat.coinvariants hI)
            (Bialgebra.CounitAlgebra k
              (CommHopfAlgCat.coinvariants hI) k)) ≤
        Module.finrank k
          (Derivation k (CommHopfAlgCat.quotient G.obj J)
            (Bialgebra.CounitAlgebra k (CommHopfAlgCat.quotient G.obj J) k))) :
    IsIso (CommHopfAlgCat.coinvariantsι hI ≫
      CommHopfAlgCat.mkQuotient G.obj J) := by
  have hG_red := geometricallyReducedCommHopfAlgProperty_of_smooth k G.obj
    ((smoothCommHopfAlgProperty_iff _).mpr inferInstance)
  have : Algebra.IsGeometricallyReduced k G := hG_red.isGeometricallyReduced
  let _ := hI.isHopfSubalgebra_coinvariants.hopfAlgebra
  have : Algebra.FiniteType k (CommHopfAlgCat.coinvariants hI) := hI.finiteType_coinvariants
  -- `O(G ⧸ N)` is a Hopf subalgebra of `O(G)`, so it inherits geometric reducedness
  -- (hence smoothness) and geometric connectedness from `G`.
  have hinj : Function.Injective (CommHopfAlgCat.coinvariantsι hI).hom.toAlgHom :=
    CommHopfAlgCat.hopfSubalgebraι_injective hI.isHopfSubalgebra_coinvariants
  have hQ_smooth : smoothCommHopfAlgProperty k (CommHopfAlgCat.coinvariants hI) :=
    smoothCommHopfAlgProperty_of_geometricallyReduced k _
      (geometricallyReducedCommHopfAlgProperty.of_injective _ hinj hG_red)
  exact CommHopfAlgCat.isIso_of_kernelHopfIdeal_eq_augmentation_of_finrank_le _
    hQ_smooth
    (geometricallyConnectedCommHopfAlgProperty.of_injective _ hinj hG).connectedSpace
    hJ_smooth hJ_connected hker hfinrank

end TauCeti.FiniteTypeCommHopfAlgCat
