/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.ComparisonDegreeTwo
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Conjugation.AllDegrees
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Conjugation.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ContinuousCohomologyIso

/-!
# Conjugation in low degrees: the explicit model against the canonical object

Let `M` be a discrete `G`-module and `U`, `V = gUg⁻¹` conjugate subgroups of `G`. The all-degree
conjugation `(g)_* : Hⁿ(U, M) ⟶ Hⁿ(V, M)` of `Conjugation/AllDegrees.lean` is the map of the
compatible pair `(v ↦ g⁻¹ v g, g • ·)` on Mathlib's canonical continuous cohomology. On the
explicit inhomogeneous complex the same pair pulls a cochain `c` back to
`(v₁, …, vₙ) ↦ g • c (g⁻¹ v₁ g, …, g⁻¹ vₙ g)`. This file proves that the comparison isomorphisms
between the explicit `H⁰`, `H¹`, `H²` and the canonical objects carry the one to the other, so
that a computation of `(g)_*` on explicit cocycles is a computation on canonical classes.

For a normal subgroup `N`, `(g)_*` is the endomorphism `conjNormalMap` of `Hⁿ(N, M)`, and in
degree one the explicit side is the conjugation action `g • x = explicitConj1 N g x` on the
explicit `H¹(N, M)`, the action of `G ⧸ N` that the inflation-restriction sequence uses
(`TauCeti.ContCohomology.explicitIso_conjNormalMap`).

## Main results

* `TauCeti.ContCohomology.explicitH0Iso_conjMap`, `TauCeti.ContCohomology.explicitIso_conjMap`,
  `TauCeti.ContCohomology.explicitIso_conjMap2`: in degrees `0`, `1` and `2`, the comparison
  carries the explicit pullback along the conjugation pair to `conjMap`.
* `TauCeti.ContCohomology.explicitIso_conjNormalMap`: in degree one, for a normal subgroup, the
  comparison carries the explicit conjugation action `g • x` to `conjNormalMap`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  Chapter I, §5, for the conjugation maps on inhomogeneous cochains.
-/

public section

open CategoryTheory

namespace TauCeti.ContCohomology

open TauCeti.ContinuousCohomology

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (U V : Subgroup G) (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M]

/-- **Conjugation in degree zero.** The comparison `H⁰ ≅ continuousCohomology 0` carries the
explicit map `M^U → M^V`, `m ↦ g • m`, of the conjugation pair to `conjMap`. -/
@[simp]
theorem explicitH0Iso_conjMap (g : G) (hVU : V = U.map (MulAut.conj g).toMonoidHom)
    (x : H0 U M) :
    conjMap U V M g hVU 0 ((explicitH0IsoContinuousCohomology U M).hom x) =
      (explicitH0IsoContinuousCohomology V M).hom
        (explicitMap0 U M (conjHom U V g hVU : V →* U) (DistribSMul.toAddMonoidHom M g)
          (conjHom_smul U V g hVU) x) := by
  rw [conjMap_def, conjPair_def]
  exact explicitH0Iso_map U M V M (conjHom U V g hVU) (DistribSMul.toAddMonoidHom M g)
    (conjHom_smul U V g hVU) x

variable [ContinuousSMul G M] [CompactSpace U] [CompactSpace V]

/-- **Conjugation in degree one.** The comparison `H¹ ≅ continuousCohomology 1` carries the
explicit pullback along the conjugation pair, which sends a cocycle `c` to `v ↦ g • c (g⁻¹ v g)`,
to `conjMap`. -/
@[simp]
theorem explicitIso_conjMap (g : G) (hVU : V = U.map (MulAut.conj g).toMonoidHom)
    (x : DiscreteH1 U M) :
    conjMap U V M g hVU 1 ((explicitH1IsoContinuousCohomology U M).hom x) =
      (explicitH1IsoContinuousCohomology V M).hom
        ((discreteH1Equiv V M).symm
          (explicitMap1 U M V M (conjHom U V g hVU) (DistribSMul.toAddMonoidHom M g)
            continuous_of_discreteTopology (conjHom_smul U V g hVU)
            (discreteH1Equiv U M x))) := by
  rw [conjMap_def, conjPair_def]
  exact explicitIso_map U M V M (conjHom U V g hVU) (DistribSMul.toAddMonoidHom M g)
    (conjHom_smul U V g hVU) x

/-- **Conjugation in degree two.** The comparison `H² ≅ continuousCohomology 2` carries the
explicit pullback along the conjugation pair, which sends a cocycle `c` to
`(v, w) ↦ g • c (g⁻¹ v g, g⁻¹ w g)`, to `conjMap`. -/
@[simp]
theorem explicitIso_conjMap2 (g : G) (hVU : V = U.map (MulAut.conj g).toMonoidHom)
    (x : DiscreteH2 U M) :
    conjMap U V M g hVU 2 ((explicitH2IsoContinuousCohomology U M).hom x) =
      (explicitH2IsoContinuousCohomology V M).hom
        ((discreteH2Equiv V M).symm
          (explicitMap2 U M V M (conjHom U V g hVU) (DistribSMul.toAddMonoidHom M g)
            continuous_of_discreteTopology (conjHom_smul U V g hVU)
            (discreteH2Equiv U M x))) := by
  rw [conjMap_def, conjPair_def]
  exact explicitIso_map2 U M V M (conjHom U V g hVU) (DistribSMul.toAddMonoidHom M g)
    (conjHom_smul U V g hVU) x

/-- **Conjugation on a normal subgroup in degree one.** For a normal subgroup `N`, the comparison
`H¹ ≅ continuousCohomology 1` carries the explicit conjugation action `x ↦ g • x` on `H¹(N, M)`,
which is `TauCeti.ContCohomology.explicitConj1`, to `conjNormalMap`. -/
@[simp]
theorem explicitIso_conjNormalMap (N : Subgroup G) [N.Normal] [CompactSpace N] (g : G)
    (x : DiscreteH1 N M) :
    conjNormalMap N M g 1 ((explicitH1IsoContinuousCohomology N M).hom x) =
      (explicitH1IsoContinuousCohomology N M).hom
        ((discreteH1Equiv N M).symm (g • discreteH1Equiv N M x)) := by
  have hN : N = N.map (MulAut.conj g).toMonoidHom := (Subgroup.Normal.map_conj_eq N g).symm
  rw [← conjMap_eq_conjNormalMap N M g hN, explicitIso_conjMap N N M g hN x]
  congr 2
  -- Both sides pull a cocycle back along `v ↦ g⁻¹ v g`, presented once as `conjHom` and once as
  -- `Subgroup.inverseConjugationHom`; the two continuous homomorphisms are equal.
  have hφ : conjHom N N g hN = N.inverseConjugationHom g :=
    ContinuousMonoidHom.ext fun v => Subtype.ext (by simp)
  rw [explicitMap1_congr_of_eq (hq := continuous_of_discreteTopology)
    (hψ := N.inverseConjugationHom_smul g) (hφeq := hφ) (hfeq := rfl)]
  induction discreteH1Equiv N M x using QuotientAddGroup.induction_on with
  | H c => exact (explicitMap1_mk N M N M _ _ _ _ c).trans (smul_mk N g c).symm

end TauCeti.ContCohomology
