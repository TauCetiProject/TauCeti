/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.GroupCohomologyIso.Basic
import TauCeti.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# Compatible pairs in the explicit-to-algebraic cohomology comparison

For discrete groups `G` and `H`, the explicit low-degree cohomology groups are Mathlib's
`groupCohomology` of `Rep.ofDistribMulAction ℤ`, through `explicitH0IsoGroupCohomology`,
`explicitH1IsoGroupCohomology` and `explicitH2IsoGroupCohomology`. This file proves that these
comparisons carry the explicit compatible-pair maps `explicitMap0`, `explicitMap1` and
`explicitMap2` to Mathlib's `groupCohomology.map`.

A compatible pair consists of a group homomorphism `φ : H → G` and an additive map `f : M →+ N`
with `f (φ h • m) = h • f m`. On the algebraic side it is a morphism of representations
`F : Rep.res φ (Rep.ofDistribMulAction ℤ G M) ⟶ Rep.ofDistribMulAction ℤ H N`. The statements
take any such `F` whose underlying function is `f`, so that a consumer may build `F` in whatever
form its own representations come in.

The equations are the discrete-group counterparts of the comparisons of the explicit groups with
canonical continuous cohomology along compatible pairs,
`TauCeti.ContCohomology.explicitH1AddEquivContinuousCohomology_map` and its siblings. They are what
transports an operation defined by compatible pairs, such as the transition maps of the
finite-quotient system, from one description to the other.

## Main statements

* `TauCeti.ContCohomology.explicitH0IsoGroupCohomology_map`,
  `TauCeti.ContCohomology.explicitH1IsoGroupCohomology_map` and
  `TauCeti.ContCohomology.explicitH2IsoGroupCohomology_map`: the comparison in degrees zero, one
  and two intertwines `groupCohomology.map` with the explicit compatible-pair map.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. I, §5, for
  the functoriality of cohomology in compatible pairs.
-/

public section

open CategoryTheory groupCohomology

namespace TauCeti.ContCohomology

section Degree0

variable {G H : Type} [Group G] [Group H] {M N : Type} [AddCommGroup M] [DistribMulAction G M]
  [AddCommGroup N] [DistribMulAction H N]
  (φ : H →* G) (f : M →+ N) (hφf : ∀ (h : H) (m : M), f (φ h • m) = h • f m)
  (F : Rep.res φ (Rep.ofDistribMulAction ℤ G M) ⟶ Rep.ofDistribMulAction ℤ H N)
  (hF : ∀ m, F.hom m = f m)

include hF in
/-- The degree-zero comparison with `groupCohomology` carries the explicit compatible-pair map
`explicitMap0` to `groupCohomology.map`. -/
theorem explicitH0IsoGroupCohomology_map (x : H0 G M) :
    groupCohomology.map φ F 0 (explicitH0IsoGroupCohomology G M x) =
      explicitH0IsoGroupCohomology H N (explicitMap0 G M φ f hφf x) := by
  rw [explicitH0IsoGroupCohomology_apply, explicitH0IsoGroupCohomology_apply]
  -- Both sides are compared inside the coefficients `N`, after `H0Iso` and the inclusion of the
  -- invariants, which are injective.
  apply ConcreteCategory.injective_of_mono_of_preservesPullback (H0Iso _).hom
  rw [Iso.inv_hom_id_apply]
  apply ConcreteCategory.injective_of_mono_of_preservesPullback (shortComplexH0 _).f
  rw [map_H0Iso_hom_f_apply, Iso.inv_hom_id_apply, hF]
  simp only [shortComplexH0_f, ModuleCat.hom_ofHom, Submodule.coe_subtype, H0AddEquivInvariants_val]
  exact ((H0AddEquivInvariants_val H N _).trans (coe_explicitMap0 G M φ f hφf x)).symm

end Degree0

section PositiveDegree

variable {G H : Type} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [Group H] [TopologicalSpace H] [DiscreteTopology H]
  {M N : Type} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]
  [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
  [DistribMulAction H N] [ContinuousSMul H N]
  (φ : H →ₜ* G) (f : M →+ N) (hf : Continuous f)
  (hφf : ∀ (h : H) (m : M), f (φ h • m) = h • f m)
  (F : Rep.res (φ : H →* G) (Rep.ofDistribMulAction ℤ G M) ⟶ Rep.ofDistribMulAction ℤ H N)
  (hF : ∀ m, F.hom m = f m)

include hF in
/-- The degree-one comparison with `groupCohomology` carries the explicit compatible-pair map
`explicitMap1` to `groupCohomology.map`. -/
theorem explicitH1IsoGroupCohomology_map (x : H1 G M) :
    groupCohomology.map (φ : H →* G) F 1 (explicitH1IsoGroupCohomology G M x) =
      explicitH1IsoGroupCohomology H N (explicitMap1 G M H N φ f hf hφf x) := by
  induction x using QuotientAddGroup.induction_on with
  | H z =>
    rw [explicitMap1_mk, explicitH1IsoGroupCohomology_mk, explicitH1IsoGroupCohomology_mk,
      H1π_comp_map_apply]
    refine congrArg _ (cocycles₁_ext fun h ↦ ?_)
    rw [TauCeti.groupCohomology.mapCocycles₁_apply, Z1AddEquivCocycles₁_coe,
      Z1AddEquivCocycles₁_coe, cocyclesMap1_apply]
    exact hF _

include hF in
/-- The degree-two comparison with `groupCohomology` carries the explicit compatible-pair map
`explicitMap2` to `groupCohomology.map`. -/
theorem explicitH2IsoGroupCohomology_map (x : H2 G M) :
    groupCohomology.map (φ : H →* G) F 2 (explicitH2IsoGroupCohomology G M x) =
      explicitH2IsoGroupCohomology H N (explicitMap2 G M H N φ f hf hφf x) := by
  induction x using QuotientAddGroup.induction_on with
  | H z =>
    rw [explicitMap2_mk, explicitH2IsoGroupCohomology_mk, explicitH2IsoGroupCohomology_mk,
      H2π_comp_map_apply]
    refine congrArg _ (cocycles₂_ext fun h k ↦ ?_)
    rw [TauCeti.groupCohomology.mapCocycles₂_apply, Z2AddEquivCocycles₂_coe,
      Z2AddEquivCocycles₂_coe, cocyclesMap2_apply]
    exact hF _

end PositiveDegree

end TauCeti.ContCohomology
