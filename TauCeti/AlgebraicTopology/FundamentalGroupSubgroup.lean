/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

/-!
# Subgroups of the fundamental group under basepoint change

The classification of connected covers records, for a pointed cover, a subgroup of
`π₁(X, x₀)`. Changing the basepoint along a path transports this subgroup by the usual
basepoint-change isomorphism. This file packages that transport, together with the membership,
order/lattice, and normality API needed by the universal-covers roadmap's pointed/unpointed
bookkeeping.

Mathlib already provides the basepoint-change equivalence
`FundamentalGroup.fundamentalGroupMulEquivOfPath`; the declarations here are only the
subgroup-level spelling of mapping a subgroup along that equivalence.

## Main declarations

* `TauCeti.FundamentalGroup.basepointChangeSubgroupOrderIso`: the order isomorphism between the
  subgroup lattices of `π₁(X, x₀)` and `π₁(X, x₁)` induced by the basepoint-change equivalence.
* `TauCeti.FundamentalGroup.basepointChangeSubgroup`: transport a subgroup of `π₁(X, x₀)`
  to a subgroup of `π₁(X, x₁)` along a path from `x₀` to `x₁`.
* `TauCeti.FundamentalGroup.basepointChangeSubgroupEquiv`: the induced multiplicative
  equivalence between the original subgroup and its transported subgroup.
* `TauCeti.FundamentalGroup.normal_basepointChangeSubgroup_iff`: normality is invariant under
  basepoint change.

## References

This supplies a small algebraic prerequisite for `TauCetiRoadmap/UniversalCovers/README.md`,
Stage 2, items 7 and 8: the recovered subgroup of a pointed cover transforms by conjugacy under
basepoint change, and unpointed connected covers are classified by conjugacy classes of
subgroups.
-/

public section

noncomputable section

namespace TauCeti

namespace FundamentalGroup

open scoped FundamentalGroupoid

variable {X : Type*} [TopologicalSpace X] {x₀ x₁ x₂ : X}

/-- The order isomorphism between the subgroup lattices of `π₁(X, x₀)` and `π₁(X, x₁)`
induced by the basepoint-change equivalence along a path from `x₀` to `x₁`. -/
@[expose]
def basepointChangeSubgroupOrderIso (γ : Path x₀ x₁) :
    Subgroup (_root_.FundamentalGroup X x₀) ≃o Subgroup (_root_.FundamentalGroup X x₁) :=
  (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ).mapSubgroup

/-- Transport a subgroup of `π₁(X, x₀)` to a subgroup of `π₁(X, x₁)` along a path from `x₀`
to `x₁`. This is the application of `basepointChangeSubgroupOrderIso`, packaged as a `def` so
consumers go through the membership and order/lattice API below rather than unfolding to
`Subgroup.map`. -/
@[expose]
def basepointChangeSubgroup (γ : Path x₀ x₁)
    (H : Subgroup (_root_.FundamentalGroup X x₀)) :
    Subgroup (_root_.FundamentalGroup X x₁) :=
  basepointChangeSubgroupOrderIso γ H

/-- The basepoint-change order isomorphism agrees with subgroup transport. -/
lemma basepointChangeSubgroupOrderIso_apply (γ : Path x₀ x₁)
    (H : Subgroup (_root_.FundamentalGroup X x₀)) :
    basepointChangeSubgroupOrderIso γ H = basepointChangeSubgroup γ H :=
  rfl

/-- Subgroup transport is the image of the subgroup under the basepoint-change equivalence. -/
lemma basepointChangeSubgroup_eq_map (γ : Path x₀ x₁)
    (H : Subgroup (_root_.FundamentalGroup X x₀)) :
    basepointChangeSubgroup γ H =
      H.map (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ : _ →* _) :=
  rfl

/-- Membership in a basepoint-changed subgroup, expressed by transporting back along the
inverse basepoint-change equivalence. -/
@[simp]
lemma mem_basepointChangeSubgroup_iff (γ : Path x₀ x₁)
    (H : Subgroup (_root_.FundamentalGroup X x₀)) (η : _root_.FundamentalGroup X x₁) :
    η ∈ basepointChangeSubgroup γ H ↔
      (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ).symm η ∈ H := by
  rw [basepointChangeSubgroup_eq_map]
  exact Subgroup.mem_map_equiv

/-- The image of an element of `H` under basepoint change lies in the transported subgroup. -/
@[simp]
lemma fundamentalGroupMulEquivOfPath_mem_basepointChangeSubgroup (γ : Path x₀ x₁)
    (H : Subgroup (_root_.FundamentalGroup X x₀)) (η : _root_.FundamentalGroup X x₀)
    (hη : η ∈ H) :
    _root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ η ∈
      basepointChangeSubgroup γ H := by
  rw [basepointChangeSubgroup_eq_map]
  exact Subgroup.mem_map_of_mem _ hη

/-- The basepoint-change equivalence restricts to an equivalence from a subgroup to its
transported subgroup. Packaged as a `def` so consumers use the coercion lemmas below rather
than unfolding to `MulEquiv.subgroupMap`. -/
@[expose]
def basepointChangeSubgroupEquiv (γ : Path x₀ x₁)
    (H : Subgroup (_root_.FundamentalGroup X x₀)) :
    H ≃* basepointChangeSubgroup γ H :=
  (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ).subgroupMap H

/-- On underlying loop classes, the subgroup equivalence is the usual basepoint-change
equivalence. -/
@[simp]
lemma basepointChangeSubgroupEquiv_apply_coe (γ : Path x₀ x₁)
    (H : Subgroup (_root_.FundamentalGroup X x₀)) (η : H) :
    (basepointChangeSubgroupEquiv γ H η : _root_.FundamentalGroup X x₁) =
      _root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ η.1 :=
  rfl

/-- The inverse subgroup equivalence is the inverse basepoint-change equivalence on underlying
loop classes. -/
@[simp]
lemma basepointChangeSubgroupEquiv_symm_apply_coe (γ : Path x₀ x₁)
    (H : Subgroup (_root_.FundamentalGroup X x₀)) (η : basepointChangeSubgroup γ H) :
    ((basepointChangeSubgroupEquiv γ H).symm η : _root_.FundamentalGroup X x₀) =
      (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ).symm η.1 :=
  rfl

/-- Transporting the bottom subgroup along basepoint change gives the bottom subgroup. -/
@[simp]
lemma basepointChangeSubgroup_bot (γ : Path x₀ x₁) :
    basepointChangeSubgroup γ (⊥ : Subgroup (_root_.FundamentalGroup X x₀)) = ⊥ := by
  rw [basepointChangeSubgroup_eq_map]
  exact Subgroup.map_bot
    (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ).toMonoidHom

/-- Transporting the top subgroup along basepoint change gives the top subgroup. -/
@[simp]
lemma basepointChangeSubgroup_top (γ : Path x₀ x₁) :
    basepointChangeSubgroup γ (⊤ : Subgroup (_root_.FundamentalGroup X x₀)) = ⊤ := by
  rw [basepointChangeSubgroup_eq_map]
  exact Subgroup.map_top_of_surjective
    (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ).toMonoidHom
    (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ).surjective

/-- Basepoint-change transport is monotone on subgroups. -/
lemma basepointChangeSubgroup_mono (γ : Path x₀ x₁)
    {H K : Subgroup (_root_.FundamentalGroup X x₀)} (hHK : H ≤ K) :
    basepointChangeSubgroup γ H ≤ basepointChangeSubgroup γ K := by
  simp only [basepointChangeSubgroup_eq_map]
  exact Subgroup.map_mono hHK

/-- Inclusion of basepoint-changed subgroups can be checked before transport. -/
@[simp]
lemma basepointChangeSubgroup_le_basepointChangeSubgroup_iff (γ : Path x₀ x₁)
    (H K : Subgroup (_root_.FundamentalGroup X x₀)) :
    basepointChangeSubgroup γ H ≤ basepointChangeSubgroup γ K ↔ H ≤ K := by
  rw [← basepointChangeSubgroupOrderIso_apply γ H, ← basepointChangeSubgroupOrderIso_apply γ K]
  exact (basepointChangeSubgroupOrderIso γ).le_iff_le

/-- Basepoint-change transport is injective on subgroups. -/
lemma basepointChangeSubgroup_injective (γ : Path x₀ x₁) :
    Function.Injective (basepointChangeSubgroup γ :
      Subgroup (_root_.FundamentalGroup X x₀) → Subgroup (_root_.FundamentalGroup X x₁)) := by
  intro H K hHK
  apply le_antisymm
  · exact (basepointChangeSubgroup_le_basepointChangeSubgroup_iff γ H K).mp (hHK.le)
  · exact (basepointChangeSubgroup_le_basepointChangeSubgroup_iff γ K H).mp (hHK.ge)

/-- Basepoint-change transport preserves finite intersections of subgroups. -/
@[simp]
lemma basepointChangeSubgroup_inf (γ : Path x₀ x₁)
    (H K : Subgroup (_root_.FundamentalGroup X x₀)) :
    basepointChangeSubgroup γ (H ⊓ K) =
      basepointChangeSubgroup γ H ⊓ basepointChangeSubgroup γ K := by
  simp only [basepointChangeSubgroup_eq_map]
  exact Subgroup.map_inf H K
    (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ).toMonoidHom
    (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ).injective

/-- Basepoint-change transport preserves joins of subgroups. -/
@[simp]
lemma basepointChangeSubgroup_sup (γ : Path x₀ x₁)
    (H K : Subgroup (_root_.FundamentalGroup X x₀)) :
    basepointChangeSubgroup γ (H ⊔ K) =
      basepointChangeSubgroup γ H ⊔ basepointChangeSubgroup γ K := by
  simp only [basepointChangeSubgroup_eq_map]
  exact Subgroup.map_sup H K
    (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ).toMonoidHom

/-- Basepoint-change transport preserves arbitrary joins of subgroups. -/
@[simp]
lemma basepointChangeSubgroup_iSup {ι : Sort*} (γ : Path x₀ x₁)
    (H : ι → Subgroup (_root_.FundamentalGroup X x₀)) :
    basepointChangeSubgroup γ (⨆ i, H i) = ⨆ i, basepointChangeSubgroup γ (H i) := by
  simp only [basepointChangeSubgroup_eq_map]
  exact Subgroup.map_iSup
    (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ).toMonoidHom H

/-- A subgroup is normal exactly when its basepoint-changed subgroup is normal. -/
lemma normal_basepointChangeSubgroup_iff (γ : Path x₀ x₁)
    (H : Subgroup (_root_.FundamentalGroup X x₀)) :
    (basepointChangeSubgroup γ H).Normal ↔ H.Normal := by
  rw [basepointChangeSubgroup_eq_map]
  exact MulEquiv.normal_map_iff

end FundamentalGroup

end TauCeti

end
