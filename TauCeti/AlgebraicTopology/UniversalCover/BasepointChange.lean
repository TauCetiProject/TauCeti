/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import TauCeti.Algebra.Group.NormalizerQuotientConjugation

/-!
# Basepoint change for fundamental-group subgroups

The pointed classification of connected covers records a subgroup of the fundamental group at
a chosen basepoint. Changing the basepoint along a path transports that subgroup by the
standard path-conjugation isomorphism of fundamental groups. This file packages that transport
and the induced transport of the normalizer quotient `N(H) / H` used for deck groups of covers
attached to subgroups.

Mathlib already supplies the fundamental-group isomorphism
`FundamentalGroup.fundamentalGroupMulEquivOfPath`; the declarations here are only the
subgroup and normalizer-quotient bookkeeping needed by the universal-covers roadmap.

## Main declarations

* `TauCeti.FundamentalGroup.basepointChangeSubgroup`: transport a subgroup of `π₁(X, x₀)`
  along a path `γ : Path x₀ x₁`.
* `TauCeti.FundamentalGroup.basepointChangeNormalizerQuotientEquiv`: the corresponding
  isomorphism `N(H) / H ≃* N(γ₊H) / γ₊H`.
* Representative simp lemmas for both constructions.

## References

This supplies a small prerequisite for `TauCetiRoadmap/UniversalCovers/README.md`, Stage 2,
items 7 and 8: the pointed cover attached to `H ≤ π₁(X, x₀)`, conjugacy under basepoint
change, and the normalizer quotient `N(H) / H` appearing as the deck group of that cover.
-/

public section

namespace TauCeti

namespace FundamentalGroup

variable {X : Type*} [TopologicalSpace X] {x₀ x₁ : X}

/-- The subgroup of `π₁(X, x₁)` obtained from `H ≤ π₁(X, x₀)` by changing basepoint along a
path `γ : Path x₀ x₁`. This is the subgroup-level form of conjugating loops by `γ`. -/
noncomputable abbrev basepointChangeSubgroup (γ : Path x₀ x₁)
    (H : Subgroup (_root_.FundamentalGroup X x₀)) :
    Subgroup (_root_.FundamentalGroup X x₁) :=
  H.map (((_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ) :
    _root_.FundamentalGroup X x₀ →* _root_.FundamentalGroup X x₁))

/-- Membership in the basepoint-changed subgroup is witnessed by a loop in the original
subgroup whose image under path-conjugation is the target loop. -/
lemma mem_basepointChangeSubgroup_iff (γ : Path x₀ x₁)
    (H : Subgroup (_root_.FundamentalGroup X x₀)) (η : _root_.FundamentalGroup X x₁) :
    η ∈ basepointChangeSubgroup γ H ↔
      ∃ ζ ∈ H, _root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ ζ = η :=
  Iff.rfl

/-- A loop in `H` maps into the basepoint-changed subgroup. -/
@[simp]
lemma fundamentalGroupMulEquivOfPath_mem_basepointChangeSubgroup (γ : Path x₀ x₁)
    (H : Subgroup (_root_.FundamentalGroup X x₀)) (ζ : _root_.FundamentalGroup X x₀) :
    _root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ ζ ∈
      basepointChangeSubgroup γ H ↔ ζ ∈ H := by
  constructor
  · rintro ⟨η, hη, hηζ⟩
    have hη_eq : η = ζ :=
      (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ).injective hηζ
    simpa [hη_eq] using hη
  · intro hζ
    exact ⟨ζ, hζ, rfl⟩

/-- The basepoint-change equivalence identifies a subgroup with its transported subgroup. -/
@[expose] noncomputable def basepointChangeSubgroupEquiv (γ : Path x₀ x₁)
    (H : Subgroup (_root_.FundamentalGroup X x₀)) :
    H ≃* basepointChangeSubgroup γ H :=
  (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ).subgroupMap H

/-- On underlying loops, the subgroup equivalence induced by basepoint change is Mathlib's
path-conjugation equivalence. -/
@[simp]
lemma basepointChangeSubgroupEquiv_apply_coe (γ : Path x₀ x₁)
    (H : Subgroup (_root_.FundamentalGroup X x₀)) (ζ : H) :
    (basepointChangeSubgroupEquiv γ H ζ : _root_.FundamentalGroup X x₁) =
      _root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ (ζ : _root_.FundamentalGroup X x₀) :=
  by simp [basepointChangeSubgroupEquiv]

/-- The inverse subgroup equivalence induced by basepoint change applies the inverse
path-conjugation equivalence on loops. -/
@[simp]
lemma basepointChangeSubgroupEquiv_symm_apply_coe (γ : Path x₀ x₁)
    (H : Subgroup (_root_.FundamentalGroup X x₀))
    (η : basepointChangeSubgroup γ H) :
    ((basepointChangeSubgroupEquiv γ H).symm η : _root_.FundamentalGroup X x₀) =
      (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ).symm
        (η : _root_.FundamentalGroup X x₁) :=
  by simp [basepointChangeSubgroupEquiv]

/-- The normalizer quotient `N(H) / H` transported along a basepoint-change path. -/
noncomputable abbrev basepointChangeNormalizerQuotientEquiv (γ : Path x₀ x₁)
    (H : Subgroup (_root_.FundamentalGroup X x₀)) :
    Subgroup.normalizerQuotient H ≃*
      Subgroup.normalizerQuotient (basepointChangeSubgroup γ H) :=
  Subgroup.normalizerQuotientEquivMap H
    (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ)

/-- On normalizer representatives, basepoint change applies the path-conjugation equivalence. -/
@[simp]
lemma basepointChangeNormalizerQuotientEquiv_mk (γ : Path x₀ x₁)
    (H : Subgroup (_root_.FundamentalGroup X x₀))
    (ζ : _root_.Subgroup.normalizer (H : Set (_root_.FundamentalGroup X x₀))) :
    basepointChangeNormalizerQuotientEquiv γ H
        (Subgroup.normalizerQuotientMk H ζ) =
      Subgroup.normalizerQuotientMk (basepointChangeSubgroup γ H)
        (Subgroup.normalizerEquivMap H
          (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ) ζ) :=
  Subgroup.normalizerQuotientEquivMap_mk H
    (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ) ζ

/-- On underlying loops, the transported normalizer representative is the basepoint-changed
loop. -/
lemma basepointChangeNormalizerQuotientEquiv_mk_coe (γ : Path x₀ x₁)
    (H : Subgroup (_root_.FundamentalGroup X x₀))
    (ζ : _root_.Subgroup.normalizer (H : Set (_root_.FundamentalGroup X x₀))) :
    basepointChangeNormalizerQuotientEquiv γ H
        (Subgroup.normalizerQuotientMk H ζ) =
      Subgroup.normalizerQuotientMk (basepointChangeSubgroup γ H)
        ⟨_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ
            (ζ : _root_.FundamentalGroup X x₀), by
          rw [← Subgroup.normalizerEquivMap_apply_coe H
            (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ) ζ]
          exact (Subgroup.normalizerEquivMap H
            (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ) ζ).2⟩ := by
  exact Subgroup.normalizerQuotientEquivMap_mk_coe H
    (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ) ζ

/-- The inverse normalizer-quotient basepoint-change equivalence applies inverse
path-conjugation to representatives. -/
@[simp]
lemma basepointChangeNormalizerQuotientEquiv_symm_mk (γ : Path x₀ x₁)
    (H : Subgroup (_root_.FundamentalGroup X x₀))
    (η : _root_.Subgroup.normalizer
      ((basepointChangeSubgroup γ H) : Set (_root_.FundamentalGroup X x₁))) :
    (basepointChangeNormalizerQuotientEquiv γ H).symm
        (Subgroup.normalizerQuotientMk (basepointChangeSubgroup γ H) η) =
      Subgroup.normalizerQuotientMk H
        ((Subgroup.normalizerEquivMap H
          (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ)).symm η) :=
  Subgroup.normalizerQuotientEquivMap_symm_mk H
    (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ) η

end FundamentalGroup

end TauCeti
