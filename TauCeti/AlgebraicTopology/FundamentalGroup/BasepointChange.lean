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
* `TauCeti.FundamentalGroup.mem_basepointChangeSubgroup` and the representative `[simp]`
  lemmas for membership and quotient calculations under these domain-specific names.

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
noncomputable def basepointChangeSubgroup (γ : Path x₀ x₁)
    (H : Subgroup (_root_.FundamentalGroup X x₀)) :
    Subgroup (_root_.FundamentalGroup X x₁) :=
  H.map (((_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ) :
    _root_.FundamentalGroup X x₀ →* _root_.FundamentalGroup X x₁))

/-- Membership in the subgroup transported along a basepoint-change path. -/
lemma mem_basepointChangeSubgroup (γ : Path x₀ x₁)
    (H : Subgroup (_root_.FundamentalGroup X x₀))
    (g : _root_.FundamentalGroup X x₁) :
    g ∈ basepointChangeSubgroup γ H ↔
      ∃ h ∈ H, _root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ h = g :=
  Iff.rfl

/-- The normalizer quotient `N(H) / H` transported along a basepoint-change path. -/
noncomputable def basepointChangeNormalizerQuotientEquiv (γ : Path x₀ x₁)
    (H : Subgroup (_root_.FundamentalGroup X x₀)) :
    Subgroup.normalizerQuotient H ≃*
      Subgroup.normalizerQuotient (basepointChangeSubgroup γ H) :=
  (Subgroup.normalizerQuotientEquivMap H
    (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ)).trans
    (Subgroup.normalizerQuotientCongr (by rw [basepointChangeSubgroup]))

/-- On normalizer representatives, basepoint-change transport is induced by the
path-conjugation isomorphism of fundamental groups. -/
@[simp]
lemma basepointChangeNormalizerQuotientEquiv_mk (γ : Path x₀ x₁)
    (H : Subgroup (_root_.FundamentalGroup X x₀))
    (g : _root_.Subgroup.normalizer (H : Set (_root_.FundamentalGroup X x₀))) :
    basepointChangeNormalizerQuotientEquiv γ H (Subgroup.normalizerQuotientMk H g) =
      Subgroup.normalizerQuotientMk (basepointChangeSubgroup γ H)
        (MulEquiv.subgroupCongr (by rw [basepointChangeSubgroup])
          (Subgroup.normalizerEquivMap H
            (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ) g)) := by
  rw [basepointChangeNormalizerQuotientEquiv, MulEquiv.trans_apply,
    Subgroup.normalizerQuotientEquivMap_mk,
    Subgroup.normalizerQuotientCongr_mk]

/-- The inverse basepoint-change transport sends a target representative to the inverse
path-conjugation representative. -/
@[simp]
lemma basepointChangeNormalizerQuotientEquiv_symm_mk (γ : Path x₀ x₁)
    (H : Subgroup (_root_.FundamentalGroup X x₀))
    (g : _root_.Subgroup.normalizer
      ((basepointChangeSubgroup γ H) : Set (_root_.FundamentalGroup X x₁))) :
    (basepointChangeNormalizerQuotientEquiv γ H).symm
        (Subgroup.normalizerQuotientMk (basepointChangeSubgroup γ H) g) =
      Subgroup.normalizerQuotientMk H
        ((Subgroup.normalizerEquivMap H
          (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ)).symm
          ((MulEquiv.subgroupCongr (by rw [basepointChangeSubgroup])).symm g)) := by
  rw [basepointChangeNormalizerQuotientEquiv, MulEquiv.symm_trans_apply,
    Subgroup.normalizerQuotientCongr_symm_mk, Subgroup.normalizerQuotientEquivMap_symm_mk]
  -- The forward and inverse `subgroupCongr` agree on representatives (both are the identity on
  -- underlying elements), so the two transported representatives coincide.
  rfl

/-- On representatives, basepoint-change transport applies the path-conjugation isomorphism
of fundamental groups. -/
lemma basepointChangeNormalizerQuotientEquiv_mk_coe (γ : Path x₀ x₁)
    (H : Subgroup (_root_.FundamentalGroup X x₀))
    (g : _root_.Subgroup.normalizer (H : Set (_root_.FundamentalGroup X x₀))) :
    basepointChangeNormalizerQuotientEquiv γ H (Subgroup.normalizerQuotientMk H g) =
      Subgroup.normalizerQuotientMk (basepointChangeSubgroup γ H)
        (MulEquiv.subgroupCongr (by rw [basepointChangeSubgroup])
          (⟨_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ
              (g : _root_.FundamentalGroup X x₀),
            by
              rw [← Subgroup.normalizerEquivMap_apply_coe H
                (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ) g]
              exact (Subgroup.normalizerEquivMap H
                (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ) g).2⟩ :
            _root_.Subgroup.normalizer
              ((H.map ((_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ) :
                _root_.FundamentalGroup X x₀ →* _root_.FundamentalGroup X x₁)) :
                  Set (_root_.FundamentalGroup X x₁)))) := by
  rw [basepointChangeNormalizerQuotientEquiv, MulEquiv.trans_apply,
    Subgroup.normalizerQuotientEquivMap_mk_coe,
    Subgroup.normalizerQuotientCongr_mk]

end FundamentalGroup

end TauCeti
