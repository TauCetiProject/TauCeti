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
subgroup and normalizer-quotient bookkeeping needed by the universal-covers roadmap. The
basepoint-specific simp lemmas below restate the generic `Subgroup`-map and
`Subgroup.normalizerQuotientEquivMap` behavior using these names.

## Main declarations

* `TauCeti.FundamentalGroup.basepointChangeSubgroup`: transport a subgroup of `π₁(X, x₀)`
  along a path `γ : Path x₀ x₁`.
* `TauCeti.FundamentalGroup.basepointChangeSubgroupEquiv`: the induced isomorphism
  `H ≃* γ₊H` between a subgroup and its transport.
* `TauCeti.FundamentalGroup.basepointChangeNormalizerQuotientEquiv`: the corresponding
  isomorphism `N(H) / H ≃* N(γ₊H) / γ₊H`.

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

/-- Membership in the basepoint-changed subgroup is membership in the image of the original
subgroup under path-conjugation. -/
@[simp]
lemma mem_basepointChangeSubgroup (γ : Path x₀ x₁)
    (H : Subgroup (_root_.FundamentalGroup X x₀))
    (g : _root_.FundamentalGroup X x₁) :
    g ∈ basepointChangeSubgroup γ H ↔
      ∃ h ∈ H, _root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ h = g :=
  Subgroup.mem_map

/-- The basepoint-change equivalence identifies a subgroup with its transported subgroup. The
action on loops is the generic `MulEquiv.coe_subgroupMap_apply` for the path-conjugation
equivalence. -/
noncomputable abbrev basepointChangeSubgroupEquiv (γ : Path x₀ x₁)
    (H : Subgroup (_root_.FundamentalGroup X x₀)) :
    H ≃* basepointChangeSubgroup γ H :=
  (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ).subgroupMap H

/-- On subgroup elements, `basepointChangeSubgroupEquiv` applies path-conjugation. -/
@[simp]
lemma basepointChangeSubgroupEquiv_apply_coe (γ : Path x₀ x₁)
    (H : Subgroup (_root_.FundamentalGroup X x₀)) (h : H) :
    ((basepointChangeSubgroupEquiv γ H h : basepointChangeSubgroup γ H) :
      _root_.FundamentalGroup X x₁) =
      _root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ h :=
  MulEquiv.coe_subgroupMap_apply
    (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ) H h

/-- The inverse subgroup equivalence applies inverse path-conjugation. -/
@[simp]
lemma basepointChangeSubgroupEquiv_symm_apply (γ : Path x₀ x₁)
    (H : Subgroup (_root_.FundamentalGroup X x₀)) (g : basepointChangeSubgroup γ H) :
    (basepointChangeSubgroupEquiv γ H).symm g =
      ⟨(_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ).symm g,
        SetLike.mem_coe.1 <|
          Set.mem_image_equiv.1 (show (g : _root_.FundamentalGroup X x₁) ∈
            H.map (((_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ) :
              _root_.FundamentalGroup X x₀ →* _root_.FundamentalGroup X x₁)) from g.2)⟩ :=
  MulEquiv.subgroupMap_symm_apply
    (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ) H g

/-- The normalizer quotient `N(H) / H` transported along a basepoint-change path. The action on
representatives is the generic `Subgroup.normalizerQuotientEquivMap_mk` for the path-conjugation
equivalence. -/
noncomputable abbrev basepointChangeNormalizerQuotientEquiv (γ : Path x₀ x₁)
    (H : Subgroup (_root_.FundamentalGroup X x₀)) :
    Subgroup.normalizerQuotient H ≃*
      Subgroup.normalizerQuotient (basepointChangeSubgroup γ H) :=
  Subgroup.normalizerQuotientEquivMap H
    (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ)

/-- On normalizer representatives, the basepoint-change normalizer-quotient equivalence applies
path-conjugation. -/
@[simp]
lemma basepointChangeNormalizerQuotientEquiv_mk (γ : Path x₀ x₁)
    (H : Subgroup (_root_.FundamentalGroup X x₀))
    (g : _root_.Subgroup.normalizer (H : Set (_root_.FundamentalGroup X x₀))) :
    basepointChangeNormalizerQuotientEquiv γ H (Subgroup.normalizerQuotientMk H g) =
      Subgroup.normalizerQuotientMk (basepointChangeSubgroup γ H)
        (Subgroup.normalizerEquivMap H
          (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ) g) :=
  Subgroup.normalizerQuotientEquivMap_mk H
    (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ) g

/-- The inverse basepoint-change normalizer-quotient equivalence applies inverse
path-conjugation on representatives. -/
@[simp]
lemma basepointChangeNormalizerQuotientEquiv_symm_mk (γ : Path x₀ x₁)
    (H : Subgroup (_root_.FundamentalGroup X x₀))
    (g : _root_.Subgroup.normalizer
      ((basepointChangeSubgroup γ H) : Set (_root_.FundamentalGroup X x₁))) :
    (basepointChangeNormalizerQuotientEquiv γ H).symm
        (Subgroup.normalizerQuotientMk (basepointChangeSubgroup γ H) g) =
      Subgroup.normalizerQuotientMk H
        ((Subgroup.normalizerEquivMap H
          (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ)).symm g) :=
  Subgroup.normalizerQuotientEquivMap_symm_mk H
    (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ) g

end FundamentalGroup

end TauCeti
