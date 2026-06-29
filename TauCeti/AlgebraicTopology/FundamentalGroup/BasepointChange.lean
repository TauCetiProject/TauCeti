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
subgroup and normalizer-quotient bookkeeping needed by the universal-covers roadmap. Each is a
transparent specialization, so the action and inverse action are characterized by the existing
generic `Subgroup`-map and `Subgroup.normalizerQuotientEquivMap` lemmas without any
basepoint-specific restatements.

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

/-- The basepoint-change equivalence identifies a subgroup with its transported subgroup. The
action on loops is the generic `MulEquiv.coe_subgroupMap_apply` for the path-conjugation
equivalence. -/
noncomputable abbrev basepointChangeSubgroupEquiv (γ : Path x₀ x₁)
    (H : Subgroup (_root_.FundamentalGroup X x₀)) :
    H ≃* basepointChangeSubgroup γ H :=
  (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ).subgroupMap H

/-- The normalizer quotient `N(H) / H` transported along a basepoint-change path. The action on
representatives is the generic `Subgroup.normalizerQuotientEquivMap_mk` for the path-conjugation
equivalence. -/
noncomputable abbrev basepointChangeNormalizerQuotientEquiv (γ : Path x₀ x₁)
    (H : Subgroup (_root_.FundamentalGroup X x₀)) :
    Subgroup.normalizerQuotient H ≃*
      Subgroup.normalizerQuotient (basepointChangeSubgroup γ H) :=
  Subgroup.normalizerQuotientEquivMap H
    (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ)

end FundamentalGroup

end TauCeti
