/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Action
public import TauCeti.Topology.Covering.Proper

/-!
# Compact universal covers and finite fundamental groups

The basepoint-fibre equivalence from `TauCeti.AlgebraicTopology.UniversalCover.Basic`
identifies the fibre with the fundamental group. This file uses it to relate compactness of
the universal cover to finiteness of the fundamental group.

For a locally path-connected, semilocally simply connected space with closed points, a compact
universal cover has finite fundamental group. The basepoint fibre is closed in the compact
total space and discrete by the covering theorem. In particular, a geometric argument may
first prove compactness upstairs, then deduce finiteness of the fundamental group without
using finiteness to construct the cover.

Conversely, over a compact base, a finite fundamental group makes the universal cover compact:
its covering projection has finite fibres and is therefore proper.

## Main declarations

* `TauCeti.UniversalCover.finite_fundamentalGroup_of_compactSpace`: compactness upstairs
  implies finiteness of the fundamental group.
* `TauCeti.UniversalCover.compactSpace_iff`: over a path-connected base with closed points,
  the universal cover is compact exactly when the base is compact and its fundamental group
  is finite.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 11
  (the universal-cover argument in the Bonnet–Myers theorem).

The native based-path cover and its fundamental-group action are adapted from Kim Morrison's
[mathlib4#38292](https://github.com/leanprover-community/mathlib4/pull/38292).
-/

public section

open Set

namespace TauCeti.UniversalCover

variable {X : Type*} [TopologicalSpace X] (x₀ : X)

variable [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X]

/-- A compact universal cover of a space with closed points has finite fundamental group.
No connectedness or compactness of the base is required. -/
theorem finite_fundamentalGroup_of_compactSpace [T1Space X]
    [CompactSpace (UniversalCover x₀)] : Finite (FundamentalGroup X x₀) := by
  have hclosed : IsClosed ((proj : UniversalCover x₀ → X) ⁻¹' {x₀}) :=
    isClosed_singleton.preimage (continuous_proj x₀)
  have : CompactSpace ((proj : UniversalCover x₀ → X) ⁻¹' {x₀}) :=
    isCompact_iff_compactSpace.mp hclosed.isCompact
  have : Finite ((proj : UniversalCover x₀ → X) ⁻¹' {x₀}) :=
    finite_of_compact_of_discrete
  exact Finite.of_equiv _ (fiberEquivFundamentalGroup x₀)

/-- A finite fundamental group makes the universal covering projection proper, including
when the base has components not met by this based cover. -/
theorem isProperMap_proj [Finite (FundamentalGroup X x₀)] :
    IsProperMap (proj : UniversalCover x₀ → X) := by
  apply (isCoveringMap x₀).isProperMap
  intro x
  cases isEmpty_or_nonempty ((proj : UniversalCover x₀ → X) ⁻¹' {x}) with
  | inl h => infer_instance
  | inr h =>
    obtain ⟨e⟩ := h
    -- A nonempty fibre is an orbit of the finite fundamental-group action.
    have hsub : (proj : UniversalCover x₀ → X) ⁻¹' {x} ⊆
        MulAction.orbit (FundamentalGroup X x₀) e.1 :=
      fun z hz ↦ proj_eq_iff_mem_orbit.mp (hz.trans e.2.symm)
    exact ((Finite.finite_mulAction_orbit e.1).subset hsub).to_subtype

/-- The universal cover of a compact space with finite fundamental group is
compact. -/
theorem compactSpace_of_finite_fundamentalGroup [CompactSpace X]
    [Finite (FundamentalGroup X x₀)] : CompactSpace (UniversalCover x₀) := by
  rw [← isCompact_univ_iff]
  simpa using (isProperMap_proj x₀).isCompact_preimage isCompact_univ

variable [PathConnectedSpace X]

/-- For a path-connected space with closed points, its universal cover is compact exactly
when the base is compact and its fundamental group is finite. -/
theorem compactSpace_iff [T1Space X] :
    CompactSpace (UniversalCover x₀) ↔ CompactSpace X ∧ Finite (FundamentalGroup X x₀) := by
  constructor
  · intro h
    have := h
    exact ⟨proj_surjective.compactSpace (continuous_proj x₀),
      finite_fundamentalGroup_of_compactSpace x₀⟩
  · rintro ⟨hcompact, hfinite⟩
    have := hcompact
    have := hfinite
    exact compactSpace_of_finite_fundamentalGroup x₀

end TauCeti.UniversalCover
