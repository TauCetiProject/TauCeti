/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LocalField.Basic
import TauCeti.NumberTheory.LocalField.UnitsDecomposition

/-!
# Topological properties of a nonarchimedean local field

A nonarchimedean local field `K` is σ-compact, and `0` is not an isolated point of `K`. These are
the hypotheses under which Haar-measure arguments on `K` and on `ι → K` run. For example, a
coordinate hyperplane of `ι → K` is a null set (`MeasureTheory.Measure.measure_hyperplane`).

## Main declarations

* `TauCeti.instSigmaCompactSpace`: `K` is σ-compact, as the union of `0` and the σ-compact group
  of units `TauCeti.instSigmaCompactSpaceUnits`.
* `TauCeti.instNeBotNhdsNEZero`: `0` is not isolated in `K`. Otherwise `K` would be discrete, and
  the compact ring of integers `𝒪[K]` would be finite, hence a field.
-/

public section

open ValuativeRel Topology

namespace TauCeti

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- A nonarchimedean local field is σ-compact: it is the union of `{0}` and the image of its
σ-compact group of units. -/
instance instSigmaCompactSpace : SigmaCompactSpace K := by
  refine isSigmaCompact_univ_iff.1 ?_
  have h : (Set.univ : Set K) = insert 0 (Set.range ((↑) : Kˣ → K)) := by
    ext x
    simp only [Set.mem_univ, Set.mem_insert_iff, Set.mem_range, true_iff]
    by_cases hx : x = 0
    · exact .inl hx
    · exact .inr ⟨Units.mk0 x hx, rfl⟩
  rw [h, Set.insert_eq, Set.union_eq_iUnion]
  exact isSigmaCompact_iUnion _ fun b ↦ b.casesOn (isSigmaCompact_range Units.continuous_val)
    isCompact_singleton.isSigmaCompact

/-- `0` is not an isolated point of a nonarchimedean local field: otherwise the field would be
discrete, so its compact ring of integers would be finite, hence a field, which a discrete
valuation ring is not. -/
instance instNeBotNhdsNEZero : (𝓝[≠] (0 : K)).NeBot := by
  refine ⟨fun h ↦ ?_⟩
  have : DiscreteTopology K :=
    discreteTopology_iff_isOpen_singleton_zero.2 ((isOpen_singleton_iff_punctured_nhds 0).2 h)
  have : Finite 𝒪[K] := Set.finite_univ_iff.1 isCompact_univ.finite_of_discrete
  exact IsDiscreteValuationRing.not_a_field 𝒪[K]
    ((IsLocalRing.isField_iff_maximalIdeal_eq).1 (Finite.isField_of_domain 𝒪[K]))

end TauCeti
