/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.OuterMeasure.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Vanishing density quotients for outer measures

General comparison lemmas for vanishing quotients `μ (S r) / d r → 0` along an arbitrary filter `l`
with arbitrary denominator `d : α → ℝ≥0∞`. Because only monotonicity, finite subadditivity, and
vanishing on null sets are used, all statements are phrased for `OuterMeasureClass`, covering both
outer measures and measures without requiring a measurable space or metric structure.

## Main results

* `TauCeti.tendsto_measure_div_of_subset`: monotonicity of vanishing density quotients.
* `TauCeti.tendsto_measure_div_of_subset_union`: finite subadditivity of vanishing density
  quotients.
* `TauCeti.tendsto_measure_inter_div_of_measure_eq_zero`: subsets of null sets have vanishing
  density quotients against arbitrary test sets.
* `TauCeti.tendsto_measure_sdiff_inter_div_of_subset`: when `A ⊆ B`, `A \ B` has vanishing density
  quotients against arbitrary test sets.
-/

public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace TauCeti

variable {α X F : Type*} [FunLike F (Set X) ℝ≥0∞] [OuterMeasureClass F X] {μ : F}

/-- Monotonicity of vanishing density quotients: if `S r ⊆ T r` for all `r` and `μ (T r) / d r → 0`,
then `μ (S r) / d r → 0`. -/
theorem tendsto_measure_div_of_subset {S T : α → Set X} {d : α → ℝ≥0∞} {l : Filter α}
    (h : Tendsto (fun r => μ (T r) / d r) l (𝓝 0)) (hsub : ∀ r, S r ⊆ T r) :
    Tendsto (fun r => μ (S r) / d r) l (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
    (Eventually.of_forall fun _ => zero_le)
    (Eventually.of_forall fun r => ENNReal.div_le_div_right (measure_mono (hsub r)) _)

/-- Subadditivity of vanishing density quotients: if `S r ⊆ T₁ r ∪ T₂ r` for all `r` and both
`μ (T₁ r) / d r → 0` and `μ (T₂ r) / d r → 0`, then `μ (S r) / d r → 0`. -/
theorem tendsto_measure_div_of_subset_union {S T₁ T₂ : α → Set X} {d : α → ℝ≥0∞} {l : Filter α}
    (h₁ : Tendsto (fun r => μ (T₁ r) / d r) l (𝓝 0))
    (h₂ : Tendsto (fun r => μ (T₂ r) / d r) l (𝓝 0)) (hsub : ∀ r, S r ⊆ T₁ r ∪ T₂ r) :
    Tendsto (fun r => μ (S r) / d r) l (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (by simpa using h₁.add h₂)
    (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall fun r => ?_)
  rw [← ENNReal.add_div]
  exact ENNReal.div_le_div_right ((measure_mono (hsub r)).trans (measure_union_le _ _)) _

/-- Any subset `T` of a `μ`-null set `S` has vanishing density quotients against arbitrary test
sets. -/
theorem tendsto_measure_inter_div_of_measure_eq_zero {S T : Set X} (hTS : T ⊆ S) (hS : μ S = 0)
    (t : α → Set X) (d : α → ℝ≥0∞) (l : Filter α) :
    Tendsto (fun r => μ (T ∩ t r) / d r) l (𝓝 0) := by
  refine tendsto_const_nhds.congr fun r => ?_
  rw [measure_mono_null (inter_subset_left.trans hTS) hS, ENNReal.zero_div]

/-- When `A ⊆ B`, the set difference `A \ B` is empty and therefore has vanishing density quotients.
In particular (`A = B`), `(A \ A) ∩ t r` has zero density quotients. -/
theorem tendsto_measure_sdiff_inter_div_of_subset {A B : Set X} (hAB : A ⊆ B)
    (t : α → Set X) (d : α → ℝ≥0∞) (l : Filter α) :
    Tendsto (fun r => μ ((A \ B) ∩ t r) / d r) l (𝓝 0) :=
  tendsto_measure_inter_div_of_measure_eq_zero (sdiff_eq_empty.2 hAB).subset measure_empty t d l

end TauCeti
