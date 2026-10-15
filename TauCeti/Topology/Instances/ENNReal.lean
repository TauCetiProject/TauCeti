/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Limits of `ℝ≥0∞`-valued functions

This file collects squeeze arguments for functions valued in `ℝ≥0∞`, where the usual
subtraction-based estimates are unavailable, and the superadditivity of the lower limit of
`ℝ≥0∞`-valued families, the counterpart of Mathlib's `le_liminf_add` for ordered groups.

## Main declarations

* `TauCeti.tendsto_nhds_zero_of_le_enorm_mul`: a quantity dominated by `‖h‖ₑ` times a finite
  constant vanishes as `h → 0`.
* `TauCeti.tendsto_of_le_add_of_le_add`: a family within `wᵢ` of `b` from both sides converges
  to `b` when `wᵢ → 0`.
* `ENNReal.le_liminf_add` and `ENNReal.sum_liminf_le_liminf_sum`: the sum of the lower limits of
  finitely many `ℝ≥0∞`-valued families is at most the lower limit of their sum.
-/

public section

namespace TauCeti

open scoped ENNReal

variable {E : Type*} [TopologicalSpace E] [ESeminormedAddMonoid E]

/-- A quantity dominated by `‖h‖ₑ` times a finite constant vanishes as `h → 0`. This is the form
in which a linear modulus of continuity yields the qualitative limit. -/
theorem tendsto_nhds_zero_of_le_enorm_mul {G : E → ℝ≥0∞} {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hG : ∀ h : E, G h ≤ ‖h‖ₑ * C) :
    Filter.Tendsto G (nhds 0) (nhds 0) := by
  have h0 : Filter.Tendsto (fun h : E => ‖h‖ₑ) (nhds 0) (nhds 0) :=
    continuous_enorm.tendsto' 0 0 (by simp)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using ENNReal.Tendsto.mul_const h0 (Or.inr hC)) (fun _ => zero_le) hG

/-- In `ℝ≥0∞`, a family that is within `wᵢ` of a fixed value `b` from both sides converges to `b`
when `wᵢ → 0`. -/
theorem tendsto_of_le_add_of_le_add {ι : Type*} {l : Filter ι} {a w : ι → ℝ≥0∞}
    {b : ℝ≥0∞} (hw : Filter.Tendsto w l (nhds 0)) (hle : ∀ᶠ i in l, a i ≤ b + w i)
    (hge : ∀ᶠ i in l, b ≤ a i + w i) : Filter.Tendsto a l (nhds b) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun i ↦ b - w i)
    (h := fun i ↦ b + w i) ?_ ?_ (hge.mono fun i hi ↦ tsub_le_iff_right.2 hi) hle
  · simpa using ENNReal.Tendsto.sub tendsto_const_nhds hw (Or.inr ENNReal.zero_ne_top)
  · simpa using tendsto_const_nhds.add hw

/-- The sum of the lower limits of two `ℝ≥0∞`-valued families is at most the lower limit of their
sum. -/
theorem _root_.ENNReal.le_liminf_add {ι : Type*} {l : Filter ι} (u v : ι → ℝ≥0∞) :
    Filter.liminf u l + Filter.liminf v l ≤ Filter.liminf (fun i ↦ u i + v i) l := by
  rcases eq_or_ne (Filter.liminf u l) 0 with hu | hu
  · rw [hu, zero_add]
    exact Filter.liminf_le_liminf (Filter.Eventually.of_forall fun i ↦ le_add_self)
  rcases eq_or_ne (Filter.liminf v l) 0 with hv | hv
  · rw [hv, add_zero]
    exact Filter.liminf_le_liminf (Filter.Eventually.of_forall fun i ↦ le_self_add)
  refine le_of_forall_lt_imp_le_of_dense fun c hc ↦ ?_
  obtain ⟨a, ha, b, hb, hab⟩ := ENNReal.exists_lt_add_of_lt_add hc hu hv
  refine Filter.le_liminf_of_le (by isBoundedDefault) ?_
  filter_upwards [Filter.eventually_lt_of_lt_liminf ha, Filter.eventually_lt_of_lt_liminf hb]
    with i hai hbi
  exact hab.le.trans (add_le_add hai.le hbi.le)

/-- The sum of the lower limits of finitely many `ℝ≥0∞`-valued families is at most the lower
limit of their sum. -/
theorem _root_.ENNReal.sum_liminf_le_liminf_sum {ι κ : Type*} {l : Filter ι} (s : Finset κ)
    (f : κ → ι → ℝ≥0∞) :
    ∑ j ∈ s, Filter.liminf (f j) l ≤ Filter.liminf (fun i ↦ ∑ j ∈ s, f j i) l := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact (add_le_add le_rfl ih).trans (ENNReal.le_liminf_add _ _)

end TauCeti
