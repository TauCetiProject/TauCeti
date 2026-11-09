/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Shifting the argument of a real exponential

The decay profile `exp (-c (t - R))`, normalised to equal `1` at `t = R`, is the radial profile
`exp (-c t)` rescaled by the constant amplitude `exp (c R)`. This is how exponential decay
estimates past a radius `R` are converted into bounds of the form `K exp (-c t)`. Conversely, a
bound `K exp (-c ‖x‖)` outside a compact set extends to the whole space for a continuous
function, after enlarging the constant. The analogous statement on a closed forward ray absorbs
an initial compact time interval into the constant.

## Main declarations

* `TauCeti.exp_neg_mul_sub`: `exp (-c (t - R)) = exp (c R) exp (-c t)`.
* `TauCeti.exists_forall_le_mul_exp_of_eventually_le`: an exponential bound outside a compact set
  extends to the whole space for a continuous function, with a larger constant.
* `ContinuousOn.exists_forall_le_mul_exp_Ici_of_eventually_le`: an eventual exponential bound
  on a closed forward ray extends to the whole ray, with a larger constant.
* `TauCeti.abs_exp_mul_sub_le_exp`: a bound `|f x| ≤ M` bounds `|exp (t * (f x - I))|` by
  `exp (|t| * (M + |I|))`.
-/

public section

namespace TauCeti

/-- Shifting the radius in an exponential: `exp (-c (t - R)) = exp (c R) exp (-c t)`. -/
theorem exp_neg_mul_sub (c t R : ℝ) :
    Real.exp (-(c * (t - R))) = Real.exp (c * R) * Real.exp (-(c * t)) := by
  rw [← Real.exp_add]
  ring_nf

open Filter Metric in
/-- A continuous function bounded by `K exp (-c ‖x‖)` outside a compact set is bounded by
`K' exp (-c ‖x‖)` everywhere, for some constant `K'`. -/
theorem exists_forall_le_mul_exp_of_eventually_le {E : Type*} [NormedAddCommGroup E]
    [ProperSpace E] {f : E → ℝ} (hf : Continuous f) {c K : ℝ}
    (h : ∀ᶠ x in cocompact E, f x ≤ K * Real.exp (-(c * ‖x‖))) :
    ∃ K', ∀ x, f x ≤ K' * Real.exp (-(c * ‖x‖)) := by
  obtain ⟨R, -, hR⟩ := hasBasis_cobounded_norm.eventually_iff.mp
    (cobounded_eq_cocompact (α := E) ▸ h)
  -- Inside the ball, bound `f x exp (c ‖x‖)` by compactness.
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : E) R).exists_bound_of_continuousOn
    (f := fun x ↦ f x * Real.exp (c * ‖x‖)) (by fun_prop)
  refine ⟨max K M, fun x ↦ ?_⟩
  have he : 0 < Real.exp (-(c * ‖x‖)) := Real.exp_pos _
  rcases le_or_gt R ‖x‖ with hx | hx
  · exact (hR hx).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) he.le)
  · have hb := hM x (mem_closedBall_zero_iff.mpr hx.le)
    rw [Real.norm_eq_abs] at hb
    calc f x = f x * Real.exp (c * ‖x‖) * Real.exp (-(c * ‖x‖)) := by
          rw [Real.exp_neg, mul_inv_cancel_right₀ (Real.exp_ne_zero _)]
      _ ≤ max K M * Real.exp (-(c * ‖x‖)) :=
          mul_le_mul_of_nonneg_right (((le_abs_self _).trans hb).trans (le_max_right _ _)) he.le

open Filter Set in
/-- An eventual exponential bound on a continuous real function on a closed forward ray extends
to the entire ray, after enlarging the constant. The exponential rate is unchanged. -/
theorem _root_.ContinuousOn.exists_forall_le_mul_exp_Ici_of_eventually_le
    {g : ℝ → ℝ} {a c K : ℝ}
    (hg : ContinuousOn g (Ici a)) (h : ∀ᶠ t in atTop, g t ≤ K * Real.exp (-(c * t))) :
    ∃ C > 0, ∀ t ≥ a, g t ≤ C * Real.exp (-(c * t)) := by
  obtain ⟨T, hT⟩ := eventually_atTop.1 h
  have hcont : ContinuousOn (fun t ↦ g t * Real.exp (c * t)) (Icc a T) :=
    (hg.mono Icc_subset_Ici_self).mul (by fun_prop)
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hcont
  refine ⟨max 1 (max K B), lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun t ht ↦ ?_⟩
  by_cases htT : T ≤ t
  · exact (hT t htT).trans (by gcongr; exact (le_max_left K B).trans (le_max_right _ _))
  · have hb : g t * Real.exp (c * t) ≤ B := hB (mem_image_of_mem _ ⟨ht, le_of_not_ge htT⟩)
    calc g t = (g t * Real.exp (c * t)) * Real.exp (-(c * t)) := by
          rw [Real.exp_neg, mul_inv_cancel_right₀ (Real.exp_ne_zero _)]
      _ ≤ max 1 (max K B) * Real.exp (-(c * t)) := by
          gcongr
          exact hb.trans ((le_max_right K B).trans (le_max_right _ _))

/-- A bound on `f` bounds the shifted exponential `exp (t * (f x - I))` for any shift `I`. -/
theorem abs_exp_mul_sub_le_exp {α : Type*} {f : α → ℝ} {M : ℝ} (hMf : ∀ x, |f x| ≤ M)
    (I t : ℝ) (x : α) : |Real.exp (t * (f x - I))| ≤ Real.exp (|t| * (M + |I|)) := by
  rw [Real.abs_exp]
  apply Real.exp_le_exp.mpr
  calc
    t * (f x - I) ≤ |t * (f x - I)| := le_abs_self _
    _ = |t| * |f x - I| := abs_mul _ _
    _ ≤ |t| * (M + |I|) :=
      mul_le_mul_of_nonneg_left ((abs_sub (f x) I).trans (by linarith [hMf x]))
        (abs_nonneg t)

end TauCeti
