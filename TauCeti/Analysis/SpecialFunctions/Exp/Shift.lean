/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.Exponential
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
* `TauCeti.abs_exp_mul_sub_le_exp`: a bound `|f x| ≤ M` bounds `|exp (t * (f x - I))|` by
  `exp (|t| * (M + |I|))`.
* `ContinuousOn.exists_forall_le_mul_exp_Ici_of_eventually_le`: an eventual exponential bound
  on a closed forward ray extends to the whole ray, with a larger constant.
* `TauCeti.isBigO_exp_neg_mul_norm_one`: for `c ≥ 0` the weight `exp (-c ‖x‖)` is bounded.
* `TauCeti.exp_neg_mul_norm_add_le`: translating by `‖k‖ ≤ 1` changes the weight
  `exp (-c ‖x‖)` by at most the factor `exp c`.
* `TauCeti.norm_sub_comp_add_le_of_norm_fderiv_le`: a mean value bound for a map whose
  derivative decays like `exp (-c ‖x‖)`.
* `TauCeti.exists_nonneg_forall_norm_le_mul_exp_of_isBigO`: an `O(exp (-c ‖x‖))` bound at infinity
  holds outside an explicit ball, with a nonnegative constant.
-/

public section

namespace TauCeti

/-- Shifting the radius in an exponential: `exp (-c (t - R)) = exp (c R) exp (-c t)`. -/
theorem exp_neg_mul_sub (c t R : ℝ) :
    Real.exp (-(c * (t - R))) = Real.exp (c * R) * Real.exp (-(c * t)) := by
  rw [← Real.exp_add]
  ring_nf

open Filter in
/-- A continuous function bounded by `K exp (-c ‖x‖)` outside a compact set is bounded by
`K' exp (-c ‖x‖)` everywhere, for some constant `K'`. -/
theorem exists_forall_le_mul_exp_of_eventually_le {E : Type*} [NormedAddCommGroup E]
    {f : E → ℝ} (hf : Continuous f) {c K : ℝ}
    (h : ∀ᶠ x in cocompact E, f x ≤ K * Real.exp (-(c * ‖x‖))) :
    ∃ K', ∀ x, f x ≤ K' * Real.exp (-(c * ‖x‖)) := by
  obtain ⟨S, hS, hR⟩ := mem_cocompact.mp h
  -- On the compact set, bound `f x exp (c ‖x‖)` by compactness.
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn
    (f := fun x ↦ f x * Real.exp (c * ‖x‖)) (by fun_prop)
  refine ⟨max K M, fun x ↦ ?_⟩
  have he : 0 < Real.exp (-(c * ‖x‖)) := Real.exp_pos _
  by_cases hx : x ∈ S
  · have hb := hM x hx
    rw [Real.norm_eq_abs] at hb
    calc f x = f x * Real.exp (c * ‖x‖) * Real.exp (-(c * ‖x‖)) := by
          rw [Real.exp_neg, mul_inv_cancel_right₀ (Real.exp_ne_zero _)]
      _ ≤ max K M * Real.exp (-(c * ‖x‖)) :=
          mul_le_mul_of_nonneg_right (((le_abs_self _).trans hb).trans (le_max_right _ _)) he.le
  · exact (hR hx).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) he.le)

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

section NormWeight

open Filter Metric Asymptotics

variable {E : Type*} [NormedAddCommGroup E]

/-- For `c ≥ 0` the weight `exp (-c ‖x‖)` is bounded. -/
theorem isBigO_exp_neg_mul_norm_one {c : ℝ} (hc : 0 ≤ c) (l : Filter E) :
    (fun x : E ↦ Real.exp (-(c * ‖x‖))) =O[l] fun _ ↦ (1 : ℝ) :=
  IsBigO.of_bound 1 (Eventually.of_forall fun x ↦ by
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, norm_one, one_mul, Real.exp_le_one_iff]
    exact neg_nonpos.mpr (by positivity))

/-- Translating by `‖k‖ ≤ 1` changes the weight `exp (-c ‖x‖)`, `c ≥ 0`, by at most the factor
`exp c`. -/
theorem exp_neg_mul_norm_add_le {c : ℝ} (hc : 0 ≤ c) (x : E) {k : E} (hk : ‖k‖ ≤ 1) :
    Real.exp (-(c * ‖x + k‖)) ≤ Real.exp c * Real.exp (-(c * ‖x‖)) := by
  rw [← Real.exp_add, Real.exp_le_exp]
  nlinarith [norm_le_add_norm_add x k]

/-- An `O(exp (-c ‖x‖))` bound at infinity on a proper space holds outside an explicit ball, with a
nonnegative constant. -/
theorem exists_nonneg_forall_norm_le_mul_exp_of_isBigO [ProperSpace E] {f : E → ℝ} {c : ℝ}
    (h : f =O[cocompact E] fun x ↦ Real.exp (-(c * ‖x‖))) :
    ∃ K R, 0 ≤ K ∧ ∀ x : E, R ≤ ‖x‖ → ‖f x‖ ≤ K * Real.exp (-(c * ‖x‖)) := by
  obtain ⟨K, hK⟩ := h.bound
  obtain ⟨R, -, hR⟩ := hasBasis_cobounded_norm.eventually_iff.mp
    (cobounded_eq_cocompact (α := E) ▸ hK)
  refine ⟨max K 0, R, le_max_right _ _, fun x hx ↦ (hR hx).trans ?_⟩
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le

variable [NormedSpace ℝ E]

/-- **A mean value bound for exponentially decaying derivatives.** If the derivative of `φ` is
bounded by `K exp (-c ‖w‖)` outside the ball of radius `R`, where `c, K ≥ 0`, then for `‖z‖ ≥ R + 1`
and `‖k‖ ≤ 1`, `‖φ z - φ (z + k)‖ ≤ K exp c exp (-c ‖z‖) ‖k‖`. -/
theorem norm_sub_comp_add_le_of_norm_fderiv_le {B : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] {φ : E → B} (hφ : Differentiable ℝ φ) {c K R : ℝ} (hc : 0 ≤ c)
    (hK : 0 ≤ K) (hbd : ∀ w : E, R ≤ ‖w‖ → ‖fderiv ℝ φ w‖ ≤ K * Real.exp (-(c * ‖w‖)))
    {z k : E} (hz : R + 1 ≤ ‖z‖) (hk : ‖k‖ ≤ 1) :
    ‖φ z - φ (z + k)‖ ≤ K * Real.exp c * Real.exp (-(c * ‖z‖)) * ‖k‖ := by
  have hball : ∀ w ∈ closedBall z 1,
      ‖fderiv ℝ φ w‖ ≤ K * Real.exp c * Real.exp (-(c * ‖z‖)) := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm] at hw
    have hzw := norm_le_add_norm_add z (w - z)
    have hexp := exp_neg_mul_norm_add_le hc z hw
    rw [add_sub_cancel] at hzw hexp
    refine (hbd w (by linarith)).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hexp hK
  have h := (convex_closedBall z 1).norm_image_sub_le_of_norm_fderiv_le (fun w _ ↦ hφ w) hball
    (mem_closedBall_self zero_le_one)
    (show z + k ∈ closedBall z 1 by rwa [mem_closedBall, dist_eq_norm, add_sub_cancel_left])
  rwa [add_sub_cancel_left, norm_sub_rev] at h

end NormWeight

end TauCeti
