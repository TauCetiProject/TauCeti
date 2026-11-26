/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.NonlinearCaratheodory.Basic
public import TauCeti.Analysis.ODE.VariationOfConstants
import TauCeti.Analysis.Normed.Operator.Basic

/-!
# Checks for the nonlinear Carathéodory theorem

Examples for the nonlinear Carathéodory theorem: the linear field recovers the variation of
constants formula, and without the Lipschitz bound uniqueness fails.

* **The linear field.** For `P` and `G` integrable on `[a, b]`, the field
  `F(t, x) = P(t) x + G(t)` satisfies the hypotheses of the nonlinear Carathéodory theorem: its
  sections `t ↦ F(t, x)` are integrable on `[a, b]` (`TauCeti.integrableOn_Icc_clm_apply_add`),
  and `F t` is Lipschitz with the integrable constant `L = ‖P‖`
  (`ContinuousLinearMap.lipschitzWith_add_const`).
  The bound `‖F(t, x₀)‖ ≤ m(t)` of the a priori estimate holds with `m = ‖P‖ ‖x₀‖ + ‖G‖`
  (`TauCeti.Examples.NonlinearCaratheodory.norm_linear_le`). The solution is that of the linear
  theory, the variation of constants formula `N_P(t, t₀) x₀ + ∫ s in t₀..t, N_P(t, s) G(s)`
  (`TauCeti.Examples.NonlinearCaratheodory.eq_propagator_apply_add_integral_of_linear`,
  `TauCeti.Examples.NonlinearCaratheodory.exists_eq_propagator_apply_add_integral_of_linear`).
* **The Lipschitz bound is needed.** The field `F(t, x) = 2 √|x|` on `ℝ`, from `x₀ = 0` at
  `t₀ = 0`, has the two solutions `0` and `t²` on `[0, 1]`
  (`TauCeti.Examples.NonlinearCaratheodory.sq_eq_picard_sqrt`,
  `TauCeti.Examples.NonlinearCaratheodory.zero_eq_picard_sqrt`); `x ↦ 2 √|x|` is not Lipschitz
  (`TauCeti.Examples.NonlinearCaratheodory.not_lipschitzWith_sqrt`).
-/

public section

open MeasureTheory Set intervalIntegral Real

open scoped NNReal

namespace TauCeti.Examples.NonlinearCaratheodory

section Linear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {P : ℝ → E →L[ℝ] E} {G : ℝ → E}
  {a b t₀ : ℝ} {x₀ : E}

/-- The linear field satisfies `‖P(t) x₀ + G(t)‖ ≤ ‖P(t)‖ ‖x₀‖ + ‖G(t)‖`. -/
theorem norm_linear_le (t : ℝ) : ‖P t x₀ + G t‖ ≤ ‖P t‖ * ‖x₀‖ + ‖G t‖ :=
  (norm_add_le _ _).trans (add_le_add_left ((P t).le_opNorm x₀) _)

/-- **The linear field: the solution is that of the linear theory.** For `P` and `G` integrable
on `[a, b]` and `t₀, t ∈ [a, b]`, a curve continuous on `[a, b]` solving
`x t = x₀ + ∫ s in t₀..t, (P(s) x(s) + G(s))` there is the variation of constants formula
`N_P(t, t₀) x₀ + ∫ s in t₀..t, N_P(t, s) G(s)`. Such a curve exists by the nonlinear Carathéodory
theorem with `L = ‖P‖`
(`TauCeti.Examples.NonlinearCaratheodory.exists_eq_propagator_apply_add_integral_of_linear`). -/
theorem eq_propagator_apply_add_integral_of_linear [CompleteSpace E]
    (hP : IntegrableOn P (Icc a b)) (hG : IntegrableOn G (Icc a b)) (ht₀ : t₀ ∈ Icc a b) {Y : ℝ → E}
    (hY : ContinuousOn Y (Icc a b))
    (h : ∀ t ∈ Icc a b, Y t = ODE.picard (fun s x ↦ P s x + G s) t₀ x₀ Y t) {t : ℝ}
    (ht : t ∈ Icc a b) :
    Y t = propagator P t t₀ x₀ + ∫ s in t₀..t, propagator P t s (G s) := by
  have hY₀ : Y t₀ = x₀ := by rw [h t₀ ht₀]; simp [ODE.picard_apply]
  rw [← hY₀]
  exact eq_propagator_apply_add_integral hP hG ht₀ ht hY fun r hr ↦ by
    rw [h r hr, ODE.picard_apply, hY₀]

/-- **The linear field: existence.** The nonlinear Carathéodory theorem, applied to the linear
field with `L = ‖P‖`, gives a solution, and it is the variation of constants formula. -/
theorem exists_eq_propagator_apply_add_integral_of_linear [CompleteSpace E]
    (hP : IntegrableOn P (Icc a b)) (hG : IntegrableOn G (Icc a b)) (ht₀ : t₀ ∈ Icc a b) :
    ∃ Y : ℝ → E, ContinuousOn Y (Icc a b) ∧
      ∀ t ∈ Icc a b, Y t = ODE.picard (fun s x ↦ P s x + G s) t₀ x₀ Y t ∧
        Y t = propagator P t t₀ x₀ + ∫ s in t₀..t, propagator P t s (G s) := by
  obtain ⟨Y, hY, h⟩ := exists_continuousOn_forall_mem_Icc_eq_picard_of_lipschitzWith
    (F := fun s x ↦ P s x + G s) (L := fun t ↦ ‖P t‖₊)
    (fun _ ↦ integrableOn_Icc_clm_apply_add hP hG continuousOn_const)
    (by
      have h : IntegrableOn (fun t ↦ ‖P t‖) (Icc a b) := hP.norm
      simpa only [coe_nnNorm] using h)
    (.of_forall fun t ↦ (P t).lipschitzWith_add_const (G t)) ht₀ x₀
  exact ⟨Y, hY, fun t ht ↦ ⟨h t ht, eq_propagator_apply_add_integral_of_linear hP hG ht₀ hY h ht⟩⟩

end Linear

section Sqrt

/-- The curve `t²` solves `x t = ∫ s in 0..t, 2 √|x s|` on `[0, 1]`. -/
theorem sq_eq_picard_sqrt {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    t ^ 2 = ODE.picard (fun _ x ↦ 2 * √|x|) 0 0 (fun s ↦ s ^ 2) t := by
  rw [ODE.picard_apply, zero_add]
  have h : ∫ s in (0 : ℝ)..t, 2 * √|s ^ 2| = ∫ s in (0 : ℝ)..t, 2 * s := by
    refine integral_congr fun s hs ↦ ?_
    rw [uIcc_of_le ht.1] at hs
    simp [abs_of_nonneg (sq_nonneg s), sqrt_sq hs.1]
  rw [h, intervalIntegral.integral_const_mul, integral_id]
  ring

/-- The zero curve solves `x t = ∫ s in 0..t, 2 √|x s|`. -/
theorem zero_eq_picard_sqrt (t : ℝ) :
    (0 : ℝ) = ODE.picard (fun _ x ↦ 2 * √|x|) 0 0 (fun _ ↦ 0) t := by
  simp [ODE.picard_apply]

/-- The two solutions `0` and `t²` are different on `(0, 1]`. -/
theorem sq_ne_zero_of_mem_Ioc {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) : t ^ 2 ≠ 0 :=
  pow_ne_zero 2 ht.1.ne'

/-- **The Lipschitz bound is needed.** The field `x ↦ 2 √|x|` is not Lipschitz: at
`x = 1 / (L + 1) ^ 2` it exceeds `L |x|`. -/
theorem not_lipschitzWith_sqrt (L : ℝ≥0) : ¬LipschitzWith L fun x : ℝ ↦ 2 * √|x| := by
  intro hL
  set x : ℝ := 1 / ((L : ℝ) + 1) ^ 2
  have hL1 : (0 : ℝ) < L + 1 := by positivity
  have hx : √|x| = 1 / (L + 1) := by
    rw [abs_of_nonneg (by positivity), sqrt_div' _ (by positivity), sqrt_one, sqrt_sq hL1.le]
  have h := hL.dist_le_mul x 0
  simp only [Real.dist_eq, sub_zero, abs_zero, sqrt_zero, mul_zero, hx] at h
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)] at h
  have : 2 / ((L : ℝ) + 1) ≤ L / ((L : ℝ) + 1) ^ 2 := by simpa [x, div_eq_mul_inv] using h
  rw [div_le_div_iff₀ hL1 (by positivity)] at this
  nlinarith [L.coe_nonneg]

end Sqrt

end TauCeti.Examples.NonlinearCaratheodory
