/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.NonlinearCaratheodory.Basic
public import TauCeti.Analysis.ODE.VariationOfConstants
public import Mathlib.Analysis.ODE.ExistUnique
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
* **Agreement with Mathlib's Picard-Lindelöf theorem.** For a field `F` continuous in time
  with every `F t` Lipschitz with one constant `K`, a solution of the integral equation on
  `[a, b]` agrees there with every solution of `x' = F(t, x)`, `x(t₀) = x₀`, in the sense of Mathlib
  (`TauCeti.Examples.NonlinearCaratheodory.eqOn_of_hasDerivWithinAt`); in particular with the
  solution given by `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀`
  (`TauCeti.Examples.NonlinearCaratheodory.exists_eqOn_of_isPicardLindelof`).
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

section PicardLindelof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {F : ℝ → E → E}
  {K : ℝ≥0} {a b t₀ : ℝ} {x₀ : E}

/-- A solution of `x' = F(t, x)` on `[a, b]` in the sense of Mathlib solves the integral
equation there, when `F` is continuous in time and every `F t` is `K`-Lipschitz. -/
private theorem eq_picard_of_hasDerivWithinAt (hLip : ∀ t, LipschitzWith K (F t))
    (hc : ∀ x, ContinuousOn (F · x) (Icc a b)) (ht₀ : t₀ ∈ Icc a b) {y : ℝ → E}
    (hy₀ : y t₀ = x₀) (hy : ∀ t ∈ Icc a b, HasDerivWithinAt y (F t (y t)) (Icc a b) t) {t : ℝ}
    (ht : t ∈ Icc a b) : y t = ODE.picard F t₀ x₀ y t := by
  have hyc : ContinuousOn y (Icc a b) := fun t ht ↦ (hy t ht).continuousWithinAt
  have hFy : ContinuousOn (fun s ↦ F s (y s)) (Icc a b) :=
    ODE.continuousOn_comp (u := univ) (continuousOn_prod_of_continuousOn_lipschitzOnWith'
      (Function.uncurry F) K (fun s _ ↦ (hLip s).lipschitzOnWith) fun x _ ↦ hc x) hyc
      (mapsTo_univ _ _)
  have hsub : uIcc t₀ t ⊆ Icc a b := uIcc_subset_Icc ht₀ ht
  rw [ODE.picard_apply, integral_eq_sub_of_hasDeriv_right (hyc.mono hsub) (fun s hs ↦ ?_)
    ((hFy.mono hsub).intervalIntegrable), hy₀, add_sub_cancel]
  have hs' : s ∈ Ioo a b := ⟨(le_min ht₀.1 ht.1).trans_lt hs.1, hs.2.trans_le (max_le ht₀.2 ht.2)⟩
  exact ((hy s (Ioo_subset_Icc_self hs')).hasDerivAt (Icc_mem_nhds hs'.1 hs'.2)).hasDerivWithinAt

/-- **Agreement with Mathlib's notion of solution.** Let `F` be continuous in time on `[a, b]`,
with every `F t` Lipschitz with one constant `K`. A curve continuous on `[a, b]` solving the
integral equation `x t = x₀ + ∫ s in t₀..t, F s (x s)` there agrees on `[a, b]` with every
solution of `y' = F(t, y)`, `y(t₀) = x₀`, in the sense of Mathlib. -/
theorem eqOn_of_hasDerivWithinAt (hLip : ∀ t, LipschitzWith K (F t))
    (hc : ∀ x, ContinuousOn (F · x) (Icc a b)) (ht₀ : t₀ ∈ Icc a b) {x y : ℝ → E}
    (hx : ContinuousOn x (Icc a b)) (hxp : ∀ t ∈ Icc a b, x t = ODE.picard F t₀ x₀ x t)
    (hy₀ : y t₀ = x₀) (hy : ∀ t ∈ Icc a b, HasDerivWithinAt y (F t (y t)) (Icc a b) t) :
    EqOn x y (Icc a b) :=
  eqOn_of_forall_mem_Icc_eq_picard_of_lipschitzWith (L := fun _ ↦ K)
    (fun x ↦ (hc x).integrableOn_Icc) continuousOn_const.integrableOn_Icc
    (Filter.Eventually.of_forall hLip) ht₀ hx
    (fun t ht ↦ (hy t ht).continuousWithinAt) hxp
    fun _ ht ↦ eq_picard_of_hasDerivWithinAt hLip hc ht₀ hy₀ hy ht

/-- **Agreement with Mathlib's Picard-Lindelöf theorem.** If `F` satisfies `IsPicardLindelof` on
`[a, b]` with initial time `t₀` and value `x₀`, and moreover is continuous in time with every
`F t` Lipschitz with one constant `K`, then the solution given by Mathlib
(`IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀`) is the solution of the integral
equation of the nonlinear Carathéodory theorem on `[a, b]`. -/
theorem exists_eqOn_of_isPicardLindelof {t₀ : Icc a b} {r L K' : ℝ≥0}
    (hPL : IsPicardLindelof F t₀ x₀ r 0 L K') (hLip : ∀ t, LipschitzWith K (F t))
    (hc : ∀ x, ContinuousOn (F · x) (Icc a b)) :
    ∃ y : ℝ → E, y t₀ = x₀ ∧ (∀ t ∈ Icc a b, HasDerivWithinAt y (F t (y t)) (Icc a b) t) ∧
      ∀ x : ℝ → E, ContinuousOn x (Icc a b) →
        (∀ t ∈ Icc a b, x t = ODE.picard F t₀ x₀ x t) → EqOn x y (Icc a b) := by
  obtain ⟨y, hy₀, hy⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨y, hy₀, hy, fun x hx hxp ↦ eqOn_of_hasDerivWithinAt hLip hc t₀.property hx hxp hy₀ hy⟩

end PicardLindelof

end TauCeti.Examples.NonlinearCaratheodory
