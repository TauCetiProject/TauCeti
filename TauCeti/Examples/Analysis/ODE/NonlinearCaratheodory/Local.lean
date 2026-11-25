/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.NonlinearCaratheodory.Ball
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Checks for the local nonlinear Carathéodory theorem

Checks for the nonlinear Carathéodory theorem on a ball
(`TauCeti.exists_continuousOn_mapsTo_closedBall_forall_mem_Icc_eq_picard`,
`TauCeti.eqOn_of_mapsTo_closedBall_of_forall_mem_Icc_eq_picard`,
`TauCeti.mapsTo_closedBall_of_forall_mem_Icc_eq_picard`).

* **Agreement with Mathlib.** For a field satisfying `IsPicardLindelof` with a constant Lipschitz
  bound, the solutions with values in the ball are Mathlib's solution, provided that solution also
  takes values in the ball
  (`TauCeti.Examples.NonlinearCaratheodoryLocal.eqOn_of_isPicardLindelof`).
* **A global Lipschitz bound is needed for the global statement.** The field `F(t, x) = x²` from
  `x₀ = 1` at `t₀ = 0` has the solution `1/(1 − t)` on `[0, 1)`
  (`TauCeti.Examples.NonlinearCaratheodoryLocal.inv_one_sub_eq_picard_sq`), which leaves every ball
  before `t = 1` (`TauCeti.Examples.NonlinearCaratheodoryLocal.exists_lt_inv_one_sub`). On the
  ball of radius `r = 1` about `1` the field is Lipschitz with `L = 2(1 + r) = 4`
  (`TauCeti.Examples.NonlinearCaratheodoryLocal.lipschitzOnWith_sq`) and `|F(t, 1)| ≤ m = 1`, and
  `τ = 1/10` satisfies `τ e^{4τ} < 1`
  (`TauCeti.Examples.NonlinearCaratheodoryLocal.integral_mul_exp_integral_lt_one`). So the local
  form applies on `[0, 1/10]`, and every solution there is `1/(1 − t)`
  (`TauCeti.Examples.NonlinearCaratheodoryLocal.eqOn_inv_one_sub_of_picard_sq`), which indeed stays
  in the ball.
* **The local uniqueness clause needs the ball or the strict inequality.** Let `F(t, x) = 1` for
  `t < 1` and `F(t, x) = 2 √(max (x − 1) 0)` for `t ≥ 1`, with `x₀ = 0`, `t₀ = 0` and `r = 1`. On
  the ball `[−1, 1]` every `F(t, ·)` is constant, so Lipschitz with `L = 0`, and
  `|F(t, 0)| ≤ m(t) = 1_{t < 1}`, so that `(∫₀² m) e⁰ = 1 = r`
  (`TauCeti.Examples.NonlinearCaratheodoryLocal.integral_indicator_mul_exp_integral_eq_one`).
  Both `min(t, 1)` and the curve equal to `t` on `[0, 1]` and to `1 + (t − 1)²` on `[1, 2]` solve
  the equation on `[0, 2]`
  (`TauCeti.Examples.NonlinearCaratheodoryLocal.min_eq_picard_switch`,
  `TauCeti.Examples.NonlinearCaratheodoryLocal.escape_eq_picard_switch`); the second leaves the
  ball (`TauCeti.Examples.NonlinearCaratheodoryLocal.escape_two_notMem_closedBall`). For `τ < 1`
  the inequality is strict and `t` is the only solution on `[0, τ]`
  (`TauCeti.Examples.NonlinearCaratheodoryLocal.eqOn_id_of_picard_switch`).
-/

public section

open MeasureTheory Set intervalIntegral Real Metric

open scoped NNReal Interval

namespace TauCeti.Examples.NonlinearCaratheodoryLocal

section PicardLindelof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {f : ℝ → E → E}
  {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ : E} {a r L K : ℝ≥0}

/-- **Agreement with Mathlib's Picard–Lindelöf theorem.** Let `f` satisfy the hypotheses
`IsPicardLindelof` on `[tmin, tmax]` from `t₀`, with the constant Lipschitz bound `K` on the ball
of radius `a` about `x₀`, and let `α` be a solution of the initial value problem in Mathlib's sense
(`α t₀ = x₀` and `α' = f(t, α)` on `[tmin, tmax]`, as given by
`IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt`) that moreover takes values in the
ball. Then every curve continuous on `[tmin, tmax]` with values in the ball that solves the
integral equation of the nonlinear Carathéodory theorem with `L = K` is `α`. -/
theorem eqOn_of_isPicardLindelof (hf : IsPicardLindelof f t₀ x₀ a r L K) {α : ℝ → E}
    (hα₀ : α t₀ = x₀)
    (hα : ∀ t ∈ Icc tmin tmax, HasDerivWithinAt α (f t (α t)) (Icc tmin tmax) t)
    (hαB : MapsTo α (Icc tmin tmax) (closedBall x₀ a)) {Y : ℝ → E}
    (hY : ContinuousOn Y (Icc tmin tmax)) (hYB : MapsTo Y (Icc tmin tmax) (closedBall x₀ a))
    (h : ∀ t ∈ Icc tmin tmax, Y t = ODE.picard f t₀ x₀ Y t) :
    EqOn Y α (Icc tmin tmax) := by
  -- Mathlib's solution solves the integral equation, by the fundamental theorem of calculus.
  have hαsol : ∀ t ∈ Icc tmin tmax, α t = ODE.picard f t₀ x₀ α t := fun t htI ↦ by
    have hsub : uIcc (t₀ : ℝ) t ⊆ Icc tmin tmax := uIcc_subset_Icc t₀.property htI
    rw [← hα₀]
    exact (ODE.picard_eq_of_hasDerivAt
      (hf.continuousOn_uncurry.mono (prod_mono hsub subset_rfl))
      (fun t' ht' ↦ (hα t' (hsub ht')).mono hsub) (hαB.mono_left hsub)).symm
  exact eqOn_of_mapsTo_closedBall_of_forall_mem_Icc_eq_picard (L := fun _ ↦ K) t₀.property
    (fun x hx ↦ (hf.continuousOn x hx).integrableOn_compact isCompact_Icc)
    (integrableOn_const (by simp)) (ae_restrict_of_forall_mem measurableSet_Icc hf.lipschitzOnWith)
    hY (HasDerivWithinAt.continuousOn hα) hYB hαB h hαsol

end PicardLindelof

section Square

/-- The curve `1/(1 − t)` solves `x t = 1 + ∫ s in 0..t, x(s)²` on `[0, 1)`. -/
theorem inv_one_sub_eq_picard_sq {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    (1 - t)⁻¹ = ODE.picard (fun _ x ↦ x ^ 2) 0 1 (fun s ↦ (1 - s)⁻¹) t := by
  rw [ODE.picard_apply]
  have hne : ∀ s ∈ uIcc 0 t, 1 - s ≠ 0 := fun s hs ↦ by
    rw [uIcc_of_le ht.1] at hs
    exact (sub_pos.2 (hs.2.trans_lt ht.2)).ne'
  have hderiv : ∀ s ∈ uIcc 0 t, HasDerivAt (fun s ↦ (1 - s)⁻¹) ((1 - s)⁻¹ ^ 2) s := fun s hs ↦ by
    refine (((hasDerivAt_id s).const_sub 1).inv (hne s hs)).congr_deriv ?_
    simp only [id, neg_neg, one_div, inv_pow]
  have hcont : ContinuousOn (fun s : ℝ ↦ (1 - s)⁻¹ ^ 2) (uIcc 0 t) :=
    ((continuousOn_const.sub continuousOn_id).inv₀ hne).pow 2
  rw [integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  simp

/-- **The solution leaves every ball before `t = 1`.** -/
theorem exists_lt_inv_one_sub (R : ℝ) : ∃ t ∈ Ico (0 : ℝ) 1, R < (1 - t)⁻¹ := by
  set R' := max R 1
  refine ⟨1 - (R' + 1)⁻¹, ⟨?_, ?_⟩, ?_⟩
  · rw [sub_nonneg]
    exact inv_le_one_of_one_le₀ (by linarith [le_max_right R 1])
  · rw [sub_lt_self_iff]
    positivity
  · rw [sub_sub_cancel, inv_inv]
    linarith [le_max_left R 1]

/-- On the ball of radius `1` about `1`, the field `x ↦ x²` is Lipschitz with constant
`2 (1 + 1) = 4`. -/
theorem lipschitzOnWith_sq : LipschitzOnWith 4 (fun x : ℝ ↦ x ^ 2) (closedBall 1 1) := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_
  rw [mem_closedBall, Real.dist_eq, abs_le] at hx hy
  rw [Real.dist_eq, Real.dist_eq, show x ^ 2 - y ^ 2 = (x + y) * (x - y) by ring, abs_mul]
  have hxy : |x + y| ≤ 4 := abs_le.2 ⟨by linarith, by linarith⟩
  push_cast
  exact mul_le_mul_of_nonneg_right hxy (abs_nonneg _)

/-- The smallness condition of the local form holds strictly for `τ = 1/10`:
`(∫₀^τ 1) e^{∫₀^τ 4} = e^{2/5}/10 < 1`. -/
theorem integral_mul_exp_integral_lt_one :
    (∫ _ in (0 : ℝ)..1 / 10, (1 : ℝ)) * exp (∫ _ in (0 : ℝ)..1 / 10, ((4 : ℝ≥0) : ℝ)) < 1 := by
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
  have h : exp (1 / 10 * ((4 : ℝ≥0) : ℝ)) < 10 := by
    calc exp (1 / 10 * ((4 : ℝ≥0) : ℝ)) ≤ exp 1 := exp_le_exp.2 (by norm_num)
      _ < 10 := Real.exp_one_lt_d9.trans (by norm_num)
  linarith

/-- **The local form applies on `[0, 1/10]`, and its solution is `1/(1 − t)`.** Every curve
continuous on `[0, 1/10]` solving `x t = 1 + ∫ s in 0..t, x(s)²` there is `1/(1 − t)`: by the
strict inequality it stays in the ball of radius `1` about `1`, where the field is Lipschitz. -/
theorem eqOn_inv_one_sub_of_picard_sq {Y : ℝ → ℝ} (hY : ContinuousOn Y (Icc 0 (1 / 10)))
    (h : ∀ t ∈ Icc (0 : ℝ) (1 / 10), Y t = ODE.picard (fun _ x ↦ x ^ 2) 0 1 Y t) :
    EqOn Y (fun t ↦ (1 - t)⁻¹) (Icc 0 (1 / 10)) := by
  have ht₀ : (0 : ℝ) ∈ Icc (0 : ℝ) (1 / 10) := ⟨le_rfl, by norm_num⟩
  have hLip : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) (1 / 10)),
      LipschitzOnWith ((fun _ ↦ (4 : ℝ≥0)) t) ((fun _ x ↦ x ^ 2) t) (closedBall (1 : ℝ) 1) :=
    .of_forall fun _ ↦ lipschitzOnWith_sq
  have hL : IntegrableOn (fun _ ↦ ((4 : ℝ≥0) : ℝ)) (Icc (0 : ℝ) (1 / 10)) :=
    integrableOn_const (by simp)
  have hm : IntegrableOn (fun _ ↦ (1 : ℝ)) (Icc (0 : ℝ) (1 / 10)) := integrableOn_const (by simp)
  have hFm : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) (1 / 10)),
      ‖(fun _ x ↦ x ^ 2) t (1 : ℝ)‖ ≤ (fun _ ↦ (1 : ℝ)) t := .of_forall fun _ ↦ by simp
  have hcont : ContinuousOn (fun t : ℝ ↦ (1 - t)⁻¹) (Icc 0 (1 / 10)) :=
    (continuousOn_const.sub continuousOn_id).inv₀ fun t ht ↦
      (sub_pos.2 (by linarith [ht.2] : t < 1)).ne'
  have hsol : ∀ t ∈ Icc (0 : ℝ) (1 / 10),
      (1 - t)⁻¹ = ODE.picard (fun _ x ↦ x ^ 2) 0 1 (fun s ↦ (1 - s)⁻¹) t :=
    fun t ht ↦ inv_one_sub_eq_picard_sq ⟨ht.1, by linarith [ht.2]⟩
  exact eqOn_of_mapsTo_closedBall_of_forall_mem_Icc_eq_picard ht₀
    (fun x _ ↦ integrableOn_const (C := x ^ 2) (by simp)) hL hLip hY hcont
    (mapsTo_closedBall_of_forall_mem_Icc_eq_picard hL hLip hm hFm
      integral_mul_exp_integral_lt_one hY h)
    (mapsTo_closedBall_of_forall_mem_Icc_eq_picard hL hLip hm hFm
      integral_mul_exp_integral_lt_one hcont hsol)
    h hsol

end Square

section Switch

/-- The field `F(t, x) = 1` for `t < 1` and `F(t, x) = 2 √(max (x − 1) 0)` for `t ≥ 1`. -/
noncomputable def switch (t x : ℝ) : ℝ :=
  if t < 1 then 1 else 2 * √(max (x - 1) 0)

/-- The curve equal to `t` on `[0, 1]` and to `1 + (t − 1)²` for `t ≥ 1`. -/
noncomputable def escape (t : ℝ) : ℝ :=
  if t ≤ 1 then t else 1 + (t - 1) ^ 2

/-- On the ball `[−1, 1]` the field `switch t` is constant, so Lipschitz with constant `0`. -/
theorem lipschitzOnWith_switch (t : ℝ) : LipschitzOnWith 0 (switch t) (closedBall 0 1) := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_
  rw [mem_closedBall, Real.dist_eq, sub_zero, abs_le] at hx hy
  have hx' : max (x - 1) 0 = 0 := max_eq_right (by linarith)
  have hy' : max (y - 1) 0 = 0 := max_eq_right (by linarith)
  simp [switch, hx', hy']

/-- At the initial value the field is bounded by `m = 1_{t < 1}`. -/
theorem norm_switch_zero_le (t : ℝ) :
    ‖switch t 0‖ ≤ (Iio (1 : ℝ)).indicator 1 t := by
  by_cases ht : t < 1
  · simp [switch, ht]
  · simp [switch, ht]

/-- `(∫₀² 1_{t < 1}) e⁰ = 1`: the smallness condition of the local form holds with equality for
`r = 1`. -/
theorem integral_indicator_mul_exp_integral_eq_one :
    (∫ t in (0 : ℝ)..2, (Iio (1 : ℝ)).indicator 1 t) * exp (∫ _ in (0 : ℝ)..2, ((0 : ℝ≥0) : ℝ)) =
      1 := by
  rw [integral_of_le (by norm_num), MeasureTheory.integral_indicator measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio]
  have h : Iio (1 : ℝ) ∩ Ioc 0 2 = Ioo 0 1 := by
    ext x
    simp only [mem_inter_iff, mem_Iio, mem_Ioc, mem_Ioo]
    exact ⟨fun ⟨h1, h2, _⟩ ↦ ⟨h2, h1⟩, fun ⟨h1, h2⟩ ↦ ⟨h2, h1, by linarith⟩⟩
  simp [h]

/-- The integral of a function equal to `1` before time `1` and to a continuous `g` from time `1`
on: `∫₀ᵗ = min t 1 + ∫₁^{max t 1} g`. -/
private theorem integral_ite_lt_one {g : ℝ → ℝ} (hg : Continuous g) {t : ℝ} (ht : 0 ≤ t) :
    ∫ s in (0 : ℝ)..t, (if s < 1 then 1 else g s) = min t 1 + ∫ s in (1 : ℝ)..max t 1, g s := by
  set f : ℝ → ℝ := fun s ↦ if s < 1 then 1 else g s
  -- Before time `1`, `f` is `1` almost everywhere.
  have hae {b : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1) :
      ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ι 0 b → f s = 1 := by
    filter_upwards [volume.ae_ne (1 : ℝ)] with s hs hsI
    rw [uIoc_of_le hb] at hsI
    simp [f, lt_of_le_of_ne (hsI.2.trans hb1) hs]
  have hI {b : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1) : IntervalIntegrable f volume 0 b :=
    (intervalIntegrable_const (c := (1 : ℝ))).congr_ae
      ((ae_restrict_iff' measurableSet_uIoc).2 ((hae hb hb1).mono fun _ h hs ↦ (h hs).symm))
  rcases le_total t 1 with h1 | h1
  · rw [min_eq_left h1, max_eq_right h1, integral_same, add_zero,
      integral_congr_ae (hae ht h1)]
    simp
  · have hfg : ∀ s ∈ uIcc 1 t, f s = g s := fun s hs ↦ by
      rw [uIcc_of_le h1] at hs
      simp [f, not_lt.2 hs.1]
    have hI₂ : IntervalIntegrable f volume 1 t :=
      (hg.intervalIntegrable 1 t).congr_ae ((ae_restrict_iff' measurableSet_uIoc).2
        (.of_forall fun s hs ↦ (hfg s (uIoc_subset_uIcc hs)).symm))
    rw [← integral_add_adjacent_intervals (hI zero_le_one le_rfl) hI₂, min_eq_right h1,
      max_eq_left h1, integral_congr_ae (hae zero_le_one le_rfl), integral_congr hfg]
    simp

/-- The curve `min t 1` solves the equation of `switch` on `[0, 2]`. -/
theorem min_eq_picard_switch {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) :
    min t 1 = ODE.picard switch 0 0 (fun s ↦ min s 1) t := by
  rw [ODE.picard_apply, zero_add]
  have h : (fun s ↦ switch s (min s 1)) = fun s ↦ if s < 1 then 1 else (fun _ ↦ (0 : ℝ)) s :=
    funext fun s ↦ by
      by_cases hs : s < 1
      · simp [switch, hs]
      · simp [switch, hs, min_eq_right (not_lt.1 hs)]
  rw [h, integral_ite_lt_one continuous_const ht.1]
  simp

/-- The curve `escape`, equal to `t` on `[0, 1]` and to `1 + (t − 1)²` after, also solves the
equation of `switch` on `[0, 2]`. -/
theorem escape_eq_picard_switch {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) :
    escape t = ODE.picard switch 0 0 escape t := by
  rw [ODE.picard_apply, zero_add]
  have h : (fun s ↦ switch s (escape s)) =
      fun s ↦ if s < 1 then 1 else (fun s ↦ 2 * (s - 1)) s :=
    funext fun s ↦ by
      by_cases hs : s < 1
      · simp [switch, hs]
      · have hs' : 1 ≤ s := not_lt.1 hs
        have hmax : max (escape s - 1) 0 = (s - 1) ^ 2 := by
          by_cases hs1 : s ≤ 1
          · simp [escape, le_antisymm hs1 hs']
          · simp [escape, hs1, sq_nonneg]
        simp [switch, hs, hmax, sqrt_sq (sub_nonneg.2 hs')]
  rw [h, integral_ite_lt_one (by fun_prop) ht.1]
  rcases le_total t 1 with h1 | h1
  · simp [escape, h1]
  · rcases h1.eq_or_lt with h1 | h1
    · simp [escape, ← h1]
    · simp only [escape, not_le.2 h1, ↓reduceIte, min_eq_right h1.le, max_eq_left h1.le]
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
        intervalIntegral.intervalIntegrable_id intervalIntegrable_const, integral_id,
        intervalIntegral.integral_const]
      simp only [smul_eq_mul, mul_one]
      ring

/-- The curve `escape` leaves the ball `[−1, 1]`, since `escape 2 = 2`. -/
theorem escape_two_notMem_closedBall : escape 2 ∉ closedBall (0 : ℝ) 1 := by
  rw [show escape 2 = 2 by norm_num [escape], mem_closedBall, Real.dist_eq]
  norm_num

/-- **With the strict inequality the solution is unique.** For `0 ≤ τ < 1`,
`(∫₀^τ 1) e⁰ = τ < 1`, and every curve continuous on `[0, τ]` solving the equation of `switch`
there is `t`. -/
theorem eqOn_id_of_picard_switch {τ : ℝ} (hτ : τ < 1) {Y : ℝ → ℝ}
    (hY : ContinuousOn Y (Icc 0 τ)) (h : ∀ t ∈ Icc (0 : ℝ) τ, Y t = ODE.picard switch 0 0 Y t) :
    EqOn Y id (Icc 0 τ) := by
  rcases lt_or_ge τ 0 with hτ0 | hτ0
  · simp [Icc_eq_empty_of_lt hτ0]
  have ht₀ : (0 : ℝ) ∈ Icc (0 : ℝ) τ := ⟨le_rfl, hτ0⟩
  have hF1 : ∀ t ∈ Icc (0 : ℝ) τ, ∀ x, switch t x = 1 := fun t ht x ↦ by
    simp [switch, ht.2.trans_lt hτ]
  have hLip : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) τ),
      LipschitzOnWith ((fun _ ↦ (0 : ℝ≥0)) t) (switch t) (closedBall (0 : ℝ) 1) :=
    .of_forall fun t ↦ lipschitzOnWith_switch t
  have hL : IntegrableOn (fun _ ↦ ((0 : ℝ≥0) : ℝ)) (Icc (0 : ℝ) τ) := by simp
  have hm : IntegrableOn (fun _ ↦ (1 : ℝ)) (Icc (0 : ℝ) τ) := integrableOn_const (by simp)
  have hFm : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) τ), ‖switch t 0‖ ≤ (fun _ ↦ (1 : ℝ)) t :=
    .of_forall fun t ↦ (norm_switch_zero_le t).trans (by
      by_cases ht : t < 1 <;> simp [ht])
  have hr : (∫ _ in (0 : ℝ)..τ, (1 : ℝ)) * exp (∫ _ in (0 : ℝ)..τ, ((0 : ℝ≥0) : ℝ)) < 1 := by
    simpa using hτ
  have hsol : ∀ t ∈ Icc (0 : ℝ) τ, id t = ODE.picard switch 0 0 id t := fun t ht ↦ by
    rw [ODE.picard_apply, zero_add, integral_congr (g := fun _ ↦ (1 : ℝ)) fun s hs ↦ hF1 s
      (uIcc_subset_Icc ht₀ ht hs) _]
    simp
  have hF : ∀ x ∈ closedBall (0 : ℝ) 1, IntegrableOn (fun t ↦ switch t x) (Icc 0 τ) :=
    fun x _ ↦ hm.congr_fun (fun t ht ↦ (hF1 t ht x).symm) measurableSet_Icc
  exact eqOn_of_mapsTo_closedBall_of_forall_mem_Icc_eq_picard ht₀ hF hL hLip hY
    continuousOn_id (mapsTo_closedBall_of_forall_mem_Icc_eq_picard hL hLip hm hFm hr hY h)
    (mapsTo_closedBall_of_forall_mem_Icc_eq_picard hL hLip hm hFm hr continuousOn_id hsol)
    h hsol

end Switch

end TauCeti.Examples.NonlinearCaratheodoryLocal
