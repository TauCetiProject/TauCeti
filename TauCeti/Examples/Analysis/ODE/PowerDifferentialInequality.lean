/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.Gronwall.Power

/-!
# Checks for the differential inequality `y' ≤ C yⁿ⁺¹`

These checks exercise `TauCeti.pow_le_div_one_sub_of_deriv_le_mul_pow` and
`TauCeti.inv_le_pow_of_deriv_le_mul_pow_of_not_bddAbove` in the two forms in which energy
methods for the Navier–Stokes and Euler equations integrate them, and show that their constants
are optimal.

* **The existence time of an `Hˢ` bound.** A positive `y` with `y' ≤ C y²` on `(0, t)` obeys
  `y t ≤ y 0 / (1 - C t y 0)` while `C t y 0 < 1`
  (`TauCeti.PowerDifferentialInequalityExample.le_div_one_sub_of_deriv_le_mul_sq`); with
  `y = ‖u‖_{Hˢ}` this keeps `y ≤ 2 y 0` up to time `1 / (2 C y 0)`.
* **Leray's blow-up rate.** If the enstrophy `y = ‖∇u‖₂²` satisfies `y' ≤ C ν⁻³ y³` and is
  unbounded on `[t, T)`, then `ν³ / (2 C (T - t)) ≤ y t ²`
  (`TauCeti.PowerDifferentialInequalityExample.div_le_sq_of_deriv_le_div_mul_pow_three`), so that
  `‖∇u(t)‖₂ ≥ c ν^{3/4} (T - t)^{-1/4}`, and the maximal time obeys `ν³ / (2 C y 0 ²) ≤ T`
  (`TauCeti.PowerDifferentialInequalityExample.div_le_of_deriv_le_div_mul_pow_three`).
* **Sharpness.** For `C > 0` the function `z t = (C (T - t))⁻¹` solves `z' = C z²` on
  `(-∞, T)` (`TauCeti.PowerDifferentialInequalityExample.hasDerivAt_riccatiBlowUp`), is
  unbounded on every `[t, T)`
  (`TauCeti.PowerDifferentialInequalityExample.not_bddAbove_riccatiBlowUp`), and attains both
  bounds with equality
  (`TauCeti.PowerDifferentialInequalityExample.riccatiBlowUp_eq_div_one_sub`, and
  `z t = (C (T - t))⁻¹` by definition).
-/

public section

open Set

namespace TauCeti.PowerDifferentialInequalityExample

variable {y y' : ℝ → ℝ} {C : ℝ}

/-- The existence-time bound for an energy with `y' ≤ C y²`: a positive solution satisfies
`y t ≤ y 0 / (1 - C t y 0)` as long as `C t y 0 < 1`. -/
theorem le_div_one_sub_of_deriv_le_mul_sq {t : ℝ} (ht : 0 ≤ t)
    (hy : ContinuousOn y (Icc 0 t)) (hpos : ∀ s ∈ Icc 0 t, 0 < y s)
    (hy' : ∀ s ∈ Ioo 0 t, HasDerivAt y (y' s) s) (hle : ∀ s ∈ Ioo 0 t, y' s ≤ C * y s ^ 2)
    (hlt : C * t * y 0 < 1) :
    y t ≤ y 0 / (1 - C * t * y 0) := by
  simpa using pow_le_div_one_sub_of_deriv_le_mul_pow (n := 1) ht hy hpos hy' hle
    (by simpa using hlt)

/-- **Leray's blow-up rate for the enstrophy.** If `y' ≤ C ν⁻³ y³` along a positive `y` that is
unbounded on `[t, T)`, then `ν³ / (2 C (T - t)) ≤ y t ²`. -/
theorem div_le_sq_of_deriv_le_div_mul_pow_three {ν t T : ℝ}
    (hy : ContinuousOn y (Ico t T)) (hpos : ∀ s ∈ Ico t T, 0 < y s)
    (hy' : ∀ s ∈ Ioo t T, HasDerivAt y (y' s) s)
    (hle : ∀ s ∈ Ioo t T, y' s ≤ C / ν ^ 3 * y s ^ 3) (hunb : ¬BddAbove (y '' Ico t T)) :
    ν ^ 3 / (2 * C * (T - t)) ≤ y t ^ 2 := by
  have h := inv_le_pow_of_deriv_le_mul_pow_of_not_bddAbove (n := 2) hy hpos hy' hle hunb
  rwa [Nat.cast_ofNat, show 2 * (C / ν ^ 3) * (T - t) = 2 * C * (T - t) / ν ^ 3 by ring,
    inv_div] at h

/-- **Leray's lower bound on the blow-up time.** If `y' ≤ C ν⁻³ y³` along a positive `y` that is
unbounded on `[0, T)`, with `C > 0`, then `ν³ / (2 C y 0 ²) ≤ T`. -/
theorem div_le_of_deriv_le_div_mul_pow_three {ν T : ℝ} (hC : 0 < C)
    (hy : ContinuousOn y (Ico 0 T)) (hpos : ∀ s ∈ Ico 0 T, 0 < y s)
    (hy' : ∀ s ∈ Ioo 0 T, HasDerivAt y (y' s) s)
    (hle : ∀ s ∈ Ioo 0 T, y' s ≤ C / ν ^ 3 * y s ^ 3) (hunb : ¬BddAbove (y '' Ico 0 T)) :
    ν ^ 3 / (2 * C * y 0 ^ 2) ≤ T := by
  have hT : 0 < T := by
    by_contra! h
    exact hunb (by simp [Ico_eq_empty (not_lt.2 h)])
  have h := div_le_sq_of_deriv_le_div_mul_pow_three hy hpos hy' hle hunb
  have hy0 := hpos 0 ⟨le_rfl, hT⟩
  rw [sub_zero, div_le_iff₀ (by positivity)] at h
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- The explicit solution `(C (T - t))⁻¹` of the Riccati equation `z' = C z²`, which blows up at
time `T` when `C > 0`. -/
noncomputable def riccatiBlowUp (C T t : ℝ) : ℝ :=
  (C * (T - t))⁻¹

/-- The function `riccatiBlowUp C T` solves `z' = C z²` before its blow-up time `T`. -/
theorem hasDerivAt_riccatiBlowUp {T t : ℝ} (hC : C ≠ 0) (ht : t < T) :
    HasDerivAt (riccatiBlowUp C T) (C * riccatiBlowUp C T t ^ 2) t := by
  have hne : C * (T - t) ≠ 0 := mul_ne_zero hC (sub_ne_zero.2 ht.ne')
  have h := (((hasDerivAt_id' t).const_sub T).const_mul C).inv hne
  unfold riccatiBlowUp
  convert h using 1
  field_simp

/-- The bound before blow-up is attained by `riccatiBlowUp C T` on `[a, b]` with `b < T`. -/
theorem riccatiBlowUp_eq_div_one_sub {T a b : ℝ} (hC : C ≠ 0) (hb : b < T) (hab : a ≤ b) :
    riccatiBlowUp C T b = riccatiBlowUp C T a / (1 - C * (b - a) * riccatiBlowUp C T a) := by
  have h1 : T - b ≠ 0 := sub_ne_zero.2 hb.ne'
  have h2 : T - a ≠ 0 := sub_ne_zero.2 (hab.trans_lt hb).ne'
  have h3 : 1 - C * (b - a) * (C * (T - a))⁻¹ = (T - b) / (T - a) := by
    field_simp
    ring
  simp only [riccatiBlowUp]
  rw [h3]
  field_simp

/-- For `C > 0` the function `riccatiBlowUp C T` is unbounded on every `[t, T)` with `t < T`. -/
theorem not_bddAbove_riccatiBlowUp {T t : ℝ} (hC : 0 < C) (ht : t < T) :
    ¬BddAbove (riccatiBlowUp C T '' Ico t T) := by
  rintro ⟨M, hM⟩
  -- At `s = T - δ` with `δ = min (T - t) (C (|M| + 1))⁻¹ / 2`, the value `(C δ)⁻¹` exceeds `M`.
  set δ := min (T - t) (C * (|M| + 1))⁻¹ / 2 with hδ
  have hδpos : 0 < δ := by positivity
  have hmem : T - δ ∈ Ico t T := ⟨by linarith [min_le_left (T - t) (C * (|M| + 1))⁻¹], by linarith⟩
  have hval := hM ⟨T - δ, hmem, rfl⟩
  simp only [riccatiBlowUp, sub_sub_cancel] at hval
  have hlt : C * δ < (|M| + 1)⁻¹ := by
    have : δ < (C * (|M| + 1))⁻¹ := by
      linarith [min_le_right (T - t) (C * (|M| + 1))⁻¹]
    calc C * δ < C * (C * (|M| + 1))⁻¹ := by gcongr
      _ = (|M| + 1)⁻¹ := by field_simp
  have : |M| + 1 < (C * δ)⁻¹ := by
    rw [lt_inv_comm₀ (by positivity) (by positivity)]
    exact hlt
  linarith [le_abs_self M]

end TauCeti.PowerDifferentialInequalityExample
