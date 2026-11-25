/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.SiegelFunction.Basic

/-!
# Leading terms of Siegel functions at infinity

For `0 ≤ r₁ < 1`, the leading exponential of `g_r(τ)` is
`exp (π i B₂(r₁) τ)`. After removing it the limit is
`-exp (π i r₂ (r₁ - 1))`, except on the boundary `r₁ = 0`, where the additional factor
`1 - exp (2π i r₂)` remains. These limits hold as `Im τ → ∞`, uniformly with respect to the
unrestricted real part, and retain the exact complex phase.

For `r ∉ ℤ²` the leading coefficient is nonzero. Consequently the logarithmic `q`-order is
`B₂(r₁)/2`: `log ‖g_r(τ)‖ / log ‖exp (2π i τ)‖ → B₂(r₁)/2`.
This is the growth calculation underlying the orders of Siegel modular units at cusps;
it does not assert that an arbitrary real-indexed Siegel function has an integral Laurent
expansion in `q`. In the same way every integral power `g_r^m` with `r ∉ ℤ²` is
`O(|q|^(m B₂({r₁})/2))` at `i∞`, where `{r₁}` is the fractional part of `r₁`
(`TauCeti.ModularForm.isBigO_siegelFunction_zpow`); this bounds products of Siegel functions at
the cusps, so that they extend to meromorphic functions on modular curves.

## References

* D. S. Kubert, S. Lang, *Modular Units*, Chapter 2, §1.
* D. H. Shin, *Generation of class fields by Siegel–Ramachandra invariants*, §2.
-/

public section

open Complex Filter
open UpperHalfPlane hiding I
open scoped Real Topology

namespace TauCeti.ModularForm

/-- The infinite-product part of `g_r` tends to `1` when `-1 < r₁ < 1`. -/
private theorem tendsto_siegelFunction_product {r : Fin 2 → ℝ}
    (hlo : -1 < r 0) (hhi : r 0 < 1) :
    Tendsto (fun τ : ℍ ↦
      (∏' n : ℕ, (1 - cexp (2 * π * I * (τ : ℂ)) ^ (n + 1) *
        cexp (2 * π * I * (r 0 * (τ : ℂ) + r 1)))) *
      ∏' n : ℕ, (1 - cexp (2 * π * I * (τ : ℂ)) ^ (n + 1) *
        cexp (-(2 * π * I * (r 0 * (τ : ℂ) + r 1))))) atImInfty (𝓝 1) := by
  have hq := UpperHalfPlane.tendsto_exp_two_pi_I_mul_add (by norm_num : (0 : ℝ) < 1) 0
  simp only [ofReal_one, one_mul, ofReal_zero, add_zero] at hq
  have hplus : Tendsto (fun τ : ℍ ↦ cexp (2 * π * I * (τ : ℂ)) *
      cexp (2 * π * I * (r 0 * (τ : ℂ) + r 1))) atImInfty (𝓝 0) := by
    convert UpperHalfPlane.tendsto_exp_two_pi_I_mul_add
      (by linarith : 0 < 1 + r 0) (r 1) using 1
    funext τ
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hminus : Tendsto (fun τ : ℍ ↦ cexp (2 * π * I * (τ : ℂ)) *
      cexp (-(2 * π * I * (r 0 * (τ : ℂ) + r 1)))) atImInfty (𝓝 0) := by
    convert UpperHalfPlane.tendsto_exp_two_pi_I_mul_add
      (by linarith : 0 < 1 - r 0) (-r 1) using 1
    funext τ
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simpa only [one_mul] using
    (tendsto_tprod_one_sub_pow_mul hq hplus).mul (tendsto_tprod_one_sub_pow_mul hq hminus)

/-- **The exact leading coefficient of a Siegel function.** For `0 ≤ r₁ < 1`, removing
`exp (π i B₂(r₁) τ)` leaves `-exp (π i r₂ (r₁ - 1))`, with the extra factor
`1 - exp (2π i r₂)` when `r₁ = 0`. -/
theorem tendsto_siegelFunction_mul_exp_neg {r : Fin 2 → ℝ}
    (hlo : 0 ≤ r 0) (hhi : r 0 < 1) :
    Tendsto (fun τ : ℍ ↦ siegelFunction r τ * cexp (-(π * I * bernoulliFun 2 (r 0) * τ)))
      atImInfty (𝓝 (-cexp (π * I * r 1 * (r 0 - 1)) *
        (if r 0 = 0 then 1 - cexp (2 * π * I * r 1) else 1))) := by
  have hfirst : Tendsto (fun τ : ℍ ↦ 1 - cexp (2 * π * I * (r 0 * (τ : ℂ) + r 1)))
      atImInfty (𝓝 (if r 0 = 0 then 1 - cexp (2 * π * I * r 1) else 1)) := by
    by_cases hzero : r 0 = 0
    · simp [hzero]
    · simpa [hzero] using tendsto_const_nhds.sub
        (UpperHalfPlane.tendsto_exp_two_pi_I_mul_add (lt_of_le_of_ne hlo (Ne.symm hzero)) (r 1))
  have h := (hfirst.mul (tendsto_siegelFunction_product (by linarith) hhi)).const_mul
    (-cexp (π * I * r 1 * (r 0 - 1)))
  simp only [mul_one] at h
  refine h.congr fun τ ↦ ?_
  rw [siegelFunction_eq_mul_tprod_mul_tprod r τ.im_pos]
  simp only [Complex.exp_neg]
  field_simp

/-- **The leading absolute value of a Siegel function.** For `0 ≤ r₁ < 1`, its norm divided by
`|q|^(B₂(r₁)/2)` tends to `1`, or to `|1 - exp (2π i r₂)|` on the boundary `r₁ = 0`. -/
theorem tendsto_norm_siegelFunction_div_rpow {r : Fin 2 → ℝ}
    (hlo : 0 ≤ r 0) (hhi : r 0 < 1) :
    Tendsto (fun τ : ℍ ↦ ‖siegelFunction r τ‖ /
      ‖cexp (2 * π * I * (τ : ℂ))‖ ^ (bernoulliFun 2 (r 0) / 2)) atImInfty
      (𝓝 (if r 0 = 0 then ‖1 - cexp (2 * π * I * r 1)‖ else 1)) := by
  have h := (tendsto_siegelFunction_mul_exp_neg hlo hhi).norm
  have hphase : ‖cexp (π * I * r 1 * (r 0 - 1))‖ = 1 := by simp [Complex.norm_exp]
  simp only [norm_mul, norm_neg, hphase, one_mul] at h
  simp only [apply_ite norm, norm_one] at h
  convert h using 1
  funext τ
  rw [UpperHalfPlane.norm_exp_two_pi_I_mul, ← Real.exp_mul, div_eq_mul_inv,
    ← Real.exp_neg, Complex.norm_exp]
  congr 2
  simp only [neg_re, mul_re, mul_im, Complex.I_re, Complex.I_im, ofReal_re, ofReal_im,
    mul_zero, zero_add, add_zero, mul_one, coe_im]
  ring

/-- For `r ∉ ℤ²` the leading coefficient in
`TauCeti.ModularForm.tendsto_norm_siegelFunction_div_rpow` is nonzero: on the boundary `r₁ = 0`,
the coordinate `r₂` is not an integer. -/
private theorem leadingCoeff_ne_zero {r : Fin 2 → ℝ} (hr : ∀ s : Fin 2 → ℤ, r ≠ fun i ↦ (s i : ℝ)) :
    (if r 0 = 0 then ‖1 - cexp (2 * π * I * r 1)‖ else 1) ≠ 0 := by
  split_ifs with hz
  · rw [norm_ne_zero_iff, sub_ne_zero, ne_comm, Ne, Complex.exp_eq_one_iff]
    rintro ⟨k, hk⟩
    have h2π : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    have hk' : (r 1 : ℂ) = k := mul_left_cancel₀ h2π (by rw [hk]; ring)
    refine hr ![0, k] ?_
    ext i
    fin_cases i
    · simp [hz]
    · simpa using (by exact_mod_cast hk' : r 1 = k)
  · exact one_ne_zero

/-- **The logarithmic `q`-order of a Siegel function.** For `0 ≤ r₁ < 1` and `r ∉ ℤ²`, the
logarithmic `q`-order of `g_r` is `B₂(r₁)/2`. The nonintegrality hypothesis excludes the
identically zero function at the corner of the strip. -/
theorem tendsto_log_norm_siegelFunction_div_log_norm_q {r : Fin 2 → ℝ}
    (hlo : 0 ≤ r 0) (hhi : r 0 < 1)
    (hr : ∀ s : Fin 2 → ℤ, r ≠ fun i ↦ (s i : ℝ)) :
    Tendsto (fun τ : ℍ ↦ Real.log ‖siegelFunction r τ‖ /
      Real.log ‖cexp (2 * π * I * (τ : ℂ))‖) atImInfty
      (𝓝 (bernoulliFun 2 (r 0) / 2)) := by
  have hlog := (tendsto_norm_siegelFunction_div_rpow hlo hhi).log (leadingCoeff_ne_zero hr)
  have him : Tendsto (fun τ : ℍ ↦ τ.im) atImInfty atTop := tendsto_comap
  have hden : Tendsto (fun τ : ℍ ↦ Real.log ‖cexp (2 * π * I * (τ : ℂ))‖)
      atImInfty atBot := by
    simpa [UpperHalfPlane.norm_exp_two_pi_I_mul, Real.log_exp, coe_im, neg_mul] using
      him.const_mul_atTop_of_neg (neg_neg_of_pos (by positivity : 0 < 2 * π))
  have hlim := hlog.div_atBot hden
  have h := hlim.add_const (bernoulliFun 2 (r 0) / 2)
  simp only [zero_add] at h
  refine h.congr fun τ ↦ ?_
  have hg := siegelFunction_ne_zero hr τ.im_pos
  have hq : 0 < ‖cexp (2 * π * I * (τ : ℂ))‖ := norm_pos_iff.mpr (Complex.exp_ne_zero _)
  have hq1 : ‖cexp (2 * π * I * (τ : ℂ))‖ ≠ 1 :=
    ne_of_lt (UpperHalfPlane.norm_exp_two_pi_I_lt_one τ)
  rw [Real.log_div (norm_ne_zero_iff.mpr hg) (ne_of_gt (Real.rpow_pos_of_pos hq _)),
    Real.log_rpow hq]
  field_simp [Real.log_ne_zero_of_pos_of_ne_one hq hq1]
  ring

/-- The decomposition `r = ({r₁}, r₂) + (⌊r₁⌋, 0)` into a parameter with first coordinate in
`[0, 1)` and an integral translation. -/
private theorem eq_fract_add_floor (r : Fin 2 → ℝ) :
    r = ![Int.fract (r 0), r 1] + fun i ↦ ((![⌊r 0⌋, 0] : Fin 2 → ℤ) i : ℝ) := by
  ext i; fin_cases i <;> simp [Int.fract_add_floor]

/-- Moving `r₁` into `[0, 1)` by an integral translation does not change `‖g_r‖`. -/
private theorem norm_siegelFunction_fract (r : Fin 2 → ℝ) {τ : ℂ} (hτ : 0 < τ.im) :
    ‖siegelFunction r τ‖ = ‖siegelFunction ![Int.fract (r 0), r 1] τ‖ := by
  conv_lhs => rw [eq_fract_add_floor r, siegelFunction_add_intCast _ _ hτ]
  simp [Complex.norm_exp]

/-- **Exponential growth of integral powers of a Siegel function.** For `r ∉ ℤ²` and every
integer `m`, `g_r(τ)^m = O(|q|^(m B₂({r₁})/2))` at `i∞`, where `{r₁}` is the fractional part of
`r₁` and `|q| = exp (-2π Im τ)`. For negative `m` this bounds `g_r` from below. -/
theorem isBigO_siegelFunction_zpow {r : Fin 2 → ℝ} (hr : ∀ s : Fin 2 → ℤ, r ≠ fun i ↦ (s i : ℝ))
    (m : ℤ) :
    (fun τ : ℍ ↦ siegelFunction r τ ^ m) =O[atImInfty]
      fun τ ↦ Real.exp (-(π * m * bernoulliFun 2 (Int.fract (r 0))) * τ.im) := by
  set r' : Fin 2 → ℝ := ![Int.fract (r 0), r 1]
  have hr' : ∀ s : Fin 2 → ℤ, r' ≠ fun i ↦ (s i : ℝ) := fun s h ↦
    hr (s + ![⌊r 0⌋, 0]) <| (eq_fract_add_floor r).trans <| by
      rw [show ![Int.fract (r 0), r 1] = r' from rfl, h]
      ext i
      simp
  have hlim := tendsto_norm_siegelFunction_div_rpow (r := r') (Int.fract_nonneg _)
    (Int.fract_lt_one _)
  have hbdd := ((hlim.zpow₀ m (Or.inl (leadingCoeff_ne_zero hr'))).isBigO_one ℝ).mul
    (Asymptotics.isBigO_refl (fun τ : ℍ ↦
      Real.exp (-(π * m * bernoulliFun 2 (Int.fract (r 0))) * τ.im)) atImInfty)
  simp only [one_mul] at hbdd
  refine Asymptotics.isBigO_norm_left.mp (hbdd.congr_left fun τ ↦ ?_)
  have hA : 0 < ‖cexp (2 * π * I * (τ : ℂ))‖ := norm_pos_iff.mpr (Complex.exp_ne_zero _)
  have hpow : (‖cexp (2 * π * I * (τ : ℂ))‖ ^ (bernoulliFun 2 (r' 0) / 2)) ^ m =
      Real.exp (-(π * m * bernoulliFun 2 (Int.fract (r 0))) * τ.im) := by
    rw [← Real.rpow_intCast, ← Real.rpow_mul hA.le, UpperHalfPlane.norm_exp_two_pi_I_mul,
      ← Real.exp_mul]
    simp only [r', Matrix.cons_val_zero, coe_im]
    ring_nf
  rw [← hpow, div_zpow, div_mul_cancel₀ _ (zpow_ne_zero _ (Real.rpow_pos_of_pos hA _).ne'),
    norm_zpow, norm_siegelFunction_fract r τ.im_pos]

end TauCeti.ModularForm
