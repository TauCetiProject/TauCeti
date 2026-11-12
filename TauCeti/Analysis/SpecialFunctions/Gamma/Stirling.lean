/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.Log
public import TauCeti.Analysis.SpecialFunctions.Gamma.SectorialDigamma
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Stirling's formula on sectors

For `0 < δ < π` and every nonzero `s` with `|arg s| ≤ π - δ`, the normalized holomorphic
logarithm of Gamma satisfies
`‖logGamma s - ((s - 1/2) log s - s + log (2π) / 2)‖ ≤ 2 / ((1 - cos δ) ^ 3 ‖s‖)`,
with `log` the principal branch. This is the leading-order case of
[DLMF 5.11.1](https://dlmf.nist.gov/5.11.E1), with an explicit (non-optimal) error constant proved
here. Taking real parts gives the corresponding statement for `log ‖Γ s‖`.

The proof uses only the derivative of the error
`E(s) = logGamma s - ((s - 1/2) log s - s + log (2π) / 2)`, which is
`ψ(s) - log s + 1 / (2s)` and is bounded by `K / ‖s‖²` on the sector, with
`K = 2 / (1 - cos δ) ^ 3`, by the second-order sectorial digamma bound.

* Along a ray, `‖E(λ s) - E(s)‖ ≤ K / ‖s‖` for every `λ ≥ 1`.
* Along an arc of radius `r` inside the sector, `E` varies by at most `π K / r`.
* At the integers, `E(n + 1) → 0`: this is Stirling's formula for `n!`, which fixes the
  constant `log (2π) / 2`.

Moving from `s` out along its ray to radius `n + 1` and then along the arc to the real point
`n + 1`, and letting `n → ∞`, gives `‖E(s)‖ ≤ K / ‖s‖`.

## Main declarations

* `Stirling.tendsto_log_factorial_sub_stirling`: the logarithmic form of Stirling's formula at
  `n + 1`.
* `TauCeti.norm_logGamma_sub_stirling_le`: the explicit uniform bound on a closed sector.
* `TauCeti.exists_norm_logGamma_sub_stirling_le`, `TauCeti.isBigO_logGamma_sub_stirling`:
  the `O(1 / ‖s‖)` forms.
* `TauCeti.abs_log_norm_Gamma_sub_stirling_le`: the real-part form for `log ‖Γ s‖`.
-/

public section

open Complex Real Filter Set Topology Asymptotics Bornology

namespace Stirling

/-- Stirling's formula in logarithmic form at `n + 1`:
`log n! - ((n + 1/2) log (n + 1) - (n + 1) + log (2π) / 2) → 0`. -/
theorem tendsto_log_factorial_sub_stirling :
    Tendsto (fun n : ℕ ↦ Real.log (n.factorial : ℝ) -
      (((n : ℝ) + 1 / 2) * Real.log ((n : ℝ) + 1) - ((n : ℝ) + 1) + Real.log (2 * π) / 2))
      atTop (𝓝 0) := by
  have hs : Tendsto (fun n : ℕ ↦ Real.log (stirlingSeq n)) atTop (𝓝 (Real.log √π)) :=
    (continuousAt_log (by positivity)).tendsto.comp tendsto_stirlingSeq_sqrt_pi
  have hm : Tendsto (fun n : ℕ ↦ (n : ℝ) * Real.log (1 + 1 / (n : ℝ))) atTop (𝓝 1) :=
    (tendsto_mul_log_one_add_div_atTop 1).comp tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun n : ℕ ↦ Real.log (1 + 1 / (n : ℝ))) atTop (𝓝 0) := by
    have h := ((continuousAt_log (by norm_num : (1 : ℝ) + 0 ≠ 0)).tendsto.comp
      ((tendsto_one_div_atTop_nhds_zero_nat).const_add (1 : ℝ)))
    simpa [Function.comp_def] using h
  have hlim := ((hs.sub_const (Real.log π / 2)).sub hm).sub (hl.const_mul (1 / 2)) |>.add_const 1
  rw [Real.log_sqrt pi_pos.le] at hlim
  simp only [mul_zero, sub_zero] at hlim
  rw [show Real.log π / 2 - Real.log π / 2 - 1 + 1 = 0 by ring] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [log_stirlingSeq_formula, show (1 : ℝ) + 1 / n = (n + 1) / n by field_simp,
    Real.log_div (by positivity) hn0.ne', Real.log_mul two_ne_zero hn0.ne',
    Real.log_div hn0.ne' (exp_pos 1).ne', Real.log_exp, Real.log_mul two_ne_zero pi_ne_zero]
  ring

end Stirling

namespace TauCeti

/-- The error in Stirling's formula for the normalized logarithm of Gamma. -/
private noncomputable def stirlingError (s : ℂ) : ℂ :=
  logGamma s - ((s - 1 / 2) * Complex.log s - s + (Real.log (2 * π) / 2 : ℝ))

private theorem stirlingError_apply (s : ℂ) :
    stirlingError s = logGamma s - ((s - 1 / 2) * Complex.log s - s + (Real.log (2 * π) / 2 : ℝ)) :=
  rfl

/-- The derivative of the Stirling error is `ψ(s) - log s + 1 / (2s)`. -/
private theorem hasDerivAt_stirlingError {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt stirlingError (digamma z - Complex.log z + (2 * z)⁻¹) z := by
  have hz0 := slitPlane_ne_zero hz
  have hL : HasDerivAt logGamma (digamma z) z := by
    rw [← deriv_logGamma hz]
    exact (differentiableOn_logGamma.differentiableAt
      (isOpen_slitPlane.mem_nhds hz)).hasDerivAt
  have hlog := Complex.hasDerivAt_log hz
  have h := hL.sub ((((hasDerivAt_id z).sub_const (1 / 2 : ℂ)).mul hlog).sub
    (hasDerivAt_id z) |>.add_const ((Real.log (2 * π) / 2 : ℝ) : ℂ))
  refine h.congr_deriv ?_
  simp only [id]
  field_simp
  ring

private theorem stirlingConst_nonneg {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) :
    0 ≤ 2 / (1 - Real.cos δ) ^ 3 :=
  div_nonneg zero_le_two (pow_nonneg (one_sub_cos_pos hδ (by linarith)).le 3)

/-- Along a ray in the sector the Stirling error varies by at most `K / ‖s‖`. -/
private theorem norm_stirlingError_real_mul_sub_le {s : ℂ} {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π)
    (hs : |s.arg| ≤ π - δ) (hs0 : s ≠ 0) {l : ℝ} (hl : 1 ≤ l) :
    ‖stirlingError (l * s) - stirlingError s‖ ≤ 2 / (1 - Real.cos δ) ^ 3 / ‖s‖ := by
  set K := 2 / (1 - Real.cos δ) ^ 3
  have hK : 0 ≤ K := stirlingConst_nonneg hδ hδπ
  have hmem {x : ℝ} (hx : 0 < x) : (x : ℂ) * s ∈ slitPlane := by
    refine mem_slitPlane_of_abs_arg_le hδ ?_ (mul_ne_zero (ofReal_ne_zero.mpr hx.ne') hs0)
    rwa [arg_real_mul s hx]
  have hd {x : ℝ} (hx : 0 < x) : HasDerivAt (fun y : ℝ ↦ stirlingError (y * s) - stirlingError s)
      (s * (digamma (x * s) - Complex.log (x * s) + (2 * (x * s))⁻¹)) x := by
    have hm : HasDerivAt (fun y : ℝ ↦ (y : ℂ) * s) s x := by
      simpa using (hasDerivAt_id (x : ℂ)).comp_ofReal.mul_const s
    have hc := (hasDerivAt_stirlingError (hmem hx)).comp x hm
    simpa [mul_comm] using hc.sub_const (stirlingError s)
  have hbound := image_norm_le_of_norm_deriv_right_le_deriv_boundary'
    (f := fun y : ℝ ↦ stirlingError (y * s) - stirlingError s) (a := 1) (b := l)
    (B := fun y ↦ K / ‖s‖ * (1 - y⁻¹)) (B' := fun y ↦ K / ‖s‖ * (y ^ 2)⁻¹)
    (fun y hy ↦ (hd (by linarith [hy.1])).continuousAt.continuousWithinAt)
    (fun y hy ↦ (hd (by linarith [hy.1])).hasDerivWithinAt)
    (by simp)
    (fun y hy ↦ (continuousAt_const.mul (continuousAt_const.sub
      (continuousAt_inv₀ (by linarith [hy.1])))).continuousWithinAt)
    (fun y hy ↦ by
      have h := ((hasDerivAt_inv (by linarith [hy.1] : y ≠ 0)).const_sub 1).const_mul (K / ‖s‖)
      simpa using h.hasDerivWithinAt)
    (fun y hy ↦ by
      have hy0 : 0 < y := by linarith [hy.1]
      have hz := (norm_digamma_sub_log_add_inv_two_mul_le_of_abs_arg_le hδ hδπ
        (show |((y : ℂ) * s).arg| ≤ π - δ by rwa [arg_real_mul s hy0])).trans_eq
        (div_div _ _ _).symm
      rw [norm_mul, norm_real, Real.norm_of_nonneg hy0.le] at hz
      rw [norm_mul]
      calc
        ‖s‖ * ‖digamma (y * s) - Complex.log (y * s) + (2 * (y * s))⁻¹‖ ≤
            ‖s‖ * (K / (y * ‖s‖) ^ 2) := by gcongr
        _ = K / ‖s‖ * (y ^ 2)⁻¹ := by field_simp)
    (right_mem_Icc.mpr hl)
  refine hbound.trans ?_
  have : 0 ≤ l⁻¹ := inv_nonneg.mpr (by linarith)
  calc
    K / ‖s‖ * (1 - l⁻¹) ≤ K / ‖s‖ * 1 := by gcongr; linarith
    _ = K / ‖s‖ := mul_one _

/-- Along an arc of radius `r` inside the sector the Stirling error varies by at most
`K |θ| / r`. -/
private theorem norm_stirlingError_arc_sub_le {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) {r θ : ℝ}
    (hr : 0 < r) (hθ : |θ| ≤ π - δ) :
    ‖stirlingError (r * exp (θ * I)) - stirlingError r‖ ≤
      2 / (1 - Real.cos δ) ^ 3 / r * |θ| := by
  set K := 2 / (1 - Real.cos δ) ^ 3
  set S : Set ℝ := Icc (-(π - δ)) (π - δ)
  have hargS {φ : ℝ} (hφ : φ ∈ S) : ((r : ℂ) * exp (φ * I)).arg = φ := by
    rw [arg_real_mul _ hr, arg_exp_mul_I, toIocMod_eq_self]
    constructor <;> linarith [hφ.1, hφ.2]
  have hmemS {φ : ℝ} (hφ : φ ∈ S) : (r : ℂ) * exp (φ * I) ∈ slitPlane := by
    refine mem_slitPlane_of_abs_arg_le hδ ?_ (mul_ne_zero (ofReal_ne_zero.mpr hr.ne')
      (Complex.exp_ne_zero _))
    rw [hargS hφ, abs_le]
    exact ⟨hφ.1, hφ.2⟩
  have hd {φ : ℝ} (hφ : φ ∈ S) : HasDerivAt (fun ψ : ℝ ↦ stirlingError (r * exp (ψ * I)))
      ((digamma (r * exp (φ * I)) - Complex.log (r * exp (φ * I)) +
        (2 * (r * exp (φ * I)))⁻¹) * (r * exp (φ * I) * I)) φ := by
    have he : HasDerivAt (fun ψ : ℝ ↦ (r : ℂ) * exp (ψ * I)) (r * exp (φ * I) * I) φ := by
      have h := ((hasDerivAt_id (φ : ℂ)).mul_const I).cexp.comp_ofReal.const_mul (r : ℂ)
      simpa [mul_assoc] using h
    exact (hasDerivAt_stirlingError (hmemS hφ)).comp φ he
  have hS : Convex ℝ S := convex_Icc _ _
  have h0 : (0 : ℝ) ∈ S := ⟨by linarith, by linarith⟩
  have hθS : θ ∈ S := abs_le.mp hθ
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun ψ : ℝ ↦ stirlingError (r * exp (ψ * I))) (C := K / r)
    (fun φ hφ ↦ (hd hφ).hasDerivWithinAt) (fun φ hφ ↦ by
      have hz := (norm_digamma_sub_log_add_inv_two_mul_le_of_abs_arg_le hδ hδπ
        (s := r * exp (φ * I)) (by rw [hargS hφ, abs_le]; exact ⟨hφ.1, hφ.2⟩)).trans_eq
        (div_div _ _ _).symm
      have hn : ‖(r : ℂ) * exp (φ * I)‖ = r := by
        rw [norm_mul, norm_exp_ofReal_mul_I, norm_real, Real.norm_of_nonneg hr.le, mul_one]
      rw [hn] at hz
      rw [norm_mul, norm_mul, hn, norm_I, mul_one]
      calc
        _ ≤ K / r ^ 2 * r := by gcongr
        _ = K / r := by field_simp) hS h0 hθS
  simpa [Real.norm_eq_abs] using hmv

/-- At the integers the Stirling error tends to zero: this is Stirling's formula for `n!`. -/
private theorem tendsto_stirlingError_natCast_add_one :
    Tendsto (fun n : ℕ ↦ stirlingError ((n : ℝ) + 1 : ℝ)) atTop (𝓝 0) := by
  have h := (continuous_ofReal.tendsto 0).comp Stirling.tendsto_log_factorial_sub_stirling
  rw [ofReal_zero] at h
  refine h.congr fun n ↦ ?_
  have hn : (0 : ℝ) < n + 1 := by positivity
  rw [Function.comp_apply, stirlingError_apply, logGamma_ofReal hn, Real.Gamma_nat_eq_factorial,
    ← ofReal_log hn.le]
  push_cast
  ring

/-- Scaling a nonzero `s` by `R / ‖s‖` moves it along its ray to the point of norm `R`. -/
private theorem ofReal_div_norm_mul_self {s : ℂ} (hs0 : s ≠ 0) (R : ℝ) :
    ((R / ‖s‖ : ℝ) : ℂ) * s = (R : ℂ) * exp (s.arg * I) := by
  have hr' : (‖s‖ : ℂ) ≠ 0 := ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hs0)
  calc ((R / ‖s‖ : ℝ) : ℂ) * s = ((R / ‖s‖ : ℝ) : ℂ) * (‖s‖ * exp (s.arg * I)) :=
        congrArg _ (norm_mul_exp_arg_mul_I s).symm
    _ = (R : ℂ) * exp (s.arg * I) := by
      push_cast
      field_simp

/-- The Stirling error on the sector is at most `K / ‖s‖`: compare `s` with the real point
`n + 1` through the ray from `s` and the arc of radius `n + 1`, and let `n → ∞`. -/
private theorem norm_stirlingError_le {s : ℂ} {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π)
    (hs : |s.arg| ≤ π - δ) (hs0 : s ≠ 0) :
    ‖stirlingError s‖ ≤ 2 / (1 - Real.cos δ) ^ 3 / ‖s‖ := by
  set K := 2 / (1 - Real.cos δ) ^ 3
  set r := ‖s‖
  have hr : 0 < r := norm_pos_iff.mpr hs0
  have hint : Tendsto (fun n : ℕ ↦ ‖stirlingError ((n : ℝ) + 1 : ℝ)‖) atTop (𝓝 0) := by
    simpa using tendsto_stirlingError_natCast_add_one.norm
  have hlim : Tendsto (fun n : ℕ ↦ K / r + K / ((n : ℝ) + 1) * π +
      ‖stirlingError ((n : ℝ) + 1 : ℝ)‖) atTop (𝓝 (K / r + 0 * π + 0)) :=
    (tendsto_const_nhds.add ((tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)).mul_const π)).add hint
  simp only [zero_mul, add_zero] at hlim
  refine ge_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop ⌈r⌉₊] with n hn
  have hn1 : r ≤ (n : ℝ) + 1 := by linarith [Nat.le_ceil r, (Nat.cast_le (α := ℝ)).mpr hn]
  have hn0 : (0 : ℝ) < n + 1 := by positivity
  set l := ((n : ℝ) + 1) / r
  have hl : 1 ≤ l := (one_le_div hr).mpr hn1
  -- along the ray from `s` to `l * s`, then along the arc from `l * s` to `n + 1`
  have h1 := norm_stirlingError_real_mul_sub_le hδ hδπ hs hs0 hl
  have h2 := norm_stirlingError_arc_sub_le hδ hδπ hn0 hs
  rw [← ofReal_div_norm_mul_self hs0] at h2
  have htri : ‖stirlingError s‖ ≤ ‖stirlingError (l * s) - stirlingError s‖ +
      ‖stirlingError (l * s) - stirlingError ((n : ℝ) + 1 : ℝ)‖ +
      ‖stirlingError ((n : ℝ) + 1 : ℝ)‖ := by
    have h := norm_add₃_le (a := -(stirlingError (l * s) - stirlingError s))
      (b := stirlingError (l * s) - stirlingError ((n : ℝ) + 1 : ℝ))
      (c := stirlingError ((n : ℝ) + 1 : ℝ))
    rw [norm_neg] at h
    convert h using 2
    ring
  have hK : 0 ≤ K / ((n : ℝ) + 1) := div_nonneg (stirlingConst_nonneg hδ hδπ) hn0.le
  have h2' := h2.trans (mul_le_mul_of_nonneg_left (abs_arg_le_pi s) hK)
  linarith

/-- **Stirling's formula on a sector**, with an explicit constant: for `0 < δ < π` and nonzero
`s` with `|arg s| ≤ π - δ`,
`‖logGamma s - ((s - 1/2) log s - s + log (2π) / 2)‖ ≤ 2 / ((1 - cos δ) ^ 3 ‖s‖)`. -/
theorem norm_logGamma_sub_stirling_le {s : ℂ} {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π)
    (hs : |s.arg| ≤ π - δ) (hs0 : s ≠ 0) :
    ‖logGamma s - ((s - 1 / 2) * Complex.log s - s + (Real.log (2 * π) / 2 : ℝ))‖ ≤
      2 / ((1 - Real.cos δ) ^ 3 * ‖s‖) := by
  rw [← div_div, ← stirlingError_apply]
  exact norm_stirlingError_le hδ hδπ hs hs0

/-- Stirling's formula on a sector, existential form: for `0 < δ < π` there is `C` with
`‖logGamma s - ((s - 1/2) log s - s + log (2π) / 2)‖ ≤ C / ‖s‖` whenever `|arg s| ≤ π - δ` and
`s ≠ 0`. -/
theorem exists_norm_logGamma_sub_stirling_le {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) :
    ∃ C, ∀ s : ℂ, |s.arg| ≤ π - δ → s ≠ 0 →
      ‖logGamma s - ((s - 1 / 2) * Complex.log s - s + (Real.log (2 * π) / 2 : ℝ))‖ ≤
        C / ‖s‖ :=
  ⟨2 / (1 - Real.cos δ) ^ 3, fun _ hs hs0 ↦
    (norm_logGamma_sub_stirling_le hδ hδπ hs hs0).trans_eq (div_div _ _ _).symm⟩

/-- Stirling's formula on a sector: the error is `O(1 / ‖s‖)` as `s → ∞` with
`|arg s| ≤ π - δ`. -/
theorem isBigO_logGamma_sub_stirling {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) :
    (fun s : ℂ ↦ logGamma s - ((s - 1 / 2) * Complex.log s - s + (Real.log (2 * π) / 2 : ℝ)))
      =O[cobounded ℂ ⊓ 𝓟 {s : ℂ | |s.arg| ≤ π - δ}] (fun s : ℂ ↦ ‖s‖⁻¹) := by
  refine IsBigO.of_bound (2 / (1 - Real.cos δ) ^ 3) ?_
  rw [eventually_inf_principal]
  filter_upwards [tendsto_norm_cobounded_atTop.eventually_gt_atTop 0] with s hs0 hs
  rw [norm_inv, norm_norm, ← div_eq_mul_inv, div_div]
  exact norm_logGamma_sub_stirling_le hδ hδπ hs (norm_pos_iff.mp hs0)

/-- Stirling's formula for `log ‖Γ s‖` on a sector: for `0 < δ < π` and nonzero `s` with
`|arg s| ≤ π - δ`,
`|log ‖Γ s‖ - ((re s - 1/2) log ‖s‖ - im s · arg s - re s + log (2π) / 2)| ≤
2 / ((1 - cos δ) ^ 3 ‖s‖)`. -/
theorem abs_log_norm_Gamma_sub_stirling_le {s : ℂ} {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π)
    (hs : |s.arg| ≤ π - δ) (hs0 : s ≠ 0) :
    |Real.log ‖Complex.Gamma s‖ - ((s.re - 1 / 2) * Real.log ‖s‖ - s.im * s.arg - s.re +
      Real.log (2 * π) / 2)| ≤ 2 / ((1 - Real.cos δ) ^ 3 * ‖s‖) := by
  refine le_trans (le_of_eq ?_) ((abs_re_le_norm _).trans
    (norm_logGamma_sub_stirling_le hδ hδπ hs hs0))
  congr 1
  rw [sub_re, logGamma_re (mem_slitPlane_of_abs_arg_le hδ hs hs0)]
  simp only [sub_re, add_re, mul_re, log_re, log_im, ofReal_re, sub_im, one_div, inv_re,
    normSq_ofNat, re_ofNat]
  norm_num

end TauCeti
