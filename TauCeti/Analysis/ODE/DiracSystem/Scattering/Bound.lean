/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.DiracSystem.Scattering
import TauCeti.Analysis.Matrix.EuclideanLin
import TauCeti.Analysis.ODE.Gronwall.CoshSinh
import TauCeti.Analysis.ODE.Propagator
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Primitive

/-!
# The Dyson bounds for the scattering functions

Let `q` be integrable on `[0, t]` with `t ≥ 0`, let `L = ∫₀ᵗ |q|`, and let `z` be in the closed
upper half-plane. The scattering functions `a = (G_q)₂₂` and `b = (G_q)₂₁`
(`TauCeti.diracScatteringA`, `TauCeti.diracScatteringB`) satisfy

* `|a(t, z)| ≤ cosh L` and `|a(t, z) - 1| ≤ cosh L - 1`
  (`TauCeti.norm_diracScatteringA_le`, `TauCeti.norm_diracScatteringA_sub_one_le`);
* `|b(t, z)| ≤ sinh L` and `|b(t, z) - ∫₀ᵗ q(s) e^{2isz} ds| ≤ sinh L - L`
  (`TauCeti.norm_diracScatteringB_le`, `TauCeti.norm_diracScatteringB_sub_integral_le`).

## Implementation notes

The bottom row of `N(t, s)`, the propagator of the scattering coefficient from `s` to `t`, solves
the backward integral equation (`TauCeti.propagator_eq_one_add_integral_right`). With
`m(s) = N(t, s)₂₂` and `n(s) = e^{-2isz} N(t, s)₂₁` it reads
`n(s) = ∫ₛᵗ e^{2i(r - s)z} q(r) m(r) dr` and `m(s) = 1 + ∫ₛᵗ conj q(r) n(r) dr`. For `Im z ≥ 0` the
factor `e^{2i(r - s)z}` has modulus at most `1`, so `|n| ≤ ∫ₛᵗ |q| |m|` and
`|m| ≤ 1 + ∫ₛᵗ |q| |n|`, and the comparison with `cosh` and `sinh`
(`TauCeti.le_cosh_and_le_sinh_of_le_integral`) bounds them. At `s = 0`, `m(0) = a(t, z)` and
`n(0) = b(t, z)`. This avoids expanding the Dyson series.

## References

* A. Poltoratski, *Pointwise convergence of the non-linear Fourier transform*, Ann. of Math. (2)
  199 (2024), 741–793, §5.
-/

public section

open MeasureTheory Set Matrix Complex ComplexConjugate intervalIntegral
open scoped Interval

namespace TauCeti

variable {q : ℝ → ℂ} {t : ℝ} {z : ℂ}

/-- `|e^{2i u z}| ≤ 1` for `u ≥ 0` and `Im z ≥ 0`. -/
private theorem norm_exp_two_I_mul_le_one (hz : 0 ≤ z.im) {u : ℝ} (hu : 0 ≤ u) :
    ‖exp (2 * I * (u * z))‖ ≤ 1 := by
  rw [norm_exp, Real.exp_le_one_iff]
  simp only [mul_re, re_ofNat, I_re, im_ofNat, I_im, ofReal_re, ofReal_im, mul_im]
  nlinarith

/-- The diagonal entries of the scattering coefficient vanish. -/
private theorem diracScatteringCoeff_apply_self (q : ℝ → ℂ) (z : ℂ) (r : ℝ) (i : Fin 2) :
    diracScatteringCoeff q z r i i = 0 := by
  fin_cases i <;> simp [diracScatteringCoeff_def]

/-- The top-right entry of the scattering coefficient. -/
private theorem diracScatteringCoeff_apply_zero_one (q : ℝ → ℂ) (z : ℂ) (r : ℝ) :
    diracScatteringCoeff q z r 0 1 = exp (-2 * I * (r * z)) * conj (q r) := by
  simp [diracScatteringCoeff_def]

/-- The bottom-left entry of the scattering coefficient. -/
private theorem diracScatteringCoeff_apply_one_zero (q : ℝ → ℂ) (z : ℂ) (r : ℝ) :
    diracScatteringCoeff q z r 1 0 = exp (2 * I * (r * z)) * q r := by
  simp [diracScatteringCoeff_def]

/-- The bottom-right entry `m(s) = N(t, s)₂₂` of the propagator from `s` to `t`. -/
private noncomputable def bm (q : ℝ → ℂ) (z : ℂ) (t s : ℝ) : ℂ :=
  euclideanEntryCLM ℂ 1 1 (propagator (fun r ↦ toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)
    (diracScatteringCoeff q z r)) t s)

/-- The rescaled bottom-left entry `n(s) = e^{-2isz} N(t, s)₂₁`. -/
private noncomputable def bn (q : ℝ → ℂ) (z : ℂ) (t s : ℝ) : ℂ :=
  exp (-2 * I * (s * z)) * euclideanEntryCLM ℂ 1 0
    (propagator (fun r ↦ toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (diracScatteringCoeff q z r)) t s)

/-- `m` and `n` are continuous on `[0, t]`. -/
private theorem continuousOn_bm_bn (hq : IntegrableOn q (Icc 0 t)) (ht : 0 ≤ t) :
    ContinuousOn (bm q z t) (Icc 0 t) ∧ ContinuousOn (bn q z t) (Icc 0 t) := by
  have hNc := continuousOn_propagator_right
    (integrableOn_toEuclideanCLM_diracScatteringCoeff hq z) (⟨ht, le_rfl⟩ : t ∈ Icc 0 t)
  exact ⟨(euclideanEntryCLM ℂ 1 1).continuous.comp_continuousOn hNc,
    (by fun_prop : Continuous fun s : ℝ ↦ exp (-2 * I * (s * z))).continuousOn.mul
      ((euclideanEntryCLM ℂ 1 0).continuous.comp_continuousOn hNc)⟩

/-- **The backward equations of the bottom row.** For `s ∈ [0, t]`,
`m(s) = 1 + ∫ₛᵗ conj q(r) n(r) dr` and `n(s) = ∫ₛᵗ e^{2i(r - s)z} q(r) m(r) dr`. -/
private theorem bm_bn_eq (hq : IntegrableOn q (Icc 0 t)) (ht : 0 ≤ t) {s : ℝ}
    (hs : s ∈ Icc 0 t) :
    bm q z t s = 1 + ∫ r in s..t, conj (q r) * bn q z t r ∧
      bn q z t s = ∫ r in s..t, exp (2 * I * ((r - s) * z)) * q r * bm q z t r := by
  set P := fun r ↦ toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (diracScatteringCoeff q z r)
    with hPdef
  have hP : IntegrableOn P (Icc 0 t) := integrableOn_toEuclideanCLM_diracScatteringCoeff hq z
  have htt : t ∈ Icc 0 t := ⟨ht, le_rfl⟩
  have hNP := intervalIntegrable_propagator_comp_right hP hs htt
  -- The entries of the backward integral equation.
  have hback (i j : Fin 2) : euclideanEntryCLM ℂ i j (propagator P t s) =
      euclideanEntryCLM ℂ i j 1 + ∫ r in s..t,
        ∑ k, euclideanEntryCLM ℂ i k (propagator P t r) * diracScatteringCoeff q z r k j := by
    rw [propagator_eq_one_add_integral_right hP hs htt, map_add,
      ← (euclideanEntryCLM ℂ i j).intervalIntegral_comp_comm hNP]
    simp only [P, euclideanEntryCLM_comp_toEuclideanCLM]
  simp only [bm, bn, ← hPdef]
  constructor
  · rw [hback 1 1]
    congr 1
    · simp
    refine integral_congr fun r _ ↦ ?_
    rw [Fin.sum_univ_two, diracScatteringCoeff_apply_zero_one, diracScatteringCoeff_apply_self]
    ring
  · rw [hback 1 0, (by simp : euclideanEntryCLM ℂ (1 : Fin 2) 0 1 = 0), zero_add,
      ← intervalIntegral.integral_const_mul]
    refine integral_congr fun r _ ↦ ?_
    have he : exp (2 * I * ((r - s) * z)) = exp (-2 * I * (s * z)) * exp (2 * I * (r * z)) := by
      rw [← exp_add]; ring_nf
    rw [Fin.sum_univ_two, diracScatteringCoeff_apply_one_zero, diracScatteringCoeff_apply_self, he]
    ring

/-- The core estimate: for every `s ∈ [0, t]`, `|m(s)| ≤ cosh Lₛ`, `|n(s)| ≤ sinh Lₛ` and
`|m(s) - 1| ≤ cosh Lₛ - 1`, where `Lₛ = ∫ₛᵗ |q|`. -/
private theorem bounds_aux (hq : IntegrableOn q (Icc 0 t)) (ht : 0 ≤ t) (hz : 0 ≤ z.im) {s : ℝ}
    (hs : s ∈ Icc 0 t) :
    ‖bm q z t s‖ ≤ Real.cosh (∫ r in s..t, ‖q r‖) ∧ ‖bn q z t s‖ ≤ Real.sinh (∫ r in s..t, ‖q r‖) ∧
      ‖bm q z t s - 1‖ ≤ Real.cosh (∫ r in s..t, ‖q r‖) - 1 := by
  obtain ⟨hmc, hnc⟩ := continuousOn_bm_bn (z := z) hq ht
  have hqn : IntegrableOn (fun r ↦ ‖q r‖) (Icc 0 t) := hq.norm
  have hsub {s : ℝ} (hs : s ∈ Icc 0 t) : uIcc s t ⊆ Icc 0 t := uIcc_subset_Icc hs ⟨ht, le_rfl⟩
  have hqi {s : ℝ} (hs : s ∈ Icc 0 t) : IntervalIntegrable (fun r ↦ ‖q r‖) volume s t :=
    (hqn.mono_set (hsub hs)).intervalIntegrable
  have hnle (s : ℝ) (hs : s ∈ Icc 0 t) : ‖bn q z t s‖ ≤ ∫ r in s..t, ‖q r‖ * ‖bm q z t r‖ := by
    rw [(bm_bn_eq hq ht hs).2]
    refine norm_integral_le_of_norm_le hs.2 (ae_of_all _ fun r hr ↦ ?_)
      ((hqi hs).mul_continuousOn (hmc.norm.mono (hsub hs)))
    rw [norm_mul, norm_mul]
    calc ‖exp (2 * I * ((r - s) * z))‖ * ‖q r‖ * ‖bm q z t r‖ ≤ 1 * ‖q r‖ * ‖bm q z t r‖ := by
          gcongr
          simpa using norm_exp_two_I_mul_le_one hz (sub_nonneg.2 hr.1.le)
      _ = ‖q r‖ * ‖bm q z t r‖ := by rw [one_mul]
  have hm1le (s : ℝ) (hs : s ∈ Icc 0 t) :
      ‖bm q z t s - 1‖ ≤ ∫ r in s..t, ‖q r‖ * ‖bn q z t r‖ := by
    rw [(bm_bn_eq hq ht hs).1, add_sub_cancel_left]
    refine norm_integral_le_of_norm_le hs.2 (ae_of_all _ fun r _ ↦ ?_)
      ((hqi hs).mul_continuousOn (hnc.norm.mono (hsub hs)))
    rw [norm_mul, RCLike.norm_conj]
  have hmle (s : ℝ) (hs : s ∈ Icc 0 t) : ‖bm q z t s‖ ≤ 1 + ∫ r in s..t, ‖q r‖ * ‖bn q z t r‖ := by
    calc ‖bm q z t s‖ = ‖1 + (bm q z t s - 1)‖ := by rw [add_sub_cancel]
      _ ≤ 1 + ‖bm q z t s - 1‖ := (norm_add_le _ _).trans_eq (by rw [norm_one])
      _ ≤ _ := add_le_add le_rfl (hm1le s hs)
  have hcmp (s : ℝ) (hs : s ∈ Icc 0 t) := le_cosh_and_le_sinh_of_le_integral hqn
    (ae_of_all _ fun r ↦ norm_nonneg _) hmc.norm hnc.norm hmle hnle hs
  refine ⟨(hcmp s hs).1, (hcmp s hs).2, (hm1le s hs).trans ?_⟩
  -- `∫ₛᵗ |q| |n| ≤ ∫ₛᵗ |q| sinh L = cosh Lₛ - 1`.
  rw [cosh_integral_eq_one_add_integral hqn hs, add_sub_cancel_left]
  refine integral_mono_on hs.2 ((hqi hs).mul_continuousOn (hnc.norm.mono (hsub hs)))
    ((hqi hs).mul_continuousOn ((Real.continuous_sinh.comp_continuousOn
      hqn.continuousOn_intervalIntegral_left).mono (hsub hs)))
    fun r hr ↦ mul_le_mul_of_nonneg_left (hcmp r ⟨hs.1.trans hr.1, hr.2⟩).2 (norm_nonneg _)

/-- At `s = 0` the bottom row of `N(t, s)` is `(b(t, z), a(t, z))`. -/
private theorem bm_bn_zero (q : ℝ → ℂ) (t : ℝ) (z : ℂ) :
    bm q z t 0 = diracScatteringA q t z ∧ bn q z t 0 = diracScatteringB q t z := by
  rw [bm, bn, ← toEuclideanCLM_diracScatteringMatrix, euclideanEntryCLM_toEuclideanCLM,
    euclideanEntryCLM_toEuclideanCLM]
  simp [diracScatteringA_def, diracScatteringB_def]

/-- **The Dyson bound for `a`.** For `q` integrable on `[0, t]` with `t ≥ 0` and `Im z ≥ 0`,
`|a(t, z)| ≤ cosh ∫₀ᵗ |q|`. -/
theorem norm_diracScatteringA_le (hq : IntegrableOn q (Icc 0 t)) (ht : 0 ≤ t) (hz : 0 ≤ z.im) :
    ‖diracScatteringA q t z‖ ≤ Real.cosh (∫ s in (0 : ℝ)..t, ‖q s‖) := by
  rw [← (bm_bn_zero q t z).1]
  exact (bounds_aux hq ht hz ⟨le_rfl, ht⟩).1

/-- **The Dyson bound for `a - 1`.** For `q` integrable on `[0, t]` with `t ≥ 0` and `Im z ≥ 0`,
`|a(t, z) - 1| ≤ cosh (∫₀ᵗ |q|) - 1`. -/
theorem norm_diracScatteringA_sub_one_le (hq : IntegrableOn q (Icc 0 t)) (ht : 0 ≤ t)
    (hz : 0 ≤ z.im) :
    ‖diracScatteringA q t z - 1‖ ≤ Real.cosh (∫ s in (0 : ℝ)..t, ‖q s‖) - 1 := by
  rw [← (bm_bn_zero q t z).1]
  exact (bounds_aux hq ht hz ⟨le_rfl, ht⟩).2.2

/-- **The Dyson bound for `b`.** For `q` integrable on `[0, t]` with `t ≥ 0` and `Im z ≥ 0`,
`|b(t, z)| ≤ sinh ∫₀ᵗ |q|`. -/
theorem norm_diracScatteringB_le (hq : IntegrableOn q (Icc 0 t)) (ht : 0 ≤ t) (hz : 0 ≤ z.im) :
    ‖diracScatteringB q t z‖ ≤ Real.sinh (∫ s in (0 : ℝ)..t, ‖q s‖) := by
  rw [← (bm_bn_zero q t z).2]
  exact (bounds_aux hq ht hz ⟨le_rfl, ht⟩).2.1

/-- **The first-order Dyson bound for `b`.** For `q` integrable on `[0, t]` with `t ≥ 0` and
`Im z ≥ 0`, `|b(t, z) - ∫₀ᵗ q(s) e^{2isz} ds| ≤ sinh L - L` with `L = ∫₀ᵗ |q|`. -/
theorem norm_diracScatteringB_sub_integral_le (hq : IntegrableOn q (Icc 0 t)) (ht : 0 ≤ t)
    (hz : 0 ≤ z.im) :
    ‖diracScatteringB q t z - ∫ s in (0 : ℝ)..t, q s * exp (2 * I * (s * z))‖ ≤
      Real.sinh (∫ s in (0 : ℝ)..t, ‖q s‖) - ∫ s in (0 : ℝ)..t, ‖q s‖ := by
  set m := bm q z t
  have h0 : (0 : ℝ) ∈ Icc 0 t := ⟨le_rfl, ht⟩
  have hqn : IntegrableOn (fun r ↦ ‖q r‖) (Icc 0 t) := hq.norm
  have hsub : uIcc 0 t ⊆ Icc 0 t := uIcc_subset_Icc h0 ⟨ht, le_rfl⟩
  have hqi : IntervalIntegrable q volume 0 t := (hq.mono_set hsub).intervalIntegrable
  have hqni : IntervalIntegrable (fun r ↦ ‖q r‖) volume 0 t :=
    (hqn.mono_set hsub).intervalIntegrable
  have hmc : ContinuousOn m (uIcc 0 t) := (continuousOn_bm_bn hq ht).1.mono hsub
  have hLc := hqn.continuousOn_intervalIntegral_left.mono hsub
  have he : ContinuousOn (fun r : ℝ ↦ exp (2 * I * (r * z))) (uIcc 0 t) := by fun_prop
  -- `b - ∫ q e^{2isz} = ∫ e^{2isz} q (m - 1)`.
  have hb : diracScatteringB q t z - ∫ s in (0 : ℝ)..t, q s * exp (2 * I * (s * z)) =
      ∫ r in (0 : ℝ)..t, exp (2 * I * (r * z)) * q r * (m r - 1) := by
    rw [← (bm_bn_zero q t z).2, (bm_bn_eq hq ht h0).2]
    simp only [ofReal_zero, sub_zero]
    rw [← intervalIntegral.integral_sub]
    · refine integral_congr fun r _ ↦ ?_
      simp only [m]
      ring
    · exact (hqi.continuousOn_mul he).mul_continuousOn hmc
    · exact hqi.mul_continuousOn he
  rw [hb, sinh_integral_eq_integral hqn h0]
  calc ‖∫ r in (0 : ℝ)..t, exp (2 * I * (r * z)) * q r * (m r - 1)‖
      ≤ ∫ r in (0 : ℝ)..t, ‖q r‖ * (Real.cosh (∫ u in r..t, ‖q u‖) - 1) := by
        refine norm_integral_le_of_norm_le ht (ae_of_all _ fun r hr ↦ ?_)
          (hqni.mul_continuousOn ((Real.continuous_cosh.comp_continuousOn hLc).sub
            continuousOn_const))
        have hr' : r ∈ Icc 0 t := Ioc_subset_Icc_self hr
        rw [norm_mul, norm_mul]
        calc ‖exp (2 * I * (r * z))‖ * ‖q r‖ * ‖m r - 1‖ ≤ 1 * ‖q r‖ * ‖m r - 1‖ := by
              gcongr; exact norm_exp_two_I_mul_le_one hz hr'.1
          _ ≤ ‖q r‖ * (Real.cosh (∫ u in r..t, ‖q u‖) - 1) := by
              rw [one_mul]
              exact mul_le_mul_of_nonneg_left (bounds_aux hq ht hz hr').2.2 (norm_nonneg _)
    _ = (∫ r in (0 : ℝ)..t, ‖q r‖ * Real.cosh (∫ u in r..t, ‖q u‖)) - ∫ r in (0 : ℝ)..t, ‖q r‖ := by
        simp_rw [mul_sub, mul_one]
        exact intervalIntegral.integral_sub
          (hqni.mul_continuousOn (Real.continuous_cosh.comp_continuousOn hLc)) hqni

end TauCeti
