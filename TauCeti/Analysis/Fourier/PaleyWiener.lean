/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.Analysis.Fourier.LpSpace
import TauCeti.Analysis.LaplaceTransform.Truncated

/-!
# Paley–Wiener functions

For `t ≥ 0` and a density `φ ∈ L²(-t, t)`, the **Paley–Wiener function** of `φ` is
`F(z) = ∫_{-t}^{t} φ(s) e^{isz} ds` (`TauCeti.paleyWienerFunction`). These functions form the
Paley–Wiener space `PW_t`; on the real line `F` is, up to a rescaling, the Fourier transform of the
extension of `φ` by zero, and in the complex plane it is entire of exponential type at most `t`.

## Main results

* `TauCeti.differentiable_paleyWienerFunction`: `F` is entire.
* `TauCeti.norm_paleyWienerFunction_le`: `|F(z)| ≤ (∫_{-t}^{t} |φ|) e^{t |Im z|}`, and
  `TauCeti.norm_paleyWienerFunction_le_sqrt`: `|F(z)| ≤ √(2t) ‖φ‖₂ e^{t |Im z|}`.
* `TauCeti.paleyWienerFunction_ofReal_eq_fourier`: on `ℝ`, `F(x) = 𝓕(φ 1_{(-t, t]})(-x / 2π)`
  for Mathlib's Fourier transform `𝓕 g(w) = ∫ e^{-2πivw} g(v) dv`.
* `TauCeti.integral_paleyWienerFunction_mul_conj`: Parseval's identity
  `∫_ℝ F(x) conj(G(x)) dx = 2π ∫_{-t}^{t} φ(s) conj(ψ(s)) ds` for the Paley–Wiener functions `F`,
  `G` of `φ`, `ψ`; in particular `TauCeti.integral_norm_paleyWienerFunction_sq`:
  `‖F‖²_{L²(ℝ)} = 2π ‖φ‖²_{L²(-t, t)}`, and `F` is square integrable on `ℝ`
  (`TauCeti.memLp_paleyWienerFunction`).
* `TauCeti.conj_paleyWienerFunction_conj`: the reflection `F#(z) = conj(F(conj z))` is the
  Paley–Wiener function of `s ↦ conj(φ(-s))`.
* `TauCeti.paleyWienerFunction_eq_paleyWienerFunction_indicator`: for `0 ≤ s ≤ t`, a Paley–Wiener
  function for the interval `[-s, s]` is one for `[-t, t]`, so that `PW_s ⊆ PW_t`.
* `TauCeti.paleyWienerFunction_cexp_mul`: the Paley–Wiener function of the exponential
  `e^{isw}` is `2 sin(t(z + w))/(z + w)` for `z + w ≠ 0`; for `w = 0` it is `2 sin(tz)/z` for
  `z ≠ 0`.
* `TauCeti.paleyWienerFunction_eq_integral_mul_conj_paleyWienerKernel`: the reproducing property
  `F(λ) = ∫_ℝ F(x) conj(k_t(λ, x)) dx` of the kernel
  `k_t(λ, z) = sin(t(z - conj λ))/(π(z - conj λ))` (`TauCeti.paleyWienerKernel`), which lies in
  `PW_t` (`TauCeti.paleyWienerKernel_def` with `TauCeti.memLp_paleyWienerKernel_density`), is
  square integrable on `ℝ` (`TauCeti.memLp_paleyWienerKernel`) and has
  `‖k_t(λ, ·)‖²_{L²(ℝ)} = k_t(λ, λ)` (`TauCeti.integral_norm_paleyWienerKernel_sq`).

## References

* R. E. A. C. Paley, N. Wiener, *Fourier transforms in the complex domain*, Amer. Math. Soc.
  Colloq. Publ. 19, 1934.
* A. Poltoratski, *Pointwise convergence of the non-linear Fourier transform*, Ann. of Math. (2)
  199 (2024), 741–793, §2, for the space `PW_t` and its reproducing kernel.
-/

public section

open MeasureTheory Set Complex
open scoped ComplexConjugate Real FourierTransform Interval

namespace TauCeti

variable {t : ℝ} {φ ψ : ℝ → ℂ}

/-- The **Paley–Wiener function** `F(z) = ∫_{-t}^{t} φ(s) e^{isz} ds` of a density `φ`. For
`t ≥ 0` and `φ ∈ L²(-t, t)` these functions form the Paley–Wiener space `PW_t`. -/
noncomputable def paleyWienerFunction (t : ℝ) (φ : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ s in -t..t, φ s * cexp (I * s * z)

/-- The defining formula of the Paley–Wiener function. -/
theorem paleyWienerFunction_def (t : ℝ) (φ : ℝ → ℂ) (z : ℂ) :
    paleyWienerFunction t φ z = ∫ s in -t..t, φ s * cexp (I * s * z) :=
  (rfl)

/-- On the trivial interval the Paley–Wiener function vanishes: `PW_0 = {0}`. -/
@[simp]
theorem paleyWienerFunction_zero_left (φ : ℝ → ℂ) : paleyWienerFunction 0 φ = 0 := by
  ext z
  simp [paleyWienerFunction_def]

/-- **Paley–Wiener functions are entire.** No integrability is needed: if `φ` is not integrable
on `[-t, t]`, the Paley–Wiener function is `0`. -/
theorem differentiable_paleyWienerFunction (t : ℝ) (φ : ℝ → ℂ) :
    Differentiable ℂ (paleyWienerFunction t φ) := by
  have h := (differentiable_intervalIntegral_mul_cexp_neg_mul (f := φ) (a := -t) (b := t)).comp
    (differentiable_id.const_mul (-I))
  convert h using 1
  ext z
  rw [Function.comp_apply, id_eq, paleyWienerFunction_def]
  congr 1 with s
  ring_nf

/-- The Paley–Wiener function is additive in the density. -/
theorem paleyWienerFunction_add (hφ : IntervalIntegrable φ volume (-t) t)
    (hψ : IntervalIntegrable ψ volume (-t) t) :
    paleyWienerFunction t (φ + ψ) = paleyWienerFunction t φ + paleyWienerFunction t ψ := by
  ext z
  have hc : ContinuousOn (fun s : ℝ ↦ cexp (I * s * z)) (uIcc (-t) t) := by fun_prop
  simp only [paleyWienerFunction_def, Pi.add_apply, add_mul]
  exact intervalIntegral.integral_add (hφ.mul_continuousOn hc) (hψ.mul_continuousOn hc)

/-- The Paley–Wiener function is homogeneous in the density. -/
@[simp]
theorem paleyWienerFunction_smul (c : ℂ) (t : ℝ) (φ : ℝ → ℂ) :
    paleyWienerFunction t (c • φ) = c • paleyWienerFunction t φ := by
  ext z
  simp only [paleyWienerFunction_def, Pi.smul_apply, smul_eq_mul, mul_assoc,
    intervalIntegral.integral_const_mul]

/-- The Paley–Wiener function only depends on the density almost everywhere on `[-t, t]`. -/
theorem paleyWienerFunction_congr_ae (h : ∀ᵐ s ∂volume, s ∈ Ι (-t) t → φ s = ψ s) :
    paleyWienerFunction t φ = paleyWienerFunction t ψ := by
  ext z
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [h] with s hs hmem
  rw [hs hmem]

/-! ### Growth -/

/-- `|e^{isz}| ≤ e^{t |Im z|}` for `|s| ≤ t`. -/
theorem norm_cexp_I_mul_le {s : ℝ} (hs : |s| ≤ t) (z : ℂ) :
    ‖cexp (I * s * z)‖ ≤ Real.exp (t * |z.im|) := by
  rw [norm_exp, Real.exp_le_exp]
  have : (I * s * z).re = -(s * z.im) := by simp [mul_comm]
  rw [this]
  calc -(s * z.im) ≤ |s * z.im| := neg_le_abs _
    _ = |s| * |z.im| := abs_mul _ _
    _ ≤ t * |z.im| := mul_le_mul_of_nonneg_right hs (abs_nonneg _)

/-- **Exponential type.** `|F(z)| ≤ (∫_{-t}^{t} |φ|) e^{t |Im z|}`. -/
theorem norm_paleyWienerFunction_le (ht : 0 ≤ t) (φ : ℝ → ℂ) (z : ℂ) :
    ‖paleyWienerFunction t φ z‖ ≤ (∫ s in -t..t, ‖φ s‖) * Real.exp (t * |z.im|) := by
  have htt : -t ≤ t := neg_le_self ht
  by_cases hφ : IntervalIntegrable φ volume (-t) t
  · rw [paleyWienerFunction_def, ← intervalIntegral.integral_mul_const]
    refine intervalIntegral.norm_integral_le_of_norm_le htt (.of_forall fun s hs ↦ ?_)
      (hφ.norm.mul_const _)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_cexp_I_mul_le (abs_le.2 ⟨hs.1.le, hs.2⟩) z)
      (norm_nonneg _)
  · have h0 : paleyWienerFunction t φ z = 0 := by
      rw [paleyWienerFunction_def]
      refine intervalIntegral.integral_undef fun h ↦ hφ ?_
      have hc : ContinuousOn (fun s : ℝ ↦ cexp (-(I * s * z))) (uIcc (-t) t) := by fun_prop
      exact (h.mul_continuousOn hc).congr fun s _ ↦ by simp [mul_assoc, ← Complex.exp_add]
    rw [h0, norm_zero]
    exact mul_nonneg (intervalIntegral.integral_nonneg htt fun _ _ ↦ norm_nonneg _)
      (Real.exp_pos _).le

/-- **Exponential type, `L²` form.** `|F(z)| ≤ √(2t) ‖φ‖_{L²(-t, t)} e^{t |Im z|}`. -/
theorem norm_paleyWienerFunction_le_sqrt (ht : 0 ≤ t)
    (hφ : MemLp φ 2 (volume.restrict (Ioc (-t) t))) (z : ℂ) :
    ‖paleyWienerFunction t φ z‖ ≤
      √(2 * t) * √(∫ s in -t..t, ‖φ s‖ ^ 2) * Real.exp (t * |z.im|) := by
  refine (norm_paleyWienerFunction_le ht φ z).trans
    (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
  have htt : -t ≤ t := neg_le_self ht
  rw [intervalIntegral.integral_of_le htt, intervalIntegral.integral_of_le htt]
  -- Cauchy–Schwarz for `‖φ‖` and `1` on `(-t, t]`.
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict (Ioc (-t) t))
    Real.HolderConjugate.two_two (f := fun s ↦ ‖φ s‖) (g := fun _ ↦ (1 : ℝ))
    (.of_forall fun _ ↦ norm_nonneg _) (.of_forall fun _ ↦ zero_le_one)
    (by simpa using hφ.norm) (memLp_const _)
  simp only [mul_one, Real.one_rpow, integral_const, smul_eq_mul, measureReal_restrict_apply_univ,
    Real.volume_real_Ioc_of_le htt] at h
  convert h using 1
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, mul_comm]
  norm_num [two_mul, sub_neg_eq_add]

/-! ### The Paley–Wiener function on the real line -/

/-- On the real line the Paley–Wiener function is a rescaled Fourier transform: with Mathlib's
`𝓕 g(w) = ∫ e^{-2πivw} g(v) dv`, `F(x) = 𝓕(φ 1_{(-t, t]})(-x / 2π)`. -/
theorem paleyWienerFunction_ofReal_eq_fourier (ht : 0 ≤ t) (φ : ℝ → ℂ) (x : ℝ) :
    paleyWienerFunction t φ x = 𝓕 ((Ioc (-t) t).indicator φ) (-(2 * π)⁻¹ * x) := by
  rw [Real.fourier_real_eq_integral_exp_smul, paleyWienerFunction_def,
    intervalIntegral.integral_of_le (neg_le_self ht), ← integral_indicator measurableSet_Ioc]
  congr 1 with v
  by_cases hv : v ∈ Ioc (-t) t
  · simp only [indicator_of_mem hv, smul_eq_mul]
    rw [mul_comm]
    congr 2
    push_cast
    field_simp
  · simp [indicator_of_notMem hv]

/-- **Parseval's identity for Paley–Wiener functions.** For densities `φ, ψ ∈ L²(-t, t)`,
`∫_ℝ F(x) conj(G(x)) dx = 2π ∫_{-t}^{t} φ(s) conj(ψ(s)) ds`, where `F` and `G` are the
Paley–Wiener functions of `φ` and `ψ`. -/
theorem integral_paleyWienerFunction_mul_conj (ht : 0 ≤ t)
    (hφ : MemLp φ 2 (volume.restrict (Ioc (-t) t)))
    (hψ : MemLp ψ 2 (volume.restrict (Ioc (-t) t))) :
    ∫ x : ℝ, paleyWienerFunction t φ x * conj (paleyWienerFunction t ψ x) =
      2 * π * ∫ s in -t..t, φ s * conj (ψ s) := by
  have hψ₁ := (integrable_indicator_iff measurableSet_Ioc).2 (hψ.integrable one_le_two)
  have h := hψ₁.integral_inner_fourier_fourier
    ((memLp_indicator_iff_restrict measurableSet_Ioc.nullMeasurableSet).2 hψ)
    ((integrable_indicator_iff measurableSet_Ioc).2 (hφ.integrable one_le_two))
    ((memLp_indicator_iff_restrict measurableSet_Ioc.nullMeasurableSet).2 hφ)
  simp only [RCLike.inner_apply] at h
  simp_rw [paleyWienerFunction_ofReal_eq_fourier ht]
  rw [Measure.integral_comp_mul_left (fun w ↦ 𝓕 ((Ioc (-t) t).indicator φ) w *
    conj (𝓕 ((Ioc (-t) t).indicator ψ) w)), h, intervalIntegral.integral_of_le (neg_le_self ht),
    ← integral_indicator measurableSet_Ioc]
  have h2π : |(-(2 * π)⁻¹)⁻¹| = 2 * π := by
    rw [inv_neg, inv_inv, abs_neg, abs_of_pos Real.two_pi_pos]
  rw [h2π, Complex.real_smul]
  push_cast
  congr 2 with s
  by_cases hs : s ∈ Ioc (-t) t <;> simp [hs]

/-- **Plancherel's identity for Paley–Wiener functions.** For `φ ∈ L²(-t, t)`,
`‖F‖²_{L²(ℝ)} = 2π ‖φ‖²_{L²(-t, t)}`. -/
theorem integral_norm_paleyWienerFunction_sq (ht : 0 ≤ t)
    (hφ : MemLp φ 2 (volume.restrict (Ioc (-t) t))) :
    ∫ x : ℝ, ‖paleyWienerFunction t φ x‖ ^ 2 = 2 * π * ∫ s in -t..t, ‖φ s‖ ^ 2 := by
  have h := integral_paleyWienerFunction_mul_conj ht hφ hφ
  simp_rw [Complex.mul_conj', ← ofReal_pow] at h
  rw [integral_complex_ofReal, intervalIntegral.integral_ofReal] at h
  exact_mod_cast h

/-- A Paley–Wiener function of a density in `L²(-t, t)` is square integrable on `ℝ`. -/
theorem memLp_paleyWienerFunction (ht : 0 ≤ t) (hφ : MemLp φ 2 (volume.restrict (Ioc (-t) t))) :
    MemLp (fun x : ℝ ↦ paleyWienerFunction t φ x) 2 := by
  have hφ₁ := (integrable_indicator_iff measurableSet_Ioc).2 (hφ.integrable one_le_two)
  have hF := hφ₁.memLp_fourier_two
    ((memLp_indicator_iff_restrict measurableSet_Ioc.nullMeasurableSet).2 hφ)
  have hc : Continuous fun x : ℝ ↦ paleyWienerFunction t φ x :=
    (differentiable_paleyWienerFunction t φ).continuous.comp continuous_ofReal
  refine (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).2 ?_
  simp_rw [paleyWienerFunction_ofReal_eq_fourier ht]
  exact ((memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).1 hF).comp_mul_left'
    (neg_ne_zero.2 (inv_ne_zero Real.two_pi_pos.ne'))

/-! ### Reflection and nesting -/

/-- **Reflection.** The reflection `F#(z) = conj(F(conj z))` of the Paley–Wiener function of `φ` is
the Paley–Wiener function of `s ↦ conj(φ(-s))`; in particular `F ∈ PW_t` implies `F# ∈ PW_t`. -/
theorem conj_paleyWienerFunction_conj (t : ℝ) (φ : ℝ → ℂ) (z : ℂ) :
    conj (paleyWienerFunction t φ (conj z)) =
      paleyWienerFunction t (fun s ↦ conj (φ (-s))) z := by
  have h : conj (paleyWienerFunction t φ (conj z)) =
      ∫ s in -t..t, conj (φ s) * cexp (I * (-s : ℝ) * z) := by
    rw [paleyWienerFunction_def, ← intervalIntegral.intervalIntegral_conj]
    congr 1 with s
    rw [map_mul, ← Complex.exp_conj]
    simp
  rw [h, paleyWienerFunction_def]
  simpa using intervalIntegral.integral_comp_neg
    (fun s : ℝ ↦ conj (φ (-s)) * cexp (I * s * z)) (a := -t) (b := t)

/-- **Nesting.** For `0 ≤ s ≤ t`, the Paley–Wiener function of `φ` on `[-s, s]` is the one of
`φ 1_{(-s, s]}` on `[-t, t]`; together with `MeasureTheory.memLp_indicator_iff_restrict` and
`MeasureTheory.Measure.restrict_restrict` this gives `PW_s ⊆ PW_t`. -/
theorem paleyWienerFunction_eq_paleyWienerFunction_indicator {s : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (φ : ℝ → ℂ) :
    paleyWienerFunction s φ = paleyWienerFunction t ((Ioc (-s) s).indicator φ) := by
  ext z
  rw [paleyWienerFunction_def, paleyWienerFunction_def,
    intervalIntegral.integral_of_le (neg_le_self hs),
    intervalIntegral.integral_of_le (neg_le_self (hs.trans hst))]
  have h : (fun r ↦ (Ioc (-s) s).indicator φ r * cexp (I * r * z)) =
      (Ioc (-s) s).indicator fun r ↦ φ r * cexp (I * r * z) := by
    ext r
    by_cases hr : r ∈ Ioc (-s) s <;> simp [hr]
  rw [h, setIntegral_indicator measurableSet_Ioc,
    inter_eq_right.2 (Ioc_subset_Ioc (neg_le_neg hst) hst)]

/-! ### Exponentials and the reproducing kernel -/

/-- The Paley–Wiener function of the exponential `e^{isw}` is `2 sin(t(z + w))/(z + w)` for
`z + w ≠ 0`. -/
theorem paleyWienerFunction_cexp_mul (t : ℝ) {w z : ℂ} (h : z + w ≠ 0) :
    paleyWienerFunction t (fun s ↦ cexp (I * s * w)) z = 2 * sin (t * (z + w)) / (z + w) := by
  have hc : I * (z + w) ≠ 0 := mul_ne_zero I_ne_zero h
  have h' : (fun s : ℝ ↦ cexp (I * s * w) * cexp (I * s * z)) =
      fun s : ℝ ↦ cexp (I * (z + w) * s) := by
    ext s
    rw [← Complex.exp_add]
    ring_nf
  have e₁ : I * (z + w) * (t : ℂ) = t * (z + w) * I := by ring
  have e₂ : I * (z + w) * ((-t : ℝ) : ℂ) = -(t * (z + w)) * I := by push_cast; ring
  rw [paleyWienerFunction_def, h', integral_exp_mul_complex hc, two_sin, e₁, e₂,
    div_eq_div_iff hc h]
  linear_combination (cexp (t * (z + w) * I) - cexp (-(t * (z + w)) * I)) * (z + w) * I_sq

/-- The Paley–Wiener function of the constant `1` is `2 sin(tz)/z` for `z ≠ 0`. -/
theorem paleyWienerFunction_one (t : ℝ) {z : ℂ} (hz : z ≠ 0) :
    paleyWienerFunction t 1 z = 2 * sin (t * z) / z := by
  have h := paleyWienerFunction_cexp_mul t (w := 0) (z := z) (by simpa using hz)
  simp only [mul_zero, Complex.exp_zero, add_zero] at h
  rwa [Pi.one_def]

/-- The **reproducing kernel** `k_t(λ, z)` of the Paley–Wiener space `PW_t`: the Paley–Wiener
function of `s ↦ e^{-is conj λ}/(2π)`, which is `sin(t(z - conj λ))/(π(z - conj λ))` for
`z ≠ conj λ` (`TauCeti.paleyWienerKernel_eq`). -/
noncomputable def paleyWienerKernel (t : ℝ) (w z : ℂ) : ℂ :=
  paleyWienerFunction t (fun s ↦ cexp (I * s * (-conj w)) / (2 * π)) z

/-- The defining formula of the reproducing kernel of `PW_t`. -/
theorem paleyWienerKernel_def (t : ℝ) (w z : ℂ) :
    paleyWienerKernel t w z =
      paleyWienerFunction t (fun s ↦ cexp (I * s * (-conj w)) / (2 * π)) z :=
  (rfl)

/-- The reproducing kernel of `PW_t` in closed form:
`k_t(λ, z) = sin(t(z - conj λ))/(π(z - conj λ))` for `z ≠ conj λ`. -/
theorem paleyWienerKernel_eq (t : ℝ) {w z : ℂ} (h : z ≠ conj w) :
    paleyWienerKernel t w z = sin (t * (z - conj w)) / (π * (z - conj w)) := by
  have h' : z + -conj w ≠ 0 := by rwa [← sub_eq_add_neg, sub_ne_zero]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hdiv : (fun s : ℝ ↦ cexp (I * s * (-conj w)) / (2 * π)) =
      ((2 * π : ℂ)⁻¹) • fun s : ℝ ↦ cexp (I * s * (-conj w)) := by
    ext s
    simp [div_eq_inv_mul]
  rw [paleyWienerKernel_def, hdiv, paleyWienerFunction_smul, Pi.smul_apply,
    paleyWienerFunction_cexp_mul t h', ← sub_eq_add_neg, smul_eq_mul]
  field_simp

/-- On the antidiagonal `z = conj λ` the reproducing kernel of `PW_t` is `t/π`. -/
@[simp]
theorem paleyWienerKernel_conj_self (t : ℝ) (w : ℂ) : paleyWienerKernel t w (conj w) = t / π := by
  have h : (fun s : ℝ ↦ cexp (I * s * (-conj w)) / (2 * π) * cexp (I * s * conj w)) =
      fun _ ↦ (2 * π : ℂ)⁻¹ := by
    ext s
    rw [div_mul_eq_mul_div, ← Complex.exp_add]
    simp [div_eq_inv_mul]
  rw [paleyWienerKernel_def, paleyWienerFunction_def, h, intervalIntegral.integral_const,
    real_smul]
  push_cast
  field_simp
  ring

/-- The density `s ↦ e^{-is conj λ}/(2π)` of the reproducing kernel of `PW_t` lies in
`L²(-t, t)`. -/
theorem memLp_paleyWienerKernel_density (t : ℝ) (w : ℂ) :
    MemLp (fun s : ℝ ↦ cexp (I * s * (-conj w)) / (2 * π)) 2 (volume.restrict (Ioc (-t) t)) := by
  refine MemLp.of_bound (by fun_prop) (Real.exp (t * |(-conj w).im|) / (2 * π))
    (ae_restrict_of_forall_mem measurableSet_Ioc fun s hs ↦ ?_)
  rw [norm_div, show ‖(2 * π : ℂ)‖ = 2 * π by simp]
  exact div_le_div_of_nonneg_right (norm_cexp_I_mul_le (abs_le.2 ⟨hs.1.le, hs.2⟩) _)
    Real.two_pi_pos.le

/-- The reproducing kernel `k_t(λ, ·)` of `PW_t` is square integrable on `ℝ`. -/
theorem memLp_paleyWienerKernel (ht : 0 ≤ t) (w : ℂ) :
    MemLp (fun x : ℝ ↦ paleyWienerKernel t w x) 2 :=
  memLp_paleyWienerFunction ht (memLp_paleyWienerKernel_density t w)

/-- **The reproducing property.** For `φ ∈ L²(-t, t)` with Paley–Wiener function `F` and every
`λ ∈ ℂ`, `F(λ) = ∫_ℝ F(x) conj(k_t(λ, x)) dx`. -/
theorem paleyWienerFunction_eq_integral_mul_conj_paleyWienerKernel (ht : 0 ≤ t)
    (hφ : MemLp φ 2 (volume.restrict (Ioc (-t) t))) (w : ℂ) :
    paleyWienerFunction t φ w =
      ∫ x : ℝ, paleyWienerFunction t φ x * conj (paleyWienerKernel t w x) := by
  simp_rw [paleyWienerKernel_def]
  rw [integral_paleyWienerFunction_mul_conj ht hφ (memLp_paleyWienerKernel_density t w),
    paleyWienerFunction_def, ← intervalIntegral.integral_const_mul]
  congr 1 with s
  have h : conj (cexp (I * s * (-conj w)) / (2 * π)) = cexp (I * s * w) / (2 * π) := by
    have h2π : conj (2 * π : ℂ) = 2 * π := by exact_mod_cast conj_ofReal (2 * π)
    rw [map_div₀, ← Complex.exp_conj, h2π]
    simp
  rw [h]
  field_simp

/-- The squared `L²(ℝ)` norm of the reproducing kernel `k_t(λ, ·)` of `PW_t` is `k_t(λ, λ)`: the
reproducing property applied to the kernel itself. -/
theorem integral_norm_paleyWienerKernel_sq (ht : 0 ≤ t) (w : ℂ) :
    ∫ x : ℝ, ‖paleyWienerKernel t w x‖ ^ 2 = (paleyWienerKernel t w w).re := by
  have h := paleyWienerFunction_eq_integral_mul_conj_paleyWienerKernel ht
    (memLp_paleyWienerKernel_density t w) w
  simp_rw [← paleyWienerKernel_def, Complex.mul_conj', ← ofReal_pow] at h
  rw [h, integral_complex_ofReal, ofReal_re]

end TauCeti
