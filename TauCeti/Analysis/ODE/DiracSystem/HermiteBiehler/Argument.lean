/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.DiracSystem.HermiteBiehler.Reflection
public import TauCeti.Analysis.ODE.DiracSystem.ZeroFree
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import TauCeti.Analysis.Contour.Argument.Lift
import TauCeti.Analysis.Contour.Argument.Variation
import TauCeti.Analysis.ODE.DiracSystem.RealPotential
import TauCeti.Analysis.SpecialFunctions.Complex.Arg
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Modulus and argument of the Dirac Hermite–Biehler function on the real axis

Let `q` be a potential, locally integrable on `[0, ∞)`, with `f = Re q` and `g = Im q`, and let
`E(t, z) = A(t, z) - i C(t, z)` be the Hermite–Biehler function of its Dirac system
(`TauCeti.diracHermiteBiehler`). `E(t, z)` and `E~(t, z)` do not vanish for `Im z ≥ 0`
(`TauCeti.diracHermiteBiehler_ne_zero`, `TauCeti.diracHermiteBiehlerDirichlet_ne_zero`), so for a
real `x` the curve `t ↦ E(t, x)` has a continuous argument `φ` on `[0, T]` with `φ(0) = 0`
(`TauCeti.exists_continuousOn_diracHermiteBiehler_eq_norm_mul_exp`).
On the real axis `t ↦ E(t, x)` is absolutely continuous on `[0, T]`
(`TauCeti.absolutelyContinuousOnInterval_diracHermiteBiehler`) and, since `E#(t, x) = conj E(t, x)`
there, satisfies `∂ₜ E = -ix E + q conj E` at almost every `t`
(`TauCeti.ae_hasDerivAt_diracHermiteBiehler`), which reads `∂ₜ E / E = -ix + q e^{-2iφ}`.
The real and imaginary parts of this are the modulus and argument equations

* `log |E(t, x)| = ∫₀ᵗ (f cos 2φ + g sin 2φ)`
  (`TauCeti.log_norm_diracHermiteBiehler_eq_integral`), and
* `φ(t) - φ(0) = ∫₀ᵗ (-x + g cos 2φ - f sin 2φ)`
  (`TauCeti.sub_eq_integral_of_diracHermiteBiehler_eq_norm_mul_exp`),

so that `∂ₜ log |E| = f cos 2φ + g sin 2φ` and `∂ₜ φ = -x + g cos 2φ - f sin 2φ` at almost every
`t` (`TauCeti.ae_hasDerivAt_log_norm_diracHermiteBiehler`,
`TauCeti.ae_hasDerivAt_of_diracHermiteBiehler_eq_norm_mul_exp`). The proof integrates the
logarithmic derivative of the absolutely continuous curve `t ↦ E(t, x)` against a continuous
argument (`AbsolutelyContinuousOnInterval.integral_deriv_div_eq_log_norm_add_I_mul_sub`).

For a real potential, the continuous argument of `t ↦ E(t, 0)` vanishing at `0` is identically
zero (`TauCeti.eqOn_zero_of_diracHermiteBiehler_eq_norm_mul_exp`), since `E(t, 0) = e^{∫₀ᵗ q}`.

The argument here is a continuous argument of `t ↦ E(t, x)` for each fixed `x`; it is not asserted
to depend continuously on `x`.

## References

* A. Poltoratski, *Pointwise convergence of the non-linear Fourier transform*, Ann. of Math. (2)
  199 (2024), 741–793, §2, (2.6)–(2.7).
* L. Mauth, *On pointwise convergence of the non-linear Fourier transform*, arXiv:2210.12286,
  Lemma 17.
-/

public section

open MeasureTheory Set Complex ComplexConjugate Filter Topology

namespace TauCeti

variable {q : ℝ → ℂ} {t T : ℝ}

/-- `E(t, z)` does not vanish in the closed upper half-plane `0 ≤ Im z`. -/
theorem diracHermiteBiehler_ne_zero (hq : LocallyIntegrableOn q (Ici 0)) (ht : 0 ≤ t) {z : ℂ}
    (hz : 0 ≤ z.im) : diracHermiteBiehler q t z ≠ 0 := by
  rw [diracHermiteBiehler_def]
  exact diracFundamentalMatrix_sub_I_mul_ne_zero hq ht hz 0

/-- `E~(t, z)` does not vanish in the closed upper half-plane `0 ≤ Im z`. -/
theorem diracHermiteBiehlerDirichlet_ne_zero (hq : LocallyIntegrableOn q (Ici 0)) (ht : 0 ≤ t)
    {z : ℂ} (hz : 0 ≤ z.im) : diracHermiteBiehlerDirichlet q t z ≠ 0 := by
  rw [diracHermiteBiehlerDirichlet_def]
  exact diracFundamentalMatrix_sub_I_mul_ne_zero hq ht hz 1

/-- **Continuous arguments of `E` on the real axis.** For real `x`, the curve `t ↦ E(t, x)` has a
continuous argument on `[0, T]` vanishing at `0`. -/
theorem exists_continuousOn_diracHermiteBiehler_eq_norm_mul_exp
    (hq : LocallyIntegrableOn q (Ici 0)) (T x : ℝ) :
    ∃ φ : ℝ → ℝ, ContinuousOn φ (Icc 0 T) ∧ φ 0 = 0 ∧
      ∀ s ∈ Icc 0 T, diracHermiteBiehler q s x = ‖diracHermiteBiehler q s x‖ * exp (I * φ s) := by
  rcases lt_or_ge T 0 with hT | hT
  · exact ⟨0, continuousOn_const, rfl, fun s hs ↦ absurd hs (by simp [Icc_eq_empty_of_lt hT])⟩
  obtain ⟨θ, hθ, hlift⟩ := TauCeti.Contour.exists_continuousOn_eq_norm_mul_exp
    (continuousOn_diracHermiteBiehler (hq.integrableOn_compact_subset Icc_subset_Ici_self
      isCompact_Icc) x) fun s hs ↦ diracHermiteBiehler_ne_zero hq hs.1 (by simp)
  -- `E(0, x) = 1`, so `θ 0` is a multiple of `2π` and `θ - θ 0` is still an argument.
  have h0 := hlift 0 (left_mem_Icc.2 hT)
  rw [diracHermiteBiehler_zero, norm_one, ofReal_one, one_mul] at h0
  refine ⟨fun s ↦ θ s - θ 0, hθ.sub continuousOn_const, sub_self _, fun s hs ↦ ?_⟩
  conv_lhs => rw [hlift s hs]
  rw [ofReal_sub, mul_sub, exp_sub, ← h0, div_one]

/-- The real part of the logarithmic derivative `-ix + q e^{-2iθ}`. -/
private theorem re_integrand (x : ℝ) (w : ℂ) (θ : ℝ) :
    (-I * x + w * exp (-2 * I * θ)).re = w.re * Real.cos (2 * θ) + w.im * Real.sin (2 * θ) := by
  simp [exp_re, exp_im, mul_re, mul_im]

/-- The imaginary part of the logarithmic derivative `-ix + q e^{-2iθ}`. -/
private theorem im_integrand (x : ℝ) (w : ℂ) (θ : ℝ) :
    (-I * x + w * exp (-2 * I * θ)).im =
      -x + w.im * Real.cos (2 * θ) - w.re * Real.sin (2 * θ) := by
  simp [exp_re, exp_im, mul_re, mul_im]
  ring

section RealAxis

variable (hq : LocallyIntegrableOn q (Ici 0)) (x : ℝ)
include hq

/-- The right side `-ix E(s, x) + q(s) conj E(s, x)` of the equation of `E` on the real axis. -/
private theorem intervalIntegrable_rhs (ht : 0 ≤ t) :
    IntervalIntegrable (fun s ↦ -I * x * diracHermiteBiehler q s x +
      q s * conj (diracHermiteBiehler q s x)) volume 0 t := by
  have hqt : IntegrableOn q (Icc 0 t) :=
    hq.integrableOn_compact_subset Icc_subset_Ici_self isCompact_Icc
  have hc := continuousOn_diracHermiteBiehler hqt x
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht]
  exact ((continuousOn_const.mul hc).integrableOn_compact isCompact_Icc).add
    (hqt.mul_continuousOn (continuous_conj.comp_continuousOn hc) isCompact_Icc)

/-- The equation of `E` on the real axis: `E(s, x) = 1 + ∫₀ˢ (-ix E + q conj E)` for
`s ∈ [0, T]`. -/
private theorem eqOn_one_add_integral (hT : 0 ≤ T) :
    EqOn (fun s ↦ diracHermiteBiehler q s x) (fun s ↦ 1 + ∫ r in (0 : ℝ)..s,
      (-I * x * diracHermiteBiehler q r x + q r * conj (diracHermiteBiehler q r x)))
      (uIcc 0 T) := fun s hs ↦ by
  simpa only [conj_ofReal] using
    diracHermiteBiehler_eq_one_add_integral_conj hq (uIcc_of_le hT ▸ hs).1 x

/-- **Absolute continuity of `E` on the real axis.** For real `x`, `t ↦ E(t, x)` is absolutely
continuous on `[0, T]`. -/
theorem absolutelyContinuousOnInterval_diracHermiteBiehler (hT : 0 ≤ T) :
    AbsolutelyContinuousOnInterval (fun s ↦ diracHermiteBiehler q s x) 0 T :=
  (((LipschitzWith.const (1 : ℂ)).lipschitzOnWith).absolutelyContinuousOnInterval.add
    ((intervalIntegrable_rhs hq x hT).absolutelyContinuousOnInterval_intervalIntegral'
      left_mem_uIcc)).congr (eqOn_one_add_integral hq x hT).symm

/-- **The equation of `E` on the real axis, almost everywhere.** For real `x`, at almost every
`t ∈ (0, T)`, `∂ₜ E(t, x) = -ix E(t, x) + q(t) conj E(t, x)`. -/
theorem ae_hasDerivAt_diracHermiteBiehler (hT : 0 ≤ T) :
    ∀ᵐ s, s ∈ Ioo 0 T → HasDerivAt (fun s ↦ diracHermiteBiehler q s x)
      (-I * x * diracHermiteBiehler q s x + q s * conj (diracHermiteBiehler q s x)) s := by
  filter_upwards [(intervalIntegrable_rhs hq x hT).ae_hasDerivAt_integral] with s hs hsT
  have hmem : s ∈ uIcc 0 T := uIcc_of_le hT ▸ Ioo_subset_Icc_self hsT
  refine ((hs hmem 0 left_mem_uIcc).const_add 1).congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hsT.1 hsT.2] with r hr
  exact eqOn_one_add_integral hq x hT (uIcc_of_le hT ▸ Ioo_subset_Icc_self hr)

variable {x} {φ : ℝ → ℝ}

/-- **The logarithmic integral of `E` on the real axis.** For an argument `φ` of `t ↦ E(t, x)`
continuous on `[0, t]`, `∫₀ᵗ (-ix + q e^{-2iφ}) = log |E(t, x)| + i (φ(t) - φ(0))`. -/
private theorem integral_eq_log_norm_add_I_mul_sub (ht : 0 ≤ t) (hφ : ContinuousOn φ (Icc 0 t))
    (hlift : ∀ s ∈ Icc 0 t,
      diracHermiteBiehler q s x = ‖diracHermiteBiehler q s x‖ * exp (I * φ s)) :
    ∫ s in (0 : ℝ)..t, (-I * x + q s * exp (-2 * I * φ s)) =
      (Real.log ‖diracHermiteBiehler q t x‖ : ℂ) + I * (φ t - φ 0 : ℝ) := by
  have hac := absolutelyContinuousOnInterval_diracHermiteBiehler hq x ht
  have hne (s) (hs : s ∈ Icc 0 t) : diracHermiteBiehler q s x ≠ 0 :=
    diracHermiteBiehler_ne_zero hq hs.1 (by simp)
  have h := hac.integral_deriv_div_eq_log_norm_add_I_mul_sub (θ := φ)
    (fun s hs ↦ hne s (uIcc_of_le ht ▸ hs)) (uIcc_of_le ht ▸ hφ)
    (fun s hs ↦ hlift s (uIcc_of_le ht ▸ hs))
  rw [diracHermiteBiehler_zero, norm_one, Real.log_one, sub_zero] at h
  rw [← h]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [ae_hasDerivAt_diracHermiteBiehler hq x ht, Measure.ae_ne volume t]
    with s hs hst hsI
  rw [uIoc_of_le ht] at hsI
  have hsI' : s ∈ Ioo 0 t := ⟨hsI.1, hsI.2.lt_of_ne hst⟩
  have hsc : s ∈ Icc 0 t := Ioo_subset_Icc_self hsI'
  have h0 := hne s hsc
  rw [(hs hsI').deriv, ← conj_div_eq_exp_of_eq_norm_mul_exp h0 (hlift s hsc)]
  field_simp

/-- The integrand `-ix + q e^{-2iφ}` is interval integrable on `[0, t]`. -/
private theorem intervalIntegrable_mul_exp (ht : 0 ≤ t) (hφ : ContinuousOn φ (Icc 0 t)) :
    IntervalIntegrable (fun s ↦ -I * x + q s * exp (-2 * I * φ s)) volume 0 t := by
  have hqt : IntegrableOn q (Icc 0 t) :=
    hq.integrableOn_compact_subset Icc_subset_Ici_self isCompact_Icc
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht]
  refine (integrableOn_const measure_Icc_lt_top.ne).add
    (hqt.mul_continuousOn ?_ isCompact_Icc)
  exact (continuous_exp.comp_continuousOn (continuousOn_const.mul
    (continuous_ofReal.comp_continuousOn hφ)))

/-- **The modulus equation, integrated.** For an argument `φ` of `t ↦ E(t, x)` continuous on
`[0, t]`, `log |E(t, x)| = ∫₀ᵗ (f cos 2φ + g sin 2φ)` with `f = Re q`, `g = Im q`. -/
theorem log_norm_diracHermiteBiehler_eq_integral (ht : 0 ≤ t) (hφ : ContinuousOn φ (Icc 0 t))
    (hlift : ∀ s ∈ Icc 0 t,
      diracHermiteBiehler q s x = ‖diracHermiteBiehler q s x‖ * exp (I * φ s)) :
    Real.log ‖diracHermiteBiehler q t x‖ =
      ∫ s in (0 : ℝ)..t, ((q s).re * Real.cos (2 * φ s) + (q s).im * Real.sin (2 * φ s)) := by
  have h := congrArg reCLM (integral_eq_log_norm_add_I_mul_sub hq ht hφ hlift)
  rw [← reCLM.intervalIntegral_comp_comm (intervalIntegrable_mul_exp hq (x := x) ht hφ)] at h
  simp only [reCLM_apply, re_integrand] at h
  rw [h]
  simp

/-- **The argument equation, integrated.** For an argument `φ` of `t ↦ E(t, x)` continuous on
`[0, t]`, `φ(t) - φ(0) = ∫₀ᵗ (-x + g cos 2φ - f sin 2φ)` with `f = Re q`, `g = Im q`. -/
theorem sub_eq_integral_of_diracHermiteBiehler_eq_norm_mul_exp (ht : 0 ≤ t)
    (hφ : ContinuousOn φ (Icc 0 t))
    (hlift : ∀ s ∈ Icc 0 t,
      diracHermiteBiehler q s x = ‖diracHermiteBiehler q s x‖ * exp (I * φ s)) :
    φ t - φ 0 =
      ∫ s in (0 : ℝ)..t, (-x + (q s).im * Real.cos (2 * φ s) - (q s).re * Real.sin (2 * φ s)) := by
  have h := congrArg imCLM (integral_eq_log_norm_add_I_mul_sub hq ht hφ hlift)
  rw [← imCLM.intervalIntegral_comp_comm (intervalIntegrable_mul_exp hq (x := x) ht hφ)] at h
  simp only [imCLM_apply, im_integrand] at h
  rw [h]
  simp

/-- The real and imaginary parts of the integrand `-ix + q e^{-2iφ}` are interval integrable on
`[0, T]`. -/
private theorem intervalIntegrable_re_and_im (hT : 0 ≤ T) (hφ : ContinuousOn φ (Icc 0 T)) :
    IntervalIntegrable
        (fun s ↦ (q s).re * Real.cos (2 * φ s) + (q s).im * Real.sin (2 * φ s)) volume 0 T ∧
      IntervalIntegrable
        (fun s ↦ -x + (q s).im * Real.cos (2 * φ s) - (q s).re * Real.sin (2 * φ s))
        volume 0 T := by
  have hI := intervalIntegrable_mul_exp hq (x := x) hT hφ
  have hre : IntervalIntegrable (fun s ↦ (-I * x + q s * exp (-2 * I * φ s)).re) volume 0 T :=
    ⟨hI.1.re, hI.2.re⟩
  have him : IntervalIntegrable (fun s ↦ (-I * x + q s * exp (-2 * I * φ s)).im) volume 0 T :=
    ⟨hI.1.im, hI.2.im⟩
  simp only [re_integrand, im_integrand] at hre him
  exact ⟨hre, him⟩

/-- **The modulus equation.** For an argument `φ` of `t ↦ E(t, x)` continuous on `[0, T]`, at
almost every `t ∈ (0, T)`, `∂ₜ log |E(t, x)| = f cos 2φ + g sin 2φ`, with `f = Re q`, `g = Im q`. -/
theorem ae_hasDerivAt_log_norm_diracHermiteBiehler (hT : 0 ≤ T) (hφ : ContinuousOn φ (Icc 0 T))
    (hlift : ∀ s ∈ Icc 0 T,
      diracHermiteBiehler q s x = ‖diracHermiteBiehler q s x‖ * exp (I * φ s)) :
    ∀ᵐ t, t ∈ Ioo 0 T →
      HasDerivAt (fun s ↦ Real.log ‖diracHermiteBiehler q s x‖)
        ((q t).re * Real.cos (2 * φ t) + (q t).im * Real.sin (2 * φ t)) t := by
  have hI := (intervalIntegrable_re_and_im hq (x := x) hT hφ).1
  filter_upwards [hI.ae_hasDerivAt_integral] with t h htT
  have hmem : t ∈ uIcc 0 T := uIcc_of_le hT ▸ Ioo_subset_Icc_self htT
  refine (h hmem 0 left_mem_uIcc).congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds htT.1 htT.2] with s hs
  exact log_norm_diracHermiteBiehler_eq_integral hq hs.1.le
    (hφ.mono (Icc_subset_Icc_right hs.2.le)) fun r hr ↦ hlift r (Icc_subset_Icc_right hs.2.le hr)

/-- **The argument equation.** For an argument `φ` of `t ↦ E(t, x)` continuous on `[0, T]`, at
almost every `t ∈ (0, T)`, `∂ₜ φ = -x + g cos 2φ - f sin 2φ`, with `f = Re q`, `g = Im q`. -/
theorem ae_hasDerivAt_of_diracHermiteBiehler_eq_norm_mul_exp (hT : 0 ≤ T)
    (hφ : ContinuousOn φ (Icc 0 T))
    (hlift : ∀ s ∈ Icc 0 T,
      diracHermiteBiehler q s x = ‖diracHermiteBiehler q s x‖ * exp (I * φ s)) :
    ∀ᵐ t, t ∈ Ioo 0 T →
      HasDerivAt φ (-x + (q t).im * Real.cos (2 * φ t) - (q t).re * Real.sin (2 * φ t)) t := by
  have hI := (intervalIntegrable_re_and_im hq (x := x) hT hφ).2
  filter_upwards [hI.ae_hasDerivAt_integral] with t h htT
  have hmem : t ∈ uIcc 0 T := uIcc_of_le hT ▸ Ioo_subset_Icc_self htT
  refine ((h hmem 0 left_mem_uIcc).const_add (φ 0)).congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds htT.1 htT.2] with s hs
  rw [← sub_eq_iff_eq_add', sub_eq_integral_of_diracHermiteBiehler_eq_norm_mul_exp hq hs.1.le
    (hφ.mono (Icc_subset_Icc_right hs.2.le)) fun r hr ↦ hlift r (Icc_subset_Icc_right hs.2.le hr)]

end RealAxis

/-- **The argument at `x = 0` for a real potential.** If `q` is real on `[0, T]`, then
`E(t, 0) = e^{∫₀ᵗ q} > 0`, so a continuous argument `φ` of `t ↦ E(t, 0)` on `[0, T]` with
`φ(0) = 0` vanishes on `[0, T]`. -/
theorem eqOn_zero_of_diracHermiteBiehler_eq_norm_mul_exp (hq : LocallyIntegrableOn q (Ici 0))
    (hre : ∀ s ∈ Icc 0 T, (q s).im = 0) {φ : ℝ → ℝ} (hφ : ContinuousOn φ (Icc 0 T))
    (hφ0 : φ 0 = 0)
    (hlift : ∀ s ∈ Icc 0 T,
      diracHermiteBiehler q s 0 = ‖diracHermiteBiehler q s 0‖ * exp (I * φ s)) :
    EqOn φ 0 (Icc 0 T) := by
  intro s hs
  have hE (r : ℝ) (hr : r ∈ Icc 0 T) :
      diracHermiteBiehler q r 0 = ‖diracHermiteBiehler q r 0‖ * exp (I * ((0 : ℝ → ℝ) r)) := by
    have hM := diracFundamentalMatrix_spectralParam_zero_of_im_eq_zero
      (hq.integrableOn_uIcc_of_Ici hr.1) fun u hu ↦
        hre u ⟨(uIcc_of_le hr.1 ▸ hu).1, (uIcc_of_le hr.1 ▸ hu).2.trans hr.2⟩
    rw [diracHermiteBiehler_def, hM]
    simp
  have h := TauCeti.Contour.sub_eq_sub_of_eq_norm_mul_exp isPreconnected_Icc
    (left_mem_Icc.2 (hs.1.trans hs.2)) hs
    (fun r hr ↦ diracHermiteBiehler_ne_zero hq hr.1 (by simp)) hφ
    continuousOn_const hlift hE
  simpa [hφ0] using h

end TauCeti
