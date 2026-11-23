/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Amplitude.LeftSymbol
public import TauCeti.Analysis.Pseudodifferential.Kernel
public import TauCeti.Analysis.Pseudodifferential.ProperSupport.Basic
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import TauCeti.Analysis.Fourier.FourierChar.Deriv

/-!
# Integral operators with smooth compactly supported kernels

Let `K(x, y)` be a smooth compactly supported function on `ℝⁿ × ℝⁿ` with values in `V →L[ℂ] W`.
The integral operator `u ↦ ∫ K(x, y) u(y) dy` is a pseudodifferential operator: it is the
quantization of the symbol

`r(x, ξ) = ∫ exp(-i ⟪x - y, ξ⟫) K(x, y) dy`

(`TauCeti.Symbol.ofKernel`), the Fourier transform in the displacement `x - y` of the kernel. This
symbol is smoothing (`TauCeti.Symbol.isSmoothing_ofKernel`), so it is a symbol of every order, and
it has compact spatial support (`TauCeti.Symbol.hasCompactSpatialSupport_ofKernel`). Its
quantization kernel is `K` again (`TauCeti.Symbol.quantizationKernel_ofKernel`), and conversely a
smoothing symbol whose quantization kernel has compact support is the symbol of that kernel
(`TauCeti.Symbol.ofKernel_quantizationKernel`).

In the pseudodifferential calculus the remainders of localization and patching are operators with
smooth kernels: compressing an operator by cutoffs with disjoint supports, cutting its kernel off
near the diagonal, or reading it in a second chart away from the diagonal. With the operators
`u ↦ ∫ K(x, y) u(y) dy` written as quantizations, such a remainder is absorbed into the full
symbol: `Op(a) u + ∫ K(·, y) u(y) dy = Op(a + r) u`, where `a + r` has the same order as `a`
and, for a classical symbol `a`, the same homogeneous terms, since `r` is classical with vanishing
terms (`TauCeti.ClassicalSymbol.ofIsSmoothing`). A kernel supported near the diagonal gives a
properly supported remainder (`TauCeti.Symbol.hasNearDiagonalKernel_ofKernel`).

## Main declarations

* `TauCeti.Symbol.ofKernel`: the symbol `r(x, ξ) = ∫ exp(-i ⟪x - y, ξ⟫) K(x, y) dy` of the
  integral operator with kernel `K`, a symbol of any order `m`.
* `TauCeti.Symbol.quantizeSchwartzValue_ofKernel`: `Op(r) u (x) = ∫ K(x, y) u(y) dy`, and
  `TauCeti.Symbol.eq_ofKernel_iff`: `r` is the only symbol with this property.
* `TauCeti.Symbol.isSmoothing_ofKernel` and `TauCeti.Symbol.hasCompactSpatialSupport_ofKernel`;
  `TauCeti.Symbol.hasNearDiagonalKernel_ofKernel` for kernels supported near the diagonal.
* `TauCeti.Symbol.quantizationKernel_ofKernel` and `TauCeti.Symbol.ofKernel_quantizationKernel`:
  the correspondence between smooth compactly supported kernels and smoothing symbols with
  compactly supported quantization kernels.

## The argument

Fix a smooth bump `ρ` on the frequencies with `∫ ρ(2πζ) dζ = 1`. The amplitude

`c(x, y, ξ) = ρ(ξ) exp(-i ⟪x - y, ξ⟫) K(x, y)`

vanishes at large frequencies, so it is an amplitude of every order, and it has proper input
support since `K` has compact support. In its quantization
`(2π)⁻ⁿ ∫∫ exp(i ⟪x - y, ξ⟫) c(x, y, ξ) u(y) dy dξ` the phases cancel, leaving
`(2π)⁻ⁿ ∫ ρ(ξ) dξ · ∫ K(x, y) u(y) dy = ∫ K(x, y) u(y) dy`. Its left symbol
(`TauCeti.Amplitude.leftSymbol`) is a symbol with this quantization, and computing it, the phases
cancel again and the integral of the shifted bump is `1`, leaving `r(x, ξ)`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1 (the
  operators of order `-∞`).
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I,
  (1.21)–(1.28).
-/

public section

noncomputable section

open MeasureTheory Real FourierTransform
open scoped ContDiff RealInnerProductSpace SchwartzMap

namespace TauCeti

namespace Symbol

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

/-! ### The amplitude of an integral operator -/

/-- A smooth bump on the frequencies, supported in the ball of radius `2`, with integral `1`. -/
private def frequencyBump (n : ℕ) : CoordinateSpace n → ℝ :=
  (⟨1, 2, one_pos, one_lt_two⟩ : ContDiffBump (0 : CoordinateSpace n)).normed volume

private theorem contDiff_frequencyBump : ContDiff ℝ ∞ (frequencyBump n) :=
  ContDiffBump.contDiff_normed _

private theorem integral_frequencyBump : ∫ ζ, frequencyBump n ζ = 1 :=
  ContDiffBump.integral_normed _

private theorem frequencyBump_eq_zero {ζ : CoordinateSpace n} (hζ : 2 ≤ ‖ζ‖) :
    frequencyBump n ζ = 0 := by
  refine Function.notMem_support.1 fun h ↦ ?_
  rw [frequencyBump, ContDiffBump.support_normed_eq, Metric.mem_ball, dist_zero_right] at h
  exact (lt_irrefl _ (h.trans_le hζ))

/-- The phases of the integral operator and of the amplitude cancel. -/
private theorem fourierChar_mul_fourierChar_mul_fourierChar (x y ξ θ : CoordinateSpace n) :
    (𝐞 ⟪θ, x⟫ : ℂ) * 𝐞 (-⟪y, θ⟫) * 𝐞 (-⟪x - y, ξ⟫) = 𝐞 (-⟪x - y, ξ - θ⟫) := by
  simp only [← Circle.coe_mul, ← AddChar.map_add_eq_mul]
  congr 2
  simp only [inner_sub_left, inner_sub_right, real_inner_comm θ]
  ring

/-- The Fourier transform at `θ` in the input position of the amplitude at the frequency `ξ`. -/
private theorem fourierChar_smul_fourier_eq {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    (g : CoordinateSpace n → G) (c : ℂ) (x ξ θ : CoordinateSpace n) :
    (𝐞 ⟪θ, x⟫ : ℂ) • 𝓕 (fun y ↦ (c * 𝐞 (-⟪x - y, ξ⟫)) • g y) θ =
      c • ∫ y, (𝐞 (-⟪x - y, ξ - θ⟫) : ℂ) • g y := by
  rw [Real.fourier_eq, ← integral_smul, ← integral_smul]
  refine integral_congr_ae (.of_forall fun y ↦ ?_)
  simp only [Circle.smul_def, smul_smul]
  congr 1
  rw [← fourierChar_mul_fourierChar_mul_fourierChar x y ξ θ]
  ring

private theorem inv_two_pi_smul_add_two_pi_smul (ξ θ : CoordinateSpace n) :
    (2 * π)⁻¹ • (ξ + (2 * π) • θ) = (2 * π)⁻¹ • ξ + θ := by
  rw [smul_add, smul_smul, inv_mul_cancel₀ two_pi_pos.ne', one_smul]

/-- The coefficient `ρ(ξ) exp(-i ⟪x - y, ξ⟫) K(x, y)` of the amplitude of the integral operator
with kernel `K`, with `ρ(ξ) = frequencyBump n ((2π)⁻¹ ξ)`. -/
private def kernelAmplitudeCoeff (K : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W)
    (p : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n) : V →L[ℂ] W :=
  ((frequencyBump n ((2 * π)⁻¹ • p.2.2) : ℂ) * 𝐞 (-⟪p.1 - p.2.1, (2 * π)⁻¹ • p.2.2⟫)) •
    K (p.1, p.2.1)

private theorem contDiff_kernelAmplitudeCoeff
    {K : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W} (hK : ContDiff ℝ ∞ K) :
    ContDiff ℝ ∞ (kernelAmplitudeCoeff K) := by
  have hξ : ContDiff ℝ ∞ fun p : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n ↦
      (2 * π)⁻¹ • p.2.2 :=
    contDiff_snd.snd.const_smul _
  have hρ : ContDiff ℝ ∞ fun p : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n ↦
      (frequencyBump n ((2 * π)⁻¹ • p.2.2) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_frequencyBump.comp hξ)
  have hphase : ContDiff ℝ ∞ fun p : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n ↦
      -⟪p.1 - p.2.1, (2 * π)⁻¹ • p.2.2⟫ :=
    ((contDiff_fst.sub contDiff_snd.fst).inner ℝ hξ).neg
  have hK' : ContDiff ℝ ∞ fun p : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n ↦
      K (p.1, p.2.1) :=
    hK.comp (contDiff_fst.prodMk contDiff_snd.fst)
  exact (hρ.mul hphase.fourierChar).smul hK'

/-- The amplitude `ρ(ξ) exp(-i ⟪x - y, ξ⟫) K(x, y)` of the integral operator with kernel `K`, of
every order, since it vanishes at large frequencies. -/
private def kernelAmplitude (K : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W)
    (hK : ContDiff ℝ ∞ K) : Amplitude n V W m :=
  Amplitude.ofBoundedFrequencySupport (kernelAmplitudeCoeff K) (contDiff_kernelAmplitudeCoeff hK)
    (4 * π) fun x y ξ hξ ↦ by
      have h : 2 ≤ ‖(2 * π)⁻¹ • ξ‖ := by
        rw [norm_smul, norm_inv, Real.norm_of_nonneg two_pi_pos.le,
          le_inv_mul_iff₀ two_pi_pos]
        linarith
      simp only [kernelAmplitudeCoeff, frequencyBump_eq_zero h, Complex.ofReal_zero, zero_mul,
        zero_smul]

private theorem coefficient_kernelAmplitude
    (K : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W) (hK : ContDiff ℝ ∞ K) :
    (kernelAmplitude (m := m) K hK).coefficient = kernelAmplitudeCoeff K :=
  Amplitude.coefficient_ofBoundedFrequencySupport _ _ _ _

private theorem hasProperInputSupport_kernelAmplitude
    {K : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W} (hK : ContDiff ℝ ∞ K)
    (hKc : HasCompactSupport K) : (kernelAmplitude (m := m) K hK).HasProperInputSupport :=
  Amplitude.hasProperInputSupport_iff.2 fun _ _ ↦
    ⟨Prod.snd '' tsupport K, hKc.isCompact.image continuous_snd, fun x _ y hy ξ ↦ by
      rw [coefficient_kernelAmplitude, kernelAmplitudeCoeff,
        image_eq_zero_of_notMem_tsupport fun h ↦ hy ⟨(x, y), h, rfl⟩, smul_zero]⟩

variable [CompleteSpace W]

/-- The left symbol of the amplitude of the integral operator with kernel `K` is
`r(x, ξ) = ∫ exp(-i ⟪x - y, ξ⟫) K(x, y) dy`. -/
private theorem coefficient_leftSymbol_kernelAmplitude
    {K : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W} (hK : ContDiff ℝ ∞ K)
    (hKc : HasCompactSupport K) :
    ((kernelAmplitude (m := m) K hK).leftSymbol
        (hasProperInputSupport_kernelAmplitude hK hKc)).coefficient =
      fun p ↦ ∫ y, (𝐞 (-⟪p.1 - y, (2 * π)⁻¹ • p.2⟫) : ℂ) • K (p.1, y) := by
  funext ⟨x, ξ⟩
  rw [Amplitude.coefficient_leftSymbol, coefficient_kernelAmplitude]
  simp only [kernelAmplitudeCoeff, inv_two_pi_smul_add_two_pi_smul]
  refine (integral_congr_ae (.of_forall fun θ ↦
    fourierChar_smul_fourier_eq (fun y ↦ K (x, y)) _ x _ θ)).trans ?_
  simp only [add_sub_cancel_right, Complex.coe_smul]
  rw [integral_smul_const, integral_add_left_eq_self, integral_frequencyBump, one_smul]

/-! ### The symbol of an integral operator -/

/-- **The symbol of an integral operator with a smooth compactly supported kernel.** For a smooth
compactly supported `K(x, y)`, the symbol

`r(x, ξ) = ∫ exp(-i ⟪x - y, ξ⟫) K(x, y) dy`,

of any order `m`, whose quantization is the integral operator `u ↦ ∫ K(x, y) u(y) dy`
(`TauCeti.Symbol.quantizeSchwartzValue_ofKernel`). It is smoothing
(`TauCeti.Symbol.isSmoothing_ofKernel`). -/
def ofKernel (K : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W) (hK : ContDiff ℝ ∞ K)
    (hKc : HasCompactSupport K) : Symbol n V W m where
  coefficient p := ∫ y, (𝐞 (-⟪p.1 - y, (2 * π)⁻¹ • p.2⟫) : ℂ) • K (p.1, y)
  contDiff_coefficient := by
    rw [← coefficient_leftSymbol_kernelAmplitude (m := m) hK hKc]
    exact Symbol.contDiff_coefficient _
  exists_bound := by
    rw [← coefficient_leftSymbol_kernelAmplitude (m := m) hK hKc]
    exact Symbol.exists_bound _

variable {K : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W} (hK : ContDiff ℝ ∞ K)
  (hKc : HasCompactSupport K)

@[simp]
theorem coefficient_ofKernel (x ξ : CoordinateSpace n) :
    (ofKernel (m := m) K hK hKc).coefficient (x, ξ) =
      ∫ y, (𝐞 (-⟪x - y, (2 * π)⁻¹ • ξ⟫) : ℂ) • K (x, y) :=
  (rfl)

/-- The symbol of an integral operator with a smooth compactly supported kernel is smoothing. -/
theorem isSmoothing_ofKernel : (ofKernel (m := m) K hK hKc).IsSmoothing :=
  isSmoothing_iff.2 fun _ ↦ ⟨ofKernel K hK hKc, rfl⟩

/-- The symbol of an integral operator with a compactly supported kernel has compact spatial
support. -/
theorem hasCompactSpatialSupport_ofKernel :
    (ofKernel (m := m) K hK hKc).HasCompactSpatialSupport :=
  hasCompactSpatialSupport_iff.2 ⟨Prod.fst '' tsupport K, hKc.isCompact.image continuous_fst,
    fun x hx ξ ↦ by simp [image_eq_zero_of_notMem_tsupport fun h ↦ hx ⟨(x, _), h, rfl⟩]⟩

omit [CompleteSpace W] hK hKc in
/-- The integrand `y ↦ exp(-i ⟪x - y, ξ⟫) K(x, y)` of the symbol is integrable. -/
private theorem integrable_fourierChar_smul (hK : ContDiff ℝ ∞ K) (hKc : HasCompactSupport K)
    (x ξ : CoordinateSpace n) :
    Integrable fun y ↦ (𝐞 (-⟪x - y, (2 * π)⁻¹ • ξ⟫) : ℂ) • K (x, y) := by
  refine Continuous.integrable_of_hasCompactSupport (by fun_prop) <|
    HasCompactSupport.intro (hKc.isCompact.image continuous_snd) fun y hy ↦ ?_
  rw [image_eq_zero_of_notMem_tsupport fun h ↦ hy ⟨(x, y), h, rfl⟩, smul_zero]

omit hK hKc in
@[simp]
theorem ofKernel_zero :
    ofKernel (m := m) (0 : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W) contDiff_const
      HasCompactSupport.zero = 0 := by
  ext1
  funext ⟨x, ξ⟩
  simp

omit hK hKc in
@[simp]
theorem ofKernel_add {K₁ K₂ : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W}
    (hK₁ : ContDiff ℝ ∞ K₁) (hK₁c : HasCompactSupport K₁) (hK₂ : ContDiff ℝ ∞ K₂)
    (hK₂c : HasCompactSupport K₂) :
    ofKernel (m := m) (K₁ + K₂) (hK₁.add hK₂) (hK₁c.add hK₂c) =
      ofKernel K₁ hK₁ hK₁c + ofKernel K₂ hK₂ hK₂c := by
  ext1
  funext ⟨x, ξ⟩
  simp only [coefficient_ofKernel, coefficient_add, Pi.add_apply, smul_add]
  exact integral_add (integrable_fourierChar_smul hK₁ hK₁c x ξ)
    (integrable_fourierChar_smul hK₂ hK₂c x ξ)

@[simp]
theorem ofKernel_smul (c : ℂ) :
    ofKernel (m := m) (c • K) (contDiff_const.smul hK) hKc.smul_left =
      c • ofKernel K hK hKc := by
  ext1
  funext ⟨x, ξ⟩
  simp only [coefficient_ofKernel, coefficient_smul, Pi.smul_apply, smul_comm _ c]
  exact integral_smul c _

variable [CompleteSpace V]

/-- **The quantization of the symbol of an integral operator** is the integral operator:
`Op(r) u (x) = ∫ K(x, y) u(y) dy`. -/
theorem quantizeSchwartzValue_ofKernel (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeSchwartzValue (ofKernel (m := m) K hK hKc).coefficient u x = ∫ y, K (x, y) (u y) := by
  have hc : (ofKernel (m := m) K hK hKc).coefficient = ((kernelAmplitude (m := m) K hK).leftSymbol
      (hasProperInputSupport_kernelAmplitude hK hKc)).coefficient :=
    (coefficient_leftSymbol_kernelAmplitude hK hKc).symm
  rw [hc, Amplitude.quantizeSchwartzValue_leftSymbol, quantizeAmplitudeValue_def,
    coefficient_kernelAmplitude]
  simp only [kernelAmplitudeCoeff, smul_smul, inv_mul_cancel₀ two_pi_pos.ne', one_smul,
    smul_apply]
  refine (integral_congr_ae (.of_forall fun ζ ↦
    fourierChar_smul_fourier_eq (fun y ↦ K (x, y) (u y)) _ x _ ζ)).trans ?_
  simp only [sub_self, inner_zero_right, neg_zero, AddChar.map_zero_eq_one, Circle.coe_one,
    one_smul, Complex.coe_smul]
  rw [integral_smul_const, integral_frequencyBump, one_smul]

/-- **Kernels supported near the diagonal.** If `K(x, y) = 0` whenever `x` and `y` are at distance
at least `R`, the symbol of the integral operator with kernel `K` has a kernel supported within
distance `R` of the diagonal, so its quantization is properly supported. -/
theorem hasNearDiagonalKernel_ofKernel {R : ℝ} (hR : ∀ x y, R ≤ dist x y → K (x, y) = 0) :
    (ofKernel (m := m) K hK hKc).HasNearDiagonalKernel R := by
  refine hasNearDiagonalKernel_iff.2 fun u x hu ↦ ?_
  rw [quantizeSchwartzValue_ofKernel, ← integral_zero (CoordinateSpace n) W]
  refine integral_congr_ae (.of_forall fun y ↦ ?_)
  by_cases hy : y ∈ Metric.ball x R
  · simp [hu y hy]
  · simp [hR x y (by simpa [dist_comm] using hy)]

/-- **The symbol of an integral operator is determined by its quantization**: a symbol of order `m`
quantizes to `u ↦ ∫ K(x, y) u(y) dy` exactly when it is `TauCeti.Symbol.ofKernel`. -/
theorem eq_ofKernel_iff {a : Symbol n V W m} :
    a = ofKernel K hK hKc ↔
      ∀ (u : 𝓢(CoordinateSpace n, V)) x, quantizeSchwartzValue a.coefficient u x =
        ∫ y, K (x, y) (u y) := by
  refine ⟨fun h u x ↦ h ▸ quantizeSchwartzValue_ofKernel hK hKc u x, fun h ↦ ?_⟩
  exact Symbol.ext (coefficient_eq_of_forall_quantizeSchwartzValue_eq fun u _ ↦
    funext fun x ↦ (h u x).trans (quantizeSchwartzValue_ofKernel hK hKc u x).symm)

/-- The quantization kernel of the symbol of an integral operator is its kernel. -/
@[simp]
theorem quantizationKernel_ofKernel (x y : CoordinateSpace n) :
    quantizationKernel (ofKernel (m := m) K hK hKc).coefficient x y = K (x, y) :=
  (congrFun (eq_quantizationKernel_of_forall (hK.continuous.comp (by fun_prop))
    ((isSmoothing_ofKernel hK hKc).integrable_coefficient x)
    (quantizeSchwartzValue_ofKernel hK hKc · x)) y).symm

/-- **Smoothing symbols with compactly supported kernels.** A smoothing symbol whose quantization
kernel `K_a` has compact support is the symbol `TauCeti.Symbol.ofKernel` of the integral operator
with kernel `K_a`. -/
theorem ofKernel_quantizationKernel {a : Symbol n V W m} (ha : a.IsSmoothing)
    (hac : HasCompactSupport (Function.uncurry (quantizationKernel a.coefficient))) :
    ofKernel _ ha.contDiff_quantizationKernel hac = a := by
  refine ((eq_ofKernel_iff _ _).2 fun u x ↦ ?_).symm
  exact quantizeSchwartzValue_eq_integral_quantizationKernel (ha.integrable_coefficient x) u

end Symbol

end TauCeti
