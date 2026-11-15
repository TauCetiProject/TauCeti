/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Amplitude.Basic
public import TauCeti.Analysis.Pseudodifferential.OutputSupport
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Convolution
import TauCeti.Analysis.Calculus.CoordinateDeriv.ParametricIntegral
import TauCeti.Analysis.Fourier.Parametric
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre

/-!
# The reduction of an amplitude to its left symbol

An amplitude `a(x, y, ξ)` with compact support in the input position `y`
(`TauCeti.Amplitude.HasCompactInputSupport`) is a left quantization. Its *left symbol*

`c(x, ξ) = ∫ exp(2πi ⟪θ, x⟫) â(x, θ, ξ + 2πθ) dθ`,

where `â(x, θ, ξ)` is the Fourier transform (with Mathlib's phase `exp(-2πi ⟪y, θ⟫)`) of the input
slice `y ↦ a(x, y, ξ)`, is a symbol of order `m`, and its quantization is the quantization of the
amplitude on Schwartz functions. In angular frequency,
`c(x, ξ) = (2π)⁻ⁿ ∫∫ exp(i ⟪x - y, η - ξ⟫) a(x, y, η) dy dη`.

## Main declarations

* `TauCeti.Amplitude.leftIntegrand`: the integrand `exp(2πi ⟪θ, x⟫) â(x, θ, ξ + sθ)` of the left
  symbol, with the frequency shift scaled by a parameter `s`, and its bound
  `TauCeti.Amplitude.HasCompactInputSupport.exists_norm_leftIntegrand_le`, uniform for bounded `s`.
* `TauCeti.Amplitude.leftSymbol`: the left symbol, with its formula
  `TauCeti.Amplitude.coefficient_leftSymbol` and its derivatives
  `TauCeti.Amplitude.spatialDeriv_leftSymbol` (`∂_{x_j} c` is the left symbol of
  `∂_{x_j} a + ∂_{y_j} a`) and `TauCeti.Amplitude.frequencyDeriv_leftSymbol`.
* `TauCeti.Amplitude.quantizeSchwartzValue_leftSymbol`: the reduction `Op(c) = Op(a)`, and
  `TauCeti.Amplitude.coefficient_eq_coefficient_leftSymbol_of_forall_quantizeSchwartzValue_eq`:
  `c` is the only symbol with this property.
* `TauCeti.Amplitude.leftSymbol_ofRight_ofSpatial`: the right quantization of multiplication by a
  compactly supported `f(y)` has left symbol `f(x)`.

## Proof outline

Compact input support gives the rapid decay of `â` in `θ`, and Peetre's inequality
`⟨ξ + 2πθ⟩^m ≤ C ⟨ξ⟩^m ⟨θ⟩^|m|` then bounds the integrand of `c` by `C ⟨ξ⟩^m ⟨θ⟩^(-(n + 1))`,
locally uniformly in `x`. Differentiating under the integral sign, `∂_{ξ_j} c` is the left symbol
of `∂_{ξ_j} a`; the derivative of the phase `exp(2πi ⟪θ, x⟫)` in `x_j` multiplies `â` by
`2πi θⱼ`, which gives the Fourier transform of `∂_{y_j} a`, so `∂_{x_j} c` is the left symbol of
`∂_{x_j} a + ∂_{y_j} a`. Smoothness and the symbol estimates follow by induction on the number of
derivatives. The identity `Op(c) = Op(a)` follows from the convolution formula
`𝓕(a(x, ·, η) u)(ζ) = ∫ â(x, ζ - ζ', η) û(ζ') dζ'`, Fubini's theorem for an integrand dominated by
a convolution of integrable functions, and the change of frequency `ζ = ζ' + θ`. The construction
parallels that of the adjoint symbol `TauCeti.Symbol.adjoint`: the formal adjoint of the
quantization of a symbol `b(x, ξ)` is the right quantization of the pointwise adjoint `b(y, ξ)†`.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I,
  (1.21)–(1.28).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

open MeasureTheory Real FourierTransform
open scoped ContDiff RealInnerProductSpace SchwartzMap Topology

namespace TauCeti

variable {n : ℕ}

namespace Amplitude

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

/-- Differentiation of `â(x, θ, ξ)` in the output position and the frequency under the integral
sign. -/
theorem HasCompactInputSupport.hasFDerivAt_fourier_slice {a : Amplitude n V W m}
    (ha : a.HasCompactInputSupport) (θ : CoordinateSpace n)
    (q : CoordinateSpace n × CoordinateSpace n) :
    HasFDerivAt (fun q : CoordinateSpace n × CoordinateSpace n ↦
        𝓕 (fun y ↦ a.coefficient (q.1, y, q.2)) θ)
      (∫ y, (𝐞 (-⟪y, θ⟫) : ℂ) • fderiv ℝ (fun q : CoordinateSpace n × CoordinateSpace n ↦
        a.coefficient (q.1, y, q.2)) q) q := by
  obtain ⟨L, hL, hLa⟩ := hasCompactInputSupport_iff.mp ha
  simpa only [Real.fourier_eq, Circle.smul_def] using hasFDerivAt_integral_fourierChar_smul
    (g := fun r : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n ↦
      a.coefficient (r.2.1, r.1, r.2.2))
    ((a.contDiff_coefficient.comp (by fun_prop)).of_le (by simp)) hL
    (fun y hy q ↦ hLa q.1 y hy q.2) θ q

/-- The derivative of `â(x, θ, ξ)` in the direction `v` of output positions and frequencies is the
Fourier transform of the directional derivative of `a` in the direction `(v.1, 0, v.2)`. -/
theorem HasCompactInputSupport.fderiv_fourier_slice_apply {a : Amplitude n V W m}
    (ha : a.HasCompactInputSupport) (θ : CoordinateSpace n)
    (q v : CoordinateSpace n × CoordinateSpace n) :
    (∫ y, (𝐞 (-⟪y, θ⟫) : ℂ) • fderiv ℝ (fun q : CoordinateSpace n × CoordinateSpace n ↦
        a.coefficient (q.1, y, q.2)) q) v =
      𝓕 (fun y ↦ fderiv ℝ a.coefficient (q.1, y, q.2) (v.1, 0, v.2)) θ := by
  obtain ⟨L, hL, hLa⟩ := hasCompactInputSupport_iff.mp ha
  have h := integral_fourierChar_smul_fderiv_apply
    (g := fun r : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n ↦
      a.coefficient (r.2.1, r.1, r.2.2))
    ((a.contDiff_coefficient.comp (by fun_prop)).of_le (by simp)) hL
    (fun y hy q ↦ hLa q.1 y hy q.2) θ q v
  refine h.trans ?_
  rw [Real.fourier_eq]
  refine integral_congr_ae (.of_forall fun y ↦ ?_)
  -- The slice `q ↦ a(q.1, y, q.2)` is `a` composed with an affine map with linear part
  -- `w ↦ (w.1, 0, w.2)`.
  have hφ : HasFDerivAt (fun q : CoordinateSpace n × CoordinateSpace n ↦ (q.1, y, q.2))
      ((ContinuousLinearMap.fst ℝ (CoordinateSpace n) (CoordinateSpace n)).prod
        ((0 : CoordinateSpace n × CoordinateSpace n →L[ℝ] CoordinateSpace n).prod
          (ContinuousLinearMap.snd ℝ (CoordinateSpace n) (CoordinateSpace n)))) q :=
    hasFDerivAt_fst.prodMk ((hasFDerivAt_const (𝕜 := ℝ) y q).prodMk hasFDerivAt_snd)
  have hd := ((a.contDiff_coefficient.differentiable (by simp) _).hasFDerivAt.comp q hφ)
  simp only [Function.comp_def] at hd
  simp only [hd.fderiv, Circle.smul_def]
  rfl

/-! ### The left symbol -/

/-- The integrand `exp(2πi ⟪θ, x⟫) â(x, θ, ξ + sθ)` of the left symbol of an amplitude, with the
frequency shift `2πθ` scaled to `sθ`, where `â(x, θ, ξ)` is the Fourier transform of the input
slice `y ↦ a(x, y, ξ)` at `θ`. The integrand of the left symbol is the case `s = 2π`, and the
cases `s = 2πt` with `t ∈ [0, 1]` interpolate between the restriction `a(x, x, ξ)` of `a` to the
diagonal and the left symbol (`TauCeti.Amplitude.leftSymbol_eq_sum_leftTerm_add_leftRemainder`). -/
def leftIntegrand (a : Amplitude n V W m) (s : ℝ) (p : CoordinateSpace n × CoordinateSpace n)
    (θ : CoordinateSpace n) : V →L[ℂ] W :=
  (𝐞 ⟪θ, p.1⟫ : ℂ) • 𝓕 (fun y ↦ a.coefficient (p.1, y, p.2 + s • θ)) θ

theorem leftIntegrand_apply (a : Amplitude n V W m) (s : ℝ)
    (p : CoordinateSpace n × CoordinateSpace n) (θ : CoordinateSpace n) :
    leftIntegrand a s p θ = (𝐞 ⟪θ, p.1⟫ : ℂ) • 𝓕 (fun y ↦ a.coefficient (p.1, y, p.2 + s • θ)) θ :=
  (rfl)

/-- The integrand of the left symbol is continuous in the integration variable. -/
theorem HasCompactInputSupport.continuous_leftIntegrand {a : Amplitude n V W m}
    (ha : a.HasCompactInputSupport) (s : ℝ) (p : CoordinateSpace n × CoordinateSpace n) :
    Continuous (leftIntegrand a s p) := by
  have h₁ : Continuous fun θ : CoordinateSpace n ↦ (𝐞 ⟪θ, p.1⟫ : ℂ) :=
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))
  have h₂ : Continuous fun θ ↦ 𝓕 (fun y ↦ a.coefficient (p.1, y, p.2 + s • θ)) θ :=
    ha.continuous_fourier_slice.comp (f := fun θ : CoordinateSpace n ↦
      (θ, p.1, p.2 + s • θ)) (by fun_prop)
  unfold leftIntegrand
  exact h₁.smul h₂

/-- Peetre's inequality and the rapid decay of `â` bound the integrand of the left symbol by
`C ⟨ξ⟩ ^ m ⟨θ⟩ ^ (-(n + 1))`, uniformly for scales `|s| ≤ R` and output positions in a compact
set. -/
theorem HasCompactInputSupport.exists_norm_leftIntegrand_le {a : Amplitude n V W m}
    (ha : a.HasCompactInputSupport) {K : Set (CoordinateSpace n)} (hK : IsCompact K) {R : ℝ}
    (hR : 1 ≤ R) :
    ∃ C, 0 ≤ C ∧ ∀ s : ℝ, |s| ≤ R → ∀ x ∈ K, ∀ ξ θ, ‖leftIntegrand a s (x, ξ) θ‖ ≤
      C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) * (1 + ‖θ‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) := by
  obtain ⟨C, hC0, hC⟩ := ha.exists_norm_fourier_slice_le hK (|m| + (n + 1))
  refine ⟨C * 2 ^ (|m| / 2) * R ^ |m|, by positivity, fun s hs x hx ξ θ ↦ ?_⟩
  have hpeetre := one_add_norm_add_sq_rpow_le_mul m ξ (s • θ)
  have hscale := one_add_norm_smul_sq_rpow_le hR |m| θ
  rw [abs_abs] at hscale
  have hsθ : (1 + ‖s • θ‖ ^ 2) ^ (|m| / 2) ≤ (1 + ‖R • θ‖ ^ 2) ^ (|m| / 2) := by
    have h : ‖s • θ‖ ≤ ‖R • θ‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_of_nonneg (by linarith)]
      gcongr
    gcongr
  have hθ : (1 + ‖θ‖ ^ 2) ^ (|m| / 2) * (1 + ‖θ‖ ^ 2) ^ (-(|m| + (n + 1)) / 2) =
      (1 + ‖θ‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) := by
    rw [← Real.rpow_add (by positivity)]
    ring_nf
  rw [leftIntegrand, norm_smul, Circle.norm_coe, one_mul]
  calc ‖𝓕 (fun y ↦ a.coefficient (x, y, ξ + s • θ)) θ‖
      ≤ C * (1 + ‖ξ + s • θ‖ ^ 2) ^ (m / 2) * (1 + ‖θ‖ ^ 2) ^ (-(|m| + (n + 1)) / 2) :=
        hC x hx θ _
    _ ≤ C * (2 ^ (|m| / 2) * (1 + ‖ξ‖ ^ 2) ^ (m / 2) *
          (R ^ |m| * (1 + ‖θ‖ ^ 2) ^ (|m| / 2))) *
          (1 + ‖θ‖ ^ 2) ^ (-(|m| + (n + 1)) / 2) := by
        gcongr
        exact hpeetre.trans (by gcongr; exact hsθ.trans hscale)
    _ = C * 2 ^ (|m| / 2) * R ^ |m| * (1 + ‖ξ‖ ^ 2) ^ (m / 2) *
          ((1 + ‖θ‖ ^ 2) ^ (|m| / 2) * (1 + ‖θ‖ ^ 2) ^ (-(|m| + (n + 1)) / 2)) := by ring
    _ = _ := by rw [hθ]

/-- The bound `exists_norm_leftIntegrand_le` at the scale `s = 2π` of the left symbol. -/
private theorem HasCompactInputSupport.exists_norm_leftIntegrand_two_pi_le
    {a : Amplitude n V W m} (ha : a.HasCompactInputSupport) {K : Set (CoordinateSpace n)}
    (hK : IsCompact K) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ θ, ‖leftIntegrand a (2 * π) (x, ξ) θ‖ ≤
      C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) * (1 + ‖θ‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) := by
  obtain ⟨C, hC0, hC⟩ := ha.exists_norm_leftIntegrand_le hK (R := 2 * π)
    (by linarith [Real.two_le_pi])
  exact ⟨C, hC0, hC _ (abs_of_pos Real.two_pi_pos).le⟩

/-- The integrand of the left symbol is integrable in the integration variable. -/
theorem HasCompactInputSupport.integrable_leftIntegrand {a : Amplitude n V W m}
    (ha : a.HasCompactInputSupport) (s : ℝ) (p : CoordinateSpace n × CoordinateSpace n) :
    Integrable (leftIntegrand a s p) := by
  obtain ⟨C, -, hC⟩ := ha.exists_norm_leftIntegrand_le (isCompact_singleton (x := p.1))
    (le_max_left 1 |s|)
  exact ((integrable_rpow_neg_one_add_norm_sq (by simp)).const_mul
    (C * (1 + ‖p.2‖ ^ 2) ^ (m / 2))).mono'
    (ha.continuous_leftIntegrand s p).aestronglyMeasurable
    (.of_forall fun θ ↦ hC s (le_max_right 1 |s|) p.1 rfl p.2 θ)

private theorem HasCompactInputSupport.differentiableAt_leftIntegrand {a : Amplitude n V W m}
    (ha : a.HasCompactInputSupport) (θ : CoordinateSpace n)
    (p : CoordinateSpace n × CoordinateSpace n) :
    DifferentiableAt ℝ (fun p ↦ leftIntegrand a (2 * π) p θ) p := by
  have hc : DifferentiableAt ℝ (fun p : CoordinateSpace n × CoordinateSpace n ↦
      (𝐞 ⟪θ, p.1⟫ : ℂ)) p :=
    (Real.differentiable_fourierChar _).comp p
      ((differentiableAt_const θ).inner ℝ differentiableAt_fst)
  have hF : DifferentiableAt ℝ (fun p : CoordinateSpace n × CoordinateSpace n ↦
      𝓕 (fun y ↦ a.coefficient (p.1, y, p.2 + (2 * π) • θ)) θ) p :=
    (ha.hasFDerivAt_fourier_slice θ _).differentiableAt.comp p
      (f := fun p : CoordinateSpace n × CoordinateSpace n ↦ (p.1, p.2 + (2 * π) • θ))
      (by fun_prop)
  exact hc.smul hF

/-- The derivative of the integrand in the output position `x_j` is the sum of the integrands of
`∂_{x_j} a` and `∂_{y_j} a`: the derivative of the phase `exp(2πi ⟪θ, x⟫)` is
`2πi θⱼ`, and `2πi θⱼ â` is the Fourier transform of `∂_{y_j} a`. -/
private theorem HasCompactInputSupport.coordinateDeriv_leftIntegrand_fst
    {a : Amplitude n V W m} (ha : a.HasCompactInputSupport) (j : Fin n)
    (θ x ξ : CoordinateSpace n) :
    coordinateDeriv [j] (fun x ↦ leftIntegrand a (2 * π) (x, ξ) θ) x =
      leftIntegrand (Amplitude.spatialDerivFst j a) (2 * π) (x, ξ) θ +
        leftIntegrand (Amplitude.spatialDerivSnd j a) (2 * π) (x, ξ) θ := by
  have hc : HasFDerivAt (fun x : CoordinateSpace n ↦ (𝐞 ⟪θ, x⟫ : ℂ))
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (2 * π * Complex.I * 𝐞 ⟪θ, x⟫)).comp
        (innerSL ℝ θ)) x :=
    (Real.hasDerivAt_fourierChar ⟪θ, x⟫).hasFDerivAt.comp x (innerSL ℝ θ).hasFDerivAt
  have hF := (ha.hasFDerivAt_fourier_slice θ (x, ξ + (2 * π) • θ)).comp x
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) x (ξ + (2 * π) • θ))
  have h : HasFDerivAt (fun x : CoordinateSpace n ↦ (𝐞 ⟪θ, x⟫ : ℂ) •
      𝓕 (fun y ↦ a.coefficient (x, y, ξ + (2 * π) • θ)) θ) _ x := hc.smul hF
  rw [coordinateDeriv_cons, coordinateDeriv_nil]
  simp only [leftIntegrand]
  rw [h.fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, one_apply_eq_self,
    ha.fderiv_fourier_slice_apply, ha.fourier_spatialDerivSnd_slice,
    EuclideanSpace.inner_single_right, one_mul, conj_trivial, Prod.mk_zero_zero, smul_smul,
    ← coefficient_spatialDerivFst]
  congr 2
  simp only [Complex.real_smul]
  ring

/-- The derivative of the integrand in the frequency `ξ_j` is the integrand of `∂_{ξ_j} a`. -/
private theorem HasCompactInputSupport.coordinateDeriv_leftIntegrand_snd
    {a : Amplitude n V W m} (ha : a.HasCompactInputSupport) (j : Fin n)
    (θ x ξ : CoordinateSpace n) :
    coordinateDeriv [j] (fun ξ ↦ leftIntegrand a (2 * π) (x, ξ) θ) ξ =
      leftIntegrand (Amplitude.frequencyDeriv j a) (2 * π) (x, ξ) θ := by
  have hF : HasFDerivAt (fun ξ : CoordinateSpace n ↦ (𝐞 ⟪θ, x⟫ : ℂ) •
      𝓕 (fun y ↦ a.coefficient (x, y, ξ + (2 * π) • θ)) θ) _ ξ :=
    (((ha.hasFDerivAt_fourier_slice θ (x, ξ + (2 * π) • θ)).comp ξ
      ((hasFDerivAt_prodMk_right (𝕜 := ℝ) x (ξ + (2 * π) • θ)).comp ξ
        ((hasFDerivAt_id ξ).add_const ((2 * π) • θ)))).const_smul (𝐞 ⟪θ, x⟫ : ℂ))
  rw [coordinateDeriv_cons, coordinateDeriv_nil]
  simp only [leftIntegrand]
  rw [hF.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply, ContinuousLinearMap.id_apply, ha.fderiv_fourier_slice_apply,
    ← coefficient_frequencyDeriv]


/-- The derivative of the integrand of the left symbol in the direction `v`. -/
private theorem HasCompactInputSupport.fderiv_leftIntegrand_apply {a : Amplitude n V W m}
    (ha : a.HasCompactInputSupport) (θ : CoordinateSpace n)
    (p v : CoordinateSpace n × CoordinateSpace n) :
    fderiv ℝ (fun p ↦ leftIntegrand a (2 * π) p θ) p v =
      ∑ j, v.1 j • (leftIntegrand (Amplitude.spatialDerivFst j a) (2 * π) p θ +
        leftIntegrand (Amplitude.spatialDerivSnd j a) (2 * π) p θ) +
      ∑ j, v.2 j • leftIntegrand (Amplitude.frequencyDeriv j a) (2 * π) p θ := by
  rw [fderiv_apply_eq_sum_coordinateDeriv (ha.differentiableAt_leftIntegrand θ p)]
  simp only [ha.coordinateDeriv_leftIntegrand_fst, ha.coordinateDeriv_leftIntegrand_snd]

/-- Near `p₀`, the integrand of the left symbol of an amplitude is dominated by one integrable
function of `θ`. -/
private theorem HasCompactInputSupport.exists_norm_leftIntegrand_le_of_mem_ball {s : ℝ}
    {b : Amplitude n V W s} (hb : b.HasCompactInputSupport)
    (p₀ : CoordinateSpace n × CoordinateSpace n) :
    ∃ C, 0 ≤ C ∧ ∀ θ, ∀ p ∈ Metric.ball p₀ 1,
      ‖leftIntegrand b (2 * π) p θ‖ ≤ C * (1 + ‖θ‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) := by
  obtain ⟨C, hC0, hC⟩ := hb.exists_norm_leftIntegrand_two_pi_le (isCompact_closedBall p₀.1 1)
  refine ⟨C * (2 ^ |s| * (1 + ‖p₀.2‖ ^ 2) ^ (s / 2)), by positivity, fun θ p hp ↦ ?_⟩
  have hp' : dist p p₀ < 1 := hp
  rw [Prod.dist_eq, max_lt_iff] at hp'
  have hw := one_add_norm_sq_rpow_le_of_norm_sub_le_one
    (dist_eq_norm p.2 p₀.2 ▸ hp'.2.le) s
  calc ‖leftIntegrand b (2 * π) p θ‖
      ≤ C * (1 + ‖p.2‖ ^ 2) ^ (s / 2) * (1 + ‖θ‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) :=
        hC p.1 (Metric.mem_closedBall.2 hp'.1.le) p.2 θ
    _ ≤ _ := by gcongr

/-- The coefficient `c(x, ξ) = ∫ exp(2πi ⟪θ, x⟫) â(x, θ, ξ + 2πθ) dθ` of the left symbol of an
amplitude. -/
private def leftCoeff (a : Amplitude n V W m) (p : CoordinateSpace n × CoordinateSpace n) :
    V →L[ℂ] W :=
  ∫ θ, leftIntegrand a (2 * π) p θ

/-- The coefficient of the left symbol is differentiable, with the derivative computed under the
integral sign. -/
private theorem HasCompactInputSupport.differentiableAt_leftCoeff_and_fderiv_apply
    {a : Amplitude n V W m} (ha : a.HasCompactInputSupport)
    (p₀ : CoordinateSpace n × CoordinateSpace n) :
    DifferentiableAt ℝ (leftCoeff a) p₀ ∧ ∀ v, fderiv ℝ (leftCoeff a) p₀ v =
      ∑ j, v.1 j • (∫ θ, (leftIntegrand (Amplitude.spatialDerivFst j a) (2 * π) p₀ θ +
        leftIntegrand (Amplitude.spatialDerivSnd j a) (2 * π) p₀ θ)) +
      ∑ j, v.2 j • ∫ θ, leftIntegrand (Amplitude.frequencyDeriv j a) (2 * π) p₀ θ := by
  have hb : ∀ {s : ℝ} {b : Fin n → Amplitude n V W s}, (∀ j, (b j).HasCompactInputSupport) →
      ∃ C : Fin n → ℝ, ∀ j θ, ∀ p ∈ Metric.ball p₀ 1,
        ‖leftIntegrand (b j) (2 * π) p θ‖ ≤ C j * (1 + ‖θ‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) := by
    intro s b hb
    have h := fun j ↦ (hb j).exists_norm_leftIntegrand_le_of_mem_ball p₀
    choose C _ hC using h
    exact ⟨C, hC⟩
  obtain ⟨Cx, hCx⟩ := hb fun j ↦ ha.spatialDerivFst j
  obtain ⟨Cy, hCy⟩ := hb fun j ↦ ha.spatialDerivSnd j
  obtain ⟨Cξ, hCξ⟩ := hb fun j ↦ ha.frequencyDeriv j
  refine differentiableAt_integral_and_fderiv_apply_eq_sum (E := V →L[ℂ] W)
    (F := leftIntegrand a (2 * π))
    (A := fun j p θ ↦ leftIntegrand (Amplitude.spatialDerivFst j a) (2 * π) p θ +
      leftIntegrand (Amplitude.spatialDerivSnd j a) (2 * π) p θ)
    (B := fun j p θ ↦ leftIntegrand (Amplitude.frequencyDeriv j a) (2 * π) p θ)
    (fun θ p ↦ ha.differentiableAt_leftIntegrand θ p)
    (fun θ p v ↦ ha.fderiv_leftIntegrand_apply θ p v)
    (ha.integrable_leftIntegrand (2 * π))
    (fun j p ↦ ((ha.spatialDerivFst j).continuous_leftIntegrand (2 * π) p).add
      ((ha.spatialDerivSnd j).continuous_leftIntegrand (2 * π) p))
    (fun j p ↦ (ha.frequencyDeriv j).continuous_leftIntegrand (2 * π) p)
    ((integrable_rpow_neg_one_add_norm_sq (r := n + 1) (by simp)).const_mul
      (∑ j, (Cx j + Cy j) + ∑ j, Cξ j)) p₀ fun θ p hp ↦ ?_
  rw [add_mul, Finset.sum_mul, Finset.sum_mul]
  exact add_le_add (Finset.sum_le_sum fun j _ ↦ (norm_add_le _ _).trans (by
      rw [add_mul]; exact add_le_add (hCx j θ p hp) (hCy j θ p hp)))
    (Finset.sum_le_sum fun j _ ↦ hCξ j θ p hp)

/-- The derivative `∂_{x_j} c` of the coefficient of the left symbol is the coefficient of the
left symbol of `∂_{x_j} a + ∂_{y_j} a`. -/
private theorem HasCompactInputSupport.coordinateDeriv_leftCoeff_fst {a : Amplitude n V W m}
    (ha : a.HasCompactInputSupport) (j : Fin n) (x ξ : CoordinateSpace n) :
    coordinateDeriv [j] (fun x ↦ leftCoeff a (x, ξ)) x =
      leftCoeff (Amplitude.spatialDerivFst j a) (x, ξ) +
        leftCoeff (Amplitude.spatialDerivSnd j a) (x, ξ) := by
  obtain ⟨hd, hf⟩ := ha.differentiableAt_leftCoeff_and_fderiv_apply (x, ξ)
  rw [coordinateDeriv_fst_eq_fderiv (f := leftCoeff a) (p := (x, ξ)) hd, hf]
  simp only [PiLp.ofLp_single, Pi.single_apply, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, PiLp.zero_apply, Finset.sum_const_zero,
    add_zero]
  exact integral_add ((ha.spatialDerivFst j).integrable_leftIntegrand (2 * π) _)
    ((ha.spatialDerivSnd j).integrable_leftIntegrand (2 * π) _)

/-- The derivative `∂_{ξ_j} c` of the coefficient of the left symbol is the coefficient of the
left symbol of `∂_{ξ_j} a`. -/
private theorem HasCompactInputSupport.coordinateDeriv_leftCoeff_snd {a : Amplitude n V W m}
    (ha : a.HasCompactInputSupport) (j : Fin n) (x ξ : CoordinateSpace n) :
    coordinateDeriv [j] (fun ξ ↦ leftCoeff a (x, ξ)) ξ =
      leftCoeff (Amplitude.frequencyDeriv j a) (x, ξ) := by
  obtain ⟨hd, hf⟩ := ha.differentiableAt_leftCoeff_and_fderiv_apply (x, ξ)
  rw [coordinateDeriv_snd_eq_fderiv (f := leftCoeff a) (p := (x, ξ)) hd, hf]
  simp only [PiLp.ofLp_single, Pi.single_apply, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, PiLp.zero_apply, Finset.sum_const_zero,
    zero_add]
  rfl

/-- The coefficient of the left symbol is smooth. -/
private theorem HasCompactInputSupport.contDiff_leftCoeff :
    ∀ (k : ℕ) {m : ℝ} {a : Amplitude n V W m}, a.HasCompactInputSupport →
      ContDiff ℝ k (leftCoeff a)
  | 0, _, _, ha => contDiff_zero.2 <| continuous_iff_continuousAt.2 fun p ↦
      (ha.differentiableAt_leftCoeff_and_fderiv_apply p).1.continuousAt
  | k + 1, _, a, ha => by
    rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_fderiv]
    refine ⟨fun p ↦ (ha.differentiableAt_leftCoeff_and_fderiv_apply p).1, by simp,
      contDiff_clm_apply_iff.2 fun v ↦ ?_⟩
    have h : (fun p ↦ fderiv ℝ (leftCoeff a) p v) = fun p ↦
        ∑ j, v.1 j • (leftCoeff (Amplitude.spatialDerivFst j a) p +
          leftCoeff (Amplitude.spatialDerivSnd j a) p) +
        ∑ j, v.2 j • leftCoeff (Amplitude.frequencyDeriv j a) p := funext fun p ↦ by
      rw [fderiv_apply_eq_sum_coordinateDeriv (ha.differentiableAt_leftCoeff_and_fderiv_apply p).1]
      simp only [ha.coordinateDeriv_leftCoeff_fst, ha.coordinateDeriv_leftCoeff_snd]
    rw [h]
    exact (ContDiff.sum fun j _ ↦ (((ha.spatialDerivFst j).contDiff_leftCoeff k).add
      ((ha.spatialDerivSnd j).contDiff_leftCoeff k)).const_smul _).add
      (ContDiff.sum fun j _ ↦ ((ha.frequencyDeriv j).contDiff_leftCoeff k).const_smul _)

/-- The coefficient of the left symbol grows at most like `⟨ξ⟩ ^ m`, uniformly for positions in
a compact set. -/
private theorem HasCompactInputSupport.exists_norm_leftCoeff_le {a : Amplitude n V W m}
    (ha : a.HasCompactInputSupport) {K : Set (CoordinateSpace n)} (hK : IsCompact K) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ, ‖leftCoeff a (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
  obtain ⟨C, hC0, hC⟩ := ha.exists_norm_leftIntegrand_two_pi_le hK
  set I := ∫ θ : CoordinateSpace n, (1 + ‖θ‖ ^ 2) ^ (-((n : ℝ) + 1) / 2)
  have hI : 0 ≤ I := integral_nonneg fun θ ↦ by positivity
  refine ⟨C * I, mul_nonneg hC0 hI, fun x hx ξ ↦ ?_⟩
  refine (norm_integral_le_of_norm_le ((integrable_rpow_neg_one_add_norm_sq (by simp)).const_mul
    (C * (1 + ‖ξ‖ ^ 2) ^ (m / 2))) (.of_forall fun θ ↦ hC x hx ξ θ)).trans_eq ?_
  rw [integral_const_mul]
  ring

/-- Frequency derivatives of the coefficient of the left symbol along a word `β` are the
coefficient of the left symbol of an amplitude of order `m - |β|` with compact input support. -/
private theorem HasCompactInputSupport.exists_coordinateDeriv_leftCoeff_snd :
    ∀ (β : List (Fin n)) {m : ℝ} {a : Amplitude n V W m}, a.HasCompactInputSupport →
      ∃ (m' : ℝ) (b : Amplitude n V W m'), m' = m - β.length ∧ b.HasCompactInputSupport ∧
        ∀ x, coordinateDeriv β (fun ξ ↦ leftCoeff a (x, ξ)) = fun ξ ↦ leftCoeff b (x, ξ)
  | [], m, a, ha => ⟨m, a, by simp, ha, fun _ ↦ coordinateDeriv_nil _⟩
  | j :: js, m, a, ha => by
    obtain ⟨m', b, hm', hb, hab⟩ :=
      HasCompactInputSupport.exists_coordinateDeriv_leftCoeff_snd js ha
    refine ⟨m' - 1, Amplitude.frequencyDeriv j b, by rw [hm']; simp; ring, hb.frequencyDeriv j,
      fun x ↦ ?_⟩
    rw [← List.singleton_append, coordinateDeriv_append, hab x]
    funext ξ
    exact hb.coordinateDeriv_leftCoeff_snd j x ξ

/-- Position derivatives of the coefficient of the left symbol grow at most like `⟨ξ⟩ ^ m`,
uniformly for positions in a compact set. -/
private theorem HasCompactInputSupport.exists_norm_coordinateDeriv_leftCoeff_le
    (α : List (Fin n)) : ∀ {m : ℝ} {a : Amplitude n V W m}, a.HasCompactInputSupport →
      ∀ {K : Set (CoordinateSpace n)}, IsCompact K → ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ,
        ‖coordinateDeriv α (fun x ↦ leftCoeff a (x, ξ)) x‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
  induction α using List.reverseRecOn with
  | nil => exact fun ha _ hK ↦ by simpa using ha.exists_norm_leftCoeff_le hK
  | append_singleton js j ih =>
    intro m a ha K hK
    obtain ⟨C₁, hC₁0, hC₁⟩ := ih (ha.spatialDerivFst j) hK
    obtain ⟨C₂, hC₂0, hC₂⟩ := ih (ha.spatialDerivSnd j) hK
    refine ⟨C₁ + C₂, add_nonneg hC₁0 hC₂0, fun x hx ξ ↦ ?_⟩
    have hs : ∀ {s : ℝ} {b : Amplitude n V W s}, b.HasCompactInputSupport →
        ContDiff ℝ js.length fun x ↦ leftCoeff b (x, ξ) := fun hb ↦
      (hb.contDiff_leftCoeff _).comp (contDiff_id.prodMk contDiff_const)
    have hsplit : coordinateDeriv [j] (fun x ↦ leftCoeff a (x, ξ)) =
        (fun x ↦ leftCoeff (Amplitude.spatialDerivFst j a) (x, ξ)) +
          fun x ↦ leftCoeff (Amplitude.spatialDerivSnd j a) (x, ξ) :=
      funext fun x ↦ ha.coordinateDeriv_leftCoeff_fst j x ξ
    rw [coordinateDeriv_append, hsplit,
      coordinateDeriv_add js (hs (ha.spatialDerivFst j)) (hs (ha.spatialDerivSnd j)),
      Pi.add_apply, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hC₁ x hx ξ) (hC₂ x hx ξ))

/-- **The left symbol of an amplitude.** For an amplitude `a` of order `m` with compact input
support, the symbol of order `m`

`c(x, ξ) = ∫ exp(2πi ⟪θ, x⟫) â(x, θ, ξ + 2πθ) dθ`,

where `â(x, θ, ξ)` is the Fourier transform of the input slice `y ↦ a(x, y, ξ)` at `θ`. Its
quantization is the quantization of the amplitude
(`TauCeti.Amplitude.quantizeSchwartzValue_leftSymbol`). -/
def leftSymbol (a : Amplitude n V W m) (ha : a.HasCompactInputSupport) : Symbol n V W m where
  coefficient := leftCoeff a
  contDiff_coefficient := contDiff_infty.2 fun k ↦ ha.contDiff_leftCoeff k
  exists_bound K hK α β := by
    obtain ⟨m', b, hm', hb, hab⟩ := ha.exists_coordinateDeriv_leftCoeff_snd β
    obtain ⟨C, hC0, hC⟩ := hb.exists_norm_coordinateDeriv_leftCoeff_le α hK
    refine ⟨C, hC0, fun x hx ξ ↦ ?_⟩
    rw [mixedDeriv_def]
    simp_rw [hab]
    rw [← hm']
    exact hC x hx ξ

@[simp]
theorem coefficient_leftSymbol (a : Amplitude n V W m) (ha : a.HasCompactInputSupport)
    (x ξ : CoordinateSpace n) :
    (a.leftSymbol ha).coefficient (x, ξ) =
      ∫ θ, (𝐞 ⟪θ, x⟫ : ℂ) • 𝓕 (fun y ↦ a.coefficient (x, y, ξ + (2 * π) • θ)) θ :=
  (rfl)

/-- Position derivatives of the left symbol: `∂_{x_j} c` is the left symbol of
`∂_{x_j} a + ∂_{y_j} a`. -/
theorem spatialDeriv_leftSymbol {a : Amplitude n V W m} (ha : a.HasCompactInputSupport)
    (j : Fin n) :
    Symbol.spatialDeriv j (a.leftSymbol ha) =
      (spatialDerivFst j a).leftSymbol (ha.spatialDerivFst j) +
        (spatialDerivSnd j a).leftSymbol (ha.spatialDerivSnd j) := by
  ext1
  funext ⟨x, ξ⟩
  rw [Symbol.coefficient_spatialDeriv, Symbol.coefficient_add, Pi.add_apply]
  exact ha.coordinateDeriv_leftCoeff_fst j x ξ

/-- Frequency derivatives of the left symbol: `∂_{ξ_j} c` is the left symbol of `∂_{ξ_j} a`. -/
theorem frequencyDeriv_leftSymbol {a : Amplitude n V W m} (ha : a.HasCompactInputSupport)
    (j : Fin n) :
    Symbol.frequencyDeriv j (a.leftSymbol ha) =
      (frequencyDeriv j a).leftSymbol (ha.frequencyDeriv j) := by
  ext1
  funext ⟨x, ξ⟩
  rw [Symbol.coefficient_frequencyDeriv]
  exact ha.coordinateDeriv_leftCoeff_snd j x ξ


/-! ### The quantization of the left symbol -/

/-- The Fourier transform of the product `y ↦ a(x, y, η) u(y)` is the convolution
`∫ â(x, ζ - ζ', η) û(ζ') dζ'` of the Fourier transforms. -/
private theorem HasCompactInputSupport.fourier_slice_apply [CompleteSpace V] [CompleteSpace W]
    {a : Amplitude n V W m} (ha : a.HasCompactInputSupport) (u : 𝓢(CoordinateSpace n, V))
    (x η ζ : CoordinateSpace n) :
    𝓕 (fun y ↦ a.coefficient (x, y, η) (u y)) ζ =
      ∫ ζ', 𝓕 (fun y ↦ a.coefficient (x, y, η)) (ζ - ζ') (𝓕 u ζ') := by
  have hf : ContDiff ℝ ∞ fun y ↦ a.coefficient (x, y, η) :=
    a.contDiff_coefficient.comp (by fun_prop)
  have hb := (Symbol.hasCompactSpatialSupport_ofSpatial_iff hf).2 (ha.hasCompactSupport_slice x η)
  have hc : (Symbol.ofSpatial _ hf).coefficient = fun p ↦ a.coefficient (x, p.1, η) :=
    funext (Symbol.coefficient_ofSpatial _ hf)
  have h := hb.fourier_quantizeSchwartzValue u ζ
  have hq : quantizeSchwartzValue (fun p ↦ a.coefficient (x, p.1, η)) u =
      fun y ↦ a.coefficient (x, y, η) (u y) :=
    funext (quantizeSchwartzValue_comp_fst (fun y ↦ a.coefficient (x, y, η)) u)
  rw [hc, hq] at h
  exact h

/-- The double integrand of the quantization of an amplitude, after inserting the convolution
formula for the Fourier transform of `y ↦ a(x, y, 2πζ) u(y)`, is integrable in both frequencies:
it is dominated by a convolution-type product `h(ζ') k(ζ - ζ')` of integrable functions. -/
private theorem HasCompactInputSupport.integrable_quantizeIntegrand {a : Amplitude n V W m}
    (ha : a.HasCompactInputSupport) (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    Integrable (fun q : CoordinateSpace n × CoordinateSpace n ↦ 𝐞 ⟪q.1, x⟫ •
      𝓕 (fun y ↦ a.coefficient (x, y, (2 * π) • q.1)) (q.1 - q.2) (𝓕 u q.2))
      (volume.prod volume) := by
  obtain ⟨C, -, hC⟩ := ha.exists_norm_leftIntegrand_two_pi_le (isCompact_singleton (x := x))
  have hh : Integrable fun ζ : CoordinateSpace n ↦ (1 + ‖(2 * π) • ζ‖ ^ 2) ^ (m / 2) * ‖𝓕 u ζ‖ :=
    (𝓕 u).integrable_one_add_norm_smul_sq_rpow_mul_norm (2 * π) m
  have hA : Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦
      𝓕 (fun y ↦ a.coefficient (x, y, (2 * π) • q.1)) (q.1 - q.2) :=
    ha.continuous_fourier_slice.comp (f := fun q : CoordinateSpace n × CoordinateSpace n ↦
      (q.1 - q.2, x, (2 * π) • q.1)) (by fun_prop)
  have hcont : Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦ 𝐞 ⟪q.1, x⟫ •
      𝓕 (fun y ↦ a.coefficient (x, y, (2 * π) • q.1)) (q.1 - q.2) (𝓕 u q.2) :=
    (Real.continuous_fourierChar.comp (by fun_prop)).smul
      (hA.clm_apply ((𝓕 u).continuous.comp continuous_snd))
  refine ((hh.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ)
    (integrable_rpow_neg_one_add_norm_sq (r := n + 1) (by simp))).const_mul C).mono'
    hcont.aestronglyMeasurable (.of_forall fun q ↦ ?_)
  have hξ : (2 * π) • q.1 = (2 * π) • q.2 + (2 * π) • (q.1 - q.2) := by
    rw [← smul_add, add_sub_cancel]
  have h := hC x rfl ((2 * π) • q.2) (q.1 - q.2)
  rw [leftIntegrand, norm_smul, Circle.norm_coe, one_mul, ← hξ] at h
  rw [Circle.norm_smul, ContinuousLinearMap.mul_apply']
  calc ‖𝓕 (fun y ↦ a.coefficient (x, y, (2 * π) • q.1)) (q.1 - q.2) (𝓕 u q.2)‖
      ≤ ‖𝓕 (fun y ↦ a.coefficient (x, y, (2 * π) • q.1)) (q.1 - q.2)‖ * ‖𝓕 u q.2‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ C * (1 + ‖(2 * π) • q.2‖ ^ 2) ^ (m / 2) *
          (1 + ‖q.1 - q.2‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) * ‖𝓕 u q.2‖ := by gcongr
    _ = _ := by ring

/-- **Reduction of an amplitude to its left symbol.** For an amplitude `a` with compact input
support, the quantization of the left symbol is the quantization of the amplitude: for every
Schwartz function `u`,

`Op(c) u (x) = (2π)⁻ⁿ ∫∫ exp(i ⟪x - y, ξ⟫) a(x, y, ξ) u(y) dy dξ`, with `c = a.leftSymbol ha`. -/
theorem quantizeSchwartzValue_leftSymbol [CompleteSpace V] [CompleteSpace W]
    {a : Amplitude n V W m} (ha : a.HasCompactInputSupport) (u : 𝓢(CoordinateSpace n, V))
    (x : CoordinateSpace n) :
    quantizeSchwartzValue (a.leftSymbol ha).coefficient u x =
      quantizeAmplitudeValue a.coefficient u x := by
  set G : CoordinateSpace n → CoordinateSpace n → W := fun ζ ζ' ↦ 𝐞 ⟪ζ, x⟫ •
    𝓕 (fun y ↦ a.coefficient (x, y, (2 * π) • ζ)) (ζ - ζ') (𝓕 u ζ') with hGdef
  have hG : Integrable (fun q : CoordinateSpace n × CoordinateSpace n ↦ G q.1 q.2)
      (volume.prod volume) := ha.integrable_quantizeIntegrand u x
  have hR : quantizeAmplitudeValue a.coefficient u x = ∫ ζ, ∫ ζ', G ζ ζ' := by
    rw [quantizeAmplitudeValue_def]
    refine integral_congr_ae (.of_forall fun ζ ↦ ?_)
    beta_reduce
    rw [ha.fourier_slice_apply u x ((2 * π) • ζ) ζ]
    simp only [hGdef, Circle.smul_def, integral_smul]
  rw [hR, integral_integral_swap hG, quantizeSchwartzValue_def]
  refine integral_congr_ae (.of_forall fun ζ' ↦ ?_)
  beta_reduce
  rw [← integral_add_right_eq_self (fun ζ ↦ G ζ ζ') ζ', coefficient_leftSymbol,
    ContinuousLinearMap.integral_apply, Circle.smul_def, ← integral_smul]
  swap
  · exact ha.integrable_leftIntegrand (2 * π) (x, (2 * π) • ζ')
  refine integral_congr_ae (.of_forall fun θ ↦ ?_)
  simp only [hGdef, add_sub_cancel_right, smul_add, smul_apply, Circle.smul_def,
    smul_smul, inner_add_left, AddChar.map_add_eq_mul, Circle.coe_mul]
  rw [add_comm ((2 * π) • θ), mul_comm]

/-- **Uniqueness of the left symbol.** A symbol, of any order, whose quantization agrees with that
of an amplitude with compact input support on compactly supported Schwartz functions has the
coefficient of the left symbol of the amplitude. -/
theorem coefficient_eq_coefficient_leftSymbol_of_forall_quantizeSchwartzValue_eq [CompleteSpace V]
    [CompleteSpace W] {a : Amplitude n V W m} (ha : a.HasCompactInputSupport) {m' : ℝ}
    {b : Symbol n V W m'}
    (h : ∀ u : 𝓢(CoordinateSpace n, V), HasCompactSupport u →
      quantizeSchwartzValue b.coefficient u = quantizeAmplitudeValue a.coefficient u) :
    b.coefficient = (a.leftSymbol ha).coefficient :=
  Symbol.coefficient_eq_of_forall_quantizeSchwartzValue_eq fun u hu ↦
    (h u hu).trans (funext fun x ↦ (quantizeSchwartzValue_leftSymbol ha u x).symm)


/-- The right quantization of multiplication by a compactly supported smooth `f` is
multiplication by `f`, so the left symbol of its amplitude `f(y)` is `f(x)`. -/
@[simp]
theorem leftSymbol_ofRight_ofSpatial [CompleteSpace V] [CompleteSpace W]
    {f : CoordinateSpace n → V →L[ℂ] W} (hf : ContDiff ℝ ∞ f) (hfs : HasCompactSupport f) :
    (ofRight (Symbol.ofSpatial f hf)).leftSymbol
        ((Symbol.hasCompactSpatialSupport_ofSpatial_iff hf).2 hfs).hasCompactInputSupport_ofRight =
      Symbol.ofSpatial f hf := by
  refine Symbol.ext (coefficient_eq_coefficient_leftSymbol_of_forall_quantizeSchwartzValue_eq _
    fun u _ ↦ funext fun x ↦ ?_).symm
  have hc : (Symbol.ofSpatial f hf).coefficient = fun p ↦ f p.1 :=
    funext (Symbol.coefficient_ofSpatial f hf)
  have hg : HasCompactSupport fun y ↦ f y (u y) :=
    hfs.mono fun y hy h ↦ hy (by simp [h])
  have hsm : ContDiff ℝ ∞ fun y ↦ f y (u y) := by
    have h := (Symbol.ofSpatial f hf).contDiff_quantizeSchwartzValue u
    rwa [hc, funext (quantizeSchwartzValue_comp_fst f u)] at h
  set g := hg.toSchwartzMap hsm
  have hgu : ⇑g = fun y ↦ f y (u y) := funext (HasCompactSupport.toSchwartzMap_toFun _ _)
  rw [hc, quantizeSchwartzValue_comp_fst, quantizeAmplitudeValue_def]
  simp only [coefficient_ofRight, hc]
  rw [← hgu, ← SchwartzMap.fourier_coe, ← Real.fourierInv_eq, ← SchwartzMap.fourierInv_coe,
    fourierInv_fourier_eq, hgu]

end Amplitude

end TauCeti
