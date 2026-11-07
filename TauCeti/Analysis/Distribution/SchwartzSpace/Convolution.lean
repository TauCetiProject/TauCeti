/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.FourierMultiplier
public import Mathlib.Analysis.Fourier.Convolution
import TauCeti.Analysis.Convolution.Young
import TauCeti.MeasureTheory.Integral.SchurTest

/-!
# Convolution and the Fourier transform on Schwartz space

For a Schwartz symbol `σ : 𝓢(E, ℂ)`, the Fourier multiplier `φ ↦ 𝓕⁻ (σ • 𝓕 φ)` on Schwartz
functions (Mathlib's `SchwartzMap.fourierMultiplierCLM`) is convolution with the Schwartz function
`𝓕⁻ σ`:

`𝓕⁻ (σ • 𝓕 φ) x = ∫ 𝓕⁻ σ (x - y) • φ y`.

This is the convolution theorem `SchwartzMap.fourier_convolution` read backwards. It identifies
the kernel of a multiplier whose symbol is smooth and rapidly decreasing, which is the form taken
by the truncated symbols in the Littlewood–Paley proof of the Mihlin–Hörmander multiplier theorem.
By Young's inequality (`MeasureTheory.eLpNorm_convolution_le`), such a multiplier is bounded in
every `Lᵖ` norm, `1 ≤ p ≤ ∞`, by the `L¹` norm of its kernel: `‖T_σ φ‖_p ≤ ‖𝓕⁻ σ‖₁ ‖φ‖_p`.

Dually, the Fourier transform turns pointwise products into convolutions: for Schwartz functions
`f`, `g` and a continuous bilinear map `B`,

`𝓕 (B (f ·) (g ·)) ξ = ∫ B (𝓕 f t) (𝓕 g (ξ - t)) dt`.

This follows from the inverse convolution theorem `𝓕⁻ (f ⋆ g) = 𝓕⁻ f · 𝓕⁻ g`, which in turn is
Mathlib's `Real.fourier_bilin_convolution_eq` composed with the reflection `ξ ↦ -ξ`. It is the
starting point of the estimates for multiplication operators on Sobolev spaces.

Derivatives of a convolution `κ ⋆ f` of a scalar Schwartz kernel with a Schwartz function fall on
the kernel, `∂ᵥ (κ ⋆ f) = (∂ᵥ κ) ⋆ f`, and convolution with a Schwartz kernel maps `Lᵖ` to `L^q`
whenever `1 ≤ p ≤ q ≤ ∞`, by Young's inequality for integral kernels. Together these turn an
identity `f = κ ⋆ f` on the Fourier side into `Lᵖ`–`L^q` bounds for all derivatives of `f`, as in
Bernstein's inequality for band-limited functions.

## Main declarations

* `SchwartzMap.fourierMultiplierCLM_eq_convolution`: the multiplier with symbol `σ` is
  `SchwartzMap.convolution` with `𝓕⁻ σ`.
* `SchwartzMap.fourierMultiplierCLM_apply_eq_integral`: the same, pointwise, as an integral.
* `SchwartzMap.lineDerivOp_convolution_lsmul`, `SchwartzMap.iteratedLineDerivOp_convolution_lsmul`:
  derivatives of `κ ⋆ f` fall on the scalar kernel `κ`.
* `SchwartzMap.exists_eLpNorm_convolution_le`: convolution with a Schwartz kernel maps `Lᵖ` to
  `L^q` for `1 ≤ p ≤ q ≤ ∞`.
* `SchwartzMap.eLpNorm_fourierMultiplierCLM_le`: the `Lᵖ` bound `‖T_σ φ‖_p ≤ ‖𝓕⁻ σ‖₁ ‖φ‖_p`.
* `SchwartzMap.fourierInv_convolution`: the inverse Fourier transform of a convolution is the
  pairing of the inverse Fourier transforms.
* `SchwartzMap.fourier_pairing`, `SchwartzMap.fourier_pairing_apply`: the Fourier transform of a
  pointwise product is the convolution of the Fourier transforms.
* `SchwartzMap.fourier_smulLeftCLM_apply`: the same for the product with a scalar Schwartz
  function, `𝓕 (φ • f) ξ = ∫ 𝓕 φ t • 𝓕 f (ξ - t) dt`.

## References

* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., Sections 2.2 and 2.5.
* G. B. Folland, *Real Analysis: Modern Techniques and Their Applications*, 2nd ed.,
  Proposition 8.9 (Young's inequality).
-/

public section

open scoped FourierTransform SchwartzMap ENNReal
open FourierTransform ContinuousLinearMap MeasureTheory
open scoped Convolution NNReal
open LineDeriv

namespace SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- On Schwartz functions, the multiplier with a Schwartz symbol `σ` is convolution with the
Schwartz function `𝓕⁻ σ`. -/
theorem fourierMultiplierCLM_eq_convolution (σ : 𝓢(E, ℂ)) :
    fourierMultiplierCLM F σ = convolution (lsmul ℂ ℂ) (𝓕⁻ σ) := by
  ext1 φ
  rw [← FourierPair.fourierInv_fourier_eq (F := 𝓢(E, F))
      (convolution (lsmul ℂ ℂ) (𝓕⁻ σ) φ),
    fourier_convolution, fourier_fourierInv_eq, fourierMultiplierCLM_apply]
  congr 1
  ext ξ
  simp [smulLeftCLM_apply_apply σ.hasTemperateGrowth]

/-- The multiplier with a Schwartz symbol `σ` on Schwartz functions, as an integral against the
kernel `𝓕⁻ σ`: `T_σ φ x = ∫ 𝓕⁻ σ (x - y) • φ y`. -/
theorem fourierMultiplierCLM_apply_eq_integral (σ : 𝓢(E, ℂ)) (φ : 𝓢(E, F)) (x : E) :
    fourierMultiplierCLM F σ φ x = ∫ y, 𝓕⁻ σ (x - y) • φ y := by
  rw [fourierMultiplierCLM_eq_convolution, convolution_apply, MeasureTheory.convolution_eq_swap]
  simp only [lsmul_apply]

/-- A line derivative of the convolution of a scalar Schwartz kernel with a Schwartz function
falls on the kernel. -/
theorem lineDerivOp_convolution_lsmul (κ : 𝓢(E, ℂ)) (f : 𝓢(E, F)) (v : E) :
    ∂_{v} (convolution (lsmul ℂ ℂ) κ f) = convolution (lsmul ℂ ℂ) (∂_{v} κ) f := by
  have hσ := fourierMultiplierCLM_eq_convolution (F := F) (𝓕 κ)
  have hσ' := fourierMultiplierCLM_eq_convolution (F := F) (𝓕 (∂_{v} κ))
  simp only [FourierTransform.fourierInv_fourier_eq] at hσ hσ'
  have hv : (inner ℝ · v : E → ℝ).HasTemperateGrowth := by fun_prop
  rw [← hσ, ← hσ', fourierMultiplierCLM_apply, fourierMultiplierCLM_apply,
    lineDerivOp_fourierInv_eq, fourier_lineDerivOp_eq]
  congr 1
  ext ξ
  simp only [smul_apply, smulLeftCLM_apply_apply hv,
    smulLeftCLM_apply_apply (𝓕 κ).hasTemperateGrowth,
    smulLeftCLM_apply_apply
      ((2 * Real.pi * Complex.I) • smulLeftCLM ℂ (inner ℝ · v) (𝓕 κ)).hasTemperateGrowth]
  rw [smul_assoc, smul_assoc]

/-- Iterated line derivatives of the convolution of a scalar Schwartz kernel with a Schwartz
function fall on the kernel. -/
theorem iteratedLineDerivOp_convolution_lsmul (κ : 𝓢(E, ℂ)) (f : 𝓢(E, F)) {n : ℕ}
    (m : Fin n → E) :
    ∂^{m} (convolution (lsmul ℂ ℂ) κ f) = convolution (lsmul ℂ ℂ) (∂^{m} κ) f := by
  induction n with
  | zero => simp only [iteratedLineDerivOp_fin_zero]
  | succ n ih =>
    rw [iteratedLineDerivOp_succ_left, ih, lineDerivOp_convolution_lsmul,
      ← iteratedLineDerivOp_succ_left]

omit [CompleteSpace F] in
/-- Convolution with a Schwartz kernel `κ` maps `Lᵖ` to `L^q` for `1 ≤ p ≤ q ≤ ∞`: there is `C`
with `‖κ ⋆ f‖_q ≤ C ‖f‖_p` for every a.e. strongly measurable `f`. For `q < ∞` this is Young's
inequality for integral kernels, with `κ ∈ L^r` for `1/p + 1/r = 1 + 1/q`; for `q = ∞` it is
Hölder's inequality at every point. -/
theorem exists_eLpNorm_convolution_le (κ : 𝓢(E, ℂ)) {p q : ℝ≥0∞} (hp : 1 ≤ p) (hpq : p ≤ q) :
    ∃ C : ℝ≥0, ∀ f : E → F, AEStronglyMeasurable f →
      eLpNorm (κ ⋆[lsmul ℂ ℂ] f) q ≤ C * eLpNorm f p := by
  rcases eq_or_ne q ∞ with rfl | hq
  · -- For `q = ∞` this is Hölder's inequality at every point.
    have : (ENNReal.conjExponent p).HolderConjugate p :=
      (ENNReal.HolderConjugate.conjExponent hp).symm
    have hfin : ‖lsmul ℂ ℂ (E := F)‖ₑ * eLpNorm κ (ENNReal.conjExponent p) ≠ ∞ :=
      ENNReal.mul_ne_top enorm_ne_top (κ.memLp _).eLpNorm_ne_top
    refine ⟨(‖lsmul ℂ ℂ (E := F)‖ₑ * eLpNorm κ (ENNReal.conjExponent p)).toNNReal,
      fun f hf => ?_⟩
    rw [ENNReal.coe_toNNReal hfin,
      eLpNorm_exponent_top (κ.continuous.aestronglyMeasurable.convolution _ hf)]
    exact eLpNormEssSup_le_of_ae_enorm_bound (ae_of_all _ fun x =>
      enorm_convolution_le _ κ.continuous.aestronglyMeasurable hf x)
  · -- For `q < ∞` this is Young's inequality for integral kernels, with the exponent `r` given by
    -- `1/p + 1/r = 1 + 1/q`.
    have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
    have hp_top : p ≠ ∞ := ne_top_of_le_ne_top hq hpq
    have hq0 : q ≠ 0 := (zero_lt_one.trans_le (hp.trans hpq)).ne'
    have hp' : 1 ≤ p.toReal := by simpa using ENNReal.toReal_mono hp_top hp
    have hpq' : p.toReal ≤ q.toReal := ENNReal.toReal_mono hq hpq
    have hq'0 : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
    have hp'1 : p.toReal⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hp'
    set r : ℝ := (1 + q.toReal⁻¹ - p.toReal⁻¹)⁻¹ with hr_def
    have hr0 : 0 < r := inv_pos.2 (by have := inv_pos.2 hq'0; linarith)
    have hr : p.toReal⁻¹ + r⁻¹ = 1 + q.toReal⁻¹ := by rw [hr_def, inv_inv]; ring
    set A : ℝ≥0∞ := ∫⁻ y, ‖κ y‖ₑ ^ r
    have hA : A ≠ ∞ := by
      have := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := ENNReal.ofReal r)
        (by simpa using hr0) ENNReal.ofReal_ne_top (κ.memLp _).eLpNorm_lt_top
      simpa [ENNReal.toReal_ofReal hr0.le] using this.ne
    set C' : ℝ≥0∞ := (A ^ (q.toReal * (1 - p.toReal⁻¹)) * A) ^ q.toReal⁻¹
    have hC' : C' ≠ ∞ :=
      ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 hq'0.le) (ENNReal.mul_ne_top
        (ENNReal.rpow_ne_top_of_nonneg (by have := sub_nonneg.2 hp'1; positivity) hA) hA)
    refine ⟨C'.toNNReal, fun f hf => ?_⟩
    rw [ENNReal.coe_toNNReal hC']
    have hpt (x : E) : ‖(κ ⋆[lsmul ℂ ℂ] f) x‖ₑ ≤ ∫⁻ y, ‖κ (x - y)‖ₑ * ‖f y‖ₑ := by
      rw [convolution_lsmul_swap]
      refine (enorm_integral_le_lintegral_enorm _).trans_eq ?_
      simp_rw [enorm_smul]
    have hS := TauCeti.lintegral_rpow_lintegral_mul_le_of_inv_add_inv_eq (μ := volume)
      (ν := volume) (k := fun x y => ‖κ (x - y)‖ₑ)
      ((κ.continuous.comp continuous_sub).enorm.measurable.aemeasurable) hf.enorm hp' hpq' hr
      (A := A) (B := A)
      (ae_of_all _ fun x => (lintegral_sub_left_eq_self (fun z => ‖κ z‖ₑ ^ r) x).le)
      (ae_of_all _ fun y => (lintegral_sub_right_eq_self (fun z => ‖κ z‖ₑ ^ r) y).le)
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hq
        (κ.continuous.aestronglyMeasurable.convolution _ hf),
      eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top hf]
    calc (∫⁻ x, ‖(κ ⋆[lsmul ℂ ℂ] f) x‖ₑ ^ q.toReal) ^ (1 / q.toReal)
        ≤ (∫⁻ x, (∫⁻ y, ‖κ (x - y)‖ₑ * ‖f y‖ₑ) ^ q.toReal) ^ (1 / q.toReal) := by
          gcongr with x; exact hpt x
      _ ≤ (A ^ (q.toReal * (1 - p.toReal⁻¹)) * A *
            (∫⁻ y, ‖f y‖ₑ ^ p.toReal) ^ (q.toReal / p.toReal)) ^ (1 / q.toReal) := by
          gcongr
      _ = C' * (∫⁻ y, ‖f y‖ₑ ^ p.toReal) ^ (1 / p.toReal) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul, one_div]
          congr 2
          field_simp

/-- **`Lᵖ` bound for a multiplier with Schwartz symbol.** For `1 ≤ p ≤ ∞` the multiplier with a
Schwartz symbol `σ` satisfies `‖T_σ φ‖_p ≤ ‖𝓕⁻ σ‖₁ ‖φ‖_p` on Schwartz functions. -/
theorem eLpNorm_fourierMultiplierCLM_le (σ : 𝓢(E, ℂ)) (φ : 𝓢(E, F)) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (fourierMultiplierCLM F σ φ) p ≤ eLpNorm (𝓕⁻ (σ : E → ℂ)) 1 * eLpNorm φ p := by
  have h : (fourierMultiplierCLM F σ φ : E → F) = ⇑(𝓕⁻ σ : 𝓢(E, ℂ)) ⋆[lsmul ℂ ℂ] φ := by
    funext x
    rw [fourierMultiplierCLM_eq_convolution, convolution_apply]
  rw [h, ← fourierInv_coe]
  refine (eLpNorm_convolution_le _ (𝓕⁻ σ : 𝓢(E, ℂ)).continuous.aestronglyMeasurable
    φ.continuous.aestronglyMeasurable hp).trans ?_
  grw [opENorm_lsmul_le, one_mul]

section Bilinear

variable {F₁ F₂ F₃ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℂ F₁] [CompleteSpace F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℂ F₂] [CompleteSpace F₂]
  [NormedAddCommGroup F₃] [NormedSpace ℂ F₃] [CompleteSpace F₃]

/-- The inverse Fourier transform turns the convolution of Schwartz functions into the pointwise
product of their inverse Fourier transforms. -/
theorem fourierInv_convolution_apply (B : F₁ →L[ℂ] F₂ →L[ℂ] F₃) (f : 𝓢(E, F₁)) (g : 𝓢(E, F₂))
    (ξ : E) : 𝓕⁻ (convolution B f g) ξ = B (𝓕⁻ f ξ) (𝓕⁻ g ξ) := by
  have hconv : (convolution B f g : E → F₃) = f ⋆[B] g := funext (convolution_apply B f g)
  rw [fourierInv_coe, fourierInv_coe, fourierInv_coe, hconv, Real.fourierInv_eq_fourier_neg,
    Real.fourierInv_eq_fourier_neg, Real.fourierInv_eq_fourier_neg,
    Real.fourier_bilin_convolution_eq B f.integrable g.integrable]

/-- The inverse Fourier transform of a convolution of Schwartz functions is the pairing of their
inverse Fourier transforms. -/
theorem fourierInv_convolution (B : F₁ →L[ℂ] F₂ →L[ℂ] F₃) (f : 𝓢(E, F₁)) (g : 𝓢(E, F₂)) :
    𝓕⁻ (convolution B f g) = pairing B (𝓕⁻ f) (𝓕⁻ g) := by
  ext ξ
  rw [fourierInv_convolution_apply, pairing_apply_apply]

/-- **The Fourier transform of a product is the convolution of the Fourier transforms.** For
Schwartz functions `f`, `g` and a continuous bilinear map `B`, the Fourier transform of the
pointwise product `x ↦ B (f x) (g x)` is the convolution of `𝓕 f` and `𝓕 g`. -/
theorem fourier_pairing (B : F₁ →L[ℂ] F₂ →L[ℂ] F₃) (f : 𝓢(E, F₁)) (g : 𝓢(E, F₂)) :
    𝓕 (pairing B f g) = convolution B (𝓕 f) (𝓕 g) := by
  calc 𝓕 (pairing B f g) = 𝓕 (pairing B (𝓕⁻ (𝓕 f)) (𝓕⁻ (𝓕 g))) := by
        rw [fourierInv_fourier_eq, fourierInv_fourier_eq]
    _ = 𝓕 (𝓕⁻ (convolution B (𝓕 f) (𝓕 g))) := by rw [fourierInv_convolution]
    _ = convolution B (𝓕 f) (𝓕 g) := fourier_fourierInv_eq _

/-- The Fourier transform of a pointwise product of Schwartz functions, as an integral:
`𝓕 (B (f ·) (g ·)) ξ = ∫ t, B (𝓕 f t) (𝓕 g (ξ - t))`. -/
theorem fourier_pairing_apply (B : F₁ →L[ℂ] F₂ →L[ℂ] F₃) (f : 𝓢(E, F₁)) (g : 𝓢(E, F₂))
    (ξ : E) : 𝓕 (pairing B f g) ξ = ∫ t, B (𝓕 f t) (𝓕 g (ξ - t)) := by
  rw [fourier_pairing, convolution_apply, MeasureTheory.convolution_def]

/-- The Fourier transform of the product of a Schwartz function `f` by a scalar Schwartz function
`φ` is the convolution `𝓕 (φ • f) ξ = ∫ t, 𝓕 φ t • 𝓕 f (ξ - t)`. -/
theorem fourier_smulLeftCLM_apply (φ : 𝓢(E, ℂ)) (f : 𝓢(E, F)) (ξ : E) :
    𝓕 (smulLeftCLM F (φ : E → ℂ) f) ξ = ∫ t, 𝓕 φ t • 𝓕 f (ξ - t) := by
  have h : smulLeftCLM F (φ : E → ℂ) f = pairing (lsmul ℂ ℂ) φ f := by
    ext x
    simp [smulLeftCLM_apply_apply φ.hasTemperateGrowth]
  rw [h, fourier_pairing_apply]
  simp only [lsmul_apply]

end Bilinear

end SchwartzMap
