/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.FourierMultiplier
public import Mathlib.Analysis.Fourier.Convolution
import TauCeti.Analysis.Convolution.Young

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

## Main declarations

* `SchwartzMap.fourierMultiplierCLM_eq_convolution`: the multiplier with symbol `σ` is
  `SchwartzMap.convolution` with `𝓕⁻ σ`.
* `SchwartzMap.fourierMultiplierCLM_apply_eq_integral`: the same, pointwise, as an integral.
* `SchwartzMap.eLpNorm_fourierMultiplierCLM_le`: the `Lᵖ` bound `‖T_σ φ‖_p ≤ ‖𝓕⁻ σ‖₁ ‖φ‖_p`.
* `SchwartzMap.integrable_sub_smul`: for a Schwartz function `f` and `u ∈ Lᵖ`, `1 ≤ p ≤ ∞`, the
  convolution integral `∫ f (x - y) • u y` converges absolutely at every `x`.
* `SchwartzMap.integrable_uncurry_sub_smul_smul`: for `u ∈ Lᵖ` and `v ∈ L^q`, the integrand
  `(x, y) ↦ (ψ (x - y) • u y) • (θ x • v x)` is integrable on `E × E`.
* `SchwartzMap.fourierInv_convolution`: the inverse Fourier transform of a convolution is the
  pairing of the inverse Fourier transforms.
* `SchwartzMap.fourier_pairing`, `SchwartzMap.fourier_pairing_apply`: the Fourier transform of a
  pointwise product is the convolution of the Fourier transforms.
* `SchwartzMap.fourier_smulLeftCLM_apply`: the same for the product with a scalar Schwartz
  function, `𝓕 (φ • f) ξ = ∫ 𝓕 φ t • 𝓕 f (ξ - t) dt`.

## References

* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., Sections 2.2 and 2.5.
-/

public section

open scoped FourierTransform SchwartzMap ENNReal
open FourierTransform ContinuousLinearMap MeasureTheory
open scoped Convolution

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

/-- The convolution integral of an `Lᵖ` function, `1 ≤ p ≤ ∞`, against a Schwartz function
converges absolutely at every point. -/
theorem integrable_sub_smul {𝕜 V G : Type*} [NormedField 𝕜] [NormedSpace ℝ 𝕜]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
    [BorelSpace V] [NormedAddCommGroup G] [NormedSpace 𝕜 G] {μ : Measure V} [μ.IsAddHaarMeasure]
    (f : 𝓢(V, 𝕜)) {p : ℝ≥0∞} (hp : 1 ≤ p) {u : V → G} (hu : MemLp u p μ) (x : V) :
    Integrable (fun y ↦ f (x - y) • u y) μ := by
  have := ENNReal.HolderConjugate.conjExponent hp
  have hf : MemLp (fun y ↦ f (x - y)) p.conjExponent μ :=
    (f.memLp _ μ).comp_measurePreserving (μ.measurePreserving_sub_left x)
  exact memLp_one_iff_integrable.1 (hf.smul hu)

omit [CompleteSpace F] in
/-- For Schwartz functions `ψ`, `θ` and `u ∈ Lᵖ`, `v ∈ L^q` with `1 ≤ p, q`, the integrand
`(x, y) ↦ (ψ (x - y) • u y) • (θ x • v x)` is integrable on `E × E`. This is the integrand of the
pairing of `(ψ ⋆ u) • v` with `θ` before the convolution integral is evaluated, so it justifies
exchanging the order of integration there. For fixed `x` the integral in `y` is at most
`‖ψ‖_{p'} ‖u‖_p` by Hölder's inequality, and `θ • v` is integrable. -/
theorem integrable_uncurry_sub_smul_smul {p q : ℝ≥0∞} [hp : Fact (1 ≤ p)] [hq : Fact (1 ≤ q)]
    (ψ θ : 𝓢(E, ℂ)) (u : Lp ℂ p (volume : Measure E)) (v : Lp F q (volume : Measure E)) :
    Integrable (Function.uncurry fun x y ↦ (ψ (x - y) • u y) • (θ x • v x))
      ((volume : Measure E).prod volume) := by
  have hθv : Integrable (fun x ↦ θ x • v x) := by
    have : (1 - q⁻¹)⁻¹.HolderConjugate q :=
      (ENNReal.HolderConjugate.inv_one_sub_inv' hq.out).symm
    exact memLp_one_iff_integrable.1 ((θ.memLp (1 - q⁻¹)⁻¹ (μ := volume)).smul (Lp.memLp v))
  have hmeas : AEStronglyMeasurable (Function.uncurry fun x y ↦ (ψ (x - y) • u y) • (θ x • v x))
      ((volume : Measure E).prod volume) :=
    ((ψ.continuous.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable.smul
      (Lp.aestronglyMeasurable u).comp_snd).smul
      ((θ.continuous.comp continuous_fst).aestronglyMeasurable.smul
        (Lp.aestronglyMeasurable v).comp_fst)
  refine ⟨hmeas, ?_⟩
  have : (1 - p⁻¹)⁻¹.HolderTriple p 1 := (ENNReal.HolderConjugate.inv_one_sub_inv' hp.out).symm
  set C := eLpNorm ψ (1 - p⁻¹)⁻¹ volume * eLpNorm u p volume
  have hC : C < ∞ := ENNReal.mul_lt_top (ψ.eLpNorm_lt_top _ volume) (Lp.eLpNorm_lt_top u)
  have hinner : ∀ x, ∫⁻ y, ‖(ψ (x - y) • u y) • (θ x • v x)‖ₑ ≤ C * ‖θ x • v x‖ₑ := fun x ↦ by
    simp_rw [enorm_smul _ (θ x • v x)]
    rw [lintegral_mul_const' _ _ enorm_ne_top]
    gcongr
    have hψx : AEStronglyMeasurable (fun y ↦ ψ (x - y)) volume :=
      (ψ.continuous.comp (continuous_sub_left x)).aestronglyMeasurable
    calc ∫⁻ y, ‖ψ (x - y) • u y‖ₑ = eLpNorm ((fun y ↦ ψ (x - y)) • ⇑u) 1 volume := by
          simp only [eLpNorm_one_eq_lintegral_enorm (hψx.smul (Lp.aestronglyMeasurable u)),
            Pi.smul_apply']
      _ ≤ eLpNorm (fun y ↦ ψ (x - y)) (1 - p⁻¹)⁻¹ volume * eLpNorm u p volume :=
          eLpNorm_smul_le_mul_eLpNorm hψx (Lp.aestronglyMeasurable u)
      _ = C := by
          have h := eLpNorm_comp_measurePreserving (p := (1 - p⁻¹)⁻¹)
            ψ.continuous.aestronglyMeasurable (volume.measurePreserving_sub_left x)
          rw [Function.comp_def] at h
          rw [h]
  rw [HasFiniteIntegral, lintegral_prod _ hmeas.enorm]
  calc ∫⁻ x, ∫⁻ y, ‖Function.uncurry (fun x y ↦ (ψ (x - y) • u y) • (θ x • v x)) (x, y)‖ₑ
      ≤ ∫⁻ x, C * ‖θ x • v x‖ₑ := lintegral_mono hinner
    _ = C * ∫⁻ x, ‖θ x • v x‖ₑ := lintegral_const_mul' _ _ hC.ne
    _ < ∞ := ENNReal.mul_lt_top hC hθv.2

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
