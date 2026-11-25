/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.FourierMultiplier
public import Mathlib.Analysis.Fourier.Convolution
import TauCeti.Analysis.Convolution.Basic
import TauCeti.Analysis.Convolution.Young
import TauCeti.Analysis.Distribution.SchwartzSpace.Fourier

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
* `SchwartzMap.fourier_smulLeftCLM_fourierInv_apply`: the convolution theorem
  `𝓕 (𝓕 K • 𝓕⁻ φ) y = ∫ x, K (x - y) * φ x` for an integrable kernel `K` and a test function `φ`.
* `SchwartzMap.eLpNorm_fourierMultiplierCLM_le`: the `Lᵖ` bound `‖T_σ φ‖_p ≤ ‖𝓕⁻ σ‖₁ ‖φ‖_p`.
* `SchwartzMap.fourier_convolution_fourierInv_apply`: the Fourier transform of the convolution of
  `𝓕⁻ σ` with `f` is the bilinear multiplier `ξ ↦ B (σ ξ) (𝓕 f ξ)`.
* `SchwartzMap.norm_fourierInv_bilin_fourier_apply_le`: the pointwise bound
  `‖𝓕⁻ (B (σ ·) (𝓕 f ·)) x‖ ≤ ‖B‖ ‖𝓕⁻ σ‖₁ sup ‖f‖` for a bilinear multiplier with a Schwartz
  symbol, such as an operator-valued one, and
  `SchwartzMap.norm_integral_fourierChar_smul_bilin_fourier_le`: the same bound
  `‖𝓕⁻ ρ‖₁ ‖B‖ ‖𝓕⁻ σ‖₁ sup ‖f‖` for the multiplier composed with the scalar multiplier `ρ`, written
  as a single Fourier integral.
* `SchwartzMap.integrable_sub_smul`: for a Schwartz function `f` and `u ∈ Lᵖ`, `1 ≤ p ≤ ∞`, the
  convolution integral `∫ f (x - y) • u y` converges absolutely at every `x`.
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

open scoped FourierTransform SchwartzMap ENNReal RealInnerProductSpace
open FourierTransform ContinuousLinearMap MeasureTheory
open scoped Convolution

namespace SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F]

section NotCompleteSpace

variable {F₁ F₂ F₃ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℂ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℂ F₂] [NormedAddCommGroup F₃] [NormedSpace ℂ F₃]

/-- Into a space which is not complete, the convolution of Schwartz functions is `0`, as the
inverse Fourier transform defining it is. -/
theorem convolution_eq_zero_of_not_completeSpace_target (B : F₁ →L[ℂ] F₂ →L[ℂ] F₃)
    (hF₃ : ¬CompleteSpace F₃) (f : 𝓢(E, F₁)) (g : 𝓢(E, F₂)) : convolution B f g = 0 := by
  simp [convolution, fourierInv_eq_zero_of_not_completeSpace hF₃]

/-- If the first factor takes values in a space which is not complete, the convolution of Schwartz
functions is `0`, as the Fourier transform of that factor is. -/
theorem convolution_eq_zero_of_not_completeSpace_left (B : F₁ →L[ℂ] F₂ →L[ℂ] F₃)
    (hF₁ : ¬CompleteSpace F₁) (f : 𝓢(E, F₁)) (g : 𝓢(E, F₂)) : convolution B f g = 0 := by
  simp [convolution, fourier_eq_zero_of_not_completeSpace hF₁]

/-- If the second factor takes values in a space which is not complete, the convolution of
Schwartz functions is `0`, as the Fourier transform of that factor is. -/
theorem convolution_eq_zero_of_not_completeSpace_right (B : F₁ →L[ℂ] F₂ →L[ℂ] F₃)
    (hF₂ : ¬CompleteSpace F₂) (f : 𝓢(E, F₁)) (g : 𝓢(E, F₂)) : convolution B f g = 0 := by
  simp [convolution, fourier_eq_zero_of_not_completeSpace hF₂]

end NotCompleteSpace

/-- On Schwartz functions, the multiplier with a Schwartz symbol `σ` is convolution with the
Schwartz function `𝓕⁻ σ`. -/
theorem fourierMultiplierCLM_eq_convolution (σ : 𝓢(E, ℂ)) :
    fourierMultiplierCLM F σ = convolution (lsmul ℂ ℂ) (𝓕⁻ σ) := by
  ext1 φ
  by_cases hF : CompleteSpace F
  · rw [← FourierPair.fourierInv_fourier_eq (F := 𝓢(E, F))
        (convolution (lsmul ℂ ℂ) (𝓕⁻ σ) φ),
      fourier_convolution, fourier_fourierInv_eq, fourierMultiplierCLM_apply]
    congr 1
    ext ξ
    simp [smulLeftCLM_apply_apply σ.hasTemperateGrowth]
  · simp [fourierMultiplierCLM_apply, fourier_eq_zero_of_not_completeSpace hF,
      convolution_eq_zero_of_not_completeSpace_target _ hF]

/-- The multiplier with a Schwartz symbol `σ` on Schwartz functions, as an integral against the
kernel `𝓕⁻ σ`: `T_σ φ x = ∫ 𝓕⁻ σ (x - y) • φ y`. -/
theorem fourierMultiplierCLM_apply_eq_integral (σ : 𝓢(E, ℂ)) (φ : 𝓢(E, F)) (x : E) :
    fourierMultiplierCLM F σ φ x = ∫ y, 𝓕⁻ σ (x - y) • φ y := by
  by_cases hF : CompleteSpace F
  · rw [fourierMultiplierCLM_eq_convolution, convolution_apply, MeasureTheory.convolution_eq_swap]
    simp only [lsmul_apply]
  · simp [fourierMultiplierCLM_apply, fourier_eq_zero_of_not_completeSpace hF,
      integral_of_not_completeSpace hF]

/-- **The convolution theorem against a test function.** If the symbol `g` of temperate growth is
the Fourier transform of an integrable kernel `K`, then for every test function `φ`,
`𝓕 (g • 𝓕⁻ φ) y = ∫ x, K (x - y) * φ x`. -/
theorem fourier_smulLeftCLM_fourierInv_apply {K : E → ℂ} (hK : Integrable K) {g : E → ℂ}
    (hg : g.HasTemperateGrowth) (hgK : 𝓕 K = g) (φ : 𝓢(E, ℂ)) (y : E) :
    𝓕 (smulLeftCLM ℂ g (𝓕⁻ φ)) y = ∫ x, K (x - y) * φ x := by
  set ψ := 𝓕⁻ φ
  calc 𝓕 (smulLeftCLM ℂ g ψ) y
      = ∫ ξ, 𝓕 K ξ • (𝐞 (-⟪ξ, y⟫) • ψ ξ) := by
        rw [fourier_coe, Real.fourier_eq]
        refine integral_congr_ae (.of_forall fun ξ ↦ ?_)
        dsimp only
        rw [smulLeftCLM_apply_apply hg, ← hgK, smul_comm]
    -- The multiplication formula `∫ 𝓕 K • h = ∫ K • 𝓕 h` for integrable `K` and `h`.
    _ = ∫ z, K z • VectorFourier.fourierIntegral 𝐞 volume (innerₗ E).flip
          (fun ξ ↦ 𝐞 (-⟪ξ, y⟫) • ψ ξ) z :=
        VectorFourier.integral_fourierIntegral_smul_eq_flip Real.continuous_fourierChar
          continuous_inner hK ((Real.fourierIntegral_convergent_iff y).2 ψ.integrable)
    _ = ∫ z, K z * φ (y + z) := by
        refine integral_congr_ae (.of_forall fun z ↦ ?_)
        -- The exponentials combine into the character at `y + z`.
        have hexp : ∀ ξ, ⟪z, ξ⟫ + ⟪ξ, y⟫ = ⟪ξ, y + z⟫ := fun ξ ↦ by
          rw [inner_add_right, real_inner_comm ξ z, add_comm]
        simp only [VectorFourier.fourierIntegral, LinearMap.flip_apply, innerₗ_apply_apply,
          smul_smul, ← AddChar.map_add_eq_mul, ← neg_add, hexp, smul_eq_mul]
        rw [← Real.fourier_eq, ← fourier_coe, fourier_fourierInv_eq]
    _ = ∫ x, K (x - y) * φ x := by
        rw [← integral_sub_right_eq_self (fun z ↦ K z * φ (y + z)) y]
        simp only [add_sub_cancel]

/-- **`Lᵖ` bound for a multiplier with Schwartz symbol.** For `1 ≤ p ≤ ∞` the multiplier with a
Schwartz symbol `σ` satisfies `‖T_σ φ‖_p ≤ ‖𝓕⁻ σ‖₁ ‖φ‖_p` on Schwartz functions. -/
theorem eLpNorm_fourierMultiplierCLM_le (σ : 𝓢(E, ℂ)) (φ : 𝓢(E, F))
    {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (fourierMultiplierCLM F σ φ) p ≤ eLpNorm (𝓕⁻ (σ : E → ℂ)) 1 * eLpNorm φ p := by
  by_cases hF : CompleteSpace F
  swap
  · simp [fourierMultiplierCLM_apply, fourier_eq_zero_of_not_completeSpace hF]
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

section Bilinear

variable {F₁ F₂ F₃ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℂ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℂ F₂] [NormedAddCommGroup F₃] [NormedSpace ℂ F₃]

/-- The inverse Fourier transform turns the convolution of Schwartz functions into the pointwise
product of their inverse Fourier transforms. -/
theorem fourierInv_convolution_apply [CompleteSpace F₃] (B : F₁ →L[ℂ] F₂ →L[ℂ] F₃) (f : 𝓢(E, F₁))
    (g : 𝓢(E, F₂)) (ξ : E) : 𝓕⁻ (convolution B f g) ξ = B (𝓕⁻ f ξ) (𝓕⁻ g ξ) := by
  by_cases hF₁ : CompleteSpace F₁
  · by_cases hF₂ : CompleteSpace F₂
    · have hconv : (convolution B f g : E → F₃) = f ⋆[B] g := funext (convolution_apply B f g)
      rw [fourierInv_coe, fourierInv_coe, fourierInv_coe, hconv, Real.fourierInv_eq_fourier_neg,
        Real.fourierInv_eq_fourier_neg, Real.fourierInv_eq_fourier_neg,
        Real.fourier_bilin_convolution_eq B f.integrable g.integrable]
    · simp [convolution_eq_zero_of_not_completeSpace_right _ hF₂,
        fourierInv_eq_zero_of_not_completeSpace hF₂]
  · simp [convolution_eq_zero_of_not_completeSpace_left _ hF₁,
      fourierInv_eq_zero_of_not_completeSpace hF₁]

/-- The inverse Fourier transform of a convolution of Schwartz functions is the pairing of their
inverse Fourier transforms. -/
theorem fourierInv_convolution [CompleteSpace F₃] (B : F₁ →L[ℂ] F₂ →L[ℂ] F₃) (f : 𝓢(E, F₁))
    (g : 𝓢(E, F₂)) :
    𝓕⁻ (convolution B f g) = pairing B (𝓕⁻ f) (𝓕⁻ g) := by
  ext ξ
  rw [fourierInv_convolution_apply, pairing_apply_apply]

/-- The Fourier transform of the convolution of `𝓕⁻ σ` with `f` is the bilinear multiplier
`ξ ↦ B (σ ξ) (𝓕 f ξ)`. -/
theorem fourier_convolution_fourierInv_apply [CompleteSpace F₁] [CompleteSpace F₃]
    (B : F₁ →L[ℂ] F₂ →L[ℂ] F₃) (σ : 𝓢(E, F₁)) (f : 𝓢(E, F₂)) (ξ : E) :
    𝓕 (convolution B (𝓕⁻ σ) f) ξ = B (σ ξ) (𝓕 f ξ) := by
  rw [fourier_convolution, fourier_fourierInv_eq, pairing_apply_apply]

/-- **Pointwise bound for a multiplier with a Schwartz symbol.** For a continuous bilinear map `B`,
a Schwartz symbol `σ` and a Schwartz function `f` bounded by `M`, the function
`𝓕⁻ (B (σ ·) (𝓕 f ·))`, which is the convolution of `𝓕⁻ σ` with `f`, is bounded by
`‖B‖ ‖𝓕⁻ σ‖₁ M`. -/
theorem norm_fourierInv_bilin_fourier_apply_le [CompleteSpace F₁] (B : F₁ →L[ℂ] F₂ →L[ℂ] F₃)
    (σ : 𝓢(E, F₁)) (f : 𝓢(E, F₂)) {M : ℝ} (hf : ∀ y, ‖f y‖ ≤ M) (x : E) :
    ‖𝓕⁻ (fun ξ ↦ B (σ ξ) (𝓕 f ξ)) x‖ ≤ ‖B‖ * (∫ y, ‖𝓕⁻ σ y‖) * M := by
  have hR : 0 ≤ ‖B‖ * (∫ y, ‖𝓕⁻ σ y‖) * M :=
    mul_nonneg (mul_nonneg (ContinuousLinearMap.opNorm_nonneg B)
      (integral_nonneg fun _ ↦ norm_nonneg _))
      ((norm_nonneg _).trans (hf 0))
  -- Without completeness of `F₂` or `F₃` the left side vanishes by the integral convention.
  by_cases hF₃ : CompleteSpace F₃
  swap
  · rw [Real.fourierInv_eq, integral_of_not_completeSpace hF₃, norm_zero]
    exact hR
  by_cases hF₂ : CompleteSpace F₂
  swap
  · simpa [fourier_eq_zero_of_not_completeSpace hF₂, Real.fourierInv_eq] using hR
  have h : (fun ξ ↦ B (σ ξ) (𝓕 f ξ)) = ⇑(𝓕 (convolution B (𝓕⁻ σ) f) : 𝓢(E, F₃)) :=
    funext fun ξ ↦ (fourier_convolution_fourierInv_apply B σ f ξ).symm
  have hM : ‖f.toLp ⊤‖ ≤ M := Lp.norm_le_of_ae_bound_top ((norm_nonneg _).trans (hf 0))
    ((f.coeFn_toLp ⊤ volume).mono fun y hy ↦ by rw [hy]; exact hf y)
  rw [h, ← fourierInv_coe, fourierInv_fourier_eq, convolution_apply,
    convolution_congr B (.refl _ _) (f.coeFn_toLp ⊤ volume).symm]
  refine (norm_convolution_le_integral_norm_mul_norm B (𝓕⁻ σ).integrable (f.toLp ⊤) x).trans ?_
  gcongr

/-- **Pointwise bound for a modulated multiplier.** For a scalar Schwartz function `ρ`, a
continuous bilinear map `B`, a Schwartz symbol `σ` and a Schwartz function `f` bounded by `M`,

`‖∫ 𝐞 ⟪ξ, x⟫ ρ(ξ) B (σ ξ) (𝓕 f ξ) dξ‖ ≤ ‖𝓕⁻ ρ‖₁ ‖B‖ ‖𝓕⁻ σ‖₁ M`:

the integral is the convolution of `𝓕⁻ ρ` with the convolution of `𝓕⁻ σ` with `f`. -/
theorem norm_integral_fourierChar_smul_bilin_fourier_le [CompleteSpace F₁]
    (ρ : 𝓢(E, ℂ)) (B : F₁ →L[ℂ] F₂ →L[ℂ] F₃) (σ : 𝓢(E, F₁)) (f : 𝓢(E, F₂)) {M : ℝ}
    (hf : ∀ y, ‖f y‖ ≤ M) (x : E) :
    ‖∫ ξ, 𝐞 ⟪ξ, x⟫ • ρ ξ • B (σ ξ) (𝓕 f ξ)‖ ≤
      (∫ y, ‖𝓕⁻ ρ y‖) * (‖B‖ * (∫ y, ‖𝓕⁻ σ y‖) * M) := by
  have h0 : 0 ≤ (∫ y, ‖𝓕⁻ ρ y‖) * (‖B‖ * (∫ y, ‖𝓕⁻ σ y‖) * M) :=
    mul_nonneg (integral_nonneg fun _ ↦ norm_nonneg _) (mul_nonneg (mul_nonneg
      (opNorm_nonneg B) (integral_nonneg fun _ ↦ norm_nonneg _)) ((norm_nonneg _).trans (hf 0)))
  -- Without completeness of `F₃` the left side vanishes by the integral convention.
  by_cases hF₃ : CompleteSpace F₃
  swap
  · rw [integral_of_not_completeSpace hF₃, norm_zero]
    exact h0
  set Z : 𝓢(E, F₃) := convolution B (𝓕⁻ σ) f
  have hZ : (fun ξ ↦ B (σ ξ) (𝓕 f ξ)) = ⇑(𝓕 Z : 𝓢(E, F₃)) :=
    funext fun ξ ↦ (fourier_convolution_fourierInv_apply B σ f ξ).symm
  have hZM (y : E) : ‖Z y‖ ≤ ‖B‖ * (∫ y, ‖𝓕⁻ σ y‖) * M := by
    have h := norm_fourierInv_bilin_fourier_apply_le B σ f hf y
    rwa [hZ, ← fourierInv_coe, fourierInv_fourier_eq] at h
  have hkey : ∫ ξ, 𝐞 ⟪ξ, x⟫ • ρ ξ • B (σ ξ) (𝓕 f ξ) =
      𝓕⁻ (fun ξ ↦ lsmul ℂ ℂ (ρ ξ) (𝓕 Z ξ)) x := by
    rw [Real.fourierInv_eq]
    refine integral_congr_ae (.of_forall fun ξ ↦ ?_)
    dsimp only
    rw [lsmul_apply, ← congrFun hZ ξ]
  rw [hkey]
  refine (norm_fourierInv_bilin_fourier_apply_le _ ρ Z hZM x).trans ?_
  rw [mul_assoc]
  exact mul_le_of_le_one_left h0 opNorm_lsmul_le

/-- **The Fourier transform of a product is the convolution of the Fourier transforms.** For
Schwartz functions `f`, `g` and a continuous bilinear map `B`, the Fourier transform of the
pointwise product `x ↦ B (f x) (g x)` is the convolution of `𝓕 f` and `𝓕 g`. -/
theorem fourier_pairing [CompleteSpace F₁] [CompleteSpace F₂] (B : F₁ →L[ℂ] F₂ →L[ℂ] F₃)
    (f : 𝓢(E, F₁)) (g : 𝓢(E, F₂)) :
    𝓕 (pairing B f g) = convolution B (𝓕 f) (𝓕 g) := by
  by_cases hF : CompleteSpace F₃
  · calc 𝓕 (pairing B f g) = 𝓕 (pairing B (𝓕⁻ (𝓕 f)) (𝓕⁻ (𝓕 g))) := by
          rw [fourierInv_fourier_eq, fourierInv_fourier_eq]
      _ = 𝓕 (𝓕⁻ (convolution B (𝓕 f) (𝓕 g))) := by rw [fourierInv_convolution]
      _ = convolution B (𝓕 f) (𝓕 g) := fourier_fourierInv_eq _
  · ext ξ
    simp [convolution_eq_zero_of_not_completeSpace_target _ hF,
      fourier_eq_zero_of_not_completeSpace hF]

/-- The Fourier transform of a pointwise product of Schwartz functions, as an integral:
`𝓕 (B (f ·) (g ·)) ξ = ∫ t, B (𝓕 f t) (𝓕 g (ξ - t))`. -/
theorem fourier_pairing_apply [CompleteSpace F₁] [CompleteSpace F₂] (B : F₁ →L[ℂ] F₂ →L[ℂ] F₃)
    (f : 𝓢(E, F₁)) (g : 𝓢(E, F₂)) (ξ : E) :
    𝓕 (pairing B f g) ξ = ∫ t, B (𝓕 f t) (𝓕 g (ξ - t)) := by
  by_cases hF : CompleteSpace F₃
  · rw [fourier_pairing, convolution_apply, MeasureTheory.convolution_def]
  · simp [fourier_eq_zero_of_not_completeSpace hF, integral_of_not_completeSpace hF]

/-- The Fourier transform of the product of a Schwartz function `f` by a scalar Schwartz function
`φ` is the convolution `𝓕 (φ • f) ξ = ∫ t, 𝓕 φ t • 𝓕 f (ξ - t)`. -/
theorem fourier_smulLeftCLM_apply (φ : 𝓢(E, ℂ)) (f : 𝓢(E, F)) (ξ : E) :
    𝓕 (smulLeftCLM F (φ : E → ℂ) f) ξ = ∫ t, 𝓕 φ t • 𝓕 f (ξ - t) := by
  by_cases hF : CompleteSpace F
  · have h : smulLeftCLM F (φ : E → ℂ) f = pairing (lsmul ℂ ℂ) φ f := by
      ext x
      simp [smulLeftCLM_apply_apply φ.hasTemperateGrowth]
    rw [h, fourier_pairing_apply]
    simp only [lsmul_apply]
  · simp [fourier_eq_zero_of_not_completeSpace hF]

/-- The convolution formula `SchwartzMap.fourier_smulLeftCLM_apply` with the frequency of `f` as
the integration variable: `𝓕 (φ • f) ξ = ∫ y, 𝓕 φ (ξ - y) • 𝓕 f y`. -/
theorem fourier_smulLeftCLM_apply_eq_integral_sub (φ : 𝓢(E, ℂ)) (f : 𝓢(E, F)) (ξ : E) :
    𝓕 (smulLeftCLM F (φ : E → ℂ) f) ξ = ∫ y, 𝓕 φ (ξ - y) • 𝓕 f y := by
  rw [fourier_smulLeftCLM_apply,
    ← integral_sub_left_eq_self (fun y ↦ 𝓕 φ (ξ - y) • 𝓕 f y) volume ξ]
  simp only [sub_sub_cancel]

end Bilinear

end SchwartzMap
