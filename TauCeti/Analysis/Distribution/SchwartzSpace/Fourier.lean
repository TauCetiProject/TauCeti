/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.FourierMultiplier
public import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.InnerProductSpace.PiL2
import TauCeti.Analysis.Distribution.SchwartzSpace.Basic
import TauCeti.Analysis.Distribution.TemperateGrowth
import TauCeti.Analysis.Fourier.ChangeOfVariables
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre

/-!
# Derivatives of Schwartz functions on the Fourier side

The Fourier transform turns the directional derivative `∂_v` on Schwartz space into
multiplication by `2πi ⟪ξ, v⟫` (Mathlib's `SchwartzMap.fourier_lineDerivOp_eq`). This file
records the pointwise consequences for second-order operators: with Mathlib's normalization of the
Fourier transform,

* `𝓕 (∂_v ∂_w u) ξ = -(2π)² ⟪ξ, v⟫ ⟪ξ, w⟫ 𝓕 u ξ`, and
* `𝓕 (Δ u) ξ = -(2π)² ‖ξ‖² 𝓕 u ξ`.

Since `∑ᵢ ∑ⱼ ⟪ξ, bᵢ⟫² ⟪ξ, bⱼ⟫² = ‖ξ‖⁴` for an orthonormal basis `b`, Plancherel's theorem turns
these into the identity

`∑ᵢ ∑ⱼ ‖∂_{bᵢ} ∂_{bⱼ} u‖²_{L²} = ‖Δ u‖²_{L²}`,

so the Laplacian controls the whole Hessian of `u` in `L²`. This is the `p = 2` case of the
Calderón–Zygmund estimate `‖D²u‖_{Lᵖ} ≤ C ‖Δu‖_{Lᵖ}`, and the `L²` input to elliptic regularity
for the Laplacian on `ℝⁿ`.

Fourier multipliers are additive in their symbol and commute with the Laplacian. For every
bilinear pairing `∫ M (f x) (h x)` of Schwartz functions, the transpose of the multiplier with
symbol `g` is the multiplier with the reflected symbol `g (-ξ)`; in particular a multiplier with an
even symbol, such as the Bessel potential `⟨ξ⟩ ^ s`, is symmetric.
The bilinear pairing of two Fourier transforms is the spatial pairing
with the reflection `R g (x) = g (-x)`, `∫ M (𝓕 f) (𝓕 g) = ∫ M f (R g)`, so an operator with
spatial transpose `S` has the Fourier-side transpose `R ∘ S ∘ R`.

For the inverse Fourier transform, iterating Mathlib's `SchwartzMap.fourierInv_lineDerivOp_eq`
gives `𝓕⁻ (∂_m^N σ) x = (-2πi ⟪x, m⟫) ^ N 𝓕⁻ σ x`, the inverse Fourier transform commutes with
postcomposition by a continuous linear map, and Mathlib's `norm_fourier_toL2_eq` gives
Plancherel's theorem `‖𝓕⁻ f‖_{L²} = ‖f‖_{L²}`.

The moments of a Schwartz function `K` are the derivatives of its Fourier transform at the origin,
`D^n (𝓕 K) 0 (m₁, …, mₙ) = (-2πi)ⁿ ∫ ⟪y, m₁⟫ ⋯ ⟪y, mₙ⟫ K y`. So if `D^n (𝓕 K) 0 = 0`, as happens
for every `n` when `𝓕 K` vanishes near the origin, then `K` annihilates every homogeneous
polynomial of degree `n`: `∫ K y • A (y, …, y) = 0` for every continuous `n`-multilinear map `A`.
This is the cancellation of the kernels of Littlewood–Paley blocks against Taylor polynomials.

For a Schwartz function `φ` and a nonzero `ε`, the *cut-off exponential*
`y ↦ exp(i ⟪y, ξ⟫) φ(ε y) v` is a Schwartz function whose Fourier transform
`|ε|⁻ⁿ 𝓕 φ (ε⁻¹ (ζ - ξ / 2π)) v` concentrates at the frequency `ξ / 2π` as `ε → 0`.

## Main declarations

* `SchwartzMap.fourierMultiplierCLM_add`: Fourier multipliers are additive in the symbol.
* `SchwartzMap.fourierMultiplierCLM_laplacian`: Fourier multipliers commute with the Laplacian.
* `SchwartzMap.fourierMultiplierCLM_one_add_norm_sq_rpow_fourierMultiplierCLM`: the Bessel
  multipliers of orders `t` and `t'` compose to the one of order `t + t'`.
* `SchwartzMap.fourierMultiplierCLM_one_add_norm_sq_rpow_neg_comp_fourierMultiplierCLM`: the Bessel
  multiplier of order `-t` inverts the one of order `t`.
* `SchwartzMap.fourierMultiplierCLM_one_add_norm_sq`: the Bessel multiplier of order `2` is
  `1 - (2π)⁻² Δ`.
* `SchwartzMap.fourierInv_apply_eq_fourier_neg`: `𝓕⁻ f x = 𝓕 f (-x)`.
* `SchwartzMap.integral_fourier_eq`: `∫ 𝓕 f = f 0`.
* `SchwartzMap.fourier_smulLeftCLM_fourierInv_eq`: `𝓕 (g • 𝓕⁻ f) = 𝓕⁻ (g (-·) • 𝓕 f)`.
* `SchwartzMap.integral_bilin_fourierMultiplierCLM_eq`: the transpose of a Fourier multiplier for
  bilinear pairings has the reflected symbol, `∫ M (T_g f) h = ∫ M f (T_{g (-·)} h)`.
* `SchwartzMap.integral_bilin_fourier_fourier`: bilinear Plancherel,
  `∫ M (𝓕 f ξ) (𝓕 g ξ) dξ = ∫ M (f x) (g (-x)) dx`.
* `SchwartzMap.integral_bilin_fourier_fourier_eq_of_forall_integral_bilin_eq`: an operator with
  transpose `S` for the spatial pairing has the transpose `R ∘ S ∘ R` for the Fourier-side pairing.

* `SchwartzMap.fourier_lineDerivOp_apply`: the Fourier transform of a directional derivative.
* `SchwartzMap.support_fourier_lineDerivOp_subset`,
  `SchwartzMap.support_fourier_iteratedLineDerivOp_subset`: differentiation does not enlarge the
  support of the Fourier transform.
* `SchwartzMap.fourier_compSubConstCLM_apply`, `SchwartzMap.support_fourier_compSubConstCLM`:
  translation multiplies the Fourier transform by a phase and keeps its support.
* `SchwartzMap.fourier_compCLMOfContinuousLinearEquiv_apply`: composition with a linear isometry
  equivalence commutes with the Fourier transform, `𝓕 (u ∘ A) ξ = 𝓕 u (A ξ)`.
* `SchwartzMap.fourier_lineDerivOp_lineDerivOp_apply`: the Fourier transform of a second
  directional derivative.
* `SchwartzMap.fourier_laplacian_apply`: the Fourier transform of the Laplacian.
* `SchwartzMap.fourierInv_iterate_lineDerivOp_apply`: the inverse Fourier transform of an
  iterated directional derivative, `𝓕⁻ (∂_m^N σ) x = (-2πi ⟪x, m⟫) ^ N 𝓕⁻ σ x`.
* `SchwartzMap.norm_fourierInv_iterate_lineDerivOp_sq`: its consequence for squared norms,
  `‖𝓕⁻ (∂_m^N σ) x‖² = (2π) ^ (2N) ⟪x, m⟫ ^ (2N) ‖𝓕⁻ σ x‖²`.
* `SchwartzMap.exists_seminorm_fourier_le_sum_seminorm`: each seminorm `‖ξ‖ ^ k ‖𝓕 g ξ‖` of the
  Fourier transform is bounded by finitely many Schwartz seminorms of `g`.
* `SchwartzMap.fourier_postcompCLM_apply`, `SchwartzMap.fourierInv_postcompCLM_apply`: the
  Fourier transform and its inverse commute with postcomposition by a continuous linear map.
* `SchwartzMap.norm_fourierInv_toL2_eq`: Plancherel's theorem for the inverse Fourier transform.
* `SchwartzMap.norm_toLp_fourierMultiplierCLM_eq`: Plancherel's theorem for Fourier multipliers,
  `‖𝓕⁻ (w • 𝓕 f)‖_{L²} = ‖w • 𝓕 f‖_{L²}`.
* `SchwartzMap.sum_sum_norm_toLp_lineDerivOp_lineDerivOp_sq`: the squared `L²` norms of the
  second derivatives along an orthonormal basis sum to the squared `L²` norm of the Laplacian.
* `SchwartzMap.iteratedFDeriv_fourier_zero_apply`: the moments of a Schwartz function are the
  derivatives of its Fourier transform at the origin.
* `SchwartzMap.integral_smul_apply_eq_zero_of_iteratedFDeriv_fourier_eq_zero`: a Schwartz function
  whose Fourier transform has vanishing `n`-th derivative at the origin annihilates the
  homogeneous polynomials of degree `n`.
* `SchwartzMap.cutoffExponential`: the cut-off exponential `y ↦ exp(i ⟪y, ξ⟫) φ(ε y) v`.
* `SchwartzMap.fourier_cutoffExponential`: its Fourier transform.
* `SchwartzMap.tendsto_integral_mul_cutoffExponential`: as `ε → 0`, it tends to the exponential
  `φ(0) exp(i ⟪y, ξ⟫)` as a tempered distribution, tested against integrable functions.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 9.4.
-/

public section

open scoped FourierTransform SchwartzMap RealInnerProductSpace Real Laplacian LineDeriv
open FourierTransform MeasureTheory

namespace SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F]

section NotCompleteSpace

variable [NormedSpace ℂ F]

/-- Into a space which is not complete, the Fourier transform of a Schwartz function is `0`: the
Bochner integral defining it is `0`. -/
theorem fourier_eq_zero_of_not_completeSpace (hF : ¬CompleteSpace F) (f : 𝓢(E, F)) : 𝓕 f = 0 := by
  ext ξ
  simp [fourier_coe, Real.fourier_eq, integral_of_not_completeSpace hF]

/-- Into a space which is not complete, the inverse Fourier transform of a Schwartz function is
`0`. -/
theorem fourierInv_eq_zero_of_not_completeSpace (hF : ¬CompleteSpace F) (f : 𝓢(E, F)) :
    𝓕⁻ f = 0 := by
  ext ξ
  simp [fourierInv_coe, Real.fourierInv_eq, integral_of_not_completeSpace hF]

end NotCompleteSpace

section FourierMultiplier

variable {𝕜 : Type*} [RCLike 𝕜] [NormedSpace ℂ F] [NormedSpace 𝕜 F]
  [SMulCommClass ℂ 𝕜 F]

/-- Fourier multipliers are additive in the symbol. -/
theorem fourierMultiplierCLM_add {g₁ g₂ : E → 𝕜} (hg₁ : g₁.HasTemperateGrowth)
    (hg₂ : g₂.HasTemperateGrowth) :
    fourierMultiplierCLM F (g₁ + g₂) = fourierMultiplierCLM F g₁ + fourierMultiplierCLM F g₂ := by
  ext1 f
  simp [fourierMultiplierCLM_apply, smulLeftCLM_add hg₁ hg₂]

/-- The inverse Fourier transform of a Schwartz function is its Fourier transform at the reflected
point. This is the Schwartz-space form of Mathlib's `Real.fourierInv_eq_fourier_neg`. -/
theorem fourierInv_apply_eq_fourier_neg (f : 𝓢(E, F)) (x : E) : 𝓕⁻ f x = 𝓕 f (-x) := by
  simp [fourierInv_apply_eq]

/-- The integral of the Fourier transform of a Schwartz function is its value at `0`, by Fourier
inversion. -/
theorem integral_fourier_eq [CompleteSpace F] (f : 𝓢(E, F)) : ∫ ξ, 𝓕 f ξ = f 0 := by
  have h : 𝓕⁻ (𝓕 f) = f := FourierTransform.fourierInv_fourier_eq f
  rw [← congrArg (· (0 : E)) h, fourierInv_coe, Real.fourierInv_eq]
  simp

/-- Exchanging the two Fourier transforms in `𝓕 (g • 𝓕⁻ f)` reflects the symbol: it is the
Fourier multiplier `𝓕⁻ (g (-ξ) • 𝓕 f)`. This is the identity behind the transpose of a Fourier
multiplier on tempered distributions, which Mathlib defines through the first form. -/
theorem fourier_smulLeftCLM_fourierInv_eq {g : E → ℂ} (hg : g.HasTemperateGrowth)
    (f : 𝓢(E, F)) :
    𝓕 (smulLeftCLM F g (𝓕⁻ f)) = fourierMultiplierCLM F (fun ξ ↦ g (-ξ)) f := by
  have hcomp : (smulLeftCLM F g (𝓕⁻ f) : E → F) =
      (smulLeftCLM F (fun ξ ↦ g (-ξ)) (𝓕 f) : E → F) ∘ LinearIsometryEquiv.neg ℝ := by
    ext y
    simp [smulLeftCLM_apply_apply hg, smulLeftCLM_apply_apply (g := fun ξ ↦ g (-ξ)) (by fun_prop),
      fourierInv_apply_eq_fourier_neg]
  ext x
  simp only [fourierMultiplierCLM_apply, fourierInv_apply_eq_fourier_neg]
  rw [fourier_coe, hcomp, Real.fourier_comp_linearIsometry]
  simp [fourier_coe]

variable [CompleteSpace F]

omit [CompleteSpace F] in
/-- Fourier multipliers commute with the Laplacian. Without completeness of the target or temperate
growth of the symbol the multiplier is zero. -/
theorem fourierMultiplierCLM_laplacian (g : E → 𝕜) (f : 𝓢(E, F)) :
    fourierMultiplierCLM F g (Δ f) = Δ (fourierMultiplierCLM F g f) := by
  by_cases hmain : CompleteSpace F ∧ g.HasTemperateGrowth
  · obtain ⟨hF, hg⟩ := hmain
    have hn : (fun ξ : E ↦ ‖ξ‖ ^ 2).HasTemperateGrowth := by fun_prop
    -- Commute the two symbols before transporting the identity through the Laplacian formula.
    have hcomm : fourierMultiplierCLM F g
        (fourierMultiplierCLM F (fun ξ : E ↦ ‖ξ‖ ^ 2) f) =
        fourierMultiplierCLM F (fun ξ : E ↦ ‖ξ‖ ^ 2) (fourierMultiplierCLM F g f) := by
      have hn𝕜 : (fun ξ : E ↦ RCLike.ofReal (K := 𝕜) (‖ξ‖ ^ 2)).HasTemperateGrowth := by
        fun_prop
      simp only [← fourierMultiplierCLM_ofReal 𝕜 hn]
      simp only [fourierMultiplierCLM_fourierMultiplierCLM_apply hg hn𝕜,
        fourierMultiplierCLM_fourierMultiplierCLM_apply hn𝕜 hg, mul_comm g]
    simpa only [laplacian_eq_fourierMultiplierCLM, ContinuousLinearMap.map_smul_of_tower]
      using congrArg (fun q ↦ -((2 * π) ^ 2) • q) hcomm
  · -- Without completeness or temperate growth, the Fourier multiplier is zero.
    have h : fourierMultiplierCLM F g = 0 := by
      ext1 φ
      by_cases hF : CompleteSpace F
      · have hg := fun hg ↦ hmain ⟨hF, hg⟩
        simp [fourierMultiplierCLM_apply, smulLeftCLM_of_not_hasTemperateGrowth hg]
      · simp [fourierMultiplierCLM_apply, fourier_eq_zero_of_not_completeSpace hF]
    simp only [h, zero_apply]
    exact (map_zero _).symm

/-- The Bessel multipliers compose additively on Schwartz functions: the Fourier multipliers with
symbols `⟨ξ⟩ ^ t'` and then `⟨ξ⟩ ^ t` give the one with symbol `⟨ξ⟩ ^ (t + t')`. -/
theorem fourierMultiplierCLM_one_add_norm_sq_rpow_fourierMultiplierCLM (t t' : ℝ) (ψ : 𝓢(E, F)) :
    fourierMultiplierCLM F (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (t / 2) : ℝ) : ℂ))
        (fourierMultiplierCLM F (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (t' / 2) : ℝ) : ℂ)) ψ) =
      fourierMultiplierCLM F (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ ((t + t') / 2) : ℝ) : ℂ)) ψ := by
  have h : ((fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (t / 2) : ℝ) : ℂ)) *
      fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (t' / 2) : ℝ) : ℂ)) =
      fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ ((t + t') / 2) : ℝ) : ℂ) := by
    ext x
    rw [Pi.mul_apply, ← Complex.ofReal_mul, TauCeti.one_add_norm_sq_rpow_add]
  rw [fourierMultiplierCLM_fourierMultiplierCLM_apply (by fun_prop) (by fun_prop), h]

/-- The Bessel multiplier of order `-t`, with symbol `⟨ξ⟩ ^ (-t)`, inverts the one of order `t` on
Schwartz functions. -/
theorem fourierMultiplierCLM_one_add_norm_sq_rpow_neg_comp_fourierMultiplierCLM (t : ℝ) :
    fourierMultiplierCLM F (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (-t / 2) : ℝ) : ℂ)) ∘L
        fourierMultiplierCLM F (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (t / 2) : ℝ) : ℂ)) =
      ContinuousLinearMap.id ℂ 𝓢(E, F) := by
  ext1 ψ
  rw [ContinuousLinearMap.comp_apply,
    fourierMultiplierCLM_one_add_norm_sq_rpow_fourierMultiplierCLM]
  simp

/-- The Fourier multiplier with symbol `⟨ξ⟩² = 1 + ‖ξ‖²`, the Bessel multiplier of order `2`, is
the differential operator `1 - (2π)⁻² Δ` on Schwartz functions. -/
theorem fourierMultiplierCLM_one_add_norm_sq (ψ : 𝓢(E, F)) :
    fourierMultiplierCLM F (fun x : E ↦ ((1 + ‖x‖ ^ 2 : ℝ) : ℂ)) ψ =
      ψ - ((2 * Real.pi) ^ 2)⁻¹ • Δ ψ := by
  have h1 : (fun _ : E ↦ (1 : ℂ)).HasTemperateGrowth := by fun_prop
  have h2 : (fun x : E ↦ ((‖x‖ ^ 2 : ℝ) : ℂ)).HasTemperateGrowth := by fun_prop
  have hadd : fourierMultiplierCLM F (fun x : E ↦ ((1 + ‖x‖ ^ 2 : ℝ) : ℂ)) ψ =
      fourierMultiplierCLM F (fun _ : E ↦ (1 : ℂ)) ψ +
        fourierMultiplierCLM F (fun x : E ↦ ((‖x‖ ^ 2 : ℝ) : ℂ)) ψ := by
    have hw : (fun x : E ↦ ((1 + ‖x‖ ^ 2 : ℝ) : ℂ)) =
        (fun _ ↦ (1 : ℂ)) + fun x ↦ ((‖x‖ ^ 2 : ℝ) : ℂ) := by
      ext x
      simp
    rw [hw, fourierMultiplierCLM_add h1 h2, _root_.add_apply]
  have hreal : fourierMultiplierCLM F (fun x : E ↦ ((‖x‖ ^ 2 : ℝ) : ℂ)) ψ =
      fourierMultiplierCLM F (fun x : E ↦ ‖x‖ ^ 2) ψ :=
    fourierMultiplierCLM_ofReal ℂ (Function.hasTemperateGrowth_norm_sq E) ψ
  have hπ : ((2 * Real.pi) ^ 2)⁻¹ * -(2 * Real.pi) ^ 2 = -1 := by
    field_simp
  rw [laplacian_eq_fourierMultiplierCLM, smul_smul, hπ, hadd, fourierMultiplierCLM_const, hreal]
  simp [sub_eq_add_neg]

/-- The transpose of a Fourier multiplier for a bilinear pairing of Schwartz functions has the
reflected symbol: `∫ M (T_g f) h = ∫ M f (T_{g (-·)} h)`, where `T_g = 𝓕⁻ (g • 𝓕 ·)`. In
particular a multiplier with an even symbol is symmetric. -/
theorem integral_bilin_fourierMultiplierCLM_eq {G K : Type*} [NormedAddCommGroup G]
    [NormedSpace ℂ G] [CompleteSpace G] [NormedAddCommGroup K] [NormedSpace ℂ K] {g : E → ℂ}
    (hg : g.HasTemperateGrowth) (f : 𝓢(E, F)) (h : 𝓢(E, G)) (M : F →L[ℂ] G →L[ℂ] K) :
    ∫ x, M (fourierMultiplierCLM F g f x) (h x) =
      ∫ x, M (f x) (fourierMultiplierCLM G (fun ξ ↦ g (-ξ)) h x) := by
  -- Move both inverse Fourier transforms to the other factor; the two sides then differ by the
  -- reflection `ξ ↦ -ξ`.
  rw [fourierMultiplierCLM_apply, fourierMultiplierCLM_apply, integral_bilin_fourierInv_eq]
  conv_rhs => rw [← integral_bilin_fourierInv_eq]
  simp only [smulLeftCLM_apply_apply hg,
    smulLeftCLM_apply_apply (g := fun ξ ↦ g (-ξ)) (by fun_prop), map_smul,
    fourierInv_apply_eq_fourier_neg]
  rw [← integral_neg_eq_self]
  simp

end FourierMultiplier

section BilinearPlancherel

variable [NormedSpace ℂ F] [CompleteSpace F] {G K : Type*} [NormedAddCommGroup G]
  [NormedSpace ℂ G] [CompleteSpace G] [NormedAddCommGroup K] [NormedSpace ℂ K]

/-- **Bilinear Plancherel**: the bilinear pairing of the Fourier transforms of two Schwartz
functions is the pairing of the first with the reflection of the second,
`∫ M (𝓕 f ξ) (𝓕 g ξ) dξ = ∫ M (f x) (g (-x)) dx`. No complex conjugation is involved; the
reflection comes from `𝓕 (𝓕 g) x = g (-x)`. -/
theorem integral_bilin_fourier_fourier (f : 𝓢(E, F)) (g : 𝓢(E, G)) (M : F →L[ℂ] G →L[ℂ] K) :
    ∫ ξ, M (𝓕 f ξ) (𝓕 g ξ) = ∫ x, M (f x) (g (-x)) := by
  rw [integral_bilin_fourier_eq]
  congr 1 with x
  have h := fourierInv_apply_eq_fourier_neg (𝓕 g) (-x)
  rw [FourierTransform.fourierInv_fourier_eq, neg_neg] at h
  rw [← h]

/-- **Transposes for the Fourier-side pairing.** Write `R g (x) = g (-x)` for the reflection. If
`S` is the transpose of `T` for the spatial bilinear pairing, `∫ M (T f) g = ∫ M f (S g)`, then
`R ∘ S ∘ R` is its transpose for the Fourier-side pairing `(f, g) ↦ ∫ M (𝓕 f) (𝓕 g)`. -/
theorem integral_bilin_fourier_fourier_eq_of_forall_integral_bilin_eq (M : F →L[ℂ] G →L[ℂ] K)
    {T : 𝓢(E, F) → 𝓢(E, F)} {S : 𝓢(E, G) → 𝓢(E, G)}
    (hTS : ∀ f g, ∫ x, M (T f x) (g x) = ∫ x, M (f x) (S g x)) (f : 𝓢(E, F)) (g : 𝓢(E, G)) :
    ∫ ξ, M (𝓕 (T f) ξ) (𝓕 g ξ) = ∫ ξ, M (𝓕 f ξ) (𝓕 (compCLMOfContinuousLinearEquiv ℂ
      (LinearIsometryEquiv.neg ℝ (E := E)).toContinuousLinearEquiv
        (S (compCLMOfContinuousLinearEquiv ℂ
          (LinearIsometryEquiv.neg ℝ (E := E)).toContinuousLinearEquiv g))) ξ) := by
  rw [integral_bilin_fourier_fourier, integral_bilin_fourier_fourier]
  simpa using hTS f (compCLMOfContinuousLinearEquiv ℂ
    (LinearIsometryEquiv.neg ℝ (E := E)).toContinuousLinearEquiv g)

end BilinearPlancherel

section normed

variable [NormedSpace ℂ F]

/-- The Fourier transform of the directional derivative `∂_v u` of a Schwartz function is `𝓕 u`
multiplied by `2πi ⟪ξ, v⟫`. -/
theorem fourier_lineDerivOp_apply (u : 𝓢(E, F)) (v ξ : E) :
    𝓕 (∂_{v} u) ξ = ((2 * π * Complex.I) * ⟪ξ, v⟫) • 𝓕 u ξ := by
  have hv : (inner ℝ · v : E → ℝ).HasTemperateGrowth := by fun_prop
  rw [fourier_lineDerivOp_eq, smul_apply, smulLeftCLM_apply_apply hv, ← Complex.coe_smul,
    smul_smul]

/-- The Fourier transform of an iterated directional derivative is multiplication by the
product of the corresponding linear Fourier symbols. -/
theorem fourier_iteratedLineDerivOp_apply (u : 𝓢(E, F)) {k : ℕ} (v : Fin k → E) (ξ : E) :
    𝓕 (∂^{v} u) ξ = (∏ j, ((2 * π * Complex.I) * ⟪ξ, v j⟫)) • 𝓕 u ξ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [LineDeriv.iteratedLineDerivOp_succ_left, fourier_lineDerivOp_apply, ih,
      smul_smul, Fin.prod_univ_succ]
    simp only [Fin.tail_def]

/-- The frequencies of a directional derivative of a Schwartz function are among those of the
function. -/
theorem support_fourier_lineDerivOp_subset (u : 𝓢(E, F)) (v : E) :
    Function.support ⇑(𝓕 (∂_{v} u) : 𝓢(E, F)) ⊆ Function.support ⇑(𝓕 u : 𝓢(E, F)) := by
  intro ξ hξ h0
  rw [Function.mem_support, fourier_lineDerivOp_apply, h0, smul_zero] at hξ
  exact hξ rfl

/-- The frequencies of an iterated directional derivative of a Schwartz function are among those
of the function. -/
theorem support_fourier_iteratedLineDerivOp_subset (u : 𝓢(E, F)) {n : ℕ} (m : Fin n → E) :
    Function.support ⇑(𝓕 (∂^{m} u) : 𝓢(E, F)) ⊆ Function.support ⇑(𝓕 u : 𝓢(E, F)) := by
  induction n with
  | zero => rw [LineDeriv.iteratedLineDerivOp_fin_zero]
  | succ n ih =>
    rw [LineDeriv.iteratedLineDerivOp_succ_left]
    exact (support_fourier_lineDerivOp_subset _ _).trans (ih _)

/-- The Fourier transform turns translation into modulation:
`𝓕 (u (· - a)) ξ = 𝐞 (-⟪a, ξ⟫) • 𝓕 u ξ`. -/
theorem fourier_compSubConstCLM_apply (u : 𝓢(E, F)) (a ξ : E) :
    𝓕 (u.compSubConstCLM ℂ a) ξ = 𝐞 (-⟪a, ξ⟫) • 𝓕 u ξ := by
  rw [fourier_coe, fourier_coe, funext (compSubConstCLM_apply u a),
    TauCeti.fourier_comp_sub_const]

/-- Translating a Schwartz function does not change the support of its Fourier transform. -/
theorem support_fourier_compSubConstCLM (u : 𝓢(E, F)) (a : E) :
    Function.support ⇑(𝓕 (u.compSubConstCLM ℂ a) : 𝓢(E, F)) =
      Function.support ⇑(𝓕 u : 𝓢(E, F)) := by
  rw [fourier_coe, fourier_coe, funext (compSubConstCLM_apply u a),
    TauCeti.support_fourier_comp_sub_const]

/-- The Fourier transform commutes with composition by a linear isometry equivalence:
`𝓕 (u ∘ A) ξ = 𝓕 u (A ξ)`. -/
theorem fourier_compCLMOfContinuousLinearEquiv_apply {D : Type*} [NormedAddCommGroup D]
    [InnerProductSpace ℝ D] [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D]
    (A : D ≃ₗᵢ[ℝ] E) (u : 𝓢(E, F)) (ξ : D) :
    𝓕 (compCLMOfContinuousLinearEquiv ℂ A.toContinuousLinearEquiv u) ξ = 𝓕 u (A ξ) := by
  rw [fourier_coe, fourier_coe, compCLMOfContinuousLinearEquiv_apply]
  exact Real.fourier_comp_linearIsometry A u ξ

/-- The Fourier transform of the second directional derivative `∂_v ∂_w u` of a Schwartz function
is `𝓕 u` multiplied by `-(2π)² ⟪ξ, v⟫ ⟪ξ, w⟫`. -/
theorem fourier_lineDerivOp_lineDerivOp_apply (u : 𝓢(E, F)) (v w ξ : E) :
    𝓕 (∂_{v} (∂_{w} u)) ξ = (-(2 * π) ^ 2 * (⟪ξ, v⟫ * ⟪ξ, w⟫)) • 𝓕 u ξ := by
  have hv : (inner ℝ · v : E → ℝ).HasTemperateGrowth := by fun_prop
  have hw : (inner ℝ · w : E → ℝ).HasTemperateGrowth := by fun_prop
  rw [fourier_lineDerivOp_eq, smul_apply, smulLeftCLM_apply_apply hv, fourier_lineDerivOp_eq,
    smul_apply, smulLeftCLM_apply_apply hw]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
  congr 1
  push_cast
  linear_combination (2 * π : ℂ) ^ 2 * (⟪ξ, v⟫ : ℂ) * ⟪ξ, w⟫ * Complex.I_sq

/-- The Fourier transform of the Laplacian of a Schwartz function is `𝓕 u` multiplied by
`-(2π)² ‖ξ‖²`. -/
theorem fourier_laplacian_apply (u : 𝓢(E, F)) (ξ : E) :
    𝓕 (Δ u) ξ = (-(2 * π) ^ 2 * ‖ξ‖ ^ 2) • 𝓕 u ξ := by
  let b := stdOrthonormalBasis ℝ E
  rw [laplacian_eq_sum b, FourierTransform.fourier_sum, sum_apply]
  simp only [fourier_lineDerivOp_lineDerivOp_apply, ← Finset.sum_smul, ← Finset.mul_sum, ← sq,
    b.sum_sq_inner_left]

/-- Differentiating `N` times along `m` multiplies the inverse Fourier transform by
`(-2πi ⟪x, m⟫) ^ N`. -/
theorem fourierInv_iterate_lineDerivOp_apply (σ : 𝓢(E, F)) (m : E) (N : ℕ) (x : E) :
    𝓕⁻ ((∂_{m})^[N] σ) x = (-(2 * π * Complex.I) * ⟪x, m⟫) ^ N • 𝓕⁻ σ x := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hm : (inner ℝ · m : E → ℝ).HasTemperateGrowth := by fun_prop
    rw [Function.iterate_succ_apply', fourierInv_lineDerivOp_eq, smul_apply,
      smulLeftCLM_apply_apply hm, ih, pow_succ, ← Complex.coe_smul, smul_smul, smul_smul]
    congr 1
    ring

/-- Differentiating `N` times along `m` multiplies the squared norm of the inverse Fourier
transform by `(2π) ^ (2N) ⟪x, m⟫ ^ (2N)`. -/
theorem norm_fourierInv_iterate_lineDerivOp_sq (σ : 𝓢(E, F)) (m : E) (N : ℕ) (x : E) :
    ‖𝓕⁻ ((∂_{m})^[N] σ) x‖ ^ 2 = (2 * π) ^ (2 * N) * (⟪x, m⟫ ^ (2 * N) * ‖𝓕⁻ σ x‖ ^ 2) := by
  rw [fourierInv_iterate_lineDerivOp_apply, norm_smul, mul_pow, norm_pow, norm_mul, norm_neg,
    Complex.norm_real, Complex.norm_mul, Complex.norm_I, Complex.norm_mul, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
    ← (even_two_mul N).pow_abs ⟪x, m⟫]
  ring

/-- The Fourier transform is continuous on Schwartz space, so each seminorm
`‖ξ‖ ^ k ‖𝓕 g ξ‖` of `𝓕 g` is bounded by a constant times finitely many seminorms of `g`. -/
theorem exists_seminorm_fourier_le_sum_seminorm (k : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (c : ℝ), 0 ≤ c ∧ ∀ g : 𝓢(E, F),
      SchwartzMap.seminorm ℂ k 0 (𝓕 g) ≤ c * ∑ i ∈ s, SchwartzMap.seminorm ℂ i.1 i.2 g := by
  have hq : Continuous ((SchwartzMap.seminorm ℂ k 0).comp (fourierCLM ℂ 𝓢(E, F)).toLinearMap) :=
    ((schwartz_withSeminorms ℂ _ _).continuous_seminorm (k, 0)).comp (fourierCLM ℂ _).continuous
  obtain ⟨s, c, -, hc⟩ := Seminorm.bound_sum_of_continuous (schwartz_withSeminorms ℂ _ _) _ hq
  refine ⟨s, c, c.property, fun g ↦ (hc g).trans_eq ?_⟩
  simp [schwartzSeminormFamily, NNReal.smul_def]

/-- The Fourier transform of a Schwartz function commutes with postcomposition by a continuous
complex-linear map: `𝓕 (L ∘ f) = L ∘ 𝓕 f`. -/
@[simp]
theorem fourier_postcompCLM_apply {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    [CompleteSpace F] [CompleteSpace G] (L : F →L[ℂ] G) (f : 𝓢(E, F)) (x : E) :
    𝓕 (postcompCLM L f) x = L (𝓕 f x) := by
  rw [fourier_coe, fourier_coe, Real.fourier_eq, Real.fourier_eq, ← L.integral_comp_comm]
  · simp [Circle.smul_def]
  · refine f.integrable.norm.mono' ?_ (.of_forall fun v ↦ ?_)
    · exact ((Real.continuous_fourierChar.comp (continuous_id.inner continuous_const).neg).smul
        f.continuous).aestronglyMeasurable
    · simp [Circle.norm_smul]

/-- The inverse Fourier transform of a Schwartz function commutes with postcomposition by a
continuous complex-linear map: `𝓕⁻ (L ∘ f) = L ∘ 𝓕⁻ f`. -/
@[simp]
theorem fourierInv_postcompCLM_apply {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    [CompleteSpace F] [CompleteSpace G] (L : F →L[ℂ] G) (f : 𝓢(E, F)) (x : E) :
    𝓕⁻ (postcompCLM L f) x = L (𝓕⁻ f x) := by
  rw [fourierInv_coe, fourierInv_coe, Real.fourierInv_eq, Real.fourierInv_eq,
    ← L.integral_comp_comm]
  · simp [Circle.smul_def]
  · refine f.integrable.norm.mono' ?_ (.of_forall fun v ↦ ?_)
    · exact ((Real.continuous_fourierChar.comp (continuous_id.inner continuous_const)).smul
        f.continuous).aestronglyMeasurable
    · simp [Circle.norm_smul]

end normed

section CutoffExponential

variable [NormedSpace ℂ F]

/-- The *cut-off exponential* `y ↦ exp(i ⟪y, ξ⟫) φ(ε y) v` of the angular frequency `ξ`, a
Schwartz function for `ε ≠ 0`. As `ε → 0` it tends to the exponential `exp(i ⟪y, ξ⟫) φ(0) v`
locally uniformly, while its Fourier transform concentrates at `ξ / 2π`. For `ε = 0` it is `0`
by convention (`SchwartzMap.cutoffExponential_zero`). -/
noncomputable def cutoffExponential (φ : 𝓢(E, ℂ)) (ε : ℝ) (ξ : E) (v : F) : 𝓢(E, F) :=
  if hε : ε = 0 then 0 else
    postcompCLM (ContinuousLinearMap.toSpanSingleton ℂ v)
      (smulLeftCLM ℂ (fun y : E ↦ Complex.exp (⟪y, ξ⟫ * Complex.I))
        (compCLMOfContinuousLinearEquiv ℂ
          (ContinuousLinearEquiv.smulLeft (Units.mk0 ε hε) : E ≃L[ℝ] E) φ))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The cut-off exponential at scale `ε = 0` is `0` by convention. -/
@[simp]
theorem cutoffExponential_zero (φ : 𝓢(E, ℂ)) (ξ : E) (v : F) : φ.cutoffExponential 0 ξ v = 0 := by
  simp [cutoffExponential]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The values of a cut-off exponential: `y ↦ exp(i ⟪y, ξ⟫) φ(ε y) v` for `ε ≠ 0`. -/
@[simp]
theorem cutoffExponential_apply (φ : 𝓢(E, ℂ)) {ε : ℝ} (hε : ε ≠ 0) (ξ : E) (v : F) (y : E) :
    φ.cutoffExponential ε ξ v y = (Complex.exp (⟪y, ξ⟫ * Complex.I) * φ (ε • y)) • v := by
  simp [cutoffExponential, hε,
    smulLeftCLM_apply_apply (Function.hasTemperateGrowth_exp_inner_mul_I ξ)]

/-- **The Fourier transform of a cut-off exponential** is the rescaled Fourier transform of the
cutoff, translated to the frequency `ξ / 2π`:
`𝓕 (cutoffExponential φ ε ξ v) ζ = |ε|⁻ⁿ 𝓕 φ (ε⁻¹ (ζ - ξ / 2π)) v`. -/
theorem fourier_cutoffExponential [CompleteSpace F] (φ : 𝓢(E, ℂ)) {ε : ℝ} (hε : ε ≠ 0) (ξ : E)
    (v : F) (ζ : E) :
    𝓕 (φ.cutoffExponential ε ξ v) ζ =
      |ε ^ Module.finrank ℝ E|⁻¹ • (𝓕 φ (ε⁻¹ • (ζ - (2 * π)⁻¹ • ξ)) • v) := by
  -- The factor `exp(i ⟪y, ξ⟫)` is the character `𝐞 ⟪y, ξ / 2π⟫`, a modulation.
  have hmod : ⇑(φ.cutoffExponential ε ξ v) =
      fun y ↦ 𝐞 ⟪y, (2 * π)⁻¹ • ξ⟫ • (φ (ε • y) • v) := by
    ext y
    rw [cutoffExponential_apply φ hε, TauCeti.exp_inner_mul_I_eq_fourierChar, Circle.smul_def,
      smul_smul]
  rw [fourier_coe, hmod, TauCeti.fourier_fourierChar_smul,
    TauCeti.fourier_comp_smul (fun z ↦ φ z • v), TauCeti.fourier_smul_const, fourier_coe]

open scoped Topology in
/-- **The cut-off exponentials tend to the exponential as tempered distributions.** For an
integrable `g`, as `ε → 0` the pairing of `g` with the cut-off exponential
`y ↦ exp(i ⟪y, ξ⟫) φ(ε y)` tends to `φ(0) ∫ g(y) exp(i ⟪y, ξ⟫) dy`. -/
theorem tendsto_integral_mul_cutoffExponential (φ : 𝓢(E, ℂ)) {g : E → ℂ} (hg : Integrable g)
    (ξ : E) :
    Filter.Tendsto (fun ε ↦ ∫ y, g y * φ.cutoffExponential ε ξ (1 : ℂ) y) (𝓝[≠] 0)
      (𝓝 (φ 0 * ∫ y, g y * Complex.exp (⟪y, ξ⟫ * Complex.I))) := by
  rw [← integral_const_mul]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun y ↦ ‖g y‖ * SchwartzMap.seminorm ℂ 0 0 φ)
    (.of_forall fun ε ↦ hg.aestronglyMeasurable.mul
      (φ.cutoffExponential ε ξ 1).continuous.aestronglyMeasurable)
    (eventually_mem_nhdsWithin.mono fun ε hε ↦ .of_forall fun y ↦ ?_) (hg.norm.mul_const _)
    (.of_forall fun y ↦ ?_)
  · rw [cutoffExponential_apply φ hε, smul_eq_mul, mul_one, norm_mul, norm_mul,
      Complex.norm_exp_ofReal_mul_I, one_mul]
    exact mul_le_mul_of_nonneg_left (φ.norm_le_seminorm ℂ _) (norm_nonneg _)
  · have hc : Continuous fun ε : ℝ ↦ g y * (Complex.exp (⟪y, ξ⟫ * Complex.I) * φ (ε • y)) :=
      continuous_const.mul (continuous_const.mul (φ.continuous.comp (by fun_prop)))
    have h := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
    rw [zero_smul, show g y * (Complex.exp (⟪y, ξ⟫ * Complex.I) * φ 0) =
      φ 0 * (g y * Complex.exp (⟪y, ξ⟫ * Complex.I)) by ring] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [cutoffExponential_apply φ hε, smul_eq_mul, mul_one]

end CutoffExponential

section Moments

variable [NormedSpace ℂ F]

/-- **Moments are derivatives of the Fourier transform at the origin.** The `n`-th derivative of
the Fourier transform of a Schwartz function `K` at the origin is, up to the factor `(-2πi)ⁿ`, the
moment `∫ ⟪y, m₁⟫ ⋯ ⟪y, mₙ⟫ K y`. -/
theorem iteratedFDeriv_fourier_zero_apply (K : 𝓢(E, ℂ)) (n : ℕ) (m : Fin n → E) :
    iteratedFDeriv ℝ n (𝓕 (K : E → ℂ)) 0 m =
      (-(2 * π * Complex.I)) ^ n * ∫ y, ((∏ i, ⟪y, m i⟫ : ℝ) : ℂ) * K y := by
  have hint : Integrable (fun v ↦ VectorFourier.fourierPowSMulRight (innerSL ℝ) (K : E → ℂ) v n) :=
    ((K.integrable_pow_mul volume n).const_mul ((2 * π * ‖innerSL ℝ (E := E)‖) ^ n)).mono'
      (K.continuous.fourierPowSMulRight (innerSL ℝ) n).aestronglyMeasurable
      (Filter.Eventually.of_forall fun v ↦ by
        simpa [mul_assoc] using
          VectorFourier.norm_fourierPowSMulRight_le (innerSL ℝ) (K : E → ℂ) v n)
  rw [Real.iteratedFDeriv_fourier (N := n) (fun k _ ↦ K.integrable_pow_mul volume k)
    K.continuous.aestronglyMeasurable le_rfl, Real.fourier_eq]
  simp only [inner_zero_right, neg_zero, AddChar.map_zero_eq_one, one_smul]
  rw [ContinuousMultilinearMap.integral_apply hint, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
  simp only [VectorFourier.fourierPowSMulRight_apply, smul_eq_mul, Complex.real_smul,
    Complex.ofReal_prod]
  -- The factors are `innerSL ℝ y (m i)`, which is `⟪y, m i⟫` by definition; `innerSL_apply_apply`
  -- does not rewrite them because `innerSL ℝ` appears here as a map `E →L[ℝ] E →L[ℝ] ℝ`.
  congr 3 with i

/-- **Vanishing moments.** If the `n`-th derivative of the Fourier transform of a Schwartz function
`K` vanishes at the origin, then `K` annihilates every homogeneous polynomial of degree `n`:
`∫ K y • A (y, …, y) = 0` for every continuous `n`-multilinear map `A`. -/
theorem integral_smul_apply_eq_zero_of_iteratedFDeriv_fourier_eq_zero (K : 𝓢(E, ℂ)) {n : ℕ}
    (hK : iteratedFDeriv ℝ n (𝓕 (K : E → ℂ)) 0 = 0) (A : E [×n]→L[ℝ] F) :
    ∫ y, K y • A (fun _ ↦ y) = 0 := by
  classical
  -- Expand `A (y, …, y)` in an orthonormal basis `b`: it is a combination of the products
  -- `⟪b (r 1), y⟫ ⋯ ⟪b (r n), y⟫`, whose moments against `K` vanish.
  set b := stdOrthonormalBasis ℝ E
  have hexp (y : E) : K y • A (fun _ ↦ y) =
      ∑ r : Fin n → Fin (Module.finrank ℝ E),
        (((∏ i, ⟪y, b (r i)⟫ : ℝ) : ℂ) * K y) • A (fun i ↦ b (r i)) := by
    conv_lhs => rw [← funext fun _ : Fin n ↦ b.sum_repr' y, A.map_sum]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    rw [A.map_smul_univ (fun i ↦ ⟪b (r i), y⟫) (fun i ↦ b (r i)), ← Complex.coe_smul, smul_smul,
      mul_comm]
    simp_rw [real_inner_comm]
  have hmoment (r : Fin n → Fin (Module.finrank ℝ E)) :
      ∫ y, ((∏ i, ⟪y, b (r i)⟫ : ℝ) : ℂ) * K y = 0 := by
    have h := iteratedFDeriv_fourier_zero_apply K n (fun i ↦ b (r i))
    rw [hK, zero_apply, eq_comm, mul_eq_zero] at h
    exact h.resolve_left (pow_ne_zero _ (by simp [Real.pi_ne_zero]))
  have hint (r : Fin n → Fin (Module.finrank ℝ E)) :
      Integrable (fun y ↦ ((∏ i, ⟪y, b (r i)⟫ : ℝ) : ℂ) * K y) :=
    (K.integrable_pow_mul volume n).mono'
      ((Complex.continuous_ofReal.comp (continuous_finsetProd _ fun i _ ↦
        continuous_id.inner continuous_const)).mul K.continuous).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y ↦ by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Finset.abs_prod]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        calc ∏ i, |⟪y, b (r i)⟫| ≤ ∏ _i : Fin n, ‖y‖ := by
              gcongr with i
              exact (abs_real_inner_le_norm _ _).trans (by rw [b.orthonormal.1 (r i), mul_one])
          _ = ‖y‖ ^ n := by simp)
  by_cases hF : CompleteSpace F
  swap
  · exact integral_of_not_completeSpace hF
  simp_rw [hexp]
  rw [integral_finsetSum _ fun r _ ↦ (hint r).smul_const _]
  exact Finset.sum_eq_zero fun r _ ↦ by rw [integral_smul_const, hmoment, zero_smul]

end Moments

variable [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **Plancherel's theorem** for the inverse Fourier transform of Schwartz functions. -/
@[simp]
theorem norm_fourierInv_toL2_eq (f : 𝓢(E, F)) : ‖(𝓕⁻ f).toLp 2‖ = ‖f.toLp 2‖ := by
  rw [← norm_fourier_toL2_eq (𝓕⁻ f), FourierTransform.fourier_fourierInv_eq]

/-- **Plancherel for Fourier multipliers.** For a symbol `w` of temperate growth, the `L²` norm
of the Fourier multiplier `𝓕⁻ (w • 𝓕 f)` of a Schwartz function is the `L²` norm of `w • 𝓕 f`. -/
theorem norm_toLp_fourierMultiplierCLM_eq {w : E → ℂ} (hw : w.HasTemperateGrowth)
    (f : 𝓢(E, F)) :
    ‖(fourierMultiplierCLM F w f).toLp 2‖ = (eLpNorm (fun ξ ↦ w ξ • 𝓕 f ξ) 2 volume).toReal := by
  rw [← norm_fourier_toL2_eq, fourierMultiplierCLM_apply, fourier_fourierInv_eq, norm_toLp]
  congr 2
  ext ξ
  rw [smulLeftCLM_apply_apply hw]

/-- The Laplacian controls the Hessian in `L²`: for a Schwartz function `u` and an orthonormal
basis `b`, `∑ᵢ ∑ⱼ ‖∂_{bᵢ} ∂_{bⱼ} u‖²_{L²} = ‖Δ u‖²_{L²}`. -/
theorem sum_sum_norm_toLp_lineDerivOp_lineDerivOp_sq {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (u : 𝓢(E, F)) :
    ∑ i, ∑ j, ‖(∂_{b i} (∂_{b j} u)).toLp 2‖ ^ 2 = ‖(Δ u).toLp 2‖ ^ 2 := by
  -- By Plancherel, each squared `L²` norm is the integral of `‖𝓕 g‖²`; the pointwise identity
  -- `∑ᵢ ∑ⱼ ⟪ξ, bᵢ⟫² ⟪ξ, bⱼ⟫² = ‖ξ‖⁴` then matches the integrands.
  have hF (g : 𝓢(E, F)) : ‖g.toLp 2‖ ^ 2 = ∫ ξ, ‖𝓕 g ξ‖ ^ 2 := by
    rw [← Lp.norm_fourier_eq, toLp_fourier_eq, norm_toLp' two_ne_zero ENNReal.ofNat_ne_top,
      ENNReal.toReal_ofNat, ← Real.rpow_two,
      ← Real.rpow_mul (integral_nonneg fun _ ↦ by positivity)]
    norm_num
  have hint (g : 𝓢(E, F)) : Integrable (fun ξ ↦ ‖𝓕 g ξ‖ ^ 2) :=
    ((𝓕 g).memLp 2).integrable_norm_pow two_ne_zero
  simp only [hF]
  simp_rw [← integral_finsetSum _ fun _ _ ↦ hint _]
  rw [← integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hint _]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ ↦ ?_)
  have hsum : ∑ i, ∑ j, (⟪ξ, b i⟫ * ⟪ξ, b j⟫) ^ 2 = (‖ξ‖ ^ 2) ^ 2 := by
    simp_rw [mul_pow, ← Finset.mul_sum, ← Finset.sum_mul, b.sum_sq_inner_left, sq]
  simp only [fourier_lineDerivOp_lineDerivOp_apply, fourier_laplacian_apply, norm_smul,
    mul_pow, Real.norm_eq_abs, sq_abs, ← hsum, Finset.mul_sum, Finset.sum_mul]

end SchwartzMap
