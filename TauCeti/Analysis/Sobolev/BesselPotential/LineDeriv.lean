/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace
public import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion
import TauCeti.Analysis.Distribution.SchwartzSpace.Basic
import TauCeti.Analysis.Distribution.TemperedDistribution.Deriv
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Directional derivatives on `H^s` and the Plancherel identity for the norms

For a complex Hilbert space `F` and real orders `r + 1 ≤ s`, the directional derivative `∂_m`
of a distribution in Mathlib's Bessel-potential space `H^s(E, F) = H^{s,2}(E, F)` lies in
`H^r(E, F)`
(`TemperedDistribution.MemSobolev.lineDerivOp`, with `TemperedDistribution.MemSobolev.mono`). This
file bundles it as a continuous linear map `BesselPotentialSpace.lineDerivCLM h m`, for
`h : r + 1 ≤ s`, of norm at most `2π ‖m‖`, and proves the exact Plancherel identity relating the
norms of consecutive orders: for `u ∈ H^{r+1}(E, F)` and every orthonormal basis `(eᵢ)` of `E`,

`‖u‖²_{H^{r+1}} = ‖u‖²_{H^r} + (2π)⁻² ∑ᵢ ‖∂_{eᵢ} u‖²_{H^r}`

(`BesselPotentialSpace.norm_sq_eq_norm_inclusion_sq_add_sum_norm_lineDerivCLM_sq`).

At `r = 0`, where `H^0 = L²`, this reads `‖u‖²_{H^1} = ‖u‖²_{L²} + (2π)⁻² ∑ᵢ ‖∂ᵢ u‖²_{L²}`: the
`H^{1,2}` norm is equivalent to the norm `(‖u‖²_{L²} + ∑ᵢ ‖∂ᵢ u‖²_{L²})^{1/2}` of the
weak-derivative space `W^{1,2}`, with the explicit constants `1` and `(2π)⁻²` on the derivative
term. Applied at every order `r`, the identity relates consecutive orders of the whole
Bessel-potential scale. The factor `(2π)⁻²` comes from Mathlib's normalization of the Fourier
transform: the Bessel potential is the multiplier `(1 + ‖ξ‖²)^{s/2}`, not
`(1 + 4π² ‖ξ‖²)^{s/2}`, while `∂_m` has the symbol `2πi ⟪ξ, m⟫`.

## The argument

The `H^{r+1}` norm of `u` is the `L²` norm of `W = ⟨ξ⟩^{r+1} 𝓕 u`, where `⟨ξ⟩ = (1 + ‖ξ‖²)^{1/2}`
(`BesselPotentialSpace.norm_eq_of_smulLeftCLM_fourier_eq`). The weighted Fourier transforms of
`u` and `∂_m u` at order `r` are `⟨ξ⟩⁻¹ W` and `2πi ⟪ξ, m⟫ ⟨ξ⟩⁻¹ W`, so their squared norms are
`∫ ⟨ξ⟩⁻² ‖W‖²` and `∫ 4π² ⟪ξ, m⟫² ⟨ξ⟩⁻² ‖W‖²`
(`BesselPotentialSpace.norm_inclusion_sq_eq_integral`,
`BesselPotentialSpace.norm_sq_eq_integral_of_smulLeftCLM_fourier_eq`). Parseval's identity
`∑ᵢ ⟪ξ, eᵢ⟫² = ‖ξ‖²` in `E` makes the weights add up to `⟨ξ⟩⁻² (1 + ‖ξ‖²) = 1`.

## Main declarations

* `BesselPotentialSpace.lineDerivCLM`: `∂_m : H^s(E, F) →L[ℂ] H^r(E, F)` for `r + 1 ≤ s`.
* `BesselPotentialSpace.toDistr_lineDerivCLM`: it is the distributional derivative.
* `BesselPotentialSpace.lineDerivCLM_toBesselPotentialSpaceCLM`: on Schwartz functions it is the
  derivative of Schwartz functions.
* `BesselPotentialSpace.lineDerivCLM_add`, `BesselPotentialSpace.lineDerivCLM_smul`, and
  relatives: it is linear in the direction `m`.
* `BesselPotentialSpace.inclusion_lineDerivCLM`, `BesselPotentialSpace.lineDerivCLM_inclusion`:
  it commutes with the inclusions `H^s ⊆ H^r`.
* `BesselPotentialSpace.lineDerivCLM_comm`: directional derivatives commute.
* `BesselPotentialSpace.norm_lineDerivCLM_apply_le`: `‖∂_m u‖_{H^r} ≤ 2π ‖m‖ ‖u‖_{H^s}`.
* `BesselPotentialSpace.norm_sq_eq_norm_inclusion_sq_add_sum_norm_lineDerivCLM_sq`: the Plancherel
  identity for the norms of consecutive orders.
* `SchwartzMap.norm_toBesselPotentialSpaceCLM_one_sq`: its case `r = 0` on Schwartz functions,
  `‖u‖²_{H¹} = ∫ ‖u‖² + (2π)⁻² ∑ᵢ ∫ ‖∂_{bᵢ} u‖²`.

## References

* M. Taylor, *Partial Differential Equations I*, Chapter 4, Section 1.
* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter V, §3.
-/

public section

noncomputable section

open MeasureTheory FourierTransform TemperedDistribution
open scoped ENNReal SchwartzMap BesselPotentialSpace LineDeriv Real

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

namespace BesselPotentialSpace

variable {r s t : ℝ}

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The squared Bessel weight of order `-1` is `(1 + ‖ξ‖²)⁻¹`. -/
private theorem sq_one_add_norm_sq_rpow_neg_one (x : E) :
    ((1 + ‖x‖ ^ 2) ^ ((-1 : ℝ) / 2)) ^ 2 = (1 + ‖x‖ ^ 2)⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num [Real.rpow_neg_one]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The symbol `2πi ⟪ξ, m⟫ ⟨ξ⟩⁻¹` of `∂_m : H^{r+1} → H^r` has temperate growth. -/
private theorem hasTemperateGrowth_lineDerivSymbol (m : E) :
    (fun x : E ↦ (2 * π * Complex.I) * ((inner ℝ x m : ℝ) : ℂ) *
      (((1 + ‖x‖ ^ 2) ^ ((-1 : ℝ) / 2) : ℝ) : ℂ)).HasTemperateGrowth := by
  fun_prop

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The squared modulus of the symbol of `∂_m : H^{r+1} → H^r` is
`4π² ⟪ξ, m⟫² (1 + ‖ξ‖²)⁻¹`. -/
private theorem norm_lineDerivSymbol_sq (m x : E) :
    ‖(2 * π * Complex.I) * ((inner ℝ x m : ℝ) : ℂ) *
        (((1 + ‖x‖ ^ 2) ^ ((-1 : ℝ) / 2) : ℝ) : ℂ)‖ ^ 2 =
      (2 * π) ^ 2 * inner ℝ x m ^ 2 * (1 + ‖x‖ ^ 2)⁻¹ := by
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg
    (by positivity : (0 : ℝ) ≤ (1 + ‖x‖ ^ 2) ^ ((-1 : ℝ) / 2)), mul_pow, mul_pow,
    sq_one_add_norm_sq_rpow_neg_one, Real.norm_eq_abs, sq_abs]
  simp [Complex.norm_I, abs_of_pos Real.pi_pos]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The symbol of `∂_m : H^{r+1} → H^r` is bounded by `2π ‖m‖`. -/
private theorem norm_lineDerivSymbol_le (m x : E) :
    ‖(2 * π * Complex.I) * ((inner ℝ x m : ℝ) : ℂ) *
        (((1 + ‖x‖ ^ 2) ^ ((-1 : ℝ) / 2) : ℝ) : ℂ)‖ ≤ 2 * π * ‖m‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp ?_
  rw [norm_lineDerivSymbol_sq]
  have h₁ : inner ℝ x m ^ 2 ≤ ‖m‖ ^ 2 * (1 + ‖x‖ ^ 2) := by
    rw [← sq_abs]
    calc |inner ℝ x m| ^ 2 ≤ (‖x‖ * ‖m‖) ^ 2 := by
          gcongr
          exact abs_real_inner_le_norm x m
      _ ≤ ‖m‖ ^ 2 * (1 + ‖x‖ ^ 2) := by nlinarith [sq_nonneg ‖m‖]
  calc (2 * π) ^ 2 * inner ℝ x m ^ 2 * (1 + ‖x‖ ^ 2)⁻¹
      ≤ (2 * π) ^ 2 * (‖m‖ ^ 2 * (1 + ‖x‖ ^ 2)) * (1 + ‖x‖ ^ 2)⁻¹ := by gcongr
    _ = (2 * π * ‖m‖) ^ 2 := by field_simp

omit [CompleteSpace F] in
/-- The weighted Fourier transform of `∂_m f` at order `r` is the symbol `2πi ⟪ξ, m⟫ ⟨ξ⟩⁻¹` times
the weighted Fourier transform of `f` at order `r + 1`. -/
private theorem smulLeftCLM_fourier_lineDerivOp_eq (m : E) (f : 𝓢'(E, F)) :
    smulLeftCLM F (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (r / 2) : ℝ) : ℂ)) (𝓕 (∂_{m} f)) =
      smulLeftCLM F (fun x : E ↦ (2 * π * Complex.I) * ((inner ℝ x m : ℝ) : ℂ) *
          (((1 + ‖x‖ ^ 2) ^ ((-1 : ℝ) / 2) : ℝ) : ℂ))
        (smulLeftCLM F (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ ((r + 1) / 2) : ℝ) : ℂ)) (𝓕 f)) := by
  have hm : (fun x : E ↦ ((inner ℝ x m : ℝ) : ℂ)).HasTemperateGrowth := by fun_prop
  have hw := smulLeftCLM_rpow_sub_smulLeftCLM r (r + 1) (𝓕 f)
  rw [show r - (r + 1) = -1 by ring] at hw
  have hsymb : (fun x : E ↦ (2 * π * Complex.I) * ((inner ℝ x m : ℝ) : ℂ) *
      (((1 + ‖x‖ ^ 2) ^ ((-1 : ℝ) / 2) : ℝ) : ℂ)) =
      (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ ((-1 : ℝ) / 2) : ℝ) : ℂ)) *
        (2 * π * Complex.I) • fun x : E ↦ ((inner ℝ x m : ℝ) : ℂ) := by
    ext x
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    ring
  have hcm : ((2 * π * Complex.I) • fun x : E ↦ ((inner ℝ x m : ℝ) : ℂ)).HasTemperateGrowth := by
    fun_prop
  rw [hsymb, ← smulLeftCLM_smulLeftCLM_apply (by fun_prop) hcm, hw,
    smulLeftCLM_smulLeftCLM_apply (by fun_prop) hcm, mul_smul_comm,
    smulLeftCLM_smul (by fun_prop), fourier_lineDerivOp_eq, map_smul,
    smulLeftCLM_smulLeftCLM_apply hm (by fun_prop), mul_comm (fun x : E ↦ ((inner ℝ x m : ℝ) : ℂ)),
    FunLike.coe_smul, Pi.smul_apply]

/-- `∂_m u ∈ H^r` for `u ∈ H^{r+1}`. -/
private theorem memSobolev_lineDerivOp (u : H^{r + 1}(E, F)) (m : E) :
    MemSobolev r 2 (∂_{m} u.toDistr) := by
  simpa only [add_sub_cancel_right] using u.memSobolev_toDistr.lineDerivOp (m := m)

/-- `‖∂_m u‖_{H^r} ≤ 2π ‖m‖ ‖u‖_{H^{r+1}}`. -/
private theorem norm_toBesselPotentialSpace_lineDerivOp_le (u : H^{r + 1}(E, F)) (m : E) :
    ‖(memSobolev_lineDerivOp u m).toBesselPotentialSpace‖ ≤ 2 * π * ‖m‖ * ‖u‖ :=
  norm_le_mul_norm_of_smulLeftCLM_fourier_eq (hasTemperateGrowth_lineDerivSymbol m)
    (norm_lineDerivSymbol_le m)
    (by rw [MemSobolev.toBesselPotentialSpace_toDistr, smulLeftCLM_fourier_lineDerivOp_eq])

/-- The directional derivative `∂_m : H^s(E, F) →L[ℂ] H^r(E, F)` for `r + 1 ≤ s`. It is the
distributional derivative (`BesselPotentialSpace.toDistr_lineDerivCLM`) and has norm at most
`2π ‖m‖` (`BesselPotentialSpace.norm_lineDerivCLM_le`). -/
def lineDerivCLM (h : r + 1 ≤ s) (m : E) : H^{s}(E, F) →L[ℂ] H^{r}(E, F) :=
  LinearMap.mkContinuous
    { toFun u := (memSobolev_lineDerivOp (inclusion h u) m).toBesselPotentialSpace
      map_add' u v := ext (by simp [LineDerivAdd.lineDerivOp_add])
      map_smul' c u := ext (by simp [LineDerivSMul.lineDerivOp_smul]) }
    (2 * π * ‖m‖) fun u ↦ by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      exact (norm_toBesselPotentialSpace_lineDerivOp_le _ m).trans
        (mul_le_mul_of_nonneg_left (norm_inclusion_apply_le h u) (by positivity))

/-- `∂_m : H^s → H^r` is the distributional derivative. -/
@[simp]
theorem toDistr_lineDerivCLM (h : r + 1 ≤ s) (m : E) (u : H^{s}(E, F)) :
    (lineDerivCLM h m u).toDistr = ∂_{m} u.toDistr :=
  (MemSobolev.toBesselPotentialSpace_toDistr _).trans (by rw [toDistr_inclusion])

/-- On Schwartz functions `∂_m : H^s → H^r` is the derivative of Schwartz functions. -/
@[simp]
theorem lineDerivCLM_toBesselPotentialSpaceCLM (h : r + 1 ≤ s) (m : E) (f : 𝓢(E, F)) :
    lineDerivCLM h m (SchwartzMap.toBesselPotentialSpaceCLM s 2 f) =
      SchwartzMap.toBesselPotentialSpaceCLM r 2 (∂_{m} f) :=
  ext (by simp [lineDerivOp_toTemperedDistributionCLM_eq])

/-- `∂_m : H^s → H^r` has operator norm at most `2π ‖m‖`. -/
theorem norm_lineDerivCLM_le (h : r + 1 ≤ s) (m : E) :
    ‖(lineDerivCLM h m : H^{s}(E, F) →L[ℂ] H^{r}(E, F))‖ ≤ 2 * π * ‖m‖ :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

/-- `‖∂_m u‖_{H^r} ≤ 2π ‖m‖ ‖u‖_{H^s}`. -/
theorem norm_lineDerivCLM_apply_le (h : r + 1 ≤ s) (m : E) (u : H^{s}(E, F)) :
    ‖lineDerivCLM h m u‖ ≤ 2 * π * ‖m‖ * ‖u‖ :=
  (lineDerivCLM h m).le_of_opNorm_le (norm_lineDerivCLM_le h m) u

/-- The derivative in the direction `0` vanishes. -/
@[simp]
theorem lineDerivCLM_zero (h : r + 1 ≤ s) :
    (lineDerivCLM h 0 : H^{s}(E, F) →L[ℂ] H^{r}(E, F)) = 0 :=
  ContinuousLinearMap.ext fun u ↦ ext (by simp)

/-- `∂_{m + n} = ∂_m + ∂_n`. -/
theorem lineDerivCLM_add (h : r + 1 ≤ s) (m n : E) :
    (lineDerivCLM h (m + n) : H^{s}(E, F) →L[ℂ] H^{r}(E, F)) =
      lineDerivCLM h m + lineDerivCLM h n :=
  ContinuousLinearMap.ext fun u ↦ ext (by simp [LineDerivAdd.lineDerivOp_left_add])

/-- `∂_{-m} = -∂_m`. -/
@[simp]
theorem lineDerivCLM_neg (h : r + 1 ≤ s) (m : E) :
    (lineDerivCLM h (-m) : H^{s}(E, F) →L[ℂ] H^{r}(E, F)) = -lineDerivCLM h m :=
  ContinuousLinearMap.ext fun u ↦ ext (by simp)

/-- `∂_{m - n} = ∂_m - ∂_n`. -/
theorem lineDerivCLM_sub (h : r + 1 ≤ s) (m n : E) :
    (lineDerivCLM h (m - n) : H^{s}(E, F) →L[ℂ] H^{r}(E, F)) =
      lineDerivCLM h m - lineDerivCLM h n := by
  rw [sub_eq_add_neg, lineDerivCLM_add, lineDerivCLM_neg, ← sub_eq_add_neg]

/-- `∂_{c • m} = c • ∂_m` for real `c`. -/
theorem lineDerivCLM_smul (h : r + 1 ≤ s) (c : ℝ) (m : E) :
    (lineDerivCLM h (c • m) : H^{s}(E, F) →L[ℂ] H^{r}(E, F)) = (c : ℂ) • lineDerivCLM h m :=
  ContinuousLinearMap.ext fun u ↦ ext (by
    rw [smul_apply, toDistr_smul, toDistr_lineDerivCLM, toDistr_lineDerivCLM,
      LineDerivLeftSMul.lineDerivOp_left_smul, Complex.coe_smul])

/-- Including the derivative into a lower order is taking the derivative into that order. -/
@[simp]
theorem inclusion_lineDerivCLM (h : r + 1 ≤ s) (h' : t ≤ r) (m : E) (u : H^{s}(E, F)) :
    inclusion h' (lineDerivCLM h m u) = lineDerivCLM (by linarith) m u :=
  ext (by simp)

/-- Differentiating after an inclusion is differentiating from the larger space. -/
@[simp]
theorem lineDerivCLM_inclusion (h : r + 1 ≤ t) (h' : t ≤ s) (m : E) (u : H^{s}(E, F)) :
    lineDerivCLM h m (inclusion h' u) = lineDerivCLM (h.trans h') m u :=
  ext (by simp)

/-- Directional derivatives commute: `∂_m ∂_n u = ∂_n ∂_m u`. -/
theorem lineDerivCLM_comm (h₁ : r + 1 ≤ t) (h₂ : t + 1 ≤ s) (m n : E) (u : H^{s}(E, F)) :
    lineDerivCLM h₁ m (lineDerivCLM h₂ n u) = lineDerivCLM h₁ n (lineDerivCLM h₂ m u) :=
  ext (by simp [lineDerivOp_comm _ m n])

/-- **The Plancherel identity for Bessel-potential norms.** For `u ∈ H^{r+1}(E, F)` and every
orthonormal basis `(eᵢ)` of `E`,

`‖u‖²_{H^{r+1}} = ‖u‖²_{H^r} + (2π)⁻² ∑ᵢ ‖∂_{eᵢ} u‖²_{H^r}`.

The factor `(2π)⁻²` comes from Mathlib's normalization of the Fourier transform, under which
`∂_m` has the symbol `2πi ⟪ξ, m⟫` while the Bessel potential has the symbol
`(1 + ‖ξ‖²)^{s/2}`. -/
theorem norm_sq_eq_norm_inclusion_sq_add_sum_norm_lineDerivCLM_sq {ι : Type*} [Fintype ι]
    (hrs : r + 1 = s) (b : OrthonormalBasis ι ℝ E) (u : H^{s}(E, F)) :
    ‖u‖ ^ 2 = ‖inclusion (r := r) (by linarith) u‖ ^ 2 +
      (2 * π)⁻¹ ^ 2 * ∑ i, ‖lineDerivCLM hrs.le (b i) u‖ ^ 2 := by
  subst hrs
  set G₀ : Lp F 2 (volume : Measure E) := 𝓕 u.toLp
  have hG₀ : Integrable (fun x ↦ ‖G₀ x‖ ^ 2) := (Lp.memLp G₀).integrable_norm_pow two_ne_zero
  -- The `H^r` norm of `u` on the Fourier side: the weight `⟨ξ⟩⁻²` times `‖𝓕 u.toLp‖²`.
  have hincl : ‖inclusion (le_add_of_nonneg_right zero_le_one) u‖ ^ 2 =
      ∫ x, (1 + ‖x‖ ^ 2)⁻¹ * ‖G₀ x‖ ^ 2 := by
    simp only [norm_inclusion_sq_eq_integral, sub_add_cancel_left, Real.rpow_neg_one, G₀]
  have hderiv (i : ι) : ‖lineDerivCLM le_rfl (b i) u‖ ^ 2 =
      ∫ x, (2 * π) ^ 2 * inner ℝ x (b i) ^ 2 * (1 + ‖x‖ ^ 2)⁻¹ * ‖G₀ x‖ ^ 2 := by
    rw [norm_sq_eq_integral_of_smulLeftCLM_fourier_eq (u := u)
      (hasTemperateGrowth_lineDerivSymbol (b i)) (norm_lineDerivSymbol_le (b i))]
    · simp only [norm_lineDerivSymbol_sq, G₀]
    · rw [toDistr_lineDerivCLM, smulLeftCLM_fourier_lineDerivOp_eq]
  have hint (i : ι) : Integrable fun x ↦
      (2 * π) ^ 2 * inner ℝ x (b i) ^ 2 * (1 + ‖x‖ ^ 2)⁻¹ * ‖G₀ x‖ ^ 2 := by
    refine (hG₀.const_mul ((2 * π * ‖b i‖) ^ 2)).mono' ?_ (.of_forall fun x ↦ ?_)
    · exact (Measurable.aestronglyMeasurable (by fun_prop)).mul hG₀.1
    · rw [← norm_lineDerivSymbol_sq, Real.norm_of_nonneg (by positivity)]
      gcongr
      exact norm_lineDerivSymbol_le (b i) x
  have hint₀ : Integrable fun x ↦ (1 + ‖x‖ ^ 2)⁻¹ * ‖G₀ x‖ ^ 2 := by
    refine hG₀.mono' ((Measurable.aestronglyMeasurable (by fun_prop)).mul hG₀.1)
      (.of_forall fun x ↦ ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact mul_le_of_le_one_left (by positivity) (inv_le_one_of_one_le₀ (by simp))
  rw [← norm_fourier_toLp_eq, ← Lp.integral_norm_sq_eq_norm_sq, hincl,
    Finset.sum_congr rfl fun i _ ↦ hderiv i,
    ← integral_finsetSum _ fun i _ ↦ hint i, ← integral_const_mul,
    ← integral_add hint₀ ((integrable_finsetSum _ fun i _ ↦ hint i).const_mul _)]
  refine integral_congr_ae (.of_forall fun x ↦ ?_)
  -- Parseval's identity `∑ᵢ ⟪ξ, eᵢ⟫² = ‖ξ‖²` makes the weights add up to `1`.
  have hsum : ∑ i, (2 * π) ^ 2 * inner ℝ x (b i) ^ 2 * (1 + ‖x‖ ^ 2)⁻¹ * ‖G₀ x‖ ^ 2 =
      (2 * π) ^ 2 * ‖x‖ ^ 2 * (1 + ‖x‖ ^ 2)⁻¹ * ‖G₀ x‖ ^ 2 := by
    rw [← b.sum_sq_inner_left x, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
  simp only [hsum, G₀]
  field_simp

end BesselPotentialSpace

namespace SchwartzMap

/-- **The `H¹` norm of a Schwartz function** in terms of its first derivatives: for an orthonormal
basis `b` of `E`,

`‖u‖²_{H¹} = ∫ ‖u‖² + (2π)⁻² ∑ᵢ ∫ ‖∂_{bᵢ} u‖²`.

This is the case `r = 0` of
`BesselPotentialSpace.norm_sq_eq_norm_inclusion_sq_add_sum_norm_lineDerivCLM_sq`. -/
theorem norm_toBesselPotentialSpaceCLM_one_sq {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (u : 𝓢(E, F)) :
    ‖toBesselPotentialSpaceCLM 1 2 u‖ ^ 2 =
      (∫ x, ‖u x‖ ^ 2) + (2 * π)⁻¹ ^ 2 * ∑ i, ∫ x, ‖∂_{b i} u x‖ ^ 2 := by
  rw [BesselPotentialSpace.norm_sq_eq_norm_inclusion_sq_add_sum_norm_lineDerivCLM_sq
    (r := 0) (by norm_num) b]
  simp only [BesselPotentialSpace.inclusion_toBesselPotentialSpaceCLM,
    BesselPotentialSpace.lineDerivCLM_toBesselPotentialSpaceCLM,
    ← BesselPotentialSpace.norm_toLp_eq, toLp_toBesselPotentialSpaceCLM_zero, norm_toLp_sq]

/-- The `H¹` norm of a Schwartz function bounds the `L²` norm of each of its first derivatives
along an orthonormal basis `b`: `(2π)⁻² ∫ ‖∂_{bᵢ} u‖² ≤ ‖u‖²_{H¹}`. -/
theorem inv_two_pi_sq_mul_integral_norm_lineDerivOp_sq_le {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (u : 𝓢(E, F)) (i : ι) :
    (2 * π)⁻¹ ^ 2 * ∫ x, ‖∂_{b i} u x‖ ^ 2 ≤ ‖toBesselPotentialSpaceCLM 1 2 u‖ ^ 2 := by
  rw [norm_toBesselPotentialSpaceCLM_one_sq b]
  have hi : ∫ x, ‖∂_{b i} u x‖ ^ 2 ≤ ∑ j, ∫ x, ‖∂_{b j} u x‖ ^ 2 :=
    Finset.single_le_sum (f := fun j ↦ ∫ x, ‖∂_{b j} u x‖ ^ 2)
      (fun j _ ↦ integral_nonneg fun _ ↦ by positivity) (Finset.mem_univ i)
  have h0 : 0 ≤ ∫ x, ‖u x‖ ^ 2 := integral_nonneg fun _ ↦ by positivity
  nlinarith [mul_le_mul_of_nonneg_left hi (by positivity : (0 : ℝ) ≤ (2 * π)⁻¹ ^ 2)]

end SchwartzMap
