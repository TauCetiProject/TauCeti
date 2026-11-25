/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.FourierWeight
public import TauCeti.Analysis.Sobolev.BesselPotential.Operator
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre

/-!
# Directional derivatives on `H^s` and the Plancherel identity for the norms

For a complex Hilbert space `F`, the directional derivative
`BesselPotentialSpace.lineDerivCLM : H^{r+1,p}(E, F) →L[ℂ] H^{r,p}(E, F)` at `p = 2`, between
Mathlib's Bessel-potential spaces `H^s(E, F) = H^{s,2}(E, F)`, has norm at most `2π ‖m‖`. This
file proves this bound and the exact Plancherel identity relating the norms of consecutive orders:
for `u ∈ H^{r+1}(E, F)` and every orthonormal basis `(eᵢ)` of `E`,

`‖u‖²_{H^{r+1}} = ‖u‖²_{H^r} + (2π)⁻² ∑ᵢ ‖∂_{eᵢ} u‖²_{H^r}`

(`BesselPotentialSpace.norm_sq_eq_norm_inclusion_sq_add_mul_sum_norm_lineDerivCLM_sq`).

At `r = 0`, where `H^0 = L²`, this reads `‖u‖²_{H^1} = ‖u‖²_{L²} + (2π)⁻² ∑ᵢ ‖∂ᵢ u‖²_{L²}`, the
form `BesselPotentialSpace.norm_sq_eq_norm_sq_add_mul_sum_norm_sq` of `Schwartz.lean` for elements
of `H^1` given by `L²` functions. Applied at every order `r`, the identity relates consecutive
orders of the whole Bessel-potential scale; on Schwartz functions it is
`SchwartzMap.norm_toBesselPotentialSpaceCLM_add_one_sq`. The factor `(2π)⁻²` comes from Mathlib's
normalization of the Fourier transform: the Bessel potential is the multiplier
`(1 + ‖ξ‖²)^{s/2}`, not `(1 + 4π² ‖ξ‖²)^{s/2}`, while `∂_m` has the symbol `2πi ⟪ξ, m⟫`.

## The argument

On the Fourier side, with `𝓕 u` the function `BesselPotentialSpace.fourierFun u` and
`⟨ξ⟩ = (1 + ‖ξ‖²)^{1/2}`, Plancherel's formula
`BesselPotentialSpace.norm_sq_eq_integral_one_add_norm_sq_rpow_mul_norm_fourierFun_sq` gives
`‖u‖²_{H^{r+1}} = ∫ ⟨ξ⟩^{2r+2} ‖𝓕 u‖²`. The Fourier transforms of `u` and `∂_m u` regarded in `H^r`
are, volume-almost everywhere, `𝓕 u` and `2πi ⟪ξ, m⟫ 𝓕 u`
(`BesselPotentialSpace.fourierFun_inclusion`, `BesselPotentialSpace.fourierFun_lineDerivCLM`),
so their squared `H^r` norms are `∫ ⟨ξ⟩^{2r} ‖𝓕 u‖²` and `∫ 4π² ⟪ξ, m⟫² ⟨ξ⟩^{2r} ‖𝓕 u‖²`.
Parseval's identity `∑ᵢ ⟪ξ, eᵢ⟫² = ‖ξ‖²` in `E` makes the weights add up to
`⟨ξ⟩^{2r} (1 + ‖ξ‖²) = ⟨ξ⟩^{2r+2}`.

## Main declarations

* `TauCeti.besselLineDerivSymbol`: the normalized symbol `2πi ⟪ξ, m⟫ ⟨ξ⟩⁻¹` of
  `∂_m : H^{r+1} → H^r`, bounded by `2π ‖m‖` (`TauCeti.norm_besselLineDerivSymbol_le`). It acts
  between weighted Fourier transforms: it takes the order-`r + 1` weighted Fourier transform
  `⟨ξ⟩^{r+1} 𝓕 u` to the order-`r` weighted Fourier transform `⟨ξ⟩^r 𝓕 (∂_m u)`.
* `BesselPotentialSpace.coeFn_fourier_toLp_lineDerivCLM`: at `p = 2`, volume-almost everywhere,
  the Fourier transform of `(∂_m u).toLp` (the order-`r` weighted Fourier transform of `∂_m u`) is
  `besselLineDerivSymbol m` times the Fourier transform of `u.toLp` (the order-`r + 1` weighted
  Fourier transform of `u`); on tempered distributions this is
  `TemperedDistribution.smulLeftCLM_fourier_lineDerivOp_eq`. On the unweighted Fourier transforms
  `BesselPotentialSpace.fourierFun`, `∂_m` is volume-almost everywhere multiplication by
  `2πi ⟪ξ, m⟫` (`BesselPotentialSpace.fourierFun_lineDerivCLM`).
* `BesselPotentialSpace.norm_lineDerivCLM_le`, `BesselPotentialSpace.norm_lineDerivCLM_apply_le`:
  `‖∂_m u‖_{H^r} ≤ 2π ‖m‖ ‖u‖_{H^{r+1}}`.
* `BesselPotentialSpace.norm_sq_eq_norm_inclusion_sq_add_mul_sum_norm_lineDerivCLM_sq`: the
  Plancherel identity for the norms of consecutive orders.

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

namespace TauCeti

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The normalized Fourier symbol `2πi ⟪ξ, m⟫ ⟨ξ⟩⁻¹` of `∂_m : H^{r+1} → H^r`, where
`⟨ξ⟩ = (1 + ‖ξ‖²)^{1/2}`: the symbol `2πi ⟪ξ, m⟫` of `∂_m` times the Bessel weight of order
`-1`. It acts between weighted Fourier transforms, taking the order-`r + 1` weighted Fourier
transform `⟨ξ⟩^{r+1} 𝓕 u` to the order-`r` weighted Fourier transform `⟨ξ⟩^r 𝓕 (∂_m u)`; on the
unweighted Fourier transform `𝓕 u` the symbol of `∂_m` is `2πi ⟪ξ, m⟫`. -/
def besselLineDerivSymbol (m : E) : E → ℂ := fun x ↦
  (2 * π * Complex.I) * ((inner ℝ x m : ℝ) : ℂ) * (((1 + ‖x‖ ^ 2) ^ ((-1 : ℝ) / 2) : ℝ) : ℂ)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The defining equation of `besselLineDerivSymbol`. -/
theorem besselLineDerivSymbol_apply (m x : E) :
    besselLineDerivSymbol m x =
      (2 * π * Complex.I) * ((inner ℝ x m : ℝ) : ℂ) *
        (((1 + ‖x‖ ^ 2) ^ ((-1 : ℝ) / 2) : ℝ) : ℂ) :=
  (rfl)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The symbol of `∂_m : H^{r+1} → H^r` has temperate growth. -/
theorem hasTemperateGrowth_besselLineDerivSymbol (m : E) :
    (besselLineDerivSymbol m).HasTemperateGrowth := by
  unfold besselLineDerivSymbol
  fun_prop

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The squared modulus of the symbol of `∂_m : H^{r+1} → H^r` is
`4π² ⟪ξ, m⟫² (1 + ‖ξ‖²)⁻¹`. -/
theorem norm_besselLineDerivSymbol_sq (m x : E) :
    ‖besselLineDerivSymbol m x‖ ^ 2 = (2 * π) ^ 2 * inner ℝ x m ^ 2 * (1 + ‖x‖ ^ 2)⁻¹ := by
  -- The squared Bessel weight of order `-1` is `(1 + ‖ξ‖²)⁻¹`.
  have hw : ((1 + ‖x‖ ^ 2) ^ ((-1 : ℝ) / 2)) ^ 2 = (1 + ‖x‖ ^ 2)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num [Real.rpow_neg_one]
  simp [besselLineDerivSymbol_apply, mul_pow, hw, abs_of_pos Real.pi_pos]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The symbol of `∂_m : H^{r+1} → H^r` is bounded by `2π ‖m‖`. -/
theorem norm_besselLineDerivSymbol_le (m x : E) : ‖besselLineDerivSymbol m x‖ ≤ 2 * π * ‖m‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp ?_
  rw [norm_besselLineDerivSymbol_sq]
  have h₁ : inner ℝ x m ^ 2 ≤ ‖m‖ ^ 2 * (1 + ‖x‖ ^ 2) := by
    rw [← sq_abs]
    calc |inner ℝ x m| ^ 2 ≤ (‖x‖ * ‖m‖) ^ 2 := by
          gcongr
          exact abs_real_inner_le_norm x m
      _ ≤ ‖m‖ ^ 2 * (1 + ‖x‖ ^ 2) := by nlinarith [sq_nonneg ‖m‖]
  calc (2 * π) ^ 2 * inner ℝ x m ^ 2 * (1 + ‖x‖ ^ 2)⁻¹
      ≤ (2 * π) ^ 2 * (‖m‖ ^ 2 * (1 + ‖x‖ ^ 2)) * (1 + ‖x‖ ^ 2)⁻¹ := by gcongr
    _ = (2 * π * ‖m‖) ^ 2 := by field_simp

end TauCeti

namespace TemperedDistribution

/-- The weighted Fourier transform of `∂_m f` at order `r` is the symbol `2πi ⟪ξ, m⟫ ⟨ξ⟩⁻¹` times
the weighted Fourier transform of `f` at order `r + 1`. -/
theorem smulLeftCLM_fourier_lineDerivOp_eq {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    {r : ℝ} (f : 𝓢'(E, G)) (m : E) :
    smulLeftCLM G (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (r / 2) : ℝ) : ℂ)) (𝓕 (∂_{m} f)) =
      smulLeftCLM G (TauCeti.besselLineDerivSymbol m)
        (smulLeftCLM G (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ ((r + 1) / 2) : ℝ) : ℂ)) (𝓕 f)) := by
  have hm : (fun x : E ↦ ((inner ℝ x m : ℝ) : ℂ)).HasTemperateGrowth := by fun_prop
  -- The Bessel weight of order `r + 1` times the symbol is `2πi ⟪ξ, m⟫` times the weight of
  -- order `r`.
  have hsymb : (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ ((r + 1) / 2) : ℝ) : ℂ)) *
      TauCeti.besselLineDerivSymbol m =
      (2 * π * Complex.I) • ((fun x : E ↦ ((inner ℝ x m : ℝ) : ℂ)) *
        fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (r / 2) : ℝ) : ℂ)) := by
    ext x
    have hw := TauCeti.one_add_norm_sq_rpow_add x (r + 1) (-1)
    rw [add_neg_cancel_right] at hw
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, TauCeti.besselLineDerivSymbol_apply, hw,
      Complex.ofReal_mul]
    ring
  rw [fourier_lineDerivOp_eq, map_smul, smulLeftCLM_smulLeftCLM_apply hm (by fun_prop),
    smulLeftCLM_smulLeftCLM_apply (by fun_prop)
      (TauCeti.hasTemperateGrowth_besselLineDerivSymbol m),
    hsymb, smulLeftCLM_smul (by fun_prop), smul_apply]

end TemperedDistribution

namespace BesselPotentialSpace

variable {r : ℝ}

/-- On the weighted Fourier side, `∂_m : H^{r+1} → H^r` is multiplication by the normalized
symbol `2πi ⟪ξ, m⟫ ⟨ξ⟩⁻¹`: volume-almost everywhere, the Fourier transform of `(∂_m u).toLp`, the
order-`r` weighted Fourier transform of `∂_m u`, is `besselLineDerivSymbol m` times the Fourier
transform of `u.toLp`, the order-`r + 1` weighted Fourier transform of `u`. -/
theorem coeFn_fourier_toLp_lineDerivCLM (m : E) (u : H^{r + 1}(E, F)) :
    ⇑(𝓕 (lineDerivCLM ENNReal.one_lt_two ENNReal.ofNat_ne_top m u).toLp :
        Lp F 2 (volume : Measure E)) =ᵐ[volume] fun x ↦
      TauCeti.besselLineDerivSymbol m x • (𝓕 u.toLp : Lp F 2 (volume : Measure E)) x := by
  rw [← Lp.toTemperedDistribution_eq_smulLeftCLM_iff
      (TauCeti.hasTemperateGrowth_besselLineDerivSymbol m),
    toTemperedDistribution_fourier_toLp, toTemperedDistribution_fourier_toLp,
    toDistr_lineDerivCLM, smulLeftCLM_fourier_lineDerivOp_eq]

/-- At `p = 2`, `‖∂_m u‖_{H^r} ≤ 2π ‖m‖ ‖u‖_{H^{r+1}}`. -/
theorem norm_lineDerivCLM_apply_le (m : E) (u : H^{r + 1}(E, F)) :
    ‖lineDerivCLM ENNReal.one_lt_two ENNReal.ofNat_ne_top m u‖ ≤ 2 * π * ‖m‖ * ‖u‖ := by
  rw [← norm_fourier_toLp_eq, ← norm_fourier_toLp_eq u]
  exact Lp.norm_le_mul_norm_of_ae_le_mul ((coeFn_fourier_toLp_lineDerivCLM m u).mono fun x hx ↦ by
    rw [hx, norm_smul]
    exact mul_le_mul_of_nonneg_right (TauCeti.norm_besselLineDerivSymbol_le m x) (norm_nonneg _))

/-- At `p = 2`, `∂_m : H^{r+1} → H^r` has operator norm at most `2π ‖m‖`. -/
theorem norm_lineDerivCLM_le (m : E) :
    ‖(lineDerivCLM ENNReal.one_lt_two ENNReal.ofNat_ne_top m :
      H^{r + 1}(E, F) →L[ℂ] H^{r}(E, F))‖ ≤ 2 * π * ‖m‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) (norm_lineDerivCLM_apply_le m)

/-- On the Fourier side, `∂_m` is multiplication by its symbol `2πi ⟪ξ, m⟫`: for
`u ∈ H^{r+1}(E, F)`, the Fourier transform of `∂_m u ∈ H^r` is, volume-almost everywhere,
`2πi ⟪ξ, m⟫` times that of `u`. -/
theorem fourierFun_lineDerivCLM (m : E) (u : H^{r + 1}(E, F)) :
    (lineDerivCLM ENNReal.one_lt_two ENNReal.ofNat_ne_top m u).fourierFun =ᵐ[volume] fun x ↦
      ((2 * π * Complex.I) * ((inner ℝ x m : ℝ) : ℂ)) • u.fourierFun x := by
  filter_upwards [coeFn_fourier_toLp_lineDerivCLM m u] with x hx
  simp only [fourierFun_apply, hx, smul_smul, TauCeti.besselLineDerivSymbol_apply, neg_add,
    TauCeti.one_add_norm_sq_rpow_add]
  push_cast
  ring_nf

/-- **The Plancherel identity for Bessel-potential norms.** For `u ∈ H^{r+1}(E, F)` and every
orthonormal basis `(eᵢ)` of `E`,

`‖u‖²_{H^{r+1}} = ‖u‖²_{H^r} + (2π)⁻² ∑ᵢ ‖∂_{eᵢ} u‖²_{H^r}`.

The factor `(2π)⁻²` comes from Mathlib's normalization of the Fourier transform, under which
`∂_m` has the symbol `2πi ⟪ξ, m⟫` while the Bessel potential has the symbol
`(1 + ‖ξ‖²)^{s/2}`. -/
theorem norm_sq_eq_norm_inclusion_sq_add_mul_sum_norm_lineDerivCLM_sq {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (u : H^{r + 1}(E, F)) :
    ‖u‖ ^ 2 = ‖inclusion (r := r) (by linarith) u‖ ^ 2 +
      (2 * π)⁻¹ ^ 2 * ∑ i, ‖lineDerivCLM ENNReal.one_lt_two ENNReal.ofNat_ne_top (b i) u‖ ^ 2 := by
  have hint (v : H^{r}(E, F)) := integrable_one_add_norm_sq_rpow_mul_norm_fourierFun_sq v
  simp only [norm_sq_eq_integral_one_add_norm_sq_rpow_mul_norm_fourierFun_sq]
  rw [← integral_finsetSum _ fun i _ ↦ hint _, ← integral_const_mul,
    ← integral_add (hint _) ((integrable_finsetSum _ fun i _ ↦ hint _).const_mul _)]
  refine integral_congr_ae ?_
  filter_upwards [fourierFun_inclusion (r := r) (by linarith) u,
    Filter.eventually_all.2 fun i ↦ fourierFun_lineDerivCLM (b i) u] with x hincl hderiv
  have hterm (i : ι) :
      ‖((2 * π * Complex.I) * ((inner ℝ x (b i) : ℝ) : ℂ)) • u.fourierFun x‖ ^ 2 =
        (2 * π) ^ 2 * ‖u.fourierFun x‖ ^ 2 * inner ℝ x (b i) ^ 2 := by
    simp [norm_smul, mul_pow, abs_of_pos Real.pi_pos]
    ring
  -- Parseval's identity `∑ᵢ ⟪ξ, eᵢ⟫² = ‖ξ‖²` makes the weights add up to `(1 + ‖ξ‖²)^{r+1}`.
  simp only [hincl, hderiv, hterm, ← Finset.mul_sum, b.sum_sq_inner_left,
    Real.rpow_add_one (by positivity : 1 + ‖x‖ ^ 2 ≠ 0)]
  field_simp

end BesselPotentialSpace

