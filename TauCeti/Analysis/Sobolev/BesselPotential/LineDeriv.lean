/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace
public import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Directional derivatives on `H^s` and the Plancherel identity for the norms

For a complex Hilbert space `F` and a real order `s`, the directional derivative `∂_m` maps
Mathlib's Bessel-potential space `H^{s+1}(E, F) = H^{s+1,2}(E, F)` boundedly to `H^s(E, F)`
(`TemperedDistribution.MemSobolev.lineDerivOp`). This file bundles it as a continuous linear map
`BesselPotentialSpace.lineDerivCLM m`, of norm at most `2π ‖m‖`, and proves the exact Plancherel
identity relating the norms of consecutive orders: for every orthonormal basis `(eᵢ)` of `E`,

`‖u‖²_{H^{s+1}} = ‖u‖²_{H^s} + (2π)⁻² ∑ᵢ ‖∂_{eᵢ} u‖²_{H^s}`

(`BesselPotentialSpace.norm_sq_eq_norm_inclusion_sq_add_sum_norm_lineDerivCLM_sq`).

At `s = 0`, where `H^0 = L²`, this reads `‖u‖²_{H^1} = ‖u‖²_{L²} + (2π)⁻² ∑ᵢ ‖∂ᵢ u‖²_{L²}`: the
`H^{1,2}` norm is equivalent to the norm `(‖u‖²_{L²} + ∑ᵢ ‖∂ᵢ u‖²_{L²})^{1/2}` of the
weak-derivative space `W^{1,2}`, with the explicit constants `1` and `(2π)⁻²` on the derivative
term. Applied at every order `s`, the identity relates consecutive orders of the whole
Bessel-potential scale. The factor `(2π)⁻²` comes from Mathlib's normalization of the Fourier
transform: the Bessel potential is the multiplier `(1 + ‖ξ‖²)^{s/2}`, not
`(1 + 4π² ‖ξ‖²)^{s/2}`, while `∂_m` has the symbol `2πi ⟪ξ, m⟫`.

## The argument

The `H^{s+1}` norm of `u` is the `L²` norm of `W = ⟨ξ⟩^{s+1} 𝓕 u`, where `⟨ξ⟩ = (1 + ‖ξ‖²)^{1/2}`
(`BesselPotentialSpace.norm_eq_of_smulLeftCLM_fourier_eq`). The weighted Fourier transforms of
`u` and `∂_m u` at order `s` are `⟨ξ⟩⁻¹ W` and `2πi ⟪ξ, m⟫ ⟨ξ⟩⁻¹ W`, so their squared norms are
`∫ ⟨ξ⟩⁻² ‖W‖²` and `∫ 4π² ⟪ξ, m⟫² ⟨ξ⟩⁻² ‖W‖²`. Parseval's identity `∑ᵢ ⟪ξ, eᵢ⟫² = ‖ξ‖²` in `E`
makes the weights add up to `⟨ξ⟩⁻² (1 + ‖ξ‖²) = 1`.

## Main declarations

* `BesselPotentialSpace.lineDerivCLM`: `∂_m : H^{s+1}(E, F) →L[ℂ] H^s(E, F)`.
* `BesselPotentialSpace.toDistr_lineDerivCLM`: it is the distributional derivative.
* `BesselPotentialSpace.lineDerivCLM_toBesselPotentialSpaceCLM`: on Schwartz functions it is the
  derivative of Schwartz functions.
* `BesselPotentialSpace.norm_lineDerivCLM_apply_le`: `‖∂_m u‖_{H^s} ≤ 2π ‖m‖ ‖u‖_{H^{s+1}}`.
* `BesselPotentialSpace.norm_sq_eq_norm_inclusion_sq_add_sum_norm_lineDerivCLM_sq`: the Plancherel
  identity for the norms of consecutive orders.

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

variable {s t : ℝ}

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The Bessel weights multiply: `⟨ξ⟩^a ⟨ξ⟩^b = ⟨ξ⟩^(a + b)`. -/
private theorem one_add_norm_sq_rpow_mul (a b : ℝ) :
    ((fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (a / 2) : ℝ) : ℂ)) *
        fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (b / 2) : ℝ) : ℂ)) =
      fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ ((a + b) / 2) : ℝ) : ℂ) := by
  ext x
  simp only [Pi.mul_apply, ← Complex.ofReal_mul,
    ← Real.rpow_add (by positivity : (0 : ℝ) < 1 + ‖x‖ ^ 2), add_div]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The squared Bessel weight of order `-1` is `(1 + ‖ξ‖²)⁻¹`. -/
private theorem sq_one_add_norm_sq_rpow_neg_one (x : E) :
    ((1 + ‖x‖ ^ 2) ^ ((-1 : ℝ) / 2)) ^ 2 = (1 + ‖x‖ ^ 2)⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num [Real.rpow_neg_one]

/-- The weighted Fourier transform of `u ∈ H^t` at order `t` is the Fourier transform of its `L²`
part `u.toLp`. -/
private theorem smulLeftCLM_fourier_toDistr_eq (u : H^{t}(E, F)) :
    smulLeftCLM F (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (t / 2) : ℝ) : ℂ)) (𝓕 u.toDistr) =
      (𝓕 u.toLp : Lp F 2 (volume : Measure E)) := by
  rw [← fourier_besselPotential_eq_smulLeftCLM_fourier_apply, u.bessel_toDistr_eq_toLp,
    Lp.fourier_toTemperedDistribution_eq]

/-- If the weighted Fourier transform of `v ∈ H^s` is `g` times the weighted Fourier transform of
`u ∈ H^t`, for a bounded multiplier `g` of temperate growth, then
`‖v‖² = ∫ ‖g ξ‖² ‖𝓕 u.toLp ξ‖² dξ`. -/
private theorem norm_sq_eq_integral_of_smulLeftCLM_fourier_eq (u : H^{t}(E, F))
    (v : H^{s}(E, F)) {g : E → ℂ} (hg : g.HasTemperateGrowth) {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C)
    (h : smulLeftCLM F (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) (𝓕 v.toDistr) =
      smulLeftCLM F g
        (smulLeftCLM F (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (t / 2) : ℝ) : ℂ)) (𝓕 u.toDistr))) :
    ‖v‖ ^ 2 = ∫ x, ‖g x‖ ^ 2 * ‖(𝓕 u.toLp : Lp F 2 (volume : Measure E)) x‖ ^ 2 := by
  set G₀ : Lp F 2 (volume : Measure E) := 𝓕 u.toLp
  have hmem : MemLp (fun x ↦ g x • G₀ x) 2 (volume : Measure E) :=
    (Lp.memLp G₀).of_le_mul (c := C) (hg.1.continuous.aestronglyMeasurable.smul
      (Lp.aestronglyMeasurable G₀)) (.of_forall fun x ↦ by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _))
  have hv : smulLeftCLM F (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) (𝓕 v.toDistr) =
      hmem.toLp := by
    rw [h, smulLeftCLM_fourier_toDistr_eq]
    ext φ
    rw [Lp.smulLeftCLM_toTemperedDistribution_apply hg, Lp.toTemperedDistribution_apply]
    exact integral_congr_ae (hmem.coeFn_toLp.mono fun x hx ↦ by simp only [hx, G₀])
  rw [norm_eq_of_smulLeftCLM_fourier_eq hv, MemLp.norm_toLp_sq]
  simp only [norm_smul, mul_pow]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The symbol `2πi ⟪ξ, m⟫ ⟨ξ⟩⁻¹` of `∂_m : H^{s+1} → H^s` has temperate growth. -/
private theorem hasTemperateGrowth_lineDerivSymbol (m : E) :
    (fun x : E ↦ (2 * π * Complex.I) * ((inner ℝ x m : ℝ) : ℂ) *
      (((1 + ‖x‖ ^ 2) ^ ((-1 : ℝ) / 2) : ℝ) : ℂ)).HasTemperateGrowth := by
  fun_prop

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The squared modulus of the symbol of `∂_m : H^{s+1} → H^s` is
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
/-- The symbol of `∂_m : H^{s+1} → H^s` is bounded by `2π ‖m‖`. -/
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
/-- The weighted Fourier transform of `∂_m u` at order `s` is the symbol `2πi ⟪ξ, m⟫ ⟨ξ⟩⁻¹` times
the weighted Fourier transform of `u` at order `s + 1`. -/
private theorem smulLeftCLM_fourier_lineDerivOp_eq (m : E) (f : 𝓢'(E, F)) :
    smulLeftCLM F (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) (𝓕 (∂_{m} f)) =
      smulLeftCLM F (fun x : E ↦ (2 * π * Complex.I) * ((inner ℝ x m : ℝ) : ℂ) *
          (((1 + ‖x‖ ^ 2) ^ ((-1 : ℝ) / 2) : ℝ) : ℂ))
        (smulLeftCLM F (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ ((s + 1) / 2) : ℝ) : ℂ)) (𝓕 f)) := by
  have hm : (fun x : E ↦ ((inner ℝ x m : ℝ) : ℂ)).HasTemperateGrowth := by fun_prop
  have hsymb : ((fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ ((s + 1) / 2) : ℝ) : ℂ)) *
      fun x : E ↦ (2 * π * Complex.I) * ((inner ℝ x m : ℝ) : ℂ) *
        (((1 + ‖x‖ ^ 2) ^ ((-1 : ℝ) / 2) : ℝ) : ℂ)) =
      (2 * π * Complex.I) • ((fun x : E ↦ ((inner ℝ x m : ℝ) : ℂ)) *
        fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) := by
    ext x
    have hw : (1 + ‖x‖ ^ 2) ^ ((s + 1) / 2) * (1 + ‖x‖ ^ 2) ^ ((-1 : ℝ) / 2) =
        (1 + ‖x‖ ^ 2) ^ (s / 2) := by
      rw [← Real.rpow_add (by positivity)]
      congr 1
      ring
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    rw [← hw]
    push_cast
    ring
  rw [fourier_lineDerivOp_eq, map_smul, smulLeftCLM_smulLeftCLM_apply hm (by fun_prop),
    smulLeftCLM_smulLeftCLM_apply (by fun_prop) (hasTemperateGrowth_lineDerivSymbol m), hsymb,
    smulLeftCLM_smul (by fun_prop), FunLike.coe_smul, Pi.smul_apply]

/-- The `H^s` norm of `∂_m u` for `u ∈ H^{s+1}`, on the Fourier side. -/
private theorem norm_sq_lineDeriv_eq_integral (u : H^{s + 1}(E, F)) (m : E)
    (h : MemSobolev s 2 (∂_{m} u.toDistr)) :
    ‖h.toBesselPotentialSpace‖ ^ 2 = ∫ x, (2 * π) ^ 2 * inner ℝ x m ^ 2 * (1 + ‖x‖ ^ 2)⁻¹ *
      ‖(𝓕 u.toLp : Lp F 2 (volume : Measure E)) x‖ ^ 2 := by
  rw [norm_sq_eq_integral_of_smulLeftCLM_fourier_eq u _ (hasTemperateGrowth_lineDerivSymbol m)
    (norm_lineDerivSymbol_le m)]
  · simp only [norm_lineDerivSymbol_sq]
  · rw [MemSobolev.toBesselPotentialSpace_toDistr, smulLeftCLM_fourier_lineDerivOp_eq]

/-- `∂_m u ∈ H^s` for `u ∈ H^{s+1}`. -/
private theorem memSobolev_lineDerivOp (u : H^{s + 1}(E, F)) (m : E) :
    MemSobolev s 2 (∂_{m} u.toDistr) := by
  simpa only [add_sub_cancel_right] using u.memSobolev_toDistr.lineDerivOp (m := m)

variable (s) in
/-- The directional derivative `∂_m : H^{s+1}(E, F) →L[ℂ] H^s(E, F)`. It is the distributional
derivative (`BesselPotentialSpace.toDistr_lineDerivCLM`) and has norm at most `2π ‖m‖`
(`BesselPotentialSpace.norm_lineDerivCLM_le`). -/
def lineDerivCLM (m : E) : H^{s + 1}(E, F) →L[ℂ] H^{s}(E, F) :=
  LinearMap.mkContinuous
    { toFun u := (memSobolev_lineDerivOp u m).toBesselPotentialSpace
      map_add' u v := ext (by simp [LineDerivAdd.lineDerivOp_add])
      map_smul' c u := ext (by simp [LineDerivSMul.lineDerivOp_smul]) }
    (2 * π * ‖m‖) fun u ↦ by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp ?_
      rw [norm_sq_lineDeriv_eq_integral, mul_pow (2 * π * ‖m‖), ← norm_fourier_toLp_eq,
        ← Lp.integral_norm_sq_eq_norm_sq, ← integral_const_mul]
      refine integral_mono_of_nonneg (.of_forall fun x ↦ by positivity)
        (((Lp.memLp _).integrable_norm_pow two_ne_zero).const_mul _) (.of_forall fun x ↦ ?_)
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      rw [← norm_lineDerivSymbol_sq]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_lineDerivSymbol_le m x) 2

@[simp]
theorem toDistr_lineDerivCLM (m : E) (u : H^{s + 1}(E, F)) :
    (lineDerivCLM s m u).toDistr = ∂_{m} u.toDistr :=
  MemSobolev.toBesselPotentialSpace_toDistr _

/-- On Schwartz functions `∂_m : H^{s+1} → H^s` is the derivative of Schwartz functions. -/
@[simp]
theorem lineDerivCLM_toBesselPotentialSpaceCLM (m : E) (f : 𝓢(E, F)) :
    lineDerivCLM s m (SchwartzMap.toBesselPotentialSpaceCLM (s + 1) 2 f) =
      SchwartzMap.toBesselPotentialSpaceCLM s 2 (∂_{m} f) :=
  ext (by simp [lineDerivOp_toTemperedDistributionCLM_eq])

/-- `∂_m : H^{s+1} → H^s` has operator norm at most `2π ‖m‖`. -/
theorem norm_lineDerivCLM_le (m : E) :
    ‖(lineDerivCLM s m : H^{s + 1}(E, F) →L[ℂ] H^{s}(E, F))‖ ≤ 2 * π * ‖m‖ :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

/-- `‖∂_m u‖_{H^s} ≤ 2π ‖m‖ ‖u‖_{H^{s+1}}`. -/
theorem norm_lineDerivCLM_apply_le (m : E) (u : H^{s + 1}(E, F)) :
    ‖lineDerivCLM s m u‖ ≤ 2 * π * ‖m‖ * ‖u‖ :=
  (lineDerivCLM s m).le_of_opNorm_le (norm_lineDerivCLM_le m) u

/-- **The Plancherel identity for Bessel-potential norms.** For `u ∈ H^{s+1}(E, F)` and every
orthonormal basis `(eᵢ)` of `E`,

`‖u‖²_{H^{s+1}} = ‖u‖²_{H^s} + (2π)⁻² ∑ᵢ ‖∂_{eᵢ} u‖²_{H^s}`.

The factor `(2π)⁻²` comes from Mathlib's normalization of the Fourier transform, under which
`∂_m` has the symbol `2πi ⟪ξ, m⟫` while the Bessel potential has the symbol
`(1 + ‖ξ‖²)^{s/2}`. -/
theorem norm_sq_eq_norm_inclusion_sq_add_sum_norm_lineDerivCLM_sq {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (u : H^{s + 1}(E, F)) :
    ‖u‖ ^ 2 = ‖inclusion (le_add_of_nonneg_right zero_le_one) u‖ ^ 2 +
      (2 * π)⁻¹ ^ 2 * ∑ i, ‖lineDerivCLM s (b i) u‖ ^ 2 := by
  set G₀ : Lp F 2 (volume : Measure E) := 𝓕 u.toLp
  have hG₀ : Integrable (fun x ↦ ‖G₀ x‖ ^ 2) := (Lp.memLp G₀).integrable_norm_pow two_ne_zero
  -- The `H^s` norm of `u` on the Fourier side: the weight `⟨ξ⟩⁻¹` times `𝓕 u.toLp`.
  have hincl : ‖inclusion (le_add_of_nonneg_right zero_le_one) u‖ ^ 2 =
      ∫ x, (1 + ‖x‖ ^ 2)⁻¹ * ‖G₀ x‖ ^ 2 := by
    rw [norm_sq_eq_integral_of_smulLeftCLM_fourier_eq u _
      (g := fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ ((-1 : ℝ) / 2) : ℝ) : ℂ)) (C := 1) (by fun_prop)]
    · refine integral_congr_ae (.of_forall fun x ↦ ?_)
      simp only [Complex.norm_real, Real.norm_of_nonneg (by positivity :
        (0 : ℝ) ≤ (1 + ‖x‖ ^ 2) ^ ((-1 : ℝ) / 2)), sq_one_add_norm_sq_rpow_neg_one, G₀]
    · intro x
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by simp) (by norm_num)
    · rw [toDistr_inclusion, smulLeftCLM_smulLeftCLM_apply (by fun_prop) (by fun_prop),
        one_add_norm_sq_rpow_mul, add_neg_cancel_right]
  have hderiv (i : ι) : ‖lineDerivCLM s (b i) u‖ ^ 2 =
      ∫ x, (2 * π) ^ 2 * inner ℝ x (b i) ^ 2 * (1 + ‖x‖ ^ 2)⁻¹ * ‖G₀ x‖ ^ 2 :=
    norm_sq_lineDeriv_eq_integral u (b i) _
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
