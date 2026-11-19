/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.NormEquivalence
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import TauCeti.Analysis.Sobolev.BesselPotential.Schwartz
import TauCeti.Analysis.Sobolev.Wkp.LineDeriv
import TauCeti.MeasureTheory.Function.Lp.Basic
import TauCeti.MeasureTheory.Function.Lp.CastMeasure
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Measure.Restrict

/-!
# Plancherel's identity for the `H^{1,2}` and `W^{1,2}` norms

The map `TauCeti.Wkp.toBesselPotentialSpace` identifies Tau Ceti's weak-derivative Sobolev space
`W^{1,2}(E)` on the whole space with the elements of Mathlib's Bessel-potential space
`H^{1,2}(E, ℂ)` given by real functions, with equivalent norms. At the exponent `2` Plancherel's
theorem computes both norms on the Fourier side, which makes the equivalence explicit. With
Mathlib's normalisation of the Fourier transform, `e^{-2πi⟪x, ξ⟫}` in the exponent, the
directional derivative `∂_m` has symbol `2πi⟪ξ, m⟫`, while the Bessel potential `J¹` of
`H^{1,2}` has symbol `(1 + ‖ξ‖²)^{1/2}`. Hence, for `u ∈ H^{1,2}(E)` with derivatives `∂ᵢu` along
an orthonormal basis,

`‖u‖²_{H^{1,2}} = ∫ (1 + ‖ξ‖²) ‖𝓕u(ξ)‖² dξ = ‖u‖²_{L²} + (2π)⁻² ∑ᵢ ‖∂ᵢu‖²_{L²}`

(`BesselPotentialSpace.norm_sq_eq_norm_sq_add_mul_sum_norm_sq` in
`TauCeti.Analysis.Sobolev.BesselPotential.Schwartz`, which also proves the case of Schwartz
functions, `SchwartzMap.norm_toBesselPotentialSpaceCLM_one_sq`), whereas the `W^{1,2}` norm is
`‖u‖²_{W^{1,2}} = ‖u‖²_{L²} + ‖∇u‖²_{L²}`, the integral of `1 + 4π²‖ξ‖²` against `‖𝓕u‖²`. So for
`u ∈ W^{1,2}(E)` (`TauCeti.Wkp.norm_toBesselPotentialSpace_sq`)

`‖u‖²_{H^{1,2}} = ‖u‖²_{L²} + (2π)⁻² ‖∇u‖²_{L²}`,
`‖u‖_{H^{1,2}} ≤ ‖u‖_{W^{1,2}} ≤ 2π ‖u‖_{H^{1,2}}`

(`TauCeti.Wkp.norm_toBesselPotentialSpace_le`,
`TauCeti.Wkp.norm_le_two_mul_pi_mul_norm_toBesselPotentialSpace`). The two norms are not equal: they
weigh the gradient differently, by `(2π)⁻²` and by `1`. The constants `1` and `2π` are the extreme
values of the ratio `((1 + 4π²‖ξ‖²) / (1 + ‖ξ‖²))^{1/2}` of the two symbols, approached at low and
at high frequencies.

This file applies that identity to `W^{1,2}(E)`, whose weak derivatives along an orthonormal basis
are the components `⟪bᵢ, ∇u⟫` of the weak gradient.

## Main declarations

* `TauCeti.Wkp.norm_toBesselPotentialSpace_sq`: Plancherel's identity on `W^{1,2}(E)`.
* `TauCeti.Wkp.norm_toBesselPotentialSpace_le`,
  `TauCeti.Wkp.norm_le_two_mul_pi_mul_norm_toBesselPotentialSpace`: the explicit norm equivalence.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.8.4 (characterization of `H^k` by the
  Fourier transform).
* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter V, §3.
-/

public section

noncomputable section

open MeasureTheory TemperedDistribution FourierTransform TopologicalSpace
open scoped ENNReal NNReal LineDeriv SchwartzMap BesselPotentialSpace Real

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

namespace TauCeti

namespace Wkp

/-- **Plancherel's identity for `W^{1,2}`.** For `u ∈ W^{1,2}(E)`, the norm of `u` in Mathlib's
Bessel-potential space `H^{1,2}(E, ℂ)` is given by `‖u‖²_{H^{1,2}} = ‖u‖²_{L²} + (2π)⁻² ‖∇u‖²_{L²}`,
while `‖u‖²_{W^{1,2}} = ‖u‖²_{L²} + ‖∇u‖²_{L²}`. -/
theorem norm_toBesselPotentialSpace_sq (u : Wkp (volume : Measure E) ⊤ 2 1) :
    ‖toBesselPotentialSpace Nat.one_lt_ofNat ENNReal.ofNat_ne_top 1 u‖ ^ 2 =
      ‖value 1 u‖ ^ 2 + (2 * π)⁻¹ ^ 2 * ‖iteratedGradient 0 u‖ ^ 2 := by
  have hvol : (volume : Measure E).restrict ((⊤ : Opens E) : Set E) = volume :=
    Measure.restrict_coe_opens_top volume
  let b := stdOrthonormalBasis ℝ E
  -- The components `⟪bᵢ, ∇u⟫` of the weak gradient, which are the weak derivatives `∂_{bᵢ} u`.
  let D : Fin (Module.finrank ℝ E) → Wkp (volume : Measure E) ⊤ 2 0 :=
    fun i ↦ (innerSL ℝ (b i)).compLp (iteratedGradient 0 u)
  have hcast (f : Lp ℝ 2 ((volume : Measure E).restrict ((⊤ : Opens E) : Set E))) :
      (f : E → ℝ) =ᵐ[volume] castLpₗᵢ (𝕜 := ℝ) hvol f :=
    .of_forall fun x ↦ (coeFn_castLpₗᵢ hvol f x).symm
  have hnorm (f : Lp ℝ 2 ((volume : Measure E).restrict ((⊤ : Opens E) : Set E))) :
      ‖Complex.ofRealCLM.compLp (castLpₗᵢ (𝕜 := ℝ) hvol f)‖ = ‖f‖ := by
    rw [← LinearIsometryEquiv.norm_map (castLpₗᵢ (𝕜 := ℝ) hvol) f]
    have h := (Complex.ofRealLI.compLpₗᵢ 2 (volume : Measure E)).norm_map (castLpₗᵢ (𝕜 := ℝ) hvol f)
    rwa [← LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometry.toContinuousLinearMap_compLpₗᵢ] at h
  set T := toBesselPotentialSpace (E := E) Nat.one_lt_ofNat ENNReal.ofNat_ne_top 1 u
  have key := BesselPotentialSpace.norm_sq_eq_norm_sq_add_mul_sum_norm_sq b (T.copy 1 Nat.cast_one)
    (g := Complex.ofRealCLM.compLp (castLpₗᵢ (𝕜 := ℝ) hvol (value 1 u)))
    (d := fun i ↦ Complex.ofRealCLM.compLp (castLpₗᵢ (𝕜 := ℝ) hvol (value 0 (D i))))
    (by rw [BesselPotentialSpace.toDistr_copy _ Nat.cast_one]
        exact toDistr_toBesselPotentialSpace_of_ae_eq _ _ (hcast _))
    fun i ↦ by
      rw [BesselPotentialSpace.toDistr_copy _ Nat.cast_one,
        lineDerivOp_toDistr_toBesselPotentialSpace_of_hasWeakLineDerivOn _ _ Nat.one_lt_ofNat
          ENNReal.ofNat_ne_top (hasWeakLineDerivOn_value_innerSL_compLp (b i) u)]
      exact toDistr_toBesselPotentialSpace_of_ae_eq _ _ (hcast _)
  -- The squared norm of the gradient is the sum of the squared norms of its components.
  have hgrad : ‖iteratedGradient 0 u‖ ^ 2 = ∑ i, ‖value 0 (D i)‖ ^ 2 := by
    simp only [value_zero, ← Lp.integral_norm_sq_eq_norm_sq]
    rw [← integral_finsetSum _ fun i _ ↦ (Lp.memLp _).integrable_norm_pow two_ne_zero]
    refine integral_congr_ae ?_
    filter_upwards [ae_all_iff.2 fun i ↦ (innerSL ℝ (b i)).coeFn_compLp (iteratedGradient 0 u)]
      with x hx
    simp only [D, hx, innerSL_apply_apply, Real.norm_eq_abs, sq_abs, b.sum_sq_inner_right]
  rw [← BesselPotentialSpace.norm_toLp_eq, ← BesselPotentialSpace.toLp_copy T Nat.cast_one,
    BesselPotentialSpace.norm_toLp_eq, key, hgrad]
  simp only [hnorm]

/-- The `H^{1,2}` norm of `u ∈ W^{1,2}(E)` is at most its `W^{1,2}` norm. -/
theorem norm_toBesselPotentialSpace_le (u : Wkp (volume : Measure E) ⊤ 2 1) :
    ‖toBesselPotentialSpace Nat.one_lt_ofNat ENNReal.ofNat_ne_top 1 u‖ ≤ ‖u‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [norm_toBesselPotentialSpace_sq,
    norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq 0 u, lowerOrder_zero, value_one]
  have : (2 * π)⁻¹ ^ 2 ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (by
    linarith [Real.two_le_pi]))
  nlinarith [sq_nonneg ‖iteratedGradient 0 u‖]

/-- The `W^{1,2}` norm of `u ∈ W^{1,2}(E)` is at most `2π` times its `H^{1,2}` norm. -/
theorem norm_le_two_mul_pi_mul_norm_toBesselPotentialSpace (u : Wkp (volume : Measure E) ⊤ 2 1) :
    ‖u‖ ≤ 2 * π * ‖toBesselPotentialSpace Nat.one_lt_ofNat ENNReal.ofNat_ne_top 1 u‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 ?_
  have h2 : (2 * π) ^ 2 * (2 * π)⁻¹ ^ 2 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ (by positivity), one_pow]
  rw [mul_pow, norm_toBesselPotentialSpace_sq,
    norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq 0 u, lowerOrder_zero, value_one,
    mul_add, ← mul_assoc, h2, one_mul]
  have : 1 ≤ (2 * π) ^ 2 := one_le_pow₀ (by linarith [Real.two_le_pi])
  nlinarith [sq_nonneg ‖W1p.value u‖]

end Wkp

end TauCeti
