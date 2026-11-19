/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.LpSpace
public import TauCeti.Analysis.Sobolev.BesselPotential.NormEquivalence
public import TauCeti.Analysis.Sobolev.BesselPotential.Schwartz
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import TauCeti.Analysis.Fourier.LpSpace
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding
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

(`BesselPotentialSpace.norm_sq_eq_norm_sq_add_mul_sum_norm_sq`; for Schwartz functions,
`SchwartzMap.norm_toBesselPotentialSpaceCLM_one_sq`), whereas the `W^{1,2}` norm is
`‖u‖²_{W^{1,2}} = ‖u‖²_{L²} + ‖∇u‖²_{L²}`, the integral of `1 + 4π²‖ξ‖²` against `‖𝓕u‖²`. So for
`u ∈ W^{1,2}(E)` (`TauCeti.Wkp.norm_toBesselPotentialSpace_sq`)

`‖u‖²_{H^{1,2}} = ‖u‖²_{L²} + (2π)⁻² ‖∇u‖²_{L²}`,
`‖u‖_{H^{1,2}} ≤ ‖u‖_{W^{1,2}} ≤ 2π ‖u‖_{H^{1,2}}`

(`TauCeti.Wkp.norm_toBesselPotentialSpace_le`,
`TauCeti.Wkp.norm_le_two_mul_pi_mul_norm_toBesselPotentialSpace`). The two norms are not equal: they
weigh the gradient differently, by `(2π)⁻²` and by `1`. The constants `1` and `2π` are the extreme
values of the ratio `((1 + 4π²‖ξ‖²) / (1 + ‖ξ‖²))^{1/2}` of the two symbols, approached at low and
at high frequencies.

The Fourier-side ingredients are `BesselPotentialSpace.fourier_toLp_ae_eq`, for the symbol of
`J^s`, and `MeasureTheory.Lp.fourier_ae_eq_of_lineDerivOp_eq`, for the symbol of `∂_m`.

## Main declarations

* `BesselPotentialSpace.norm_sq_eq_norm_sq_add_mul_sum_norm_sq`: Plancherel's identity
  `‖h‖²_{H^{1,2}} = ‖h‖²_{L²} + (2π)⁻² ∑ᵢ ‖∂ᵢh‖²_{L²}`.
* `SchwartzMap.norm_toBesselPotentialSpaceCLM_one_sq`: the same identity for a Schwartz function,
  `‖u‖²_{H¹} = ∫ ‖u‖² + (2π)⁻² ∑ᵢ ∫ ‖∂_{bᵢ} u‖²`.
* `SchwartzMap.inv_two_pi_sq_mul_integral_norm_lineDerivOp_sq_le`: the `H¹` norm of a Schwartz
  function bounds the `L²` norm of each of its first derivatives.
* `TauCeti.Wkp.norm_toBesselPotentialSpace_sq`: the same identity on `W^{1,2}(E)`.
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

namespace BesselPotentialSpace

/-- **Plancherel's identity for `H^{1,2}`.** Let `b` be an orthonormal basis of `E` and let
`h ∈ H^{1,2}(E, F)` be the `L²` function `g`, with derivatives `∂_{bᵢ} h` the `L²` functions `dᵢ`.
Then `‖h‖² = ‖g‖² + (2π)⁻² ∑ᵢ ‖dᵢ‖²`. The factor `(2π)⁻²` comes from Mathlib's normalisation of the
Fourier transform, under which `∂_{bᵢ}` has symbol `2πi⟪ξ, bᵢ⟫` and `J¹` has symbol
`(1 + ‖ξ‖²)^{1/2}`. -/
theorem norm_sq_eq_norm_sq_add_mul_sum_norm_sq {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (h : H^{1}(E, F)) {g : Lp F 2 (volume : Measure E)} (hg : h.toDistr = g)
    {d : ι → Lp F 2 (volume : Measure E)} (hd : ∀ i, ∂_{b i} h.toDistr = d i) :
    ‖h‖ ^ 2 = ‖g‖ ^ 2 + (2 * π)⁻¹ ^ 2 * ∑ i, ‖d i‖ ^ 2 := by
  have hv : 𝓕 h.toDistr = 𝓕 g := by rw [hg, Lp.fourier_toTemperedDistribution_eq]
  have hint (f : Lp F 2 (volume : Measure E)) : Integrable (fun ξ ↦ ‖f ξ‖ ^ 2) :=
    (Lp.memLp f).integrable_norm_pow two_ne_zero
  -- On the Fourier side, `‖𝓕 (J¹ h)‖² = (1 + ‖ξ‖²) ‖𝓕 g‖²` and `‖𝓕 dᵢ‖² = 4π² ⟪ξ, bᵢ⟫² ‖𝓕 g‖²`.
  have hpt : (fun ξ ↦ ‖𝓕 h.toLp ξ‖ ^ 2) =ᵐ[volume]
      fun ξ ↦ ‖𝓕 g ξ‖ ^ 2 + (2 * π)⁻¹ ^ 2 * ∑ i, ‖𝓕 (d i) ξ‖ ^ 2 := by
    filter_upwards [fourier_toLp_ae_eq h hv,
      ae_all_iff.2 fun i ↦ Lp.fourier_ae_eq_of_lineDerivOp_eq hv (hd i)] with ξ hξ hξd
    have hsum : ∑ i, ‖𝓕 (d i) ξ‖ ^ 2 = (2 * π) ^ 2 * ‖ξ‖ ^ 2 * ‖𝓕 g ξ‖ ^ 2 := by
      simp only [hξd, norm_smul, Complex.norm_mul, Complex.norm_ofNat, Complex.norm_real,
        Complex.norm_I, Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_one, mul_pow, sq_abs,
        ← Finset.sum_mul, ← Finset.mul_sum, b.sum_sq_inner_left]
    rw [hξ, hsum, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      ← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]
    field_simp
  rw [← norm_fourier_toLp_eq h, ← Lp.integral_norm_sq_eq_norm_sq, integral_congr_ae hpt,
    integral_add (hint _) ((integrable_finsetSum _ fun i _ ↦ hint _).const_mul _),
    integral_const_mul, integral_finsetSum _ fun i _ ↦ hint _]
  simp only [Lp.integral_norm_sq_eq_norm_sq, Lp.norm_fourier_eq]

end BesselPotentialSpace

namespace SchwartzMap

/-- **The `H¹` norm of a Schwartz function** in terms of its first derivatives: for an orthonormal
basis `b` of `E`,

`‖u‖²_{H¹} = ∫ ‖u‖² + (2π)⁻² ∑ᵢ ∫ ‖∂_{bᵢ} u‖²`.

The factor `(2π)⁻²` comes from the Fourier transform of `∂_v u` being `2πi ⟪ξ, v⟫ 𝓕 u`. -/
theorem norm_toBesselPotentialSpaceCLM_one_sq {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (u : 𝓢(E, F)) :
    ‖toBesselPotentialSpaceCLM 1 2 u‖ ^ 2 =
      (∫ x, ‖u x‖ ^ 2) + (2 * π)⁻¹ ^ 2 * ∑ i, ∫ x, ‖∂_{b i} u x‖ ^ 2 := by
  have hint (g : 𝓢(E, F)) : ∫ x, ‖g x‖ ^ 2 = ‖g.toLp 2 (volume : Measure E)‖ ^ 2 := by
    rw [← Lp.integral_norm_sq_eq_norm_sq]
    exact integral_congr_ae ((g.coeFn_toLp 2 volume).mono fun x hx ↦ by simp only [hx])
  simp only [hint]
  refine BesselPotentialSpace.norm_sq_eq_norm_sq_add_mul_sum_norm_sq b _ ?_ fun i ↦ ?_
  · rw [toDistr_toBesselPotentialSpaceCLM, Lp.toTemperedDistribution_toLp_eq]
  · rw [toDistr_toBesselPotentialSpaceCLM, Lp.toTemperedDistribution_toLp_eq]
    exact lineDerivOp_toTemperedDistributionCLM_eq u (b i)

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
  rw [norm_toBesselPotentialSpace_sq, norm_sq_eq_norm_value_sq_add_norm_iteratedGradient_sq]
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
    norm_sq_eq_norm_value_sq_add_norm_iteratedGradient_sq, mul_add, ← mul_assoc, h2, one_mul]
  have : 1 ≤ (2 * π) ^ 2 := one_le_pow₀ (by linarith [Real.two_le_pi])
  nlinarith [sq_nonneg ‖value 1 u‖]

end Wkp

end TauCeti
