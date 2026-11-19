/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.LpSpace
public import TauCeti.Analysis.Sobolev.BesselPotential.NormEquivalence
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Sobolev.W1p.Morrey
import TauCeti.Analysis.Sobolev.Wkp.LineDeriv
import TauCeti.MeasureTheory.Function.Lp.CastMeasure
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Plancherel's identity for the `H^{1,2}` and `W^{1,2}` norms

Mathlib's Bessel-potential space `H^{1,2}(E)` and Tau Ceti's weak-derivative Sobolev space
`W^{1,2}(E)` on the whole space contain the same functions
(`TauCeti.Wkp.toBesselPotentialSpace`), with equivalent norms. At the exponent `2` Plancherel's
theorem computes both norms on the Fourier side, which makes the equivalence explicit. With
Mathlib's normalisation of the Fourier transform, `e^{-2πi⟪x, ξ⟫}` in the exponent, the
directional derivative `∂_m` has symbol `2πi⟪ξ, m⟫`, while the Bessel potential `J¹` of
`H^{1,2}` has symbol `(1 + ‖ξ‖²)^{1/2}`. Hence, for `u ∈ H^{1,2}(E)` with derivatives `∂ᵢu` along
an orthonormal basis,

`‖u‖²_{H^{1,2}} = ∫ (1 + ‖ξ‖²) ‖𝓕u(ξ)‖² dξ = ‖u‖²_{L²} + (2π)⁻² ∑ᵢ ‖∂ᵢu‖²_{L²}`

(`BesselPotentialSpace.norm_sq_eq_norm_sq_add_mul_sum_norm_sq`), whereas the `W^{1,2}` norm is
`‖u‖²_{W^{1,2}} = ‖u‖²_{L²} + ‖∇u‖²_{L²}`, the integral of `1 + 4π²‖ξ‖²` against `‖𝓕u‖²`. So for
`u ∈ W^{1,2}(E)` (`TauCeti.Wkp.norm_toBesselPotentialSpace_sq`)

`‖u‖²_{H^{1,2}} = ‖u‖²_{L²} + (2π)⁻² ‖∇u‖²_{L²}`,
`‖u‖_{H^{1,2}} ≤ ‖u‖_{W^{1,2}} ≤ 2π ‖u‖_{H^{1,2}}`

(`TauCeti.Wkp.norm_toBesselPotentialSpace_le`,
`TauCeti.Wkp.norm_le_two_mul_pi_mul_norm_toBesselPotentialSpace`). The two norms are not equal: they
weigh the gradient differently, by `(2π)⁻²` and by `1`. The constants `1` and `2π` are the extreme
values of the ratio `((1 + 4π²‖ξ‖²) / (1 + ‖ξ‖²))^{1/2}` of the two symbols, approached at low and
at high frequencies.

The comparison between the scales also detects non-membership. The indicator function of `[0, 1]`
is not in `H^{1,2}(ℝ)` (`TauCeti.not_memSobolev_one_indicator_Icc`): by the identification with
`W^{1,2}(ℝ)` it would have a continuous representative by Morrey's embedding, but it jumps at `0`.
Its distributional derivative `δ₀ - δ₁` is not a function.

## Main declarations

* `BesselPotentialSpace.fourier_toLp_ae_eq`: for `h ∈ H^{s,2}` whose tempered distribution has the
  Fourier transform `v ∈ L^q`, the `L²` Fourier transform of `J^s h` is `(1 + ‖ξ‖²)^{s/2} v`.
* `MeasureTheory.Lp.fourier_ae_eq_of_lineDerivOp_eq`: the Fourier transform of an `L²` derivative
  `∂_m f` is `2πi⟪ξ, m⟫ 𝓕f`.
* `BesselPotentialSpace.norm_sq_eq_norm_sq_add_mul_sum_norm_sq`: Plancherel's identity
  `‖h‖²_{H^{1,2}} = ‖h‖²_{L²} + (2π)⁻² ∑ᵢ ‖∂ᵢh‖²_{L²}`.
* `TauCeti.Wkp.norm_toBesselPotentialSpace_sq`: the same identity on `W^{1,2}(E)`.
* `TauCeti.Wkp.norm_toBesselPotentialSpace_le`,
  `TauCeti.Wkp.norm_le_two_mul_pi_mul_norm_toBesselPotentialSpace`: the explicit norm equivalence.
* `TauCeti.not_memSobolev_one_indicator_Icc`: `1_{[0,1]} ∉ H^{1,2}(ℝ)`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.8.4 (characterization of `H^k` by the
  Fourier transform).
* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter V, §3.
-/

public section

noncomputable section

open MeasureTheory TemperedDistribution FourierTransform TopologicalSpace Set
open scoped ENNReal NNReal LineDeriv SchwartzMap BesselPotentialSpace Real

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

namespace MeasureTheory.Lp

/-- **The Fourier transform of a derivative.** If a tempered distribution `f` has the `L²`
Fourier transform `v` and its derivative in the direction `m` is an `L²` function `d`, then
`𝓕 d(ξ) = 2πi⟪ξ, m⟫ v(ξ)` almost everywhere. -/
theorem fourier_ae_eq_of_lineDerivOp_eq {f : 𝓢'(E, F)} {v d : Lp F 2 (volume : Measure E)}
    (hv : 𝓕 f = v) {m : E} (hd : ∂_{m} f = d) :
    𝓕 d =ᵐ[volume] fun ξ ↦ (2 * π * Complex.I * inner ℝ ξ m) • v ξ := by
  rw [← toTemperedDistribution_eq_smulLeftCLM_iff (by fun_prop),
    ← fourier_toTemperedDistribution_eq, ← hd, fourier_lineDerivOp_eq, hv]
  exact (DFunLike.congr_fun (smulLeftCLM_smul (F := F) (g := fun ξ : E ↦ (inner ℝ ξ m : ℂ))
    (by fun_prop) (2 * π * Complex.I)) _).symm

end MeasureTheory.Lp

namespace BesselPotentialSpace

/-- **The Fourier transform of the Bessel potential.** If `h ∈ H^{s,2}` has a tempered distribution
whose Fourier transform is an `L^q` function `v`, for any `1 ≤ q ≤ ∞`, then the Fourier transform of
the `L²` function `J^s h` is `(1 + ‖ξ‖²)^{s/2} v(ξ)` almost everywhere. -/
theorem fourier_toLp_ae_eq {s : ℝ} (h : H^{s}(E, F)) {q : ℝ≥0∞} [Fact (1 ≤ q)]
    {v : Lp F q (volume : Measure E)} (hv : 𝓕 h.toDistr = v) :
    𝓕 h.toLp =ᵐ[volume] fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) • v ξ := by
  rw [← Lp.toTemperedDistribution_eq_smulLeftCLM_iff (by fun_prop),
    ← Lp.fourier_toTemperedDistribution_eq, ← h.bessel_toDistr_eq_toLp,
    fourier_besselPotential_eq_smulLeftCLM_fourier_apply, hv]

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
    integral_const_mul, integral_finsetSum _ fun i _ ↦ hint _, Lp.integral_norm_sq_eq_norm_sq,
    Lp.norm_fourier_eq]
  simp only [Lp.integral_norm_sq_eq_norm_sq, Lp.norm_fourier_eq]

end BesselPotentialSpace

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
    rw [← LinearIsometryEquiv.norm_map (castLpₗᵢ (𝕜 := ℝ) hvol) f, Lp.norm_def, Lp.norm_def]
    exact congrArg ENNReal.toReal (eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _)
      (Lp.aestronglyMeasurable _) ((Complex.ofRealCLM.coeFn_compLp _).mono fun x hx ↦ by
        rw [hx, Complex.ofRealCLM_apply, Complex.norm_real, coeFn_castLpₗᵢ]))
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
    BesselPotentialSpace.norm_toLp_eq, key, hnorm, hgrad]
  simp only [hnorm]

/-- The `H^{1,2}` norm of `u ∈ W^{1,2}(E)` is at most its `W^{1,2}` norm. -/
theorem norm_toBesselPotentialSpace_le (u : Wkp (volume : Measure E) ⊤ 2 1) :
    ‖toBesselPotentialSpace Nat.one_lt_ofNat ENNReal.ofNat_ne_top 1 u‖ ≤ ‖u‖ := by
  have hW := norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq 0 u
  rw [lowerOrder_zero, ← value_one] at hW
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [norm_toBesselPotentialSpace_sq, hW]
  have : (2 * π)⁻¹ ^ 2 ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (by
    linarith [Real.two_le_pi]))
  nlinarith [sq_nonneg ‖iteratedGradient 0 u‖]

/-- The `W^{1,2}` norm of `u ∈ W^{1,2}(E)` is at most `2π` times its `H^{1,2}` norm. -/
theorem norm_le_two_mul_pi_mul_norm_toBesselPotentialSpace (u : Wkp (volume : Measure E) ⊤ 2 1) :
    ‖u‖ ≤ 2 * π * ‖toBesselPotentialSpace Nat.one_lt_ofNat ENNReal.ofNat_ne_top 1 u‖ := by
  have hW := norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq 0 u
  rw [lowerOrder_zero, ← value_one] at hW
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 ?_
  have h2 : (2 * π) ^ 2 * (2 * π)⁻¹ ^ 2 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ (by positivity), one_pow]
  rw [mul_pow, norm_toBesselPotentialSpace_sq, hW, mul_add, ← mul_assoc, h2, one_mul]
  have : 1 ≤ (2 * π) ^ 2 := one_le_pow₀ (by linarith [Real.two_le_pi])
  nlinarith [sq_nonneg ‖value 1 u‖]

end Wkp

/-- **The indicator function of `[0, 1]` is not in `H^{1,2}(ℝ)`.** By Calderón's identification of
`H^{1,2}(ℝ)` with `W^{1,2}(ℝ)` and Morrey's embedding, every function in `H^{1,2}(ℝ)` has a
continuous representative, while the indicator function jumps at `0`. Its distributional derivative
`δ₀ - δ₁` is not a function. -/
theorem not_memSobolev_one_indicator_Icc :
    ¬ MemSobolev 1 2 (Complex.ofRealCLM.compLp (indicatorConstLp 2
      (measurableSet_Icc (a := (0 : ℝ)) (b := 1)) measure_Icc_lt_top.ne (1 : ℝ) :
        Lp ℝ 2 (volume : Measure ℝ)) : 𝓢'(ℝ, ℂ)) := by
  have key := Lp.memSobolev_natCast_iff_exists_wkp_value_eq (p := 2) Nat.one_lt_ofNat
    ENNReal.ofNat_ne_top 1 (indicatorConstLp 2 (measurableSet_Icc (a := (0 : ℝ)) (b := 1))
      measure_Icc_lt_top.ne (1 : ℝ))
  rw [Nat.cast_one] at key
  rw [key]
  rintro ⟨w, hw⟩
  have hp : (Module.finrank ℝ ℝ : ℝ≥0) < 2 := by simp
  have : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩
  -- By Morrey's embedding the indicator agrees almost everywhere with a continuous function `f`.
  set f := W1p.morreyRepresentative (p := 2) (Wkp.firstOrder 0 w) hp
  have hf : Continuous f := W1p.continuous_morreyRepresentative _ hp
  have hw' : (W1p.value (Wkp.firstOrder 0 w) : ℝ → ℝ) =ᵐ[volume]
      (Icc (0 : ℝ) 1).indicator fun _ ↦ (1 : ℝ) := by
    rw [Wkp.value_firstOrder]
    exact hw.trans indicatorConstLp_coeFn
  have hae : f =ᵐ[volume] (Icc (0 : ℝ) 1).indicator fun _ ↦ (1 : ℝ) :=
    (W1p.value_ae_eq_morreyRepresentative (Wkp.firstOrder 0 w) hp).symm.trans hw'
  -- So `f` is `1` on `(0, 1)` and `0` on `(-1, 0)`, and by continuity both at `0`.
  have h₁ : EqOn f (fun _ ↦ 1) (Ioo 0 1) := by
    refine Measure.eqOn_open_of_ae_eq (μ := volume) ?_ isOpen_Ioo hf.continuousOn continuousOn_const
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem measurableSet_Ioo] with x hx hxI
    rw [hx, indicator_of_mem (Ioo_subset_Icc_self hxI)]
  have h₀ : EqOn f (fun _ ↦ 0) (Ioo (-1) 0) := by
    refine Measure.eqOn_open_of_ae_eq (μ := volume) ?_ isOpen_Ioo hf.continuousOn continuousOn_const
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem measurableSet_Ioo] with x hx hxI
    rw [hx, indicator_of_notMem fun h : x ∈ Icc (0 : ℝ) 1 ↦ (not_le.2 hxI.2) h.1]
  have h₁0 : f 0 = 1 := h₁.closure hf continuous_const (by simp [closure_Ioo zero_ne_one])
  have h₀0 : f 0 = 0 :=
    h₀.closure hf continuous_const (by simp [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 0)])
  exact one_ne_zero (h₁0.symm.trans h₀0)

end TauCeti
