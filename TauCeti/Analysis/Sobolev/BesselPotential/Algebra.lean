/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Sobolev
import Mathlib.Analysis.MeanInequalitiesPow
import TauCeti.Analysis.Convolution.Young
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Fourier.Convolution
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding

/-!
# The Sobolev spaces `H^s(ℝⁿ)`, `s > n / 2`, are algebras

Let `E` be a finite-dimensional real inner product space of dimension `n` and let `s > n / 2`.
The pointwise product of two functions in the Bessel-potential space `H^s(E)` (Mathlib's
`TemperedDistribution.MemSobolev s 2`) is again in `H^s(E)`
(`TemperedDistribution.MemSobolev.mul`). Already the product of an `H^s` function with any `L²`
function is an `L²` function, since the first factor is bounded by the Sobolev embedding
(`TemperedDistribution.MemSobolev.memLp_mul`). The same holds for real-valued functions
(`TemperedDistribution.exists_mem_realSobolevSubmodule_ae_eq_mul`).

This is the basic input for nonlinear analysis on the scale `H^s`, `s > n / 2`: polynomial
expressions in the fields of a gauge theory map `H^s` to itself, and the maps `1 + h`,
`h ∈ H^s`, are closed under multiplication, so that they can form a gauge group.

## The Fourier argument

Write `⟨ξ⟩ = (1 + ‖ξ‖ ^ 2) ^ (1 / 2)`. A function `u ∈ L²` lies in `H^s` exactly when
`⟨ξ⟩ ^ s 𝓕u ∈ L²`, and for `s > n / 2` Cauchy–Schwarz against `⟨ξ⟩ ^ (-s) ∈ L²` makes `𝓕u` an
`L¹` function `v` (`TemperedDistribution.MemSobolev.fourier_memL1`). So `u = 𝓕⁻ v` almost
everywhere and the product of two such functions is

`u₁ u₂ = 𝓕⁻ v₁ · 𝓕⁻ v₂ = 𝓕⁻ (v₁ ⋆ v₂)`

(`Real.fourierInv_mul_convolution_eq`), with `v₁ ⋆ v₂ ∈ L¹`. Hence `𝓕(u₁ u₂) = v₁ ⋆ v₂` as
tempered distributions, and it remains to show `⟨ξ⟩ ^ s (v₁ ⋆ v₂) ∈ L²`. Peetre's inequality
`⟨ξ⟩ ^ s ≤ 2 ^ s (⟨η⟩ ^ s + ⟨ξ - η⟩ ^ s)` (`TauCeti.one_add_norm_add_sq_rpow_le`) gives

`⟨ξ⟩ ^ s |v₁ ⋆ v₂| ≤ 2 ^ s ((⟨·⟩ ^ s |v₁|) ⋆ |v₂| + |v₁| ⋆ (⟨·⟩ ^ s |v₂|))`,

and each convolution on the right is that of an `L²` function with an `L¹` function, which lies
in `L²` by Young's inequality (`MeasureTheory.lintegral_lconvolution_sq_le`). This weighted
convolution estimate is `TauCeti.memLp_one_add_norm_sq_rpow_mul_convolution`.

## Main declarations

* `TemperedDistribution.MemSobolev.fourier_memL1_and_memLp`: for `s > n / 2`, the Fourier
  transform of `u ∈ H^s` is an `L¹` function `v` with `⟨ξ⟩ ^ s v ∈ L²`.
* `TauCeti.memLp_one_add_norm_sq_rpow_mul_convolution`: the functions `v ∈ L¹` with
  `⟨ξ⟩ ^ s v ∈ L²` are closed under convolution.
* `TemperedDistribution.MemSobolev.memLp_mul`: the product of an `H^s` function, `s > n / 2`,
  with an `L²` function is an `L²` function.
* `TemperedDistribution.MemSobolev.mul`: the product of two `H^s` functions, `s > n / 2`, lies in
  `H^s`.
* `TemperedDistribution.exists_mem_realSobolevSubmodule_ae_eq_mul`: the real form of
  `TemperedDistribution.MemSobolev.mul`.

## References

* M. E. Taylor, *Partial Differential Equations III: Nonlinear Equations*, 2nd ed., Applied
  Mathematical Sciences 117, Springer, 2011, Chapter 13, Proposition 3.7 and its proof.
* R. A. Adams and J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Theorem 4.39.
-/

public section

noncomputable section

open MeasureTheory Module ContinuousLinearMap
open scoped FourierTransform SchwartzMap ENNReal Convolution

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E]

/-! ### Weighted convolution estimate -/

namespace TauCeti

omit [MeasurableSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- The norm of the complexified Bessel weight `(1 + ‖x‖ ^ 2) ^ (s / 2)`. -/
private theorem enorm_one_add_norm_sq_rpow (s : ℝ) (x : E) :
    ‖(((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)‖ₑ = ENNReal.ofReal ((1 + ‖x‖ ^ 2) ^ (s / 2)) := by
  rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (by positivity)]

/-- The pointwise form of the weighted convolution estimate: Peetre's inequality splits the
weight `(1 + ‖x‖ ^ 2) ^ (s / 2)` of `f ⋆ g` at `x` between the two factors. -/
private theorem enorm_one_add_norm_sq_rpow_mul_convolution_le {s : ℝ} (hs : 0 ≤ s)
    {f g : E → ℂ} (hwf : AEStronglyMeasurable (fun x => (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * f x))
    (hg : AEStronglyMeasurable g) (x : E) :
    ‖(((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * (f ⋆[mul ℂ ℂ] g) x‖ₑ ≤
      ENNReal.ofReal (2 ^ s) *
        (((fun y => ‖g y‖ₑ) ⋆ₗ fun y => ‖(((1 + ‖y‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * f y‖ₑ) x +
          ((fun y => ‖f y‖ₑ) ⋆ₗ fun y => ‖(((1 + ‖y‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * g y‖ₑ) x) := by
  set w : E → ℂ := fun x => (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) with hw_def
  set a : E → ℝ≥0∞ := fun y => ‖f y‖ₑ
  set b : E → ℝ≥0∞ := fun y => ‖g y‖ₑ
  set A : E → ℝ≥0∞ := fun y => ‖w y * f y‖ₑ
  set B : E → ℝ≥0∞ := fun y => ‖w y * g y‖ₑ
  set c : ℝ≥0∞ := ENNReal.ofReal (2 ^ s)
  have hcomm : (b ⋆ₗ A) x = ∫⁻ t, A t * b (x - t) := by
    rw [lconvolution_comm, lconvolution_def]
    simp only [neg_add_eq_sub]
  -- Peetre's inequality at `x = t + (x - t)`.
  have hweight : ∀ t, ‖w x‖ₑ * (a t * b (x - t)) ≤ c * (A t * b (x - t) + a t * B (x - t)) := by
    intro t
    have hp := one_add_norm_add_sq_rpow_le hs t (x - t)
    rw [add_sub_cancel] at hp
    have hle : ‖w x‖ₑ ≤ c * (‖w t‖ₑ + ‖w (x - t)‖ₑ) := by
      simp only [hw_def, enorm_one_add_norm_sq_rpow, c]
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal hp
    calc ‖w x‖ₑ * (a t * b (x - t))
        ≤ c * (‖w t‖ₑ + ‖w (x - t)‖ₑ) * (a t * b (x - t)) := by gcongr
      _ = c * (A t * b (x - t) + a t * B (x - t)) := by
        simp only [A, B, a, b, enorm_mul]
        ring
  calc ‖w x * (f ⋆[mul ℂ ℂ] g) x‖ₑ
      ≤ ‖w x‖ₑ * ∫⁻ t, a t * b (x - t) := by
        rw [enorm_mul, convolution_def]
        gcongr
        refine (enorm_integral_le_lintegral_enorm _).trans_eq ?_
        simp only [mul_apply', enorm_mul, a, b]
    _ = ∫⁻ t, ‖w x‖ₑ * (a t * b (x - t)) :=
        (lintegral_const_mul' ‖w x‖ₑ (fun t => a t * b (x - t)) enorm_ne_top).symm
    _ ≤ ∫⁻ t, c * (A t * b (x - t) + a t * B (x - t)) := lintegral_mono hweight
    _ = c * ((b ⋆ₗ A) x + (a ⋆ₗ B) x) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_add_left' (f := fun t => A t * b (x - t)) (hwf.enorm.mul
          (hg.enorm.comp_quasiMeasurePreserving
            (quasiMeasurePreserving_sub_left_of_right_invariant volume x))),
        hcomm, lconvolution_def]
      simp only [neg_add_eq_sub, c]

/-- **The weighted convolution estimate.** For `0 ≤ s`, if `f` and `g` are integrable and
`(1 + ‖ξ‖ ^ 2) ^ (s / 2) f` and `(1 + ‖ξ‖ ^ 2) ^ (s / 2) g` are square integrable, then so is
`(1 + ‖ξ‖ ^ 2) ^ (s / 2) (f ⋆ g)`. -/
theorem memLp_one_add_norm_sq_rpow_mul_convolution {s : ℝ} (hs : 0 ≤ s) {f g : E → ℂ}
    (hf : Integrable f) (hg : Integrable g)
    (hwf : MemLp (fun x => (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * f x) 2)
    (hwg : MemLp (fun x => (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * g x) 2) :
    MemLp (fun x => (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * (f ⋆[mul ℂ ℂ] g) x) 2 := by
  have hwc : Continuous fun x : E => (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) := by fun_prop
  have hmeas : AEStronglyMeasurable
      (fun x => (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * (f ⋆[mul ℂ ℂ] g) x) volume :=
    hwc.aestronglyMeasurable.mul (hf.integrable_convolution (mul ℂ ℂ) hg).aestronglyMeasurable
  set X := (fun y => ‖g y‖ₑ) ⋆ₗ fun y => ‖(((1 + ‖y‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * f y‖ₑ
  set Y := (fun y => ‖f y‖ₑ) ⋆ₗ fun y => ‖(((1 + ‖y‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * g y‖ₑ
  -- Young's inequality bounds both convolutions in `L²`.
  have hfin : ∀ {F : E → ℂ}, MemLp F 2 → ∫⁻ x, ‖F x‖ₑ ^ 2 < ∞ := fun hF => by
    simpa using (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)
      hF.aestronglyMeasurable).1 hF.eLpNorm_lt_top
  have hX : ∫⁻ x, X x ^ 2 < ∞ :=
    (lintegral_lconvolution_sq_le hg.aestronglyMeasurable.enorm
      hwf.aestronglyMeasurable.enorm).trans_lt <| ENNReal.mul_lt_top
        (ENNReal.pow_lt_top (hasFiniteIntegral_iff_enorm.1 hg.hasFiniteIntegral)) (hfin hwf)
  have hY : ∫⁻ x, Y x ^ 2 < ∞ :=
    (lintegral_lconvolution_sq_le hf.aestronglyMeasurable.enorm
      hwg.aestronglyMeasurable.enorm).trans_lt <| ENNReal.mul_lt_top
        (ENNReal.pow_lt_top (hasFiniteIntegral_iff_enorm.1 hf.hasFiniteIntegral)) (hfin hwg)
  -- Integrate the square of the pointwise bound, using `(X + Y) ^ 2 ≤ 2 (X ^ 2 + Y ^ 2)`.
  refine (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num) hmeas).2 ?_
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  calc ∫⁻ x, ‖(((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * (f ⋆[mul ℂ ℂ] g) x‖ₑ ^ 2
      ≤ ∫⁻ x, ENNReal.ofReal (2 ^ s) ^ 2 * (2 * (X x ^ 2 + Y x ^ 2)) := by
        refine lintegral_mono fun x => ?_
        have hsq := ENNReal.rpow_add_le_mul_rpow_add_rpow (X x) (Y x) (p := 2) one_le_two
        norm_num [ENNReal.rpow_two] at hsq
        calc ‖(((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * (f ⋆[mul ℂ ℂ] g) x‖ₑ ^ 2
            ≤ (ENNReal.ofReal (2 ^ s) * (X x + Y x)) ^ 2 := by
              gcongr
              exact enorm_one_add_norm_sq_rpow_mul_convolution_le hs hwf.aestronglyMeasurable
                hg.aestronglyMeasurable x
          _ ≤ ENNReal.ofReal (2 ^ s) ^ 2 * (2 * (X x ^ 2 + Y x ^ 2)) := by
              rw [mul_pow]
              gcongr
    _ < ∞ := by
      rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top),
        lintegral_const_mul' _ _ ENNReal.ofNat_ne_top, lintegral_add_left'
          ((aemeasurable_lconvolution hg.aestronglyMeasurable.enorm
            hwf.aestronglyMeasurable.enorm).pow_const 2)]
      exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
        (ENNReal.mul_lt_top ENNReal.ofNat_lt_top (ENNReal.add_lt_top.2 ⟨hX, hY⟩))

end TauCeti

/-! ### The algebra property -/

namespace TemperedDistribution

/-- **The Fourier transform of an `H^s` function, `s > n / 2`.** For `s > dim E / 2` the Fourier
transform of a Sobolev function `f ∈ H^s` is an `L¹` function `v` for which
`(1 + ‖ξ‖ ^ 2) ^ (s / 2) v` is square integrable. -/
theorem MemSobolev.fourier_memL1_and_memLp {s : ℝ} (hs : finrank ℝ E < 2 * s) {f : 𝓢'(E, ℂ)}
    (hf : MemSobolev s 2 f) :
    ∃ v : Lp ℂ 1 (volume : Measure E), 𝓕 f = (v : 𝓢'(E, ℂ)) ∧
      MemLp (fun ξ => (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * v ξ) 2 := by
  obtain ⟨v, hv⟩ := hf.fourier_memL1 hs
  obtain ⟨U, hU⟩ := memSobolev_iff_exists_smulLeftCLM_fourier.1 hf
  refine ⟨v, hv, (Lp.memLp U).ae_eq ?_⟩
  -- The `L²` function `U` represents the weight times `v`, by comparing their pairings.
  have hwg : (fun ξ : E => (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)).HasTemperateGrowth := by fun_prop
  have hwc : Continuous fun ξ : E => (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) := hwg.1.continuous
  refine Lp.ae_eq_of_toTemperedDistribution_apply_eq U ?_ fun φ => ?_
  · refine locallyIntegrable_iff.2 fun K hK => ?_
    exact (L1.integrable_coeFn v).integrableOn.continuousOn_mul hwc.continuousOn hK
  · rw [← hU, hv, Lp.smulLeftCLM_toTemperedDistribution_apply hwg]
    simp only [smul_eq_mul]

/-- **The product of an `H^s` function, `s > n / 2`, with an `L²` function is square
integrable**, since the first factor is bounded by the Sobolev embedding. -/
theorem MemSobolev.memLp_mul {s : ℝ} (hs : finrank ℝ E < 2 * s)
    {u : Lp ℂ 2 (volume : Measure E)} (hu : MemSobolev s 2 (u : 𝓢'(E, ℂ)))
    (v : Lp ℂ 2 (volume : Measure E)) :
    MemLp (fun x => u x * v x) 2 := by
  obtain ⟨g, hg⟩ := hu.exists_zeroAtInftyContinuousMap_ae_eq hs
  have hgv : MemLp (⇑g.toBCF * ⇑v) 2 := (g.toBCF.memLp_top (μ := volume)).mul (Lp.memLp v)
  refine hgv.ae_eq ?_
  filter_upwards [hg] with x hx
  simp [hx]

/-- **The Sobolev spaces `H^s(E)`, `s > dim E / 2`, are algebras.** The pointwise product of two
`L²` functions in `H^s`, `s > dim E / 2`, lies in `H^s`. -/
theorem MemSobolev.mul {s : ℝ} (hs : finrank ℝ E < 2 * s)
    {u v : Lp ℂ 2 (volume : Measure E)} (hu : MemSobolev s 2 (u : 𝓢'(E, ℂ)))
    (hv : MemSobolev s 2 (v : 𝓢'(E, ℂ))) :
    MemSobolev s 2 ((hu.memLp_mul hs v).toLp _ : 𝓢'(E, ℂ)) := by
  have hs0 : 0 ≤ s := by
    have := (finrank ℝ E).cast_nonneg (α := ℝ)
    linarith
  obtain ⟨v₁, hFu, hw₁⟩ := hu.fourier_memL1_and_memLp hs
  obtain ⟨v₂, hFv, hw₂⟩ := hv.fourier_memL1_and_memLp hs
  have hi₁ := L1.integrable_coeFn v₁
  have hi₂ := L1.integrable_coeFn v₂
  -- The product is the inverse Fourier transform of the integrable convolution `v₁ ⋆ v₂`.
  set W : E → ℂ := (v₁ : E → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ] (v₂ : E → ℂ)
  have hW : Integrable W := hi₁.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hi₂
  set P := (hu.memLp_mul hs v).toLp _
  set R : Lp ℂ 1 (volume : Measure E) := hW.toL1 W
  have hR : 𝓕⁻ (R : E → ℂ) = 𝓕⁻ W := by
    ext x
    simp only [Real.fourierInv_eq]
    refine integral_congr_ae ?_
    filter_upwards [hW.coeFn_toL1] with y hy
    rw [hy]
  have hP : (P : 𝓢'(E, ℂ)) = 𝓕⁻ (R : 𝓢'(E, ℂ)) := by
    ext φ
    rw [Lp.fourierInv_toTemperedDistribution_apply, Lp.toTemperedDistribution_apply, hR]
    refine integral_congr_ae ?_
    filter_upwards [(hu.memLp_mul hs v).coeFn_toLp, Lp.ae_eq_fourierInv_of_fourier_eq hFu,
      Lp.ae_eq_fourierInv_of_fourier_eq hFv] with x hx h₁ h₂
    rw [hx, h₁, h₂, Real.fourierInv_mul_convolution_eq hi₁ hi₂]
  have hFP : 𝓕 (P : 𝓢'(E, ℂ)) = R := by
    rw [hP, FourierTransform.fourier_fourierInv_eq]
  -- The weighted convolution estimate puts the weight times `𝓕 P` in `L²`.
  have hmem : MemLp (fun ξ => (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * R ξ) 2 := by
    refine (TauCeti.memLp_one_add_norm_sq_rpow_mul_convolution hs0 hi₁ hi₂ hw₁ hw₂).ae_eq ?_
    filter_upwards [hW.coeFn_toL1] with ξ hξ
    rw [hξ]
  have hwg : (fun ξ : E => (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)).HasTemperateGrowth := by fun_prop
  refine memSobolev_iff_exists_smulLeftCLM_fourier.2 ⟨hmem.toLp _, ?_⟩
  ext φ
  rw [hFP, Lp.smulLeftCLM_toTemperedDistribution_apply hwg, Lp.toTemperedDistribution_apply]
  refine integral_congr_ae ?_
  filter_upwards [hmem.coeFn_toLp] with ξ hξ
  rw [hξ]
  simp only [smul_eq_mul]

/-- **Products of real `H^s` functions, `s > n / 2`.** The real `L²` functions whose
complexification lies in `H^s`, `s > dim E / 2`, are closed under pointwise multiplication. -/
theorem exists_mem_realSobolevSubmodule_ae_eq_mul {s : ℝ} (hs : finrank ℝ E < 2 * s)
    {u v : Lp ℝ 2 (volume : Measure E)} (hu : u ∈ realSobolevSubmodule E s 2)
    (hv : v ∈ realSobolevSubmodule E s 2) :
    ∃ w ∈ realSobolevSubmodule E s 2, w =ᵐ[volume] fun x => u x * v x := by
  rw [mem_realSobolevSubmodule] at hu hv
  have hm := hu.memLp_mul hs (Complex.ofRealCLM.compLp v)
  have hcu := Complex.ofRealCLM.coeFn_compLp (p := 2) (μ := volume) u
  have hcv := Complex.ofRealCLM.coeFn_compLp (p := 2) (μ := volume) v
  -- The complexified product is the complexification of the real product.
  have hae : (fun x => (Complex.ofRealCLM.compLp u : E → ℂ) x *
      (Complex.ofRealCLM.compLp v : E → ℂ) x) =ᵐ[volume] fun x => ((u x * v x : ℝ) : ℂ) := by
    filter_upwards [hcu, hcv] with x hx hy
    rw [hx, hy, Complex.ofRealCLM_apply, Complex.ofRealCLM_apply, Complex.ofReal_mul]
  have hr : MemLp (fun x => u x * v x) 2 :=
    hm.of_le ((Lp.aestronglyMeasurable u).mul (Lp.aestronglyMeasurable v)) <| by
      filter_upwards [hae] with x hx
      rw [hx, Complex.norm_real]
  refine ⟨hr.toLp _, ?_, hr.coeFn_toLp⟩
  have heq : Complex.ofRealCLM.compLp (hr.toLp _) = hm.toLp _ := by
    refine Lp.ext ?_
    filter_upwards [Complex.ofRealCLM.coeFn_compLp (p := 2) (μ := volume) (hr.toLp _),
      hr.coeFn_toLp, hm.coeFn_toLp, hae] with x h₁ h₂ h₃ h₄
    rw [h₁, h₃, h₄, Complex.ofRealCLM_apply, h₂]
  rw [mem_realSobolevSubmodule, heq]
  exact hu.mul hs hv

end TemperedDistribution
