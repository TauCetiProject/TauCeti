/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Sobolev
import TauCeti.Analysis.Convolution.Weighted
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Fourier.Convolution
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding

/-!
# The Sobolev spaces `H^s(ℝⁿ)`, `s > n / 2`, are algebras

Let `E` be a finite-dimensional real inner product space of dimension `n` and let `s > n / 2`.
The pointwise product of two functions in the Bessel-potential space `H^s(E)` (Mathlib's
`TemperedDistribution.MemSobolev s 2`) is again in `H^s(E)`
(`TemperedDistribution.MemSobolev.mul`). Already the product of an `H^s` function with any `Lᵖ`
function is an `Lᵖ` function, since the first factor is bounded by the Sobolev embedding
(`TemperedDistribution.MemSobolev.memLp_mul`). The same holds for real-valued functions
(`TemperedDistribution.exists_mem_realSobolevSubmodule_ae_eq_mul`).

This is the basic input for nonlinear analysis on the scale `H^s`, `s > n / 2`: polynomial
expressions without constant term in `H^s` fields stay in `H^s`, and the functions `1 + h`,
`h ∈ H^s`, are closed under multiplication, which is the closure step towards a gauge group.

## The Fourier argument

Write `⟨ξ⟩ = (1 + ‖ξ‖ ^ 2) ^ (1 / 2)`. A function `u ∈ L²` lies in `H^s` exactly when
`⟨ξ⟩ ^ s 𝓕u ∈ L²`, and for `s > n / 2` Cauchy–Schwarz against `⟨ξ⟩ ^ (-s) ∈ L²` makes `𝓕u` an
`L¹` function `v` (`TemperedDistribution.MemSobolev.fourier_memL1`), with `⟨ξ⟩ ^ s v ∈ L²`
(`TemperedDistribution.MemSobolev.fourier_memL1_and_memLp`). So `u = 𝓕⁻ v` almost
everywhere and the product of two such functions is

`u₁ u₂ = 𝓕⁻ v₁ · 𝓕⁻ v₂ = 𝓕⁻ (v₁ ⋆ v₂)`

(`Real.fourierInv_mul_convolution_eq`), with `v₁ ⋆ v₂ ∈ L¹`. Hence `𝓕(u₁ u₂) = v₁ ⋆ v₂` as
tempered distributions, and it remains to show `⟨ξ⟩ ^ s (v₁ ⋆ v₂) ∈ L²`. Peetre's inequality
`⟨ξ⟩ ^ s ≤ 2 ^ s (⟨η⟩ ^ s + ⟨ξ - η⟩ ^ s)` (`TauCeti.one_add_norm_add_sq_rpow_le`) gives

`⟨ξ⟩ ^ s |v₁ ⋆ v₂| ≤ 2 ^ s ((⟨·⟩ ^ s |v₁|) ⋆ |v₂| + |v₁| ⋆ (⟨·⟩ ^ s |v₂|))`,

and each convolution on the right is that of an `L²` function with an `L¹` function, which lies
in `L²` by Young's inequality (`MeasureTheory.lintegral_lconvolution_sq_le`). This weighted
convolution estimate is `TauCeti.memLp_one_add_norm_sq_rpow_mul_convolution`, in
`TauCeti.Analysis.Convolution.Weighted`.

## Main declarations

* `TemperedDistribution.MemSobolev.memLp_mul`: the product of an `H^s` function, `s > n / 2`,
  with an `Lᵖ` function is an `Lᵖ` function.
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

namespace TemperedDistribution

/-- **The product of an `H^s` function, `s > n / 2`, with an `Lᵖ` function is in `Lᵖ`**, since
the first factor is bounded by the Sobolev embedding. -/
theorem MemSobolev.memLp_mul {s : ℝ} (hs : finrank ℝ E < 2 * s)
    {u : Lp ℂ 2 (volume : Measure E)} (hu : MemSobolev s 2 (u : 𝓢'(E, ℂ))) {p : ℝ≥0∞}
    (v : Lp ℂ p (volume : Measure E)) :
    MemLp (fun x => u x * v x) p := by
  obtain ⟨g, hg⟩ := hu.exists_zeroAtInftyContinuousMap_ae_eq hs
  have hgv : MemLp (⇑g.toBCF * ⇑v) p := (g.toBCF.memLp_top (μ := volume)).mul (Lp.memLp v)
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
  have hR : 𝓕⁻ (R : E → ℂ) = 𝓕⁻ W := funext (Real.fourierInv_congr_ae hW.coeFn_toL1)
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
