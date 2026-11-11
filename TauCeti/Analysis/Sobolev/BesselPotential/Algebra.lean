/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Sobolev
public import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace
public import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion
import TauCeti.Analysis.Convolution.Weighted
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Fourier.Convolution
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Lp

/-!
# The Sobolev spaces `H^s(ℝⁿ)`, `s > n / 2`, are algebras

Let `E` be a finite-dimensional real inner product space of dimension `n` and let `s > n / 2`.
The pointwise product of two functions in the Bessel-potential space `H^s(E)` (Mathlib's
`TemperedDistribution.MemSobolev s 2`) is again in `H^s(E)`
(`TemperedDistribution.MemSobolev.mul`), and there is a constant `C`, depending only on `s` and
`E`, with

`‖u v‖_{H^s} ≤ C ‖u‖_{H^s} ‖v‖_{H^s}`

(`TemperedDistribution.exists_norm_toBesselPotentialSpace_mul_le`). Already the product of an
`H^s` function with any `Lᵖ`
function is an `Lᵖ` function, since the first factor is bounded by the Sobolev embedding
(`TemperedDistribution.MemSobolev.memLp_mul`). The same holds for real-valued functions
(`TemperedDistribution.exists_mem_realSobolevSubmodule_ae_eq_mul`).

This is the basic input for nonlinear analysis on the scale `H^s`, `s > n / 2`: polynomial
expressions without constant term in `H^s` fields stay in `H^s`, and the functions `1 + h`,
`h ∈ H^s`, are closed under multiplication, which is the closure step towards a gauge group. The
estimate makes the product a bounded bilinear operation for the `H^s` norm
(`BesselPotentialSpace.mulCLM`), so that polynomial expressions depend continuously on `H^s`
fields and multiplication `(1 + h)(1 + g)` is continuous for the distance `‖h - g‖_{H^s}`.

## The Fourier argument

Write `⟨ξ⟩ = (1 + ‖ξ‖ ^ 2) ^ (1 / 2)`. A function `u ∈ L²` lies in `H^s` exactly when
`⟨ξ⟩ ^ s 𝓕u ∈ L²`, and for `s > n / 2` Cauchy–Schwarz against `⟨ξ⟩ ^ (-s) ∈ L²` makes `𝓕u` an
`L¹` function `v` (`TemperedDistribution.MemSobolev.fourier_memL1`), with
`‖v‖₁ ≤ ‖⟨·⟩ ^ (-s)‖₂ ‖u‖_{H^s}` and `‖⟨·⟩ ^ s v‖₂ = ‖u‖_{H^s}`
(`TemperedDistribution.MemSobolev.eLpNorm_one_le_mul_enorm_toBesselPotentialSpace` and
`MemSobolev.eLpNorm_one_add_norm_sq_rpow_smul_eq_enorm_toBesselPotentialSpace`, in the same
namespace). So `u = 𝓕⁻ v` almost everywhere and the product of two such functions is

`u₁ u₂ = 𝓕⁻ v₁ · 𝓕⁻ v₂ = 𝓕⁻ (v₁ ⋆ v₂)`

(`Real.fourierInv_mul_convolution_eq`), with `v₁ ⋆ v₂ ∈ L¹`. Hence `𝓕(u₁ u₂) = v₁ ⋆ v₂` as
tempered distributions, and it remains to show `⟨ξ⟩ ^ s (v₁ ⋆ v₂) ∈ L²`. Peetre's inequality
`⟨ξ⟩ ^ s ≤ 2 ^ s (⟨η⟩ ^ s + ⟨ξ - η⟩ ^ s)` (`TauCeti.one_add_norm_add_sq_rpow_le`) gives

`⟨ξ⟩ ^ s |v₁ ⋆ v₂| ≤ 2 ^ s ((⟨·⟩ ^ s |v₁|) ⋆ |v₂| + |v₁| ⋆ (⟨·⟩ ^ s |v₂|))`,

and each convolution on the right is that of an `L²` function with an `L¹` function, which lies
in `L²` by Young's inequality (`MeasureTheory.eLpNorm_lconvolution_le`). This weighted
convolution estimate is `TauCeti.eLpNorm_one_add_norm_sq_rpow_mul_convolution_le`, in
`TauCeti.Analysis.Convolution.Weighted`; it bounds `‖u₁ u₂‖_{H^s}` by
`2 ^ s (‖v₂‖₁ ‖u₁‖_{H^s} + ‖v₁‖₁ ‖u₂‖_{H^s})`, and the `L¹` bounds above give the algebra
estimate with `C = 2 ^ (s + 1) ‖⟨·⟩ ^ (-s)‖₂`.

## Main declarations

* `TemperedDistribution.MemSobolev.memLp_mul`: the product of an `H^s` function, `s > n / 2`,
  with an `Lᵖ` function is an `Lᵖ` function.
* `TemperedDistribution.MemSobolev.mul`: the product of two `H^s` functions, `s > n / 2`, lies in
  `H^s`.
* `TemperedDistribution.exists_norm_toBesselPotentialSpace_mul_le`: the algebra estimate
  `‖u v‖_{H^s} ≤ C ‖u‖_{H^s} ‖v‖_{H^s}`.
* `TemperedDistribution.exists_norm_toBesselPotentialSpace_pow_le`: the powers of `u ∈ H^s` lie in
  `H^s`, with `‖u ^ (n + 1)‖_{H^s} ≤ C ^ n ‖u‖_{H^s} ^ (n + 1)`.
* `TemperedDistribution.exists_mem_realSobolevSubmodule_ae_eq_mul`: the real form of
  `TemperedDistribution.MemSobolev.mul`.
* `TemperedDistribution.mul_mem_realSobolevFunctions`: the same for pointwise representatives.
* `BesselPotentialSpace.mulCLM`: the product on `H^s(E)` as a continuous bilinear map,
  characterized by `BesselPotentialSpace.toDistr_mulCLM_apply`.
* `TemperedDistribution.realSobolevToBesselPotential_mul`: the complexification of a product of
  real `H^s` functions is the product `mulCLM` of their complexifications.

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

/-- The Fourier transform of the product of two `L²` functions in `H^s`, `s > dim E / 2`, is the
convolution of their Fourier transforms, which are `L¹` functions. -/
private theorem fourier_toLp_mul_eq {s : ℝ} (hs : finrank ℝ E < 2 * s)
    {u v : Lp ℂ 2 (volume : Measure E)} (hu : MemSobolev s 2 (u : 𝓢'(E, ℂ)))
    {v₁ v₂ : Lp ℂ 1 (volume : Measure E)} (h₁ : 𝓕 (u : 𝓢'(E, ℂ)) = v₁)
    (h₂ : 𝓕 (v : 𝓢'(E, ℂ)) = v₂) :
    𝓕 ((hu.memLp_mul hs v).toLp _ : 𝓢'(E, ℂ)) =
      ((((L1.integrable_coeFn v₁).integrable_convolution (ContinuousLinearMap.mul ℂ ℂ)
        (L1.integrable_coeFn v₂)).toL1 _ : Lp ℂ 1 (volume : Measure E)) : 𝓢'(E, ℂ)) := by
  have hi₁ := L1.integrable_coeFn v₁
  have hi₂ := L1.integrable_coeFn v₂
  set W : E → ℂ := (v₁ : E → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ] (v₂ : E → ℂ)
  have hW : Integrable W := hi₁.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hi₂
  -- The product is the inverse Fourier transform of the integrable convolution `v₁ ⋆ v₂`.
  have hP : ((hu.memLp_mul hs v).toLp _ : 𝓢'(E, ℂ)) =
      𝓕⁻ ((hW.toL1 W : Lp ℂ 1 (volume : Measure E)) : 𝓢'(E, ℂ)) := by
    ext φ
    rw [Lp.fourierInv_toTemperedDistribution_apply _ hW hW.coeFn_toL1,
      Lp.toTemperedDistribution_apply]
    refine integral_congr_ae ?_
    filter_upwards [(hu.memLp_mul hs v).coeFn_toLp, Lp.ae_eq_fourierInv_of_fourier_eq h₁,
      Lp.ae_eq_fourierInv_of_fourier_eq h₂] with x hx hx₁ hx₂
    rw [hx, hx₁, hx₂, Real.fourierInv_mul_convolution_eq hi₁ hi₂]
  rw [hP, FourierTransform.fourier_fourierInv_eq]

/-- **The Sobolev spaces `H^s(E)`, `s > dim E / 2`, are algebras.** The pointwise product of two
`L²` functions in `H^s`, `s > dim E / 2`, lies in `H^s`. -/
theorem MemSobolev.mul {s : ℝ} (hs : finrank ℝ E < 2 * s)
    {u v : Lp ℂ 2 (volume : Measure E)} (hu : MemSobolev s 2 (u : 𝓢'(E, ℂ)))
    (hv : MemSobolev s 2 (v : 𝓢'(E, ℂ))) :
    MemSobolev s 2 ((hu.memLp_mul hs v).toLp _ : 𝓢'(E, ℂ)) := by
  have hs0 : 0 ≤ s := by
    have := (finrank ℝ E).cast_nonneg (α := ℝ)
    linarith
  obtain ⟨v₁, h₁⟩ := hu.fourier_memL1 hs
  obtain ⟨v₂, h₂⟩ := hv.fourier_memL1 hs
  have hW := (L1.integrable_coeFn v₁).integrable_convolution (ContinuousLinearMap.mul ℂ ℂ)
    (L1.integrable_coeFn v₂)
  set R := hW.toL1 _
  -- The weighted convolution estimate puts the weight times `𝓕 (u v) = v₁ ⋆ v₂` in `L²`.
  have hmem : MemLp (fun ξ => (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * R ξ) 2 := by
    refine (TauCeti.memLp_one_add_norm_sq_rpow_mul_convolution hs0 (L1.integrable_coeFn v₁)
      (L1.integrable_coeFn v₂) (by simpa only [Complex.real_smul] using
        hu.memLp_one_add_norm_sq_rpow_smul h₁)
      (by simpa only [Complex.real_smul] using hv.memLp_one_add_norm_sq_rpow_smul h₂)).ae_eq ?_
    filter_upwards [hW.coeFn_toL1] with ξ hξ
    rw [hξ]
  have hwg : (fun ξ : E => (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)).HasTemperateGrowth := by fun_prop
  refine memSobolev_iff_exists_smulLeftCLM_fourier.2 ⟨hmem.toLp _, ?_⟩
  ext φ
  rw [fourier_toLp_mul_eq hs hu h₁ h₂, Lp.smulLeftCLM_toTemperedDistribution_apply hwg,
    Lp.toTemperedDistribution_apply]
  refine integral_congr_ae ?_
  filter_upwards [hmem.coeFn_toLp] with ξ hξ
  simp only [hξ, smul_eq_mul, R]

/-- **The algebra estimate on `H^s(E)`, `s > dim E / 2`.** There is a constant `C`, depending
only on `s` and `E`, such that the pointwise product of two `L²` functions `u, v ∈ H^s` satisfies
`‖u v‖_{H^s} ≤ C ‖u‖_{H^s} ‖v‖_{H^s}`. -/
theorem exists_norm_toBesselPotentialSpace_mul_le {s : ℝ} (hs : finrank ℝ E < 2 * s) :
    ∃ C, 0 ≤ C ∧ ∀ {u v : Lp ℂ 2 (volume : Measure E)} (hu : MemSobolev s 2 (u : 𝓢'(E, ℂ)))
      (hv : MemSobolev s 2 (v : 𝓢'(E, ℂ))),
      ‖(hu.mul hs hv).toBesselPotentialSpace‖ ≤
        C * ‖hu.toBesselPotentialSpace‖ * ‖hv.toBesselPotentialSpace‖ := by
  have hs0 : 0 ≤ s := by
    have := (finrank ℝ E).cast_nonneg (α := ℝ)
    linarith
  set K := eLpNorm (fun ξ : E => (1 + ‖ξ‖ ^ 2) ^ (-s / 2)) 2 volume
  have hK : K ≠ ∞ := (TauCeti.memLp_rpow_neg_one_add_norm_sq volume hs).ne
  refine ⟨2 ^ s * (2 * K.toReal), by positivity, fun {u v} hu hv => ?_⟩
  obtain ⟨v₁, h₁⟩ := hu.fourier_memL1 hs
  obtain ⟨v₂, h₂⟩ := hv.fourier_memL1 hs
  have hW := (L1.integrable_coeFn v₁).integrable_convolution (ContinuousLinearMap.mul ℂ ℂ)
    (L1.integrable_coeFn v₂)
  have hP := (hu.mul hs hv).eLpNorm_one_add_norm_sq_rpow_smul_eq_enorm_toBesselPotentialSpace
    (fourier_toLp_mul_eq hs hu h₁ h₂)
  rw [eLpNorm_congr_ae (by filter_upwards [hW.coeFn_toL1] with ξ hξ; rw [hξ])] at hP
  have hconv := TauCeti.eLpNorm_one_add_norm_sq_rpow_mul_convolution_le hs0
    (Lp.aestronglyMeasurable v₁) (Lp.aestronglyMeasurable v₂)
  simp only [← Complex.real_smul] at hconv
  rw [hu.eLpNorm_one_add_norm_sq_rpow_smul_eq_enorm_toBesselPotentialSpace h₁,
    hv.eLpNorm_one_add_norm_sq_rpow_smul_eq_enorm_toBesselPotentialSpace h₂, hP] at hconv
  -- Combine in `ℝ≥0∞`, then pass to real norms.
  rw [← ENNReal.ofReal_le_ofReal_iff (by positivity), ofReal_norm]
  calc ‖(hu.mul hs hv).toBesselPotentialSpace‖ₑ
      ≤ ENNReal.ofReal (2 ^ s) * (K * ‖hv.toBesselPotentialSpace‖ₑ * ‖hu.toBesselPotentialSpace‖ₑ +
          K * ‖hu.toBesselPotentialSpace‖ₑ * ‖hv.toBesselPotentialSpace‖ₑ) := by
        refine hconv.trans ?_
        gcongr
        · exact hv.eLpNorm_one_le_mul_enorm_toBesselPotentialSpace h₂
        · exact hu.eLpNorm_one_le_mul_enorm_toBesselPotentialSpace h₁
    _ = ENNReal.ofReal (2 ^ s * (2 * K.toReal) * ‖hu.toBesselPotentialSpace‖ *
          ‖hv.toBesselPotentialSpace‖) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_toReal hK, ofReal_norm, ofReal_norm, ENNReal.ofReal_ofNat]
        ring

/-- **Powers in `H^s(E)`, `s > dim E / 2`.** There is a constant `C`, depending only on `s` and
`E`, such that for every `L²` function `u ∈ H^s` and every `n`, the power `u ^ (n + 1)` is an
`L²` function in `H^s` with `‖u ^ (n + 1)‖_{H^s} ≤ C ^ n ‖u‖_{H^s} ^ (n + 1)`. The constant is that
of the algebra estimate `exists_norm_toBesselPotentialSpace_mul_le`. -/
theorem exists_norm_toBesselPotentialSpace_pow_le {s : ℝ} (hs : finrank ℝ E < 2 * s) :
    ∃ C, 0 ≤ C ∧ ∀ {u : Lp ℂ 2 (volume : Measure E)} (hu : MemSobolev s 2 (u : 𝓢'(E, ℂ)))
      (n : ℕ), ∃ v : Lp ℂ 2 (volume : Measure E), v =ᵐ[volume] (fun x => u x ^ (n + 1)) ∧
        ∃ hv : MemSobolev s 2 (v : 𝓢'(E, ℂ)),
          ‖hv.toBesselPotentialSpace‖ ≤ C ^ n * ‖hu.toBesselPotentialSpace‖ ^ (n + 1) := by
  obtain ⟨C, hC, hmul⟩ := exists_norm_toBesselPotentialSpace_mul_le (E := E) hs
  refine ⟨C, hC, fun {u} hu n => ?_⟩
  induction n with
  | zero => exact ⟨u, .of_forall fun x => (pow_one _).symm, hu, by simp⟩
  | succ n ih =>
    obtain ⟨v, hvu, hv, hvn⟩ := ih
    refine ⟨(hv.memLp_mul hs u).toLp _, ?_, hv.mul hs hu, (hmul hv hu).trans ?_⟩
    · filter_upwards [(hv.memLp_mul hs u).coeFn_toLp, hvu] with x h h'
      rw [h, h', ← pow_succ]
    · calc C * ‖hv.toBesselPotentialSpace‖ * ‖hu.toBesselPotentialSpace‖
          ≤ C * (C ^ n * ‖hu.toBesselPotentialSpace‖ ^ (n + 1)) *
              ‖hu.toBesselPotentialSpace‖ := by gcongr
        _ = C ^ (n + 1) * ‖hu.toBesselPotentialSpace‖ ^ (n + 1 + 1) := by ring

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

/-- **Products of real `H^s` functions, `s > n / 2`, pointwise.** The real functions in `H^s`,
`s > dim E / 2`, are closed under pointwise multiplication. -/
theorem mul_mem_realSobolevFunctions {s : ℝ} (hs : finrank ℝ E < 2 * s) {f g : E → ℝ}
    (hf : f ∈ realSobolevFunctions E s 2) (hg : g ∈ realSobolevFunctions E s 2) :
    f * g ∈ realSobolevFunctions E s 2 := by
  obtain ⟨u, huf, hu⟩ := mem_realSobolevFunctions.1 hf
  obtain ⟨v, hvg, hv⟩ := mem_realSobolevFunctions.1 hg
  obtain ⟨w, hw, hwuv⟩ := exists_mem_realSobolevSubmodule_ae_eq_mul hs
    (mem_realSobolevSubmodule.2 hu) (mem_realSobolevSubmodule.2 hv)
  refine mem_realSobolevFunctions_of_ae_eq (coeFn_mem_realSobolevFunctions hw) ?_
  filter_upwards [hwuv, huf, hvg] with x h h₁ h₂
  rw [h, h₁, h₂, Pi.mul_apply]

end TemperedDistribution

namespace BesselPotentialSpace

open TemperedDistribution
open scoped BesselPotentialSpace

variable {s : ℝ}

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
private theorem nonneg_of_finrank_lt (hs : finrank ℝ E < 2 * s) : 0 ≤ s := by
  have := (finrank ℝ E).cast_nonneg (α := ℝ)
  linarith

/-- The `L²` function underlying `f ∈ H^s(E)`, `s > dim E / 2`. -/
private def toL2 (hs : finrank ℝ E < 2 * s) (f : H^{s}(E)) : Lp ℂ 2 (volume : Measure E) :=
  (inclusion (nonneg_of_finrank_lt hs) f).toLp

private theorem toDistr_eq_toL2 (hs : finrank ℝ E < 2 * s) (f : H^{s}(E)) :
    f.toDistr = (toL2 hs f : 𝓢'(E, ℂ)) :=
  toDistr_eq_toLp_inclusion _ f

private theorem memSobolev_toL2 (hs : finrank ℝ E < 2 * s) (f : H^{s}(E)) :
    MemSobolev s 2 (toL2 hs f : 𝓢'(E, ℂ)) :=
  toDistr_eq_toL2 hs f ▸ f.memSobolev_toDistr

private theorem toDistr_add_eq_toL2 (hs : finrank ℝ E < 2 * s) (f g : H^{s}(E)) :
    (f + g).toDistr = ((toL2 hs f + toL2 hs g : Lp ℂ 2 (volume : Measure E)) : 𝓢'(E, ℂ)) := by
  rw [toDistr_add, toDistr_eq_toL2 hs f, toDistr_eq_toL2 hs g, Lp.toTemperedDistribution_add]

private theorem toDistr_smul_eq_toL2 (hs : finrank ℝ E < 2 * s) (c : ℂ) (f : H^{s}(E)) :
    (c • f).toDistr = ((c • toL2 hs f : Lp ℂ 2 (volume : Measure E)) : 𝓢'(E, ℂ)) := by
  rw [toDistr_smul, toDistr_eq_toL2 hs f, Lp.toTemperedDistribution_smul]

/-- The `L²` product of the functions underlying `f, g ∈ H^s(E)`. -/
private def mulL2 (hs : finrank ℝ E < 2 * s) (f g : H^{s}(E)) : Lp ℂ 2 (volume : Measure E) :=
  ((memSobolev_toL2 hs f).memLp_mul hs (toL2 hs g)).toLp _

private theorem coeFn_mulL2 (hs : finrank ℝ E < 2 * s) (f g : H^{s}(E)) :
    mulL2 hs f g =ᵐ[volume] fun x => toL2 hs f x * toL2 hs g x :=
  MemLp.coeFn_toLp _

/-- The pointwise product of two elements of `H^s(E)`, before bundling. -/
private def mulAux (hs : finrank ℝ E < 2 * s) (f g : H^{s}(E)) : H^{s}(E) :=
  ((memSobolev_toL2 hs f).mul hs (memSobolev_toL2 hs g)).toBesselPotentialSpace

private theorem toDistr_mulAux_eq_mulL2 (hs : finrank ℝ E < 2 * s) (f g : H^{s}(E)) :
    (mulAux hs f g).toDistr = (mulL2 hs f g : 𝓢'(E, ℂ)) :=
  MemSobolev.toBesselPotentialSpace_toDistr _

private theorem lp_eq_of_toTemperedDistribution_eq {u v : Lp ℂ 2 (volume : Measure E)}
    (h : (u : 𝓢'(E, ℂ)) = v) : u = v :=
  LinearMap.ker_eq_bot.1 Lp.ker_toTemperedDistributionCLM_eq_bot (by simpa using h)

private theorem toDistr_mulAux (hs : finrank ℝ E < 2 * s) {f g : H^{s}(E)}
    {u v w : Lp ℂ 2 (volume : Measure E)} (hf : f.toDistr = u) (hg : g.toDistr = v)
    (hw : w =ᵐ[volume] fun x => u x * v x) : (mulAux hs f g).toDistr = w := by
  have hu : toL2 hs f = u := lp_eq_of_toTemperedDistribution_eq (by rw [← toDistr_eq_toL2, hf])
  have hv : toL2 hs g = v := lp_eq_of_toTemperedDistribution_eq (by rw [← toDistr_eq_toL2, hg])
  rw [toDistr_mulAux_eq_mulL2]
  congr 1
  refine Lp.ext ?_
  filter_upwards [coeFn_mulL2 hs f g, hw] with x hx hx'
  rw [hx, hx', hu, hv]

private theorem norm_mulAux_le (hs : finrank ℝ E < 2 * s) (f g : H^{s}(E)) :
    ‖mulAux hs f g‖ ≤
      (exists_norm_toBesselPotentialSpace_mul_le (E := E) hs).choose * ‖f‖ * ‖g‖ := by
  have hf : (memSobolev_toL2 hs f).toBesselPotentialSpace = f :=
    ext (by rw [MemSobolev.toBesselPotentialSpace_toDistr, ← toDistr_eq_toL2])
  have hg : (memSobolev_toL2 hs g).toBesselPotentialSpace = g :=
    ext (by rw [MemSobolev.toBesselPotentialSpace_toDistr, ← toDistr_eq_toL2])
  have h := (exists_norm_toBesselPotentialSpace_mul_le (E := E) hs).choose_spec.2
    (memSobolev_toL2 hs f) (memSobolev_toL2 hs g)
  rwa [hf, hg] at h

/-- **The product on `H^s(E)`, `s > dim E / 2`, as a continuous bilinear map.** The pointwise
product of two functions in `H^s(E)` lies in `H^s(E)` (`TemperedDistribution.MemSobolev.mul`),
and the algebra estimate `TemperedDistribution.exists_norm_toBesselPotentialSpace_mul_le` bounds
it. The product is characterized by `BesselPotentialSpace.toDistr_mulCLM_apply`. -/
def mulCLM (hs : finrank ℝ E < 2 * s) : H^{s}(E) →L[ℂ] H^{s}(E) →L[ℂ] H^{s}(E) :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℂ (mulAux hs)
      (fun f₁ f₂ g ↦ ext <| by
        rw [toDistr_add, toDistr_mulAux_eq_mulL2 hs f₁ g, toDistr_mulAux_eq_mulL2 hs f₂ g,
          ← Lp.toTemperedDistribution_add]
        refine toDistr_mulAux hs (toDistr_add_eq_toL2 hs f₁ f₂) (toDistr_eq_toL2 hs g) ?_
        filter_upwards [Lp.coeFn_add (mulL2 hs f₁ g) (mulL2 hs f₂ g), coeFn_mulL2 hs f₁ g,
          coeFn_mulL2 hs f₂ g, Lp.coeFn_add (toL2 hs f₁) (toL2 hs f₂)] with x h h₁ h₂ h₃
        rw [h, Pi.add_apply, h₁, h₂, h₃, Pi.add_apply, add_mul])
      (fun c f g ↦ ext <| by
        rw [toDistr_smul, toDistr_mulAux_eq_mulL2 hs f g, ← Lp.toTemperedDistribution_smul]
        refine toDistr_mulAux hs (toDistr_smul_eq_toL2 hs c f) (toDistr_eq_toL2 hs g) ?_
        filter_upwards [Lp.coeFn_smul c (mulL2 hs f g), coeFn_mulL2 hs f g,
          Lp.coeFn_smul c (toL2 hs f)] with x h h₁ h₂
        rw [h, Pi.smul_apply, h₁, h₂, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_assoc])
      (fun f g₁ g₂ ↦ ext <| by
        rw [toDistr_add, toDistr_mulAux_eq_mulL2 hs f g₁, toDistr_mulAux_eq_mulL2 hs f g₂,
          ← Lp.toTemperedDistribution_add]
        refine toDistr_mulAux hs (toDistr_eq_toL2 hs f) (toDistr_add_eq_toL2 hs g₁ g₂) ?_
        filter_upwards [Lp.coeFn_add (mulL2 hs f g₁) (mulL2 hs f g₂), coeFn_mulL2 hs f g₁,
          coeFn_mulL2 hs f g₂, Lp.coeFn_add (toL2 hs g₁) (toL2 hs g₂)] with x h h₁ h₂ h₃
        rw [h, Pi.add_apply, h₁, h₂, h₃, Pi.add_apply, mul_add])
      (fun c f g ↦ ext <| by
        rw [toDistr_smul, toDistr_mulAux_eq_mulL2 hs f g, ← Lp.toTemperedDistribution_smul]
        refine toDistr_mulAux hs (toDistr_eq_toL2 hs f) (toDistr_smul_eq_toL2 hs c g) ?_
        filter_upwards [Lp.coeFn_smul c (mulL2 hs f g), coeFn_mulL2 hs f g,
          Lp.coeFn_smul c (toL2 hs g)] with x h h₁ h₂
        rw [h, Pi.smul_apply, h₁, h₂, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm]))
    _ (norm_mulAux_le hs)

/-- **The product on `H^s(E)` is the pointwise product.** If `f, g ∈ H^s(E)` are the tempered
distributions of the `L²` functions `u` and `v`, then `mulCLM hs f g` is the tempered distribution
of every `L²` function `w` equal to `u v` almost everywhere. -/
theorem toDistr_mulCLM_apply (hs : finrank ℝ E < 2 * s) {f g : H^{s}(E)}
    {u v w : Lp ℂ 2 (volume : Measure E)} (hf : f.toDistr = u) (hg : g.toDistr = v)
    (hw : w =ᵐ[volume] fun x => u x * v x) : (mulCLM hs f g).toDistr = w :=
  toDistr_mulAux hs hf hg hw

/-- **The algebra estimate for the bundled product.** There is a constant `C`, depending only on
`s` and `E`, with `‖f g‖_{H^s} ≤ C ‖f‖_{H^s} ‖g‖_{H^s}`. -/
theorem exists_norm_mulCLM_apply_le (hs : finrank ℝ E < 2 * s) :
    ∃ C, 0 ≤ C ∧ ∀ f g : H^{s}(E), ‖mulCLM hs f g‖ ≤ C * ‖f‖ * ‖g‖ :=
  ⟨_, (exists_norm_toBesselPotentialSpace_mul_le (E := E) hs).choose_spec.1, norm_mulAux_le hs⟩

end BesselPotentialSpace

namespace TemperedDistribution

open scoped BesselPotentialSpace

variable {s : ℝ}

/-- **`realSobolevToBesselPotential` is multiplicative.** For `s > dim E / 2`, the complexification
of the product of two real `H^s` functions is the product `mulCLM` of their complexifications. -/
theorem realSobolevToBesselPotential_mul (hs : finrank ℝ E < 2 * s)
    (f g : realSobolevFunctions E s 2) :
    realSobolevToBesselPotential E s 2 ⟨_, mul_mem_realSobolevFunctions hs f.2 g.2⟩ =
      BesselPotentialSpace.mulCLM hs (realSobolevToBesselPotential E s 2 f)
        (realSobolevToBesselPotential E s 2 g) := by
  have hmem (h : realSobolevFunctions E s 2) : MemLp (fun x ↦ ((h : E → ℝ) x : ℂ)) 2 volume :=
    Complex.ofRealCLM.comp_memLp' (memLp_of_mem_realSobolevFunctions h.2)
  have hfg : MemLp (fun x ↦ (((f : E → ℝ) * g) x : ℂ)) 2 volume :=
    Complex.ofRealCLM.comp_memLp'
      (memLp_of_mem_realSobolevFunctions (mul_mem_realSobolevFunctions hs f.2 g.2))
  refine BesselPotentialSpace.ext ?_
  rw [toDistr_realSobolevToBesselPotential _ hfg.coeFn_toLp]
  refine (BesselPotentialSpace.toDistr_mulCLM_apply hs
    (toDistr_realSobolevToBesselPotential f (hmem f).coeFn_toLp)
    (toDistr_realSobolevToBesselPotential g (hmem g).coeFn_toLp) ?_).symm
  filter_upwards [hfg.coeFn_toLp, (hmem f).coeFn_toLp, (hmem g).coeFn_toLp] with x h h₁ h₂
  rw [h, h₁, h₂, Pi.mul_apply, Complex.ofReal_mul]

end TemperedDistribution
