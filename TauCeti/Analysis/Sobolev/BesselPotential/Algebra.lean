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
estimate makes the product a bounded bilinear operation for the `H^s` norm, so that polynomial
expressions depend continuously on `H^s` fields and multiplication `(1 + h)(1 + g)` is continuous
for the distance `‖h - g‖_{H^s}`.

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
* `BesselPotentialSpace.mulCLM`: the pointwise product on `H^s(E)`, `s > n / 2`, as a continuous
  bilinear map, characterized by `BesselPotentialSpace.toDistr_mulCLM_of_ae_eq`.

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

variable {s : ℝ}

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
private theorem nonneg_of_finrank_lt (hs : finrank ℝ E < 2 * s) : 0 ≤ s := by
  have := (finrank ℝ E).cast_nonneg (α := ℝ)
  linarith

/-- The `L²` function of `u ∈ H^s`, `s > n / 2`. -/
private abbrev rep (hs : finrank ℝ E < 2 * s) (u : H^{s}(E)) : Lp ℂ 2 (volume : Measure E) :=
  (inclusion (nonneg_of_finrank_lt hs) u).toLp

private theorem toDistr_eq_rep (hs : finrank ℝ E < 2 * s) (u : H^{s}(E)) :
    u.toDistr = (rep hs u : 𝓢'(E, ℂ)) :=
  (toTemperedDistribution_toLp_inclusion _ u).symm

private theorem rep_add (hs : finrank ℝ E < 2 * s) (u v : H^{s}(E)) :
    rep hs (u + v) = rep hs u + rep hs v := by
  simp only [rep, map_add, toLp_add]

private theorem rep_smul (hs : finrank ℝ E < 2 * s) (c : ℂ) (u : H^{s}(E)) :
    rep hs (c • u) = c • rep hs u := by
  simp only [rep, map_smul, toLp_smul]

/-- Elements of `H^s`, `s > n / 2`, with the same `L²` function are equal. -/
private theorem eq_of_rep_ae_eq (hs : finrank ℝ E < 2 * s) {u v : H^{s}(E)}
    (h : rep hs u =ᵐ[volume] rep hs v) : u = v := by
  ext1
  rw [toDistr_eq_rep hs u, toDistr_eq_rep hs v, Lp.ext h]

/-- The `L²` function of `u ∈ H^s`, `s > n / 2`, lies in `H^s`. -/
private theorem memSobolev_rep (hs : finrank ℝ E < 2 * s) (u : H^{s}(E)) :
    MemSobolev s 2 (rep hs u : 𝓢'(E, ℂ)) := by
  rw [← toDistr_eq_rep]
  exact u.memSobolev_toDistr

/-- The pointwise product of the `L²` functions of `u, v ∈ H^s`, `s > n / 2`, as an element of
`H^s`. -/
private def mulAux (hs : finrank ℝ E < 2 * s) (u v : H^{s}(E)) : H^{s}(E) :=
  ((memSobolev_rep hs u).mul hs (memSobolev_rep hs v)).toBesselPotentialSpace

private theorem rep_mulAux (hs : finrank ℝ E < 2 * s) (u v : H^{s}(E)) :
    rep hs (mulAux hs u v) =ᵐ[volume] fun x ↦ rep hs u x * rep hs v x := by
  have h : rep hs (mulAux hs u v) = ((memSobolev_rep hs u).memLp_mul hs (rep hs v)).toLp _ :=
    LinearMap.ker_eq_bot.mp Lp.ker_toTemperedDistributionCLM_eq_bot <| by
      rw [ContinuousLinearMap.coe_coe, Lp.toTemperedDistributionCLM_apply,
        Lp.toTemperedDistributionCLM_apply, ← toDistr_eq_rep, mulAux,
        MemSobolev.toBesselPotentialSpace_toDistr]
  rw [h]
  exact MemLp.coeFn_toLp _

private theorem mulAux_add_left (hs : finrank ℝ E < 2 * s) (u u' v : H^{s}(E)) :
    mulAux hs (u + u') v = mulAux hs u v + mulAux hs u' v := by
  refine eq_of_rep_ae_eq hs ?_
  rw [rep_add hs (mulAux hs u v)]
  filter_upwards [rep_mulAux hs (u + u') v, rep_mulAux hs u v, rep_mulAux hs u' v,
    Lp.coeFn_add (rep hs (mulAux hs u v)) (rep hs (mulAux hs u' v)),
    Lp.coeFn_add (rep hs u) (rep hs u')] with x h h₁ h₂ h₃ h₄
  rw [h, h₃, Pi.add_apply, h₁, h₂, rep_add, h₄, Pi.add_apply, add_mul]

private theorem mulAux_add_right (hs : finrank ℝ E < 2 * s) (u v v' : H^{s}(E)) :
    mulAux hs u (v + v') = mulAux hs u v + mulAux hs u v' := by
  refine eq_of_rep_ae_eq hs ?_
  rw [rep_add hs (mulAux hs u v)]
  filter_upwards [rep_mulAux hs u (v + v'), rep_mulAux hs u v, rep_mulAux hs u v',
    Lp.coeFn_add (rep hs (mulAux hs u v)) (rep hs (mulAux hs u v')),
    Lp.coeFn_add (rep hs v) (rep hs v')] with x h h₁ h₂ h₃ h₄
  rw [h, h₃, Pi.add_apply, h₁, h₂, rep_add, h₄, Pi.add_apply, mul_add]

private theorem mulAux_smul_left (hs : finrank ℝ E < 2 * s) (c : ℂ) (u v : H^{s}(E)) :
    mulAux hs (c • u) v = c • mulAux hs u v := by
  refine eq_of_rep_ae_eq hs ?_
  rw [rep_smul hs c (mulAux hs u v)]
  filter_upwards [rep_mulAux hs (c • u) v, rep_mulAux hs u v,
    Lp.coeFn_smul c (rep hs (mulAux hs u v)), Lp.coeFn_smul c (rep hs u)] with x h h₁ h₂ h₃
  rw [h, h₂, Pi.smul_apply, h₁, rep_smul, h₃, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_assoc]

private theorem mulAux_smul_right (hs : finrank ℝ E < 2 * s) (c : ℂ) (u v : H^{s}(E)) :
    mulAux hs u (c • v) = c • mulAux hs u v := by
  refine eq_of_rep_ae_eq hs ?_
  rw [rep_smul hs c (mulAux hs u v)]
  filter_upwards [rep_mulAux hs u (c • v), rep_mulAux hs u v,
    Lp.coeFn_smul c (rep hs (mulAux hs u v)), Lp.coeFn_smul c (rep hs v)] with x h h₁ h₂ h₃
  rw [h, h₂, Pi.smul_apply, h₁, rep_smul, h₃, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
    mul_left_comm]

/-- **The product on `H^s(E)`, `s > n / 2`, as a continuous bilinear map.** It sends `u, v ∈ H^s`
to their pointwise product, which lies in `H^s` by `TemperedDistribution.MemSobolev.mul`
(`BesselPotentialSpace.toDistr_mulCLM_of_ae_eq`). Its continuity is the algebra estimate
`TemperedDistribution.exists_norm_toBesselPotentialSpace_mul_le`. -/
def mulCLM (hs : finrank ℝ E < 2 * s) : H^{s}(E) →L[ℂ] H^{s}(E) →L[ℂ] H^{s}(E) :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℂ (mulAux hs) (mulAux_add_left hs) (mulAux_smul_left hs)
      (mulAux_add_right hs) (mulAux_smul_right hs))
    (exists_norm_toBesselPotentialSpace_mul_le hs).choose fun u v ↦ by
      have hu : (memSobolev_rep hs u).toBesselPotentialSpace = u :=
        ext (by rw [MemSobolev.toBesselPotentialSpace_toDistr, toDistr_eq_rep])
      have hv : (memSobolev_rep hs v).toBesselPotentialSpace = v :=
        ext (by rw [MemSobolev.toBesselPotentialSpace_toDistr, toDistr_eq_rep])
      have h := (exists_norm_toBesselPotentialSpace_mul_le hs).choose_spec.2
        (memSobolev_rep hs u) (memSobolev_rep hs v)
      rwa [hu, hv] at h

private theorem mulCLM_apply (hs : finrank ℝ E < 2 * s) (u v : H^{s}(E)) :
    mulCLM hs u v = mulAux hs u v :=
  rfl

/-- **Characterization of the product on `H^s(E)`, `s > n / 2`.** If `u, v ∈ H^s` are the `L²`
functions `f` and `g`, then `mulCLM hs u v` is every `L²` function equal to `f g` almost
everywhere. -/
theorem toDistr_mulCLM_of_ae_eq (hs : finrank ℝ E < 2 * s) {u v : H^{s}(E)}
    {f g h : Lp ℂ 2 (volume : Measure E)} (hf : u.toDistr = f) (hg : v.toDistr = g)
    (hh : h =ᵐ[volume] fun x ↦ f x * g x) :
    (mulCLM hs u v).toDistr = h := by
  have hf' : rep hs u = f := LinearMap.ker_eq_bot.mp Lp.ker_toTemperedDistributionCLM_eq_bot <| by
    rw [ContinuousLinearMap.coe_coe, Lp.toTemperedDistributionCLM_apply,
      Lp.toTemperedDistributionCLM_apply, ← toDistr_eq_rep, hf]
  have hg' : rep hs v = g := LinearMap.ker_eq_bot.mp Lp.ker_toTemperedDistributionCLM_eq_bot <| by
    rw [ContinuousLinearMap.coe_coe, Lp.toTemperedDistributionCLM_apply,
      Lp.toTemperedDistributionCLM_apply, ← toDistr_eq_rep, hg]
  rw [toDistr_eq_rep hs, mulCLM_apply]
  congr 1
  refine Lp.ext ?_
  filter_upwards [rep_mulAux hs u v, hh] with x h₁ h₂
  rw [h₁, h₂, hf', hg']

end BesselPotentialSpace
