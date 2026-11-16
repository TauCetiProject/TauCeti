/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MellinInversion
public import Mathlib.Analysis.Convolution
public import TauCeti.Analysis.MellinTransform.Basic

/-!
# Mellin convolution and the Parseval formula (DLMF 2.5.3–2.5.5)

For `I(x) = ∫₀^∞ f(t) h(xt) dt`, the Mellin transform is `𝓜I(z) = 𝓜f(1 - z) 𝓜h(z)` wherever
both transforms on the right converge absolutely, and then Mellin inversion along a vertical line
`Re z = c` gives the Parseval formula
`I(x) = (2πi)⁻¹ ∫_{c-i∞}^{c+i∞} x^{-z} 𝓜f(1 - z) 𝓜h(z) dz`.

The proof passes to logarithmic coordinates (`TauCeti.mellinConvergent_iff_integrable_exp_smul`
and `TauCeti.mellin_eq_integral_exp_smul`). The substitution `t = e^{-u}` turns the multiplicative
convolution
`∫₀^∞ f(y) g(x/y) dy/y` into an ordinary convolution, so absolute convergence and the product
formula come from `MeasureTheory.Integrable.integrable_convolution` and
`MeasureTheory.integral_convolution`. The substitution `t ↦ 1/t` relates
`∫₀^∞ f(t) h(xt) dt` to that convolution.

The raw logarithmic-coordinate identity is stated for continuous real-bilinear maps before
imposing convergence. It underlies the complex Mellin product formula in this file.

We also package the multiplicative convolution as `TauCeti.mellinConv` and establish its algebraic
and analytic properties: commutativity for `x > 0` without integrability hypotheses, dependence
only on `(0, ∞)`, additivity and scaling, compact-support bounds, and the Mellin transform formula
both from separate `MellinConvergent` hypotheses and from joint integrability on `(0, ∞)²`.

## Main results

* `ContinuousLinearMap.integral_inv_smul_bilinear_eq_convolution`: the raw multiplicative integral
  in logarithmic coordinates, without measurability, convergence or completeness hypotheses.

* `TauCeti.hasMellin_integral_mul_div`: the Mellin transform of `∫₀^∞ f(y) g(x/y) dy/y` is
  `𝓜f(s) 𝓜g(s)`, with absolute convergence.
* `TauCeti.hasMellin_integral_mul_comp_mul`: the Mellin transform of `∫₀^∞ f(t) h(xt) dt` is
  `𝓜f(1 - z) 𝓜h(z)` (DLMF 2.5.3–2.5.4).
* `TauCeti.integral_mul_comp_mul_eq_mellinInv`: the Parseval formula (DLMF 2.5.5).
* `TauCeti.mellinConv`: the multiplicative convolution `∫₀^∞ f(y) g(x/y) dy/y`.
* `TauCeti.mellinConv_comm`: commutativity of `mellinConv` at every `x > 0`, with no integrability
  assumption.
* `TauCeti.support_mellinConv_subset`: support of `mellinConv f g` in `[a * c, b * d]` when `f`
  and `g` are supported in `[a, b]` and `[c, d]` with `0 ≤ c`.
* `TauCeti.hasMellin_mellinConv` and `TauCeti.hasMellin_mellinConv_of_integrableOn`: the Mellin
  transform of `mellinConv f g` is `𝓜f(s) 𝓜g(s)`.

## References

* [DLMF] *NIST Digital Library of Mathematical Functions*, §2.5(i), <https://dlmf.nist.gov/2.5.i>.
* Alex Kontorovich, Terence Tao, et al., *Prime Number Theorem And …*, §4.3 (Mellin convolution).

The Parseval and logarithmic-coordinate proofs are adapted from the lean-DLMF project
(<https://github.com/bjbraams/lean-DLMF>), files `DLMFMathlib/Analysis/MellinConvolution.lean` and
`DLMF/AsymptoticApproximations/Mellin/Transforms.lean`.
-/

@[expose] public section

open MeasureTheory Complex Set Filter
open scoped Topology

/-- Logarithmic coordinates turn the raw multiplicative convolution into ordinary
convolution. No convergence or measurability assumption is needed. -/
theorem ContinuousLinearMap.integral_inv_smul_bilinear_eq_convolution
    {E F G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
    [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ G]
    (L : E →L[ℝ] F →L[ℝ] G) (f : ℝ → E) (g : ℝ → F) (u : ℝ) :
    (∫ y in Ioi 0, y⁻¹ • L (f y) (g (Real.exp (-u) / y))) =
      convolution (fun v : ℝ => f (Real.exp (-v)))
        (fun v : ℝ => g (Real.exp (-v))) L volume u := by
  rw [← integral_comp_exp]
  simp only [smul_smul, mul_inv_cancel₀ (Real.exp_ne_zero _), one_smul]
  rw [← integral_neg_eq_self]
  unfold convolution
  apply integral_congr_ae (Eventually.of_forall fun v => ?_)
  have harg : Real.exp (-u) / Real.exp (-v) = Real.exp (-(u - v)) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [harg]

namespace TauCeti

/-- In logarithmic coordinates the multiplicative convolution becomes an ordinary
convolution. -/
private lemma integral_mul_div_eq_convolution (f g : ℝ → ℂ) (s : ℂ) (u : ℝ) :
    cexp (-s * u) * (∫ y in Ioi 0, f y * g (Real.exp (-u) / y) / y) =
      convolution (fun v : ℝ => cexp (-s * v) * f (Real.exp (-v)))
        (fun v : ℝ => cexp (-s * v) * g (Real.exp (-v)))
        (ContinuousLinearMap.mul ℂ ℂ) volume u := by
  have hchart := ContinuousLinearMap.integral_inv_smul_bilinear_eq_convolution
    (ContinuousLinearMap.mul ℝ ℂ) f g u
  have hraw : (∫ y in Ioi 0, f y * g (Real.exp (-u) / y) / y) =
      convolution (fun v : ℝ => f (Real.exp (-v)))
        (fun v : ℝ => g (Real.exp (-v))) (ContinuousLinearMap.mul ℂ ℂ) volume u := by
    convert hchart using 1
    · apply setIntegral_congr_fun measurableSet_Ioi
      intro y _
      dsimp only
      rw [ContinuousLinearMap.mul_apply', ← Complex.coe_smul, smul_eq_mul]
      push_cast
      ring
    · simp only [convolution, ContinuousLinearMap.mul_apply']
  rw [hraw, convolution, ← integral_const_mul]
  apply integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [ContinuousLinearMap.mul_apply']
  have he : cexp (-s * v) * cexp (-s * ((u - v : ℝ) : ℂ)) = cexp (-s * u) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [← he]
  ring

/-- The Mellin transform of the multiplicative convolution `∫₀^∞ f(y) g(x/y) dy/y` is the product
of the Mellin transforms, with absolute convergence. -/
theorem hasMellin_integral_mul_div {f g : ℝ → ℂ} {s : ℂ}
    (hf : MellinConvergent f s) (hg : MellinConvergent g s) :
    HasMellin (fun x : ℝ => ∫ y in Ioi 0, f y * g (x / y) / y) s
      (mellin f s * mellin g s) := by
  have hlog (k : ℝ → ℂ) : mellin k s = ∫ u : ℝ, cexp (-s * u) * k (Real.exp (-u)) := by
    simpa only [smul_eq_mul] using mellin_eq_integral_exp_smul k s
  have hfi : Integrable fun u : ℝ => cexp (-s * u) * f (Real.exp (-u)) := by
    simpa only [smul_eq_mul] using (mellinConvergent_iff_integrable_exp_smul f s).mp hf
  have hgi : Integrable fun u : ℝ => cexp (-s * u) * g (Real.exp (-u)) := by
    simpa only [smul_eq_mul] using (mellinConvergent_iff_integrable_exp_smul g s).mp hg
  have hfun := funext (integral_mul_div_eq_convolution f g s)
  refine ⟨(mellinConvergent_iff_integrable_exp_smul _ _).mpr ?_, ?_⟩
  · simp only [smul_eq_mul]
    rw [hfun]
    exact hfi.integrable_convolution (L := ContinuousLinearMap.mul ℂ ℂ) hgi
  · rw [hlog, hfun, integral_convolution (ContinuousLinearMap.mul ℂ ℂ) hfi hgi]
    simp only [ContinuousLinearMap.mul_apply', ← hlog]

/-- The substitution `y = 1/t` turns `∫₀^∞ f(t) h(xt) dt` into a multiplicative
convolution. -/
private lemma integral_inv_div_mul_div (f h : ℝ → ℂ) (x : ℝ) :
    (∫ y in Ioi (0 : ℝ), f y⁻¹ / y * h (x / y) / y) = ∫ t in Ioi 0, f t * h (x * t) := by
  have he := mellin_comp_inv (fun y => f y * h (x * y)) (-1 : ℂ)
  have hleft : mellin (fun y => f y⁻¹ * h (x * y⁻¹)) (-1) =
      ∫ y in Ioi (0 : ℝ), f y⁻¹ / y * h (x / y) / y := by
    unfold mellin
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y _
    dsimp only
    rw [show (-1 : ℂ) - 1 = -(2 : ℂ) by norm_num, cpow_neg, cpow_two]
    simp only [smul_eq_mul]
    rw [div_eq_mul_inv x y]
    field_simp
  rw [hleft] at he
  simpa only [neg_neg, mellin, sub_self, cpow_zero, one_smul] using he

/-- DLMF 2.5.3–2.5.4: if `𝓜f(1 - z)` and `𝓜h(z)` converge absolutely, then
`I(x) = ∫₀^∞ f(t) h(xt) dt` has the absolutely convergent Mellin transform
`𝓜I(z) = 𝓜f(1 - z) 𝓜h(z)`. -/
theorem hasMellin_integral_mul_comp_mul {f h : ℝ → ℂ} {z : ℂ} (hf : MellinConvergent f (1 - z))
    (hh : MellinConvergent h z) :
    HasMellin (fun x => ∫ t in Ioi 0, f t * h (x * t)) z (mellin f (1 - z) * mellin h z) := by
  have hk : MellinConvergent (fun y : ℝ => f y⁻¹ / y) z := by
    simpa only [smul_eq_mul, div_eq_inv_mul] using mellinConvergent_inv_smul_comp_inv hf
  have he := hasMellin_integral_mul_div hk hh
  rw [funext (integral_inv_div_mul_div f h)] at he
  have hmel : mellin (fun y : ℝ => f y⁻¹ / y) z = mellin f (1 - z) := by
    simpa only [smul_eq_mul, div_eq_inv_mul] using mellin_inv_smul_comp_inv f z
  rwa [hmel] at he

/-- DLMF 2.5.5, the Parseval formula: if `𝓜f(1 - z)` and `𝓜h(z)` converge absolutely on the line
`Re z = c`, their product is integrable along that line, and `I(x) = ∫₀^∞ f(t) h(xt) dt` is
continuous at `x > 0`, then `I(x) = (2πi)⁻¹ ∫_{c-i∞}^{c+i∞} x^{-z} 𝓜f(1 - z) 𝓜h(z) dz`. -/
theorem integral_mul_comp_mul_eq_mellinInv {f h : ℝ → ℂ} {c x : ℝ} (hx : 0 < x)
    (hconv : ∀ z : ℂ, z.re = c → MellinConvergent f (1 - z) ∧ MellinConvergent h z)
    (hint : VerticalIntegrable (fun z => mellin f (1 - z) * mellin h z) c)
    (hcont : ContinuousAt (fun x => ∫ t in Ioi 0, f t * h (x * t)) x) :
    (∫ t in Ioi 0, f t * h (x * t)) =
      mellinInv c (fun z => mellin f (1 - z) * mellin h z) x := by
  set Iv : ℝ → ℂ := fun x => ∫ t in Ioi 0, f t * h (x * t) with hIv
  have hline : ∀ y : ℝ, mellin Iv ((c : ℂ) + y * I) =
      mellin f (1 - ((c : ℂ) + y * I)) * mellin h ((c : ℂ) + y * I) := fun y => by
    have hz := hconv ((c : ℂ) + y * I) (by simp)
    exact (hasMellin_integral_mul_comp_mul hz.1 hz.2).2
  have hIc : MellinConvergent Iv (c : ℂ) := by
    have hz := hconv (c : ℂ) (by simp)
    exact (hasMellin_integral_mul_comp_mul hz.1 hz.2).1
  have hV : VerticalIntegrable (mellin Iv) c := by
    unfold VerticalIntegrable at hint ⊢
    simp only [hline]
    exact hint
  calc (∫ t in Ioi 0, f t * h (x * t)) = Iv x := by rw [hIv]
    _ = mellinInv c (mellin Iv) x := (mellinInv_mellin_eq c Iv hx hIc hV hcont).symm
    _ = _ := by
      unfold mellinInv
      simp only [hline]

end TauCeti

end

public section

open MeasureTheory Complex Set Filter

namespace TauCeti

/-- The multiplicative (Mellin) convolution of `f` and `g`:
`(mellinConv f g x) = ∫ y in Ioi 0, f y * g (x / y) / y`. -/
noncomputable def mellinConv (f g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y in Ioi 0, f y * g (x / y) / y

/-- Unfolding lemma for `mellinConv`. -/
theorem mellinConv_def (f g : ℝ → ℂ) (x : ℝ) :
    mellinConv f g x = ∫ y in Ioi 0, f y * g (x / y) / y := (rfl)

/-- For `x > 0`, `mellinConv f g x` depends on `f` and `g` only through their values on `(0, ∞)`. -/
theorem mellinConv_congr {f₁ f₂ g₁ g₂ : ℝ → ℂ} {x : ℝ} (hx : 0 < x)
    (hf : EqOn f₁ f₂ (Ioi 0)) (hg : EqOn g₁ g₂ (Ioi 0)) :
    mellinConv f₁ g₁ x = mellinConv f₂ g₂ x := by
  simp only [mellinConv_def]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy ↦ ?_
  rw [hf hy, hg (div_pos hx hy)]

/-- For `x > 0`, the involution `y ↦ x / y` on `(0, ∞)` is quasi-measure-preserving for the
restricted Lebesgue measure. -/
theorem quasiMeasurePreserving_div_left_Ioi {x : ℝ} (hx : 0 < x) :
    QuasiMeasurePreserving (fun y : ℝ ↦ x / y)
      (volume.restrict (Ioi 0)) (volume.restrict (Ioi 0)) := by
  have hmeas : Measurable (fun y : ℝ ↦ x / y) := by fun_prop
  refine ⟨hmeas.aemeasurable, Measure.AbsolutelyContinuous.mk fun s hs h0 ↦ ?_⟩
  rw [Measure.map_apply hmeas hs, Measure.restrict_apply (hmeas hs)]
  rw [Measure.restrict_apply hs] at h0
  have hpre : (fun y : ℝ ↦ x / y) ⁻¹' s ∩ Ioi 0 = (fun y : ℝ ↦ x / y) '' (s ∩ Ioi 0) := by
    ext y
    simp only [mem_inter_iff, mem_preimage, mem_Ioi, mem_image]
    constructor
    · rintro ⟨hys, hy0⟩
      refine ⟨x / y, ⟨hys, div_pos hx hy0⟩, ?_⟩
      field_simp [hy0.ne']
    · rintro ⟨z, ⟨hzs, hz0⟩, rfl⟩
      refine ⟨?_, div_pos hx hz0⟩
      have hdiv : x / (x / z) = z := by field_simp [hx.ne', hz0.ne']
      rwa [hdiv]
  rw [hpre]
  have hdiff : DifferentiableOn ℝ (fun y : ℝ ↦ x / y) (s ∩ Ioi 0) := fun y hy ↦
    ((differentiableAt_const x).div differentiableAt_id hy.2.ne').differentiableWithinAt
  exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hdiff h0

/-- Express `mellinConv f g x` at `x > 0` as a convolution in logarithmic coordinates. -/
private lemma mellinConv_eq_integral_log (f g : ℝ → ℂ) {x : ℝ} (hx : 0 < x) :
    mellinConv f g x =
      ∫ v : ℝ, f (Real.exp (-v)) * g (Real.exp (-(-Real.log x - v))) := by
  have hchart := ContinuousLinearMap.integral_inv_smul_bilinear_eq_convolution
    (ContinuousLinearMap.mul ℝ ℂ) f g (-Real.log x)
  rw [neg_neg, Real.exp_log hx] at hchart
  rw [mellinConv_def]
  trans (∫ y in Ioi 0, y⁻¹ • (ContinuousLinearMap.mul ℝ ℂ) (f y) (g (x / y)))
  · refine setIntegral_congr_fun measurableSet_Ioi fun y _ ↦ ?_
    rw [ContinuousLinearMap.mul_apply', ← Complex.coe_smul, smul_eq_mul]
    push_cast
    ring
  · rw [hchart, convolution]
    simp only [ContinuousLinearMap.mul_apply']

/-- Multiplicative convolution is commutative at every `x > 0`, with no integrability or
measurability hypothesis. -/
theorem mellinConv_comm (f g : ℝ → ℂ) {x : ℝ} (hx : 0 < x) :
    mellinConv f g x = mellinConv g f x := by
  rw [mellinConv_eq_integral_log f g hx, mellinConv_eq_integral_log g f hx,
    ← MeasureTheory.integral_sub_left_eq_self
      (fun v ↦ f (Real.exp (-v)) * g (Real.exp (-(-Real.log x - v)))) volume (-Real.log x)]
  refine integral_congr_ae (Eventually.of_forall fun v ↦ ?_)
  dsimp only
  rw [sub_sub_cancel, mul_comm]

@[simp]
theorem mellinConv_zero_left (g : ℝ → ℂ) (x : ℝ) : mellinConv 0 g x = 0 := by
  simp [mellinConv_def]

@[simp]
theorem mellinConv_zero_right (f : ℝ → ℂ) (x : ℝ) : mellinConv f 0 x = 0 := by
  simp [mellinConv_def]

/-- Scaling the left factor pulls out of `mellinConv`. -/
theorem mellinConv_const_mul_left (c : ℂ) (f g : ℝ → ℂ) (x : ℝ) :
    mellinConv (fun y ↦ c * f y) g x = c * mellinConv f g x := by
  simp only [mellinConv_def, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun y _ ↦ ?_
  ring

/-- Scaling the right factor pulls out of `mellinConv`. -/
theorem mellinConv_const_mul_right (c : ℂ) (f g : ℝ → ℂ) (x : ℝ) :
    mellinConv f (fun y ↦ c * g y) x = c * mellinConv f g x := by
  simp only [mellinConv_def, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun y _ ↦ ?_
  ring

/-- `mellinConv` is additive in the left argument when both integrals converge. -/
theorem mellinConv_add_left {f₁ f₂ g : ℝ → ℂ} {x : ℝ}
    (h₁ : IntegrableOn (fun y ↦ f₁ y * g (x / y) / y) (Ioi 0))
    (h₂ : IntegrableOn (fun y ↦ f₂ y * g (x / y) / y) (Ioi 0)) :
    mellinConv (f₁ + f₂) g x = mellinConv f₁ g x + mellinConv f₂ g x := by
  simp only [mellinConv_def, Pi.add_apply, add_mul, add_div]
  exact integral_add h₁ h₂

/-- `mellinConv` is additive in the right argument when both integrals converge. -/
theorem mellinConv_add_right {f g₁ g₂ : ℝ → ℂ} {x : ℝ}
    (h₁ : IntegrableOn (fun y ↦ f y * g₁ (x / y) / y) (Ioi 0))
    (h₂ : IntegrableOn (fun y ↦ f y * g₂ (x / y) / y) (Ioi 0)) :
    mellinConv f (g₁ + g₂) x = mellinConv f g₁ x + mellinConv f g₂ x := by
  simp only [mellinConv_def, Pi.add_apply, mul_add, add_div]
  exact integral_add h₁ h₂

@[simp]
theorem mellinConv_neg_left (f g : ℝ → ℂ) (x : ℝ) :
    mellinConv (-f) g x = -mellinConv f g x := by
  simp only [mellinConv_def, Pi.neg_apply, neg_mul, neg_div, integral_neg]

@[simp]
theorem mellinConv_neg_right (f g : ℝ → ℂ) (x : ℝ) :
    mellinConv f (-g) x = -mellinConv f g x := by
  simp only [mellinConv_def, Pi.neg_apply, mul_neg, neg_div, integral_neg]

/-- `mellinConv` respects subtraction in the left argument when both integrals converge. -/
theorem mellinConv_sub_left {f₁ f₂ g : ℝ → ℂ} {x : ℝ}
    (h₁ : IntegrableOn (fun y ↦ f₁ y * g (x / y) / y) (Ioi 0))
    (h₂ : IntegrableOn (fun y ↦ f₂ y * g (x / y) / y) (Ioi 0)) :
    mellinConv (f₁ - f₂) g x = mellinConv f₁ g x - mellinConv f₂ g x := by
  simp only [mellinConv_def, Pi.sub_apply, sub_mul, sub_div]
  exact integral_sub h₁ h₂

/-- `mellinConv` respects subtraction in the right argument when both integrals converge. -/
theorem mellinConv_sub_right {f g₁ g₂ : ℝ → ℂ} {x : ℝ}
    (h₁ : IntegrableOn (fun y ↦ f y * g₁ (x / y) / y) (Ioi 0))
    (h₂ : IntegrableOn (fun y ↦ f y * g₂ (x / y) / y) (Ioi 0)) :
    mellinConv f (g₁ - g₂) x = mellinConv f g₁ x - mellinConv f g₂ x := by
  simp only [mellinConv_def, Pi.sub_apply, mul_sub, sub_div]
  exact integral_sub h₁ h₂

/-- Convolving a function `g` with the sharp cutoff `1_(0,1]` integrates `g(y) / y` over
`(x, ∞)` for every `x > 0`, with no integrability hypothesis. -/
theorem mellinConv_indicator_Ioc_one (g : ℝ → ℂ) {x : ℝ} (hx : 0 < x) :
    mellinConv ((Ioc 0 1).indicator 1) g x = ∫ y in Ioi x, g y / y := by
  rw [mellinConv_comm _ _ hx, mellinConv_def]
  have heq : EqOn (fun y : ℝ ↦ g y * (Ioc 0 1).indicator (1 : ℝ → ℂ) (x / y) / y)
      ((Ici x).indicator (fun y : ℝ ↦ g y / y)) (Ioi 0) := by
    intro y hy
    have hy0 : 0 < y := hy
    by_cases hxy : x ≤ y
    · have hmem : x / y ∈ Ioc 0 1 := ⟨div_pos hx hy0, (div_le_one hy0).mpr hxy⟩
      simp [hmem, hxy]
    · have hnot : x / y ∉ Ioc 0 1 := fun h ↦ hxy ((div_le_one hy0).mp h.2)
      simp [hnot, hxy]
  rw [setIntegral_congr_fun measurableSet_Ioi heq, setIntegral_indicator measurableSet_Ici,
    inter_eq_right.mpr (Ici_subset_Ioi.mpr hx), integral_Ici_eq_integral_Ioi]

/-- If `f` is supported in `[a, b]` and `g` in `[c, d]` with `0 ≤ c`, then
`mellinConv f g` is supported in `[a * c, b * d]`. -/
theorem support_mellinConv_subset {f g : ℝ → ℂ} {a b c d : ℝ} (hc : 0 ≤ c)
    (hf : Function.support f ⊆ Icc a b) (hg : Function.support g ⊆ Icc c d) :
    Function.support (mellinConv f g) ⊆ Icc (a * c) (b * d) := by
  intro x hx
  by_contra hnot
  apply hx
  rw [mellinConv_def]
  refine setIntegral_eq_zero_of_forall_eq_zero fun y hy ↦ ?_
  by_contra hne
  have hfy : y ∈ Icc a b := hf fun h0 ↦ hne (by simp [h0])
  have hgx : x / y ∈ Icc c d := hg fun h0 ↦ hne (by simp [h0])
  have hy0 : 0 < y := hy
  have hcy : c * y ≤ x := (le_div_iff₀ hy0).mp hgx.1
  have hdy : x ≤ d * y := (div_le_iff₀ hy0).mp hgx.2
  have hd0 : 0 ≤ d := hc.trans (hgx.1.trans hgx.2)
  exact hnot ⟨by nlinarith [hfy.1], by nlinarith [hfy.2]⟩

/-- The Mellin transform of `mellinConv f g` at `s` is `mellin f s * mellin g s`, with absolute
convergence, whenever `f` and `g` are Mellin convergent at `s`. -/
theorem hasMellin_mellinConv {f g : ℝ → ℂ} {s : ℂ}
    (hf : MellinConvergent f s) (hg : MellinConvergent g s) :
    HasMellin (mellinConv f g) s (mellin f s * mellin g s) := by
  rw [funext (mellinConv_def f g)]
  exact hasMellin_integral_mul_div hf hg

/-- The Mellin transform of `mellinConv f g` at `s` is `mellin f s * mellin g s` whenever `f` and
`g` are Mellin convergent at `s`. -/
theorem mellin_mellinConv {f g : ℝ → ℂ} {s : ℂ}
    (hf : MellinConvergent f s) (hg : MellinConvergent g s) :
    mellin (mellinConv f g) s = mellin f s * mellin g s :=
  (hasMellin_mellinConv hf hg).2

/-- If `(x, y) ↦ f y * g (x / y) * x ^ (s - 1) / y` is jointly integrable on `(0, ∞)²`, then
`mellinConv f g` has Mellin transform `mellin f s * mellin g s` at `s`. -/
theorem hasMellin_mellinConv_of_integrableOn {f g : ℝ → ℂ} {s : ℂ}
    (h : IntegrableOn (fun p : ℝ × ℝ ↦ f p.2 * g (p.1 / p.2) * (p.1 : ℂ) ^ (s - 1) / p.2)
      (Ioi 0 ×ˢ Ioi 0)) :
    HasMellin (mellinConv f g) s (mellin f s * mellin g s) := by
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  have hprod : Integrable (fun p : ℝ × ℝ ↦ f p.2 * g (p.1 / p.2) * (p.1 : ℂ) ^ (s - 1) / p.2)
      (μ.prod μ) := by
    simpa only [IntegrableOn, μ, Measure.prod_restrict, ← Measure.volume_eq_prod] using h
  have hinner (x : ℝ) :
      (x : ℂ) ^ (s - 1) • mellinConv f g x =
        ∫ y, f y * g (x / y) * (x : ℂ) ^ (s - 1) / y ∂μ := by
    rw [mellinConv_def, smul_eq_mul, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
    ring
  refine ⟨?_, ?_⟩
  · refine (hprod.integral_prod_left).congr (Eventually.of_forall fun x ↦ (hinner x).symm)
  · rw [mellin]
    have h1 : (∫ x, (x : ℂ) ^ (s - 1) • mellinConv f g x ∂μ) =
        ∫ x, (∫ y, f y * g (x / y) * (x : ℂ) ^ (s - 1) / y ∂μ) ∂μ :=
      integral_congr_ae (Eventually.of_forall hinner)
    rw [h1, ← integral_prod _ hprod, integral_prod_symm _ hprod]
    have h2 : (∫ y, (∫ x, f y * g (x / y) * (x : ℂ) ^ (s - 1) / y ∂μ) ∂μ) =
        ∫ y, ((y : ℂ) ^ (s - 1) • f y) * mellin g s ∂μ := by
      refine setIntegral_congr_fun measurableSet_Ioi fun y hy ↦ ?_
      have hy0 : 0 < y := hy
      have hpull : (∫ x, f y * g (x / y) * (x : ℂ) ^ (s - 1) / y ∂μ) =
          (f y / y) * mellin (fun x ↦ g (x * y⁻¹)) s := by
        rw [mellin, ← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
        dsimp only
        rw [smul_eq_mul, div_eq_mul_inv x y]
        ring
      rw [hpull, mellin_comp_mul_right g s (inv_pos.mpr hy0), Complex.ofReal_inv,
        Complex.inv_cpow_ofReal_nonneg hy0.le, Complex.cpow_neg, inv_inv, smul_eq_mul,
        smul_eq_mul, Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr hy0.ne'), Complex.cpow_one]
      ring
    rw [h2, integral_mul_const]
    rfl

example {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    mellinConv ((Ioc 0 1).indicator 1) ((Ioc 0 1).indicator 1) x = (Real.log x⁻¹ : ℂ) := by
  rw [mellinConv_indicator_Ioc_one _ hx0]
  have heq : EqOn (fun y : ℝ ↦ (Ioc 0 1).indicator (1 : ℝ → ℂ) y / y)
      ((Ioc 0 1).indicator fun y : ℝ ↦ ((y⁻¹ : ℝ) : ℂ)) (Ioi x) := by
    intro y _
    by_cases hy : y ∈ Ioc 0 1 <;> simp [hy]
  have hinter : Ioi x ∩ Ioc 0 1 = Ioc x 1 := by
    ext y
    simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
    constructor <;> intro ⟨h1, h2⟩ <;> grind
  rw [setIntegral_congr_fun measurableSet_Ioi heq, setIntegral_indicator measurableSet_Ioc,
    hinter, ← intervalIntegral.integral_of_le hx1, intervalIntegral.integral_ofReal,
    integral_inv_of_pos hx0 zero_lt_one, one_div]

end TauCeti

end
