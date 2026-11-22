/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
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

## Main results

* `ContinuousLinearMap.integral_inv_smul_bilinear_eq_convolution`: the raw multiplicative integral
  in logarithmic coordinates, without measurability, convergence or completeness hypotheses.

* `TauCeti.hasMellin_integral_mul_div`: the Mellin transform of `∫₀^∞ f(y) g(x/y) dy/y` is
  `𝓜f(s) 𝓜g(s)`, with absolute convergence.
* `TauCeti.hasMellin_integral_mul_comp_mul`: the Mellin transform of `∫₀^∞ f(t) h(xt) dt` is
  `𝓜f(1 - z) 𝓜h(z)` (DLMF 2.5.3–2.5.4).
* `TauCeti.integral_mul_comp_mul_eq_mellinInv`: the Parseval formula (DLMF 2.5.5).
* `TauCeti.mellinConv`: the multiplicative Mellin convolution `∫₀^∞ f(y) g(x/y) dy/y`, with
  commutativity on `(0, ∞)` without integrability (`TauCeti.mellinConv_comm`), linearity,
  support bounds (`TauCeti.support_mellinConv_subset_Icc`), and its Fubini Mellin product formula
  (`TauCeti.mellin_mellinConv_of_integrableOn`).

## References

* [DLMF] *NIST Digital Library of Mathematical Functions*, §2.5(i), <https://dlmf.nist.gov/2.5.i>.
* A. Kontorovich, T. Tao and contributors, *Prime Number Theorem And …*, §4.3 (Mellin convolution).

The proofs of the Parseval formula are adapted from the lean-DLMF project
(<https://github.com/bjbraams/lean-DLMF>), files `DLMFMathlib/Analysis/MellinConvolution.lean` and
`DLMF/AsymptoticApproximations/Mellin/Transforms.lean`.
-/

public section

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

/-! ### Multiplicative Mellin convolution -/

/-- The multiplicative Mellin convolution of two complex-valued functions on `(0, ∞)`:
`(mellinConv f g) x = ∫ y in (0, ∞), f y * g (x / y) / y`. -/
noncomputable def mellinConv (f g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y in Ioi (0 : ℝ), f y * g (x / y) / y

/-- Definitional unfolding of `mellinConv`. -/
theorem mellinConv_def (f g : ℝ → ℂ) (x : ℝ) :
    mellinConv f g x = ∫ y in Ioi (0 : ℝ), f y * g (x / y) / y := (rfl)

@[simp]
theorem mellinConv_zero_left (g : ℝ → ℂ) (x : ℝ) : mellinConv 0 g x = 0 := by
  simp [mellinConv_def]

@[simp]
theorem mellinConv_zero_right (f : ℝ → ℂ) (x : ℝ) : mellinConv f 0 x = 0 := by
  simp [mellinConv_def]

/-- Left scalar linearity of `mellinConv`. -/
theorem mellinConv_const_mul_left (c : ℂ) (f g : ℝ → ℂ) (x : ℝ) :
    mellinConv (fun y ↦ c * f y) g x = c * mellinConv f g x := by
  simp only [mellinConv_def, mul_assoc, mul_div_assoc, integral_const_mul]

/-- Right scalar linearity of `mellinConv`. -/
theorem mellinConv_const_mul_right (c : ℂ) (f g : ℝ → ℂ) (x : ℝ) :
    mellinConv f (fun y ↦ c * g y) x = c * mellinConv f g x := by
  rw [mellinConv_def, mellinConv_def, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun y _ ↦ ?_
  ring

/-- For `x > 0`, `mellinConv f g x` depends on `f` and `g` only through their values on `(0, ∞)`. -/
theorem mellinConv_congr {f₁ f₂ g₁ g₂ : ℝ → ℂ} (hf : EqOn f₁ f₂ (Ioi 0))
    (hg : EqOn g₁ g₂ (Ioi 0)) {x : ℝ} (hx : 0 < x) :
    mellinConv f₁ g₁ x = mellinConv f₂ g₂ x := by
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy ↦ ?_
  rw [hf hy, hg (div_pos hx hy)]

/-- Mellin convolution is commutative on `(0, ∞)`, with no integrability hypothesis. -/
theorem mellinConv_comm (f g : ℝ → ℂ) {x : ℝ} (hx : 0 < x) :
    mellinConv f g x = mellinConv g f x := by
  have h_log (u v : ℝ → ℂ) :
      mellinConv u v x = ∫ t : ℝ, u (Real.exp t) * v (Real.exp (Real.log x - t)) := by
    rw [mellinConv_def, ← integral_comp_exp]
    refine integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
    dsimp only
    rw [Complex.real_smul, Real.exp_sub, Real.exp_log hx]
    have hexp : ((Real.exp t : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.exp_ne_zero t)
    field_simp [hexp]
  rw [h_log f g, h_log g f, ← integral_sub_left_eq_self _ volume (Real.log x)]
  refine integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
  dsimp only
  rw [sub_sub_cancel, mul_comm]

/-- Left additivity of `mellinConv` where both component integrals converge. -/
theorem mellinConv_add_left {f₁ f₂ g : ℝ → ℂ} {x : ℝ}
    (h₁ : IntegrableOn (fun y : ℝ ↦ f₁ y * g (x / y) / y) (Ioi 0))
    (h₂ : IntegrableOn (fun y : ℝ ↦ f₂ y * g (x / y) / y) (Ioi 0)) :
    mellinConv (f₁ + f₂) g x = mellinConv f₁ g x + mellinConv f₂ g x := by
  rw [mellinConv_def, mellinConv_def, mellinConv_def, ← integral_add h₁ h₂]
  refine setIntegral_congr_fun measurableSet_Ioi fun y _ ↦ ?_
  simp only [Pi.add_apply]
  ring

/-- Right additivity of `mellinConv` where both component integrals converge. -/
theorem mellinConv_add_right {f g₁ g₂ : ℝ → ℂ} {x : ℝ}
    (h₁ : IntegrableOn (fun y : ℝ ↦ f y * g₁ (x / y) / y) (Ioi 0))
    (h₂ : IntegrableOn (fun y : ℝ ↦ f y * g₂ (x / y) / y) (Ioi 0)) :
    mellinConv f (g₁ + g₂) x = mellinConv f g₁ x + mellinConv f g₂ x := by
  rw [mellinConv_def, mellinConv_def, mellinConv_def, ← integral_add h₁ h₂]
  refine setIntegral_congr_fun measurableSet_Ioi fun y _ ↦ ?_
  simp only [Pi.add_apply]
  ring

/-- If `f` is supported in `[a, b]` and `g` is supported in `[c, d]` with `0 ≤ c`, then
`mellinConv f g` is supported in `[a * c, b * d]`. -/
theorem support_mellinConv_subset_Icc {f g : ℝ → ℂ} {a b c d : ℝ} (hc : 0 ≤ c)
    (hf : Function.support f ⊆ Icc a b) (hg : Function.support g ⊆ Icc c d) :
    Function.support (mellinConv f g) ⊆ Icc (a * c) (b * d) := by
  intro x hx
  by_contra hx'
  apply hx
  rw [mellinConv_def]
  refine setIntegral_eq_zero_of_forall_eq_zero fun y hy ↦ ?_
  by_cases hfy : f y = 0
  · simp [hfy]
  · by_cases hgy : g (x / y) = 0
    · simp [hgy]
    · exfalso
      have hyab : y ∈ Icc a b := hf hfy
      have hxycd : x / y ∈ Icc c d := hg hgy
      have hlo : a * c ≤ x := calc
        a * c ≤ y * c := mul_le_mul_of_nonneg_right hyab.1 hc
        _ ≤ y * (x / y) := mul_le_mul_of_nonneg_left hxycd.1 (le_of_lt hy)
        _ = x := mul_div_cancel₀ x (ne_of_gt hy)
      have hhi : x ≤ b * d := calc
        x = y * (x / y) := (mul_div_cancel₀ x (ne_of_gt hy)).symm
        _ ≤ y * d := mul_le_mul_of_nonneg_left hxycd.2 (le_of_lt hy)
        _ ≤ b * d := mul_le_mul_of_nonneg_right hyab.2 ((hc.trans hxycd.1).trans hxycd.2)
      exact hx' ⟨hlo, hhi⟩

/-- Fubini form of the Mellin convolution product formula: if the joint integrand
`(x, y) ↦ f y * g (x / y) * x ^ (s - 1) / y` is integrable on `(0, ∞) × (0, ∞)`, then
`mellin (mellinConv f g) s = mellin f s * mellin g s`. -/
theorem mellin_mellinConv_of_integrableOn {f g : ℝ → ℂ} {s : ℂ}
    (h : IntegrableOn (fun p : ℝ × ℝ ↦ f p.2 * g (p.1 / p.2) * (p.1 : ℂ) ^ (s - 1) / p.2)
      (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ))) :
    mellin (mellinConv f g) s = mellin f s * mellin g s := by
  have hprod : Integrable (fun p : ℝ × ℝ ↦ f p.2 * g (p.1 / p.2) * (p.1 : ℂ) ^ (s - 1) / p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact h
  calc
    mellin (mellinConv f g) s
      = ∫ x in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ),
          f y * g (x / y) * (x : ℂ) ^ (s - 1) / y := by
        rw [mellin]
        refine setIntegral_congr_fun measurableSet_Ioi fun x _ ↦ ?_
        rw [mellinConv_def, smul_eq_mul, ← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioi fun y _ ↦ ?_
        ring
    _ = ∫ y in Ioi (0 : ℝ), ∫ x in Ioi (0 : ℝ),
          f y * g (x / y) * (x : ℂ) ^ (s - 1) / y :=
        integral_integral_swap hprod
    _ = ∫ y in Ioi (0 : ℝ), (y : ℂ) ^ (s - 1) * f y * mellin g s := by
        refine setIntegral_congr_fun measurableSet_Ioi fun y hy ↦ ?_
        have hy0 : 0 < y := hy
        have hstep : (∫ x in Ioi (0 : ℝ), f y * g (x / y) * (x : ℂ) ^ (s - 1) / y) =
            (f y / y) * mellin (fun x ↦ g (y⁻¹ * x)) s := by
          rw [mellin, ← integral_const_mul]
          refine setIntegral_congr_fun measurableSet_Ioi fun x _ ↦ ?_
          rw [smul_eq_mul, div_eq_inv_mul x y]
          ring
        rw [hstep, mellin_comp_mul_left g s (inv_pos.mpr hy0), smul_eq_mul, ofReal_inv,
          inv_cpow_ofReal_nonneg hy0.le, cpow_neg, inv_inv]
        have hyc : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy0.ne'
        rw [cpow_sub _ _ hyc, cpow_one]
        ring
    _ = mellin f s * mellin g s := by
        rw [integral_mul_const]
        simp only [mellin, smul_eq_mul]

end TauCeti
