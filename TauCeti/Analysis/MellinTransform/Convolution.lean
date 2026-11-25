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

The multiplicative Mellin convolution `mellinConv f g x = ∫₀^∞ f(y) g(x/y) dy/y` has Mellin
transform `𝓜f(s) 𝓜g(s)` wherever both transforms on the right converge absolutely. For
`I(x) = ∫₀^∞ f(t) h(xt) dt`, which is the Mellin convolution of `y ↦ f(1/y)/y` with `h`, this
gives `𝓜I(z) = 𝓜f(1 - z) 𝓜h(z)`. If moreover both transforms converge absolutely on a vertical
line `Re z = c`, their product is integrable along that line, and `I` is continuous at `x > 0`,
Mellin inversion gives the Parseval formula
`I(x) = (2πi)⁻¹ ∫_{c-i∞}^{c+i∞} x^{-z} 𝓜f(1 - z) 𝓜h(z) dz`.

The proofs pass to logarithmic coordinates (`TauCeti.mellinConvergent_iff_integrable_exp_smul`
and `TauCeti.mellin_eq_integral_exp_smul`). The substitution `t = e^{-u}` turns the multiplicative
convolution into an ordinary convolution, so absolute convergence and the product formula come
from `MeasureTheory.Integrable.integrable_convolution` and `MeasureTheory.integral_convolution`,
and commutativity on `(0, ∞)` comes from `MeasureTheory.convolution_symm`. The raw
logarithmic-coordinate identity is stated for continuous real-bilinear maps before imposing
convergence.

## Main definitions

* `TauCeti.mellinConv f g`: the multiplicative Mellin convolution `∫₀^∞ f(y) g(x/y) dy/y`.

## Main results

* `ContinuousLinearMap.integral_inv_smul_bilinear_eq_convolution`: the raw multiplicative integral
  in logarithmic coordinates, without measurability, convergence or completeness hypotheses.
* `TauCeti.mellinConv_exp_neg_eq_convolution`: in logarithmic coordinates `x = e^{-u}` the Mellin
  convolution is an ordinary convolution, with no integrability hypothesis.
* `TauCeti.mellinConv_comm_of_pos`: `mellinConv f g x = mellinConv g f x` for `x > 0`, with no
  integrability hypothesis.
* `TauCeti.mellinConv_const_mul_left`, `TauCeti.mellinConv_const_mul_right`: scalar homogeneity in
  each argument; `TauCeti.mellinConv_add_left`, `TauCeti.mellinConv_add_right`: additivity in each
  argument where both component integrals converge.
* `TauCeti.mellinConv_congr`, `TauCeti.mellinConv_congr_ae`: at `x > 0` the convolution only
  depends on the values on `(0, ∞)`, and only on their classes up to null sets there.
* `TauCeti.support_mellinConv_inter_Ioi_subset_Icc`: if `f` and `g` vanish on `(0, ∞)` off
  `[a, b]` and `[c, d]` with `0 ≤ c`, then `mellinConv f g` vanishes on `(0, ∞)` off
  `[a * c, b * d]`.
* `TauCeti.hasMellin_mellinConv`: if `f` and `g` are Mellin convergent at `s`, the Mellin
  transform of `mellinConv f g` is `𝓜f(s) 𝓜g(s)`, with absolute convergence.
* `TauCeti.mellinConv_comp_inv_div_eq_integral_mul_comp_mul`:
  `mellinConv (fun y ↦ f y⁻¹ / y) h x = ∫₀^∞ f(t) h(xt) dt`.
* `TauCeti.hasMellin_integral_mul_comp_mul`: if `f` is Mellin convergent at `1 - z` and `h` at
  `z`, the Mellin transform of `∫₀^∞ f(t) h(xt) dt` is `𝓜f(1 - z) 𝓜h(z)` (DLMF 2.5.3–2.5.4).
* `TauCeti.integral_mul_comp_mul_eq_mellinInv`: the Parseval formula (DLMF 2.5.5), under the
  hypotheses above.

## References

* [DLMF] *NIST Digital Library of Mathematical Functions*, §2.5(i), <https://dlmf.nist.gov/2.5.i>.
* A. Kontorovich, T. Tao et al., *PrimeNumberTheoremAnd*,
  <https://github.com/AlexKontorovich/PrimeNumberTheoremAnd>, file
  `PrimeNumberTheoremAnd/MellinCalculus.lean` at revision
  `a4fb6989b07e9c76b511807ae93e33e25b820e9b` (blueprint §4.3, Definition 4.3.1 and Lemma 4.3.2).

The logarithmic-coordinate identity, the product formulas and the Parseval formula are adapted
from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>), files
`DLMFMathlib/Analysis/MellinConvolution.lean` and
`DLMF/AsymptoticApproximations/Mellin/Transforms.lean`. The definition `mellinConv` and the
statements of its commutativity and support bounds follow `MellinConvolution`,
`MellinConvolutionSymmetric` and `support_MellinConvolution_subsets` in the PNT+ file above; the
proofs here go through logarithmic coordinates instead.
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

/-- Left scalar homogeneity of `mellinConv`. -/
theorem mellinConv_const_mul_left (c : ℂ) (f g : ℝ → ℂ) (x : ℝ) :
    mellinConv (fun y ↦ c * f y) g x = c * mellinConv f g x := by
  simp only [mellinConv_def, mul_assoc, mul_div_assoc, integral_const_mul]

/-- Right scalar homogeneity of `mellinConv`. -/
theorem mellinConv_const_mul_right (c : ℂ) (f g : ℝ → ℂ) (x : ℝ) :
    mellinConv f (fun y ↦ c * g y) x = c * mellinConv f g x := by
  rw [mellinConv_def, mellinConv_def, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun y _ ↦ ?_
  ring

/-- For `x > 0`, `mellinConv f g x` depends on `f` and `g` only through their values on `(0, ∞)`. -/
theorem mellinConv_congr {f₁ f₂ g₁ g₂ : ℝ → ℂ} (hf : EqOn f₁ f₂ (Ioi 0))
    (hg : EqOn g₁ g₂ (Ioi 0)) {x : ℝ} (hx : 0 < x) :
    mellinConv f₁ g₁ x = mellinConv f₂ g₂ x := by
  rw [mellinConv_def, mellinConv_def]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy ↦ ?_
  rw [hf hy, hg (div_pos hx hy)]

/-- In logarithmic coordinates `x = e^{-u}` the Mellin convolution is the ordinary convolution of
`v ↦ f (e^{-v})` and `v ↦ g (e^{-v})`, with no integrability hypothesis. -/
theorem mellinConv_exp_neg_eq_convolution (f g : ℝ → ℂ) (u : ℝ) :
    mellinConv f g (Real.exp (-u)) =
      convolution (fun v : ℝ ↦ f (Real.exp (-v))) (fun v : ℝ ↦ g (Real.exp (-v)))
        (ContinuousLinearMap.mul ℝ ℂ) volume u := by
  rw [mellinConv_def, ← ContinuousLinearMap.integral_inv_smul_bilinear_eq_convolution]
  refine setIntegral_congr_fun measurableSet_Ioi fun y _ ↦ ?_
  rw [ContinuousLinearMap.mul_apply', Complex.real_smul]
  push_cast
  ring

/-- Mellin convolution is commutative at positive arguments, with no integrability hypothesis. -/
theorem mellinConv_comm_of_pos (f g : ℝ → ℂ) {x : ℝ} (hx : 0 < x) :
    mellinConv f g x = mellinConv g f x := by
  rw [← Real.exp_log hx, ← neg_neg (Real.log x), mellinConv_exp_neg_eq_convolution,
    mellinConv_exp_neg_eq_convolution,
    convolution_symm (ContinuousLinearMap.mul ℝ ℂ) (by ext a b; simp)]

/-- For `x > 0`, `mellinConv f g x` only depends on `f` and `g` up to null subsets of `(0, ∞)`. -/
theorem mellinConv_congr_ae {f₁ f₂ g₁ g₂ : ℝ → ℂ} (hf : f₁ =ᵐ[volume.restrict (Ioi 0)] f₂)
    (hg : g₁ =ᵐ[volume.restrict (Ioi 0)] g₂) {x : ℝ} (hx : 0 < x) :
    mellinConv f₁ g₁ x = mellinConv f₂ g₂ x := by
  have hleft {f₁ f₂ : ℝ → ℂ} (g : ℝ → ℂ) (hf : f₁ =ᵐ[volume.restrict (Ioi 0)] f₂) :
      mellinConv f₁ g x = mellinConv f₂ g x := by
    rw [mellinConv_def, mellinConv_def]
    refine integral_congr_ae (hf.mono fun y hy ↦ ?_)
    simp only [hy]
  -- Commutativity on `(0, ∞)` moves `g` into the first slot.
  rw [hleft g₁ hf, mellinConv_comm_of_pos _ _ hx, hleft f₂ hg, mellinConv_comm_of_pos _ _ hx]

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

/-- If `f` vanishes on `(0, ∞)` off `[a, b]` and `g` vanishes on `(0, ∞)` off `[c, d]` with
`0 ≤ c`, then `mellinConv f g` vanishes on `(0, ∞)` off `[a * c, b * d]`. -/
theorem support_mellinConv_inter_Ioi_subset_Icc {f g : ℝ → ℂ} {a b c d : ℝ} (hc : 0 ≤ c)
    (hf : Function.support f ∩ Ioi 0 ⊆ Icc a b) (hg : Function.support g ∩ Ioi 0 ⊆ Icc c d) :
    Function.support (mellinConv f g) ∩ Ioi 0 ⊆ Icc (a * c) (b * d) := by
  rintro x ⟨hx, hx0⟩
  by_contra hx'
  apply hx
  rw [mellinConv_def]
  refine setIntegral_eq_zero_of_forall_eq_zero fun y (hy : 0 < y) ↦ ?_
  by_cases hfy : f y = 0
  · simp [hfy]
  by_cases hgy : g (x / y) = 0
  · simp [hgy]
  exfalso
  have hyab : y ∈ Icc a b := hf ⟨hfy, hy⟩
  have hxycd : x / y ∈ Icc c d := hg ⟨hgy, div_pos hx0 hy⟩
  have hxy : y * (x / y) = x := mul_div_cancel₀ x hy.ne'
  refine hx' ⟨?_, ?_⟩
  · calc a * c ≤ y * c := mul_le_mul_of_nonneg_right hyab.1 hc
      _ ≤ y * (x / y) := mul_le_mul_of_nonneg_left hxycd.1 hy.le
      _ = x := hxy
  · calc x = y * (x / y) := hxy.symm
      _ ≤ y * d := mul_le_mul_of_nonneg_left hxycd.2 hy.le
      _ ≤ b * d := mul_le_mul_of_nonneg_right hyab.2 ((hc.trans hxycd.1).trans hxycd.2)

/-! ### Mellin product formulas -/

/-- The weighted form of `TauCeti.mellinConv_exp_neg_eq_convolution`: the weight `e^{-su}` of the
Mellin transform in logarithmic coordinates distributes over the convolution. -/
private lemma exp_mul_mellinConv_eq_convolution (f g : ℝ → ℂ) (s : ℂ) (u : ℝ) :
    cexp (-s * u) * mellinConv f g (Real.exp (-u)) =
      convolution (fun v : ℝ => cexp (-s * v) * f (Real.exp (-v)))
        (fun v : ℝ => cexp (-s * v) * g (Real.exp (-v)))
        (ContinuousLinearMap.mul ℂ ℂ) volume u := by
  rw [mellinConv_exp_neg_eq_convolution, convolution_def, convolution_def, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [ContinuousLinearMap.mul_apply']
  have he : cexp (-s * v) * cexp (-s * ((u - v : ℝ) : ℂ)) = cexp (-s * u) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [← he]
  ring

/-- The Mellin transform of the multiplicative convolution `mellinConv f g` is the product of the
Mellin transforms, with absolute convergence. -/
theorem hasMellin_mellinConv {f g : ℝ → ℂ} {s : ℂ}
    (hf : MellinConvergent f s) (hg : MellinConvergent g s) :
    HasMellin (mellinConv f g) s (mellin f s * mellin g s) := by
  have hlog (k : ℝ → ℂ) : mellin k s = ∫ u : ℝ, cexp (-s * u) * k (Real.exp (-u)) := by
    simpa only [smul_eq_mul] using mellin_eq_integral_exp_smul k s
  have hfi : Integrable fun u : ℝ => cexp (-s * u) * f (Real.exp (-u)) := by
    simpa only [smul_eq_mul] using (mellinConvergent_iff_integrable_exp_smul f s).mp hf
  have hgi : Integrable fun u : ℝ => cexp (-s * u) * g (Real.exp (-u)) := by
    simpa only [smul_eq_mul] using (mellinConvergent_iff_integrable_exp_smul g s).mp hg
  have hfun := funext (exp_mul_mellinConv_eq_convolution f g s)
  refine ⟨(mellinConvergent_iff_integrable_exp_smul _ _).mpr ?_, ?_⟩
  · simp only [smul_eq_mul]
    rw [hfun]
    exact hfi.integrable_convolution (L := ContinuousLinearMap.mul ℂ ℂ) hgi
  · rw [hlog, hfun, integral_convolution (ContinuousLinearMap.mul ℂ ℂ) hfi hgi]
    simp only [ContinuousLinearMap.mul_apply', ← hlog]

/-- The substitution `y = 1/t` turns `mellinConv (fun y ↦ f y⁻¹ / y) h x` into
`∫₀^∞ f(t) h(xt) dt`. -/
theorem mellinConv_comp_inv_div_eq_integral_mul_comp_mul (f h : ℝ → ℂ) (x : ℝ) :
    mellinConv (fun y ↦ f y⁻¹ / y) h x = ∫ t in Ioi 0, f t * h (x * t) := by
  rw [mellinConv_def]
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
  have he := hasMellin_mellinConv hk hh
  rw [funext (mellinConv_comp_inv_div_eq_integral_mul_comp_mul f h)] at he
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
