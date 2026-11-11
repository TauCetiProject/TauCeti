/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.MellinInversion
public import Mathlib.Analysis.Convolution

/-!
# Mellin convolution and the Parseval formula (DLMF 2.5.3–2.5.5)

For `I(x) = ∫₀^∞ f(t) h(xt) dt`, the Mellin transform is `𝓜I(z) = 𝓜f(1 - z) 𝓜h(z)` wherever
both transforms on the right converge absolutely, and then Mellin inversion along a vertical line
`Re z = c` gives the Parseval formula
`I(x) = (2πi)⁻¹ ∫_{c-i∞}^{c+i∞} x^{-z} 𝓜f(1 - z) 𝓜h(z) dz`.

The proof passes to logarithmic coordinates. The substitution `t = e^{-u}` turns the Mellin
integrand of `f` into `e^{-su} f(e^{-u})` on the real line, and the multiplicative convolution
`∫₀^∞ f(y) g(x/y) dy/y` into an ordinary convolution, so absolute convergence and the product
formula come from `MeasureTheory.Integrable.integrable_convolution` and
`MeasureTheory.integral_convolution`. The substitution `t ↦ 1/t` relates
`∫₀^∞ f(t) h(xt) dt` to that convolution.

## Main results

* `TauCeti.mellinConvergent_iff_integrable_exp_mul`: absolute Mellin convergence is
  integrability on the real line in logarithmic coordinates.
* `TauCeti.mellin_eq_integral_exp_mul`: the Mellin transform in logarithmic coordinates.
* `TauCeti.hasMellin_integral_mul_div`: the Mellin transform of `∫₀^∞ f(y) g(x/y) dy/y` is
  `𝓜f(s) 𝓜g(s)`, with absolute convergence.
* `TauCeti.hasMellin_integral_mul_comp_mul`: the Mellin transform of `∫₀^∞ f(t) h(xt) dt` is
  `𝓜f(1 - z) 𝓜h(z)` (DLMF 2.5.3–2.5.4).
* `TauCeti.integral_mul_comp_mul_eq_mellinInv`: the Parseval formula (DLMF 2.5.5).
-/

@[expose] public section

open MeasureTheory Complex Set Filter
open scoped Topology

namespace TauCeti

/-- Under the substitution `t = e^{-u}`, absolute Mellin convergence of `f` at `s` is
integrability of `u ↦ e^{-su} f(e^{-u})` on the real line. -/
theorem mellinConvergent_iff_integrable_exp_mul (f : ℝ → ℂ) (s : ℂ) :
    MellinConvergent f s ↔ Integrable (fun u : ℝ => cexp (-s * u) * f (Real.exp (-u))) := by
  have hd : ∀ x ∈ (univ : Set ℝ),
      HasDerivWithinAt (Real.exp ∘ Neg.neg) (-Real.exp (-x)) univ x := fun x _ => by
    simpa only [mul_neg_one] using
      ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).hasDerivWithinAt (s := univ)
  have him : (Real.exp ∘ Neg.neg) '' (univ : Set ℝ) = Ioi 0 := by
    rw [Set.image_comp, Set.image_univ_of_surjective neg_surjective, Set.image_univ,
      Real.range_exp]
  have hinj : (univ : Set ℝ).InjOn (Real.exp ∘ Neg.neg) :=
    Real.exp_injective.injOn.comp neg_injective.injOn (univ.mapsTo_univ _)
  rw [MellinConvergent, ← him,
    integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ hd hinj]
  simp only [IntegrableOn, Measure.restrict_univ, Function.comp_apply, abs_neg,
    abs_of_pos (Real.exp_pos _), smul_eq_mul]
  refine integrable_congr (Eventually.of_forall fun u => ?_)
  dsimp only
  rw [Complex.real_smul]
  simp only [ofReal_exp, ofReal_neg]
  rw [← mul_assoc]
  nth_rw 1 [← cpow_one (cexp (-(u : ℂ)))]
  rw [← cpow_add _ _ (Complex.exp_ne_zero _)]
  rw [show (1 : ℂ) + (s - 1) = s by ring,
    cpow_def_of_ne_zero (Complex.exp_ne_zero _), Complex.log_exp]
  · congr 1; ring
  · simp [Real.pi_pos]
  · simp [Real.pi_nonneg]

/-- The Mellin transform in logarithmic coordinates:
`𝓜f(s) = ∫_ℝ e^{-su} f(e^{-u}) du`. -/
theorem mellin_eq_integral_exp_mul (f : ℝ → ℂ) (s : ℂ) :
    mellin f s = ∫ u : ℝ, cexp (-s * u) * f (Real.exp (-u)) := by
  rw [mellin_eq_fourier, Real.fourier_eq']
  apply integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [smul_eq_mul, Complex.real_smul]
  rw [ofReal_exp, ← mul_assoc, ← Complex.exp_add]
  congr 1
  congr 1
  conv_rhs => rw [← re_add_im s]
  simp only [RCLike.inner_apply]
  push_cast
  field_simp
  simp only [starRingEnd_apply, star_trivial]
  ring

/-- In logarithmic coordinates the multiplicative convolution becomes an ordinary
convolution. -/
private lemma integral_mul_div_eq_convolution (f g : ℝ → ℂ) (s : ℂ) (u : ℝ) :
    cexp (-s * u) * (∫ y in Ioi 0, f y * g (Real.exp (-u) / y) / y) =
      convolution (fun v : ℝ => cexp (-s * v) * f (Real.exp (-v)))
        (fun v : ℝ => cexp (-s * v) * g (Real.exp (-v)))
        (ContinuousLinearMap.mul ℂ ℂ) volume u := by
  have hmel : mellin (fun y => f y * g (Real.exp (-u) / y)) 0 =
      (∫ y in Ioi 0, f y * g (Real.exp (-u) / y) / y) := by
    unfold mellin
    dsimp only
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    simp only [zero_sub, cpow_neg_one, smul_eq_mul]
    ring
  rw [← hmel, mellin_eq_integral_exp_mul]
  simp only [neg_zero, zero_mul, Complex.exp_zero, one_mul]
  rw [← integral_const_mul, convolution]
  apply integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [ContinuousLinearMap.mul_apply']
  have harg : Real.exp (-u) / Real.exp (-v) = Real.exp (-(u - v)) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [harg]
  have he : cexp (-s * v) * cexp (-s * ((u - v : ℝ) : ℂ)) = cexp (-s * u) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc cexp (-s * u) * (f (Real.exp (-v)) * g (Real.exp (-(u - v)))) =
      (cexp (-s * v) * cexp (-s * ((u - v : ℝ) : ℂ))) *
        (f (Real.exp (-v)) * g (Real.exp (-(u - v)))) := by rw [he]
    _ = _ := by push_cast; ring

/-- The Mellin transform of the multiplicative convolution `∫₀^∞ f(y) g(x/y) dy/y` is the product
of the Mellin transforms, with absolute convergence. -/
theorem hasMellin_integral_mul_div {f g : ℝ → ℂ} {s : ℂ}
    (hf : MellinConvergent f s) (hg : MellinConvergent g s) :
    HasMellin (fun x : ℝ => ∫ y in Ioi 0, f y * g (x / y) / y) s
      (mellin f s * mellin g s) := by
  have hfi := (mellinConvergent_iff_integrable_exp_mul f s).mp hf
  have hgi := (mellinConvergent_iff_integrable_exp_mul g s).mp hg
  have hfun := funext (integral_mul_div_eq_convolution f g s)
  refine ⟨(mellinConvergent_iff_integrable_exp_mul _ _).mpr ?_, ?_⟩
  · rw [hfun]
    exact hfi.integrable_convolution (L := ContinuousLinearMap.mul ℂ ℂ) hgi
  · rw [mellin_eq_integral_exp_mul, hfun,
      integral_convolution (ContinuousLinearMap.mul ℂ ℂ) hfi hgi]
    simp only [ContinuousLinearMap.mul_apply', ← mellin_eq_integral_exp_mul]

/-- The kernel `f(1/y)/y` converges absolutely at `s` when `f` converges at `1 - s`. -/
private lemma mellinConvergent_inv_div {f : ℝ → ℂ} {s : ℂ}
    (hf : MellinConvergent f (1 - s)) :
    MellinConvergent (fun y => f y⁻¹ / y) s := by
  have hi : MellinConvergent (fun y => f y⁻¹) (s - 1) := by
    have hs : (s - 1) / ((-1 : ℝ) : ℂ) = 1 - s := by push_cast; ring
    have h := (MellinConvergent.comp_rpow (f := f) (s := s - 1) (a := -1)
      (by norm_num)).mpr (by simpa only [hs] using hf)
    simpa only [Real.rpow_neg_one] using h
  have h := (MellinConvergent.cpow_smul (f := fun y => f y⁻¹) (s := s) (a := -1)).mpr
    (by simpa only [sub_eq_add_neg] using hi)
  simpa only [cpow_neg_one, smul_eq_mul, div_eq_mul_inv, mul_comm] using h

/-- The substitution `y = 1/t` turns `∫₀^∞ f(t) h(xt) dt` into a multiplicative
convolution. -/
private lemma integral_inv_div_mul_div (f h : ℝ → ℂ) (x : ℝ) :
    (∫ y in Ioi (0 : ℝ), f y⁻¹ / y * h (x / y) / y) = ∫ t in Ioi 0, f t * h (x * t) := by
  have he := mellin_comp_inv (fun y => f y * h (x * y)) (-1 : ℂ)
  have hleft : mellin (fun y => f y⁻¹ * h (x * y⁻¹)) (-1) =
      ∫ y in Ioi (0 : ℝ), f y⁻¹ / y * h (x / y) / y := by
    unfold mellin
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
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
  have he := hasMellin_integral_mul_div (mellinConvergent_inv_div hf) hh
  rw [funext (integral_inv_div_mul_div f h)] at he
  have hmel : mellin (fun y => f y⁻¹ / y) z = mellin f (1 - z) := by
    have h := mellin_cpow_smul (fun y => f y⁻¹) z (-1)
    simp only [cpow_neg_one, smul_eq_mul] at h
    rw [mellin_comp_inv] at h
    convert h using 1
    · congr 1; funext y; ring
    · congr 1; ring
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
  have h1 := mellinInv_mellin_eq c Iv hx hIc hV hcont
  change Iv x = _
  rw [← h1]
  unfold mellinInv
  simp only [hline]

end TauCeti
