/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex, Bastiaan J Braams
-/
module

public import Mathlib.Analysis.MellinTransform

/-!
# Basic identities for Mellin transforms

For `0 ≤ a`, the Mellin transform of `(Ioi a).indicator f` is the upper Mellin integral
`∫ u in Ioi a, u ^ (s - 1) • f u`, and it converges exactly when that integrand is integrable
on `Ioi a`. These identities let a Mellin transform be split into tails over `(0, a]` and
`(a, ∞)`.

The substitution `t = e^{-u}` turns the Mellin integrand of `f` at `s` into
`e^{-su} f(e^{-u})` on the whole real line, and the substitution `t ↦ 1/t` relates the Mellin
transform of `t⁻¹ f(t⁻¹)` at `s` to that of `f` at `1 - s`.

## Main results

* `TauCeti.mellinConvergent_indicator_Ioi_iff`: convergence of the Mellin transform of an
  upper-tail indicator is integrability of the upper Mellin integrand.
* `TauCeti.mellin_indicator_Ioi`, `TauCeti.mellin_indicator_Ici`: the Mellin transform of an
  open or closed upper-tail indicator is the upper Mellin integral.
* `TauCeti.mellin_ofReal_zero`, `TauCeti.mellinConvergent_ofReal_zero_iff`: at `s = 0` the
  Mellin transform of a real function is the real integral `∫_{(0,∞)} f(x) dx/x`.
* `MellinConvergent.of_support_subset_Icc`: for a function supported in a compact interval of
  `(0, ∞)`, convergence at one exponent gives convergence at every exponent.
* `TauCeti.mellinConvergent_ofReal_of_support_subset_Icc`: a real function supported in a compact
  interval of `(0, ∞)` with `x ↦ f x / x` integrable on `(0, ∞)` converges at every exponent.
* `TauCeti.mellinConvergent_iff_integrable_exp_smul`, `TauCeti.mellin_eq_integral_exp_smul`:
  absolute convergence and value of the Mellin transform in logarithmic coordinates.
* `TauCeti.mellinConvergent_inv_smul_comp_inv`, `TauCeti.mellin_inv_smul_comp_inv`: the Mellin
  transform of `t⁻¹ f(t⁻¹)` at `s` is that of `f` at `1 - s`.
-/

public section

open Set MeasureTheory Complex

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- For `0 ≤ a`, the Mellin transform of `(Ioi a).indicator f` converges at `s` exactly when the
upper Mellin integrand `u ^ (s - 1) • f u` is integrable on `Ioi a`. -/
theorem mellinConvergent_indicator_Ioi_iff {f : ℝ → E} {a : ℝ} (ha : 0 ≤ a) {s : ℂ} :
    MellinConvergent ((Ioi a).indicator f) s ↔
      IntegrableOn (fun u : ℝ ↦ (u : ℂ) ^ (s - 1) • f u) (Ioi a) := by
  simp_rw [MellinConvergent, ← indicator_smul, integrableOn_indicator_iff
    measurableSet_Ioi.nullMeasurableSet, inter_eq_left.mpr (Ioi_subset_Ioi ha)]

/-- For `0 ≤ a`, the Mellin transform of `(Ioi a).indicator f` is the upper Mellin integral of
`f` over `Ioi a`. -/
theorem mellin_indicator_Ioi (f : ℝ → E) {a : ℝ} (ha : 0 ≤ a) (s : ℂ) :
    mellin ((Ioi a).indicator f) s = ∫ (u : ℝ) in Ioi a, (u : ℂ) ^ (s - 1) • f u := by
  simp_rw [mellin, ← indicator_smul, setIntegral_indicator measurableSet_Ioi,
    inter_eq_right.mpr (Ioi_subset_Ioi ha)]

/-- The Mellin transform of an upper closed-ray indicator equals the upper Mellin integral.
The boundary point has measure zero; the cutoff may be zero. -/
theorem mellin_indicator_Ici (f : ℝ → E) {a : ℝ} (ha : 0 ≤ a) (s : ℂ) :
    mellin ((Ici a).indicator f) s = ∫ (u : ℝ) in Ioi a, (u : ℂ) ^ (s - 1) • f u := by
  rw [← mellin_indicator_Ioi f ha s]
  simp only [mellin]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae (indicator_ae_eq_of_ae_eq_set (f := f)
    (Ioi_ae_eq_Ici (a := a)))] with t ht
  rw [ht]

/-- For a real function `f`, the Mellin transform of `f` at `0` is the real integral
`∫_{(0,∞)} f(x) dx/x`. -/
theorem mellin_ofReal_zero (f : ℝ → ℝ) :
    mellin (fun x ↦ (f x : ℂ)) 0 = ((∫ x in Ioi 0, f x / x : ℝ) : ℂ) := by
  rw [mellin, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ ↦ ?_
  simp [cpow_neg_one, div_eq_inv_mul]

/-- For a real function `f`, absolute convergence of the Mellin transform at `0` is
integrability of `x ↦ f x / x` on `(0, ∞)`. -/
theorem mellinConvergent_ofReal_zero_iff (f : ℝ → ℝ) :
    MellinConvergent (fun x ↦ (f x : ℂ)) 0 ↔ IntegrableOn (fun x ↦ f x / x) (Ioi 0) := by
  rw [MellinConvergent, integrableOn_congr_fun (g := fun x ↦ ((f x / x : ℝ) : ℂ))
    (fun x _ ↦ by simp [cpow_neg_one, div_eq_inv_mul]) measurableSet_Ioi]
  exact (Integrable.iff_ofReal (𝕜 := ℂ)).symm

private lemma exp_smul_cpow_smul_comp_neg (f : ℝ → E) (s : ℂ) (u : ℝ) :
    Real.exp (-1 * u) • ((Real.exp (-1 * u) : ℂ) ^ (s - 1) • f (Real.exp (-1 * u))) =
      cexp (-s * u) • f (Real.exp (-u)) := by
  rw [neg_one_mul, ← Complex.coe_smul, smul_smul, ofReal_exp,
    cpow_def_of_ne_zero (Complex.exp_ne_zero _), Complex.log_exp (by simp [Real.pi_pos])
      (by simp [Real.pi_nonneg]), ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Under the substitution `t = e^{-u}`, absolute Mellin convergence of `f` at `s` is
integrability of `u ↦ e^{-su} f(e^{-u})` on the real line. -/
theorem mellinConvergent_iff_integrable_exp_smul (f : ℝ → E) (s : ℂ) :
    MellinConvergent f s ↔ Integrable (fun u : ℝ ↦ cexp (-s * u) • f (Real.exp (-u))) := by
  rw [MellinConvergent, ← integrable_comp_exp,
    ← integrable_comp_mul_left_iff _ (neg_ne_zero.mpr one_ne_zero)]
  simp only [exp_smul_cpow_smul_comp_neg]

/-- The Mellin transform in logarithmic coordinates: `𝓜f(s) = ∫_ℝ e^{-su} f(e^{-u}) du`. -/
theorem mellin_eq_integral_exp_smul (f : ℝ → E) (s : ℂ) :
    mellin f s = ∫ u : ℝ, cexp (-s * u) • f (Real.exp (-u)) := by
  calc mellin f s = ∫ x : ℝ, Real.exp x • ((Real.exp x : ℂ) ^ (s - 1) • f (Real.exp x)) :=
        (integral_comp_exp _).symm
    _ = ∫ u : ℝ, Real.exp (-1 * u) •
          ((Real.exp (-1 * u) : ℂ) ^ (s - 1) • f (Real.exp (-1 * u))) := by
        have h := Measure.integral_comp_mul_left
          (fun x : ℝ ↦ Real.exp x • ((Real.exp x : ℂ) ^ (s - 1) • f (Real.exp x))) (-1)
        rw [inv_neg, inv_one, abs_neg, abs_one, one_smul] at h
        exact h.symm
    _ = _ := by simp only [exp_smul_cpow_smul_comp_neg]

/-- If the Mellin transform of `f` converges absolutely at `1 - s`, then that of
`t ↦ t⁻¹ f(t⁻¹)` converges absolutely at `s`. -/
theorem mellinConvergent_inv_smul_comp_inv {f : ℝ → E} {s : ℂ}
    (hf : MellinConvergent f (1 - s)) :
    MellinConvergent (fun t : ℝ ↦ (t : ℂ)⁻¹ • f t⁻¹) s := by
  have hi : MellinConvergent (fun t ↦ f t⁻¹) (s - 1) := by
    have hs : (s - 1) / ((-1 : ℝ) : ℂ) = 1 - s := by push_cast; ring
    simpa only [Real.rpow_neg_one] using
      (MellinConvergent.comp_rpow (f := f) (s := s - 1) (a := -1) (by norm_num)).mpr
        (by rwa [hs])
  simpa only [cpow_neg_one] using
    (MellinConvergent.cpow_smul (f := fun t ↦ f t⁻¹) (s := s) (a := -1)).mpr
      (by rwa [← sub_eq_add_neg])

/-- The Mellin transform of `t ↦ t⁻¹ f(t⁻¹)` at `s` is the Mellin transform of `f` at
`1 - s`. -/
theorem mellin_inv_smul_comp_inv (f : ℝ → E) (s : ℂ) :
    mellin (fun t : ℝ ↦ (t : ℂ)⁻¹ • f t⁻¹) s = mellin f (1 - s) := by
  have h := mellin_cpow_smul (fun t ↦ f t⁻¹) s (-1)
  simp only [cpow_neg_one] at h
  rw [h, mellin_comp_inv, neg_add, neg_neg, ← sub_eq_neg_add]

end TauCeti

/-- A function supported in a compact interval `[a, b] ⊆ (0, ∞)` whose Mellin transform converges
absolutely at one exponent converges absolutely at every exponent: the factor `t ^ (s - s₀)` is
bounded on `[a, b]`. -/
theorem MellinConvergent.of_support_subset_Icc {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f : ℝ → E} {a b : ℝ} (ha : 0 < a) (hf : Function.support f ⊆ Icc a b)
    {s₀ : ℂ} (h : MellinConvergent f s₀) (s : ℂ) : MellinConvergent f s := by
  have hc : ContinuousOn (fun t : ℝ ↦ (t : ℂ) ^ (s - s₀)) (Icc a b) := fun t ht ↦
    (continuousAt_ofReal_cpow_const _ _ (Or.inr (ha.trans_le ht.1).ne')).continuousWithinAt
  have hsub : Icc a b ⊆ Ioi 0 := fun t ht ↦ ha.trans_le ht.1
  have hI := (IntegrableOn.mono_set h hsub).continuousOn_smul hc isCompact_Icc
  refine ((integrableOn_congr_fun (fun t ht ↦ ?_) measurableSet_Icc).mp hI).of_forall_sdiff_eq_zero
    measurableSet_Ioi fun t ht ↦ ?_
  · rw [smul_smul, ← cpow_add _ _ (ofReal_ne_zero.mpr (ha.trans_le ht.1).ne'), sub_add_sub_cancel]
  · rw [Function.notMem_support.mp fun h ↦ ht.2 (hf h), smul_zero]

namespace TauCeti

/-- A real function supported in a compact interval `[a, b] ⊆ (0, ∞)` with `x ↦ f x / x`
integrable on `(0, ∞)` is Mellin convergent at every exponent. -/
theorem mellinConvergent_ofReal_of_support_subset_Icc {f : ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hf : Function.support f ⊆ Icc a b) (hfi : IntegrableOn (fun x ↦ f x / x) (Ioi 0)) (s : ℂ) :
    MellinConvergent (fun x ↦ (f x : ℂ)) s :=
  ((mellinConvergent_ofReal_zero_iff f).mpr hfi).of_support_subset_Icc ha
    (by simpa only [Function.support, ne_eq, ofReal_eq_zero] using hf) s

end TauCeti
