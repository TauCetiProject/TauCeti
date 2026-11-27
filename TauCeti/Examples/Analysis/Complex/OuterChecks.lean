/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Outer.Basic
import TauCeti.Analysis.Complex.UpperHalfPlane.Nontangential.Limit

/-!
# Checks for outer functions on the upper half-plane

Two zero-free or unimodular-looking functions that are not outer, that is, not of the form
`c O_h` (`TauCeti.upperHalfPlaneOuter`) with `h ∈ L¹(Π)`:

* *The exponential.* `e^{iz}` has boundary modulus `|e^{ix}| = 1`, but it is not outer
  (`not_exists_eqOn_cexp_I_mul_upperHalfPlaneOuter`). If `e^{iz} = c O_h` on `ℂ₊`, then
  `|O_h(z)| = e^{-Im z} / |c|` tends to `1 / |c|` nontangentially, so `e^{h} = 1 / |c|` almost
  everywhere by the boundary modulus of `O_h`. Then `P[h] = -log |c|`, so `|O_h| = 1 / |c|` is
  constant on `ℂ₊`, while `e^{-Im z}` is not.
* *A Blaschke factor.* `(z - i) / (z + i)` vanishes at `i`, while outer functions are zero-free
  (`not_exists_eqOn_blaschke_mul_upperHalfPlaneOuter`).
-/

public section

noncomputable section

namespace TauCeti.Examples.Outer

open Complex Filter MeasureTheory Set Topology
open _root_.UpperHalfPlane (upperHalfPlaneSet)

/-- **`e^{iz}` is not outer**: it is not `c O_h` on `ℂ₊` for any constant `c` and any
`h ∈ L¹(Π)`, although its boundary modulus is `1`. -/
theorem not_exists_eqOn_cexp_I_mul_upperHalfPlaneOuter :
    ¬ ∃ (c : ℂ) (h : ℝ → ℝ), Integrable h upperHalfPlanePoissonMeasure ∧
      EqOn (fun z ↦ cexp (I * z)) (fun z ↦ c * upperHalfPlaneOuter h z) upperHalfPlaneSet := by
  rintro ⟨c, h, hh, heq⟩
  have hI : I ∈ upperHalfPlaneSet := by simp
  have hc : c ≠ 0 := by
    rintro rfl
    simpa using heq hI
  have hc' : ‖c‖ ≠ 0 := norm_ne_zero_iff.2 hc
  have hnorm : ∀ z ∈ upperHalfPlaneSet,
      ‖upperHalfPlaneOuter h z‖ = Real.exp (-z.im) / ‖c‖ := fun z hz ↦ by
    have h1 := congrArg norm (heq hz)
    simp only [norm_mul, norm_exp, mul_re, I_re, zero_mul, I_im, one_mul, zero_sub] at h1
    rw [h1, mul_div_cancel_left₀ _ hc']
  have hae : ∀ᵐ x, h x = -Real.log ‖c‖ := by
    filter_upwards [ae_tendsto_nontangentialFilter_norm_upperHalfPlaneOuter hh] with x hx
    have := nontangentialFilter_neBot one_pos x
    have hlim : Tendsto (fun z ↦ ‖upperHalfPlaneOuter h z‖) (nontangentialFilter 1 x)
        (𝓝 (Real.exp (-0) / ‖c‖)) :=
      (((Real.continuous_exp.tendsto _).comp (tendsto_im_nontangentialFilter 1 x).neg).div_const
        _).congr' ((eventually_nontangentialFilter_abs_re_sub_le 1 x one_pos).mono
          fun z hz ↦ (hnorm z hz.1).symm)
    rw [← Real.log_exp (h x), tendsto_nhds_unique (hx 1) hlim, neg_zero, Real.exp_zero, one_div,
      Real.log_inv]
  have hP : ∀ z ∈ upperHalfPlaneSet,
      ∫ x, upperHalfPlanePoissonKernel z x * h x = -Real.log ‖c‖ := fun z hz ↦ by
    rw [integral_congr_ae (g := fun x ↦ upperHalfPlanePoissonKernel z x * -Real.log ‖c‖)
      (hae.mono fun x hx ↦ by simp only [hx]), integral_mul_const,
      integral_upperHalfPlanePoissonKernel hz, one_mul]
  have h1 := hnorm I hI
  rw [norm_upperHalfPlaneOuter hh, hP I hI, Real.exp_neg, Real.exp_log (norm_pos_iff.2 hc),
    I_im, eq_div_iff hc', inv_mul_cancel₀ hc', eq_comm, Real.exp_eq_one_iff] at h1
  norm_num at h1

/-- **A Blaschke factor is not outer**: `(z - i) / (z + i)` vanishes at `i`, so it is not `c O_h`
on `ℂ₊` for any constant `c` and any `h`. -/
theorem not_exists_eqOn_blaschke_mul_upperHalfPlaneOuter :
    ¬ ∃ (c : ℂ) (h : ℝ → ℝ),
      EqOn (fun z ↦ (z - I) / (z + I)) (fun z ↦ c * upperHalfPlaneOuter h z) upperHalfPlaneSet := by
  rintro ⟨c, h, heq⟩
  have hI := heq (show I ∈ upperHalfPlaneSet by simp)
  simp only [sub_self, zero_div] at hI
  have hc : c = 0 := (mul_eq_zero.1 hI.symm).resolve_right (upperHalfPlaneOuter_ne_zero h I)
  have h2 := heq (show 2 * I ∈ upperHalfPlaneSet by simp)
  simp only [hc, zero_mul] at h2
  rw [div_eq_zero_iff] at h2
  rcases h2 with h2 | h2 <;>
  · have := congrArg im h2
    norm_num at this

end TauCeti.Examples.Outer
