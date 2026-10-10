/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Primitive
public import TauCeti.Analysis.Complex.UpperHalfPlane.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# A Schwarz--Christoffel strip with two logarithmic ends

Two distinct real prevertices, each of exponent `-1`, give a conformal map onto a
strip. For `a 0 < a 1`, the logarithm of `(z - a 1) / (z - a 0)` is an affine image
of the normalized Schwarz--Christoffel primitive. It maps the upper half-plane
bijectively onto the strip `0 < im w < π`.

Both finite prevertices represent ends at infinity; the parameter at infinity
represents a regular boundary point. Thus this is a polygon with two ends, rather
than the one-ended Jordan-curve situation. The image theorem imposes no boundary
simplicity or boundary-avoidance assumption.

## References

* L. Ahlfors, *Complex Analysis*, Chapter 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Chapter 2.
-/

public section

open Complex Function Set
open UpperHalfPlane (upperHalfPlaneSet)

namespace TauCeti

/-- **The explicit Schwarz--Christoffel formula for a strip.** Two ordered prevertices
of exponent `-1` give the principal logarithm of their fractional-linear ratio, after
scaling by their separation and translating by the value at the base point. -/
theorem const_mul_schwarzChristoffelPrimitive_two_neg_one_add_eq_log (a : Fin 2 → ℝ)
    (ha : a 0 < a 1) (z₀ : UpperHalfPlane) {z : ℂ} (hz : z ∈ upperHalfPlaneSet) :
    ((a 1 - a 0 : ℝ) : ℂ) * schwarzChristoffelPrimitive a (fun _ => -1) z₀ z +
      log (((z₀ : ℂ) - (a 1 : ℂ)) / ((z₀ : ℂ) - (a 0 : ℂ))) =
      log ((z - (a 1 : ℂ)) / (z - (a 0 : ℂ))) := by
  let L : ℂ → ℂ := fun z => log ((z - (a 1 : ℂ)) / (z - (a 0 : ℂ)))
  have hsep : ((a 1 - a 0 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (sub_pos.mpr ha).ne'
  have hder (w : ℂ) (hw : w ∈ upperHalfPlaneSet) :
      HasDerivAt L (((a 1 - a 0 : ℝ) : ℂ) *
        schwarzChristoffelIntegrand a (fun _ => -1) w) w := by
    have hw0 : w - (a 0 : ℂ) ≠ 0 := sub_ne_zero.mpr (UpperHalfPlane.ne_ofReal ⟨w, hw⟩ _)
    have hw1 : w - (a 1 : ℂ) ≠ 0 := sub_ne_zero.mpr (UpperHalfPlane.ne_ofReal ⟨w, hw⟩ _)
    have hupper := (bijOn_sub_div_sub_upperHalfPlaneSet ha).mapsTo hw
    have hlog := (((hasDerivAt_id w).sub_const (a 1 : ℂ)).div
      ((hasDerivAt_id w).sub_const (a 0 : ℂ)) hw0).clog
        (Or.inr (ne_of_gt hupper))
    apply hlog.congr_deriv
    simp only [schwarzChristoffelIntegrand_def, Fin.prod_univ_two, ofReal_neg,
      ofReal_one, cpow_neg_one, ofReal_sub, one_mul, Pi.div_apply, id_eq]
    field_simp
    ring
  have heq := eqOn_schwarzChristoffelPrimitive a (fun _ => -1) z₀
    (g := fun w => (L w - L z₀) / ((a 1 - a 0 : ℝ) : ℂ))
    (fun w hw => by
      simpa only [mul_div_cancel_left₀ _ hsep] using
        ((hder w hw).sub_const (L z₀)).div_const ((a 1 - a 0 : ℝ) : ℂ))
    (by simp)
  have h := heq hz
  dsimp only [L] at h
  apply (div_eq_iff hsep).mp at h
  linear_combination -h

/-- **The Schwarz--Christoffel map onto a strip with two logarithmic ends.**
The affine image of the normalized primitive for two ordered prevertices, both of
exponent `-1`, is a bijection onto the entire strip of height `π`. -/
theorem bijOn_const_mul_schwarzChristoffelPrimitive_two_neg_one_add
    (a : Fin 2 → ℝ) (ha : a 0 < a 1) (z₀ : UpperHalfPlane) :
    BijOn (fun z => ((a 1 - a 0 : ℝ) : ℂ) *
      schwarzChristoffelPrimitive a (fun _ => -1) z₀ z +
      log (((z₀ : ℂ) - (a 1 : ℂ)) / ((z₀ : ℂ) - (a 0 : ℂ))))
      upperHalfPlaneSet {w : ℂ | w.im ∈ Ioo 0 Real.pi} :=
  (bijOn_log_upperHalfPlaneSet.comp (bijOn_sub_div_sub_upperHalfPlaneSet ha)).congr
    (fun _ hz => (const_mul_schwarzChristoffelPrimitive_two_neg_one_add_eq_log a ha z₀ hz).symm)

/-- **Every horizontal strip has a two-ended Schwarz--Christoffel representation.**
For any two ordered real prevertices and any base point, an affine image of their
normalized primitive with exponents `-1` maps the upper half-plane bijectively onto
any prescribed nonempty horizontal strip. The multiplicative constant is nonzero. -/
theorem exists_bijOn_const_mul_schwarzChristoffelPrimitive_add_strip
    (a : Fin 2 → ℝ) (ha : a 0 < a 1) (z₀ : UpperHalfPlane)
    {l h : ℝ} (hlh : l < h) :
    ∃ A : ℂ, A ≠ 0 ∧ ∃ B : ℂ,
      BijOn (fun z => A * schwarzChristoffelPrimitive a (fun _ => -1) z₀ z + B)
        upperHalfPlaneSet {w : ℂ | w.im ∈ Ioo l h} := by
  let s : ℝ := (h - l) / Real.pi
  have hs : 0 < s := div_pos (sub_pos.mpr hlh) Real.pi_pos
  have hspi : s * Real.pi = h - l := div_mul_cancel₀ _ Real.pi_ne_zero
  have hsC : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
  have hT : BijOn (fun w : ℂ => (s : ℂ) * w + (l : ℂ) * I)
      {w : ℂ | w.im ∈ Ioo 0 Real.pi} {w : ℂ | w.im ∈ Ioo l h} := by
    refine ⟨fun w hw => ?_, fun w _ v _ hwv => ?_, fun v hv => ?_⟩
    · have hlo := mul_pos hs hw.1
      have hhi := mul_lt_mul_of_pos_left hw.2 hs
      simp only [mem_ofPred_eq, add_im, mul_im, ofReal_re, ofReal_im,
        zero_mul, I_re, I_im, mul_one]
      constructor <;> linarith
    · exact mul_left_cancel₀ hsC (add_right_cancel hwv)
    · refine ⟨(v - (l : ℂ) * I) / (s : ℂ), ?_, ?_⟩
      · simp only [mem_ofPred_eq, div_ofReal_im, sub_im, mul_im, ofReal_re,
          ofReal_im, I_im, I_re, mul_one, zero_mul, add_zero]
        constructor
        · exact div_pos (sub_pos.mpr hv.1) hs
        · rw [div_lt_iff₀ hs]
          nlinarith [hv.2]
      · simp only [mul_div_cancel₀ _ hsC, sub_add_cancel]
  let c := log (((z₀ : ℂ) - (a 1 : ℂ)) / ((z₀ : ℂ) - (a 0 : ℂ)))
  refine ⟨(s : ℂ) * ((a 1 - a 0 : ℝ) : ℂ), mul_ne_zero hsC ?_,
    (s : ℂ) * c + (l : ℂ) * I, ?_⟩
  · exact ofReal_ne_zero.mpr (sub_pos.mpr ha).ne'
  · apply (hT.comp (bijOn_const_mul_schwarzChristoffelPrimitive_two_neg_one_add a ha z₀)).congr
    intro z _
    dsimp only [Function.comp_def, c]
    ring

end TauCeti
