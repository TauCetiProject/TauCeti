/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Primitive
public import TauCeti.Analysis.Complex.UpperHalfPlane.Log
public import TauCeti.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import TauCeti.Analysis.Complex.HorizontalStrip
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

/-- **The explicit Schwarz--Christoffel formula for a strip.** Two distinct prevertices
of exponent `-1` give the principal logarithm of their fractional-linear ratio, after
scaling by their separation and translating by the value at the base point. -/
@[simp]
theorem const_mul_schwarzChristoffelPrimitive_two_neg_one_add_eq_log (a : Fin 2 → ℝ)
    (ha : a 0 ≠ a 1) (z₀ : UpperHalfPlane) {z : ℂ} (hz : z ∈ upperHalfPlaneSet) :
    ((a 1 : ℂ) - (a 0 : ℂ)) * schwarzChristoffelPrimitive a (fun _ => -1) z₀ z +
      log (((z₀ : ℂ) - (a 1 : ℂ)) / ((z₀ : ℂ) - (a 0 : ℂ))) =
      log ((z - (a 1 : ℂ)) / (z - (a 0 : ℂ))) := by
  let L : ℂ → ℂ := fun z => log ((z - (a 1 : ℂ)) / (z - (a 0 : ℂ)))
  have hsep : ((a 1 : ℂ) - (a 0 : ℂ)) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr ha.symm
  have hder (w : ℂ) (hw : w ∈ upperHalfPlaneSet) :
      HasDerivAt L (((a 1 : ℂ) - (a 0 : ℂ)) *
        schwarzChristoffelIntegrand a (fun _ => -1) w) w := by
    have hw0 : w - (a 0 : ℂ) ≠ 0 := sub_ne_zero.mpr (UpperHalfPlane.ne_ofReal ⟨w, hw⟩ _)
    have hw1 : w - (a 1 : ℂ) ≠ 0 := sub_ne_zero.mpr (UpperHalfPlane.ne_ofReal ⟨w, hw⟩ _)
    have him : ((w - (a 1 : ℂ)) / (w - (a 0 : ℂ))).im ≠ 0 := by
      rw [Complex.div_im, ← sub_div]
      apply div_ne_zero
      · simp only [sub_im, ofReal_im, sub_zero, sub_re, ofReal_re]
        have heq : w.im * (w.re - a 0) - (w.re - a 1) * w.im =
            w.im * (a 1 - a 0) := by ring
        rw [heq]
        exact mul_ne_zero hw.ne' (sub_ne_zero.mpr ha.symm)
      · exact (Complex.normSq_pos.mpr hw0).ne'
    have hlog := (((hasDerivAt_id w).sub_const (a 1 : ℂ)).div
      ((hasDerivAt_id w).sub_const (a 0 : ℂ)) hw0).clog
        (Or.inr him)
    apply hlog.congr_deriv
    simp only [schwarzChristoffelIntegrand_def, Fin.prod_univ_two, ofReal_neg,
      ofReal_one, cpow_neg_one, one_mul, Pi.div_apply, id_eq]
    field_simp
    ring
  have heq := eqOn_schwarzChristoffelPrimitive a (fun _ => -1) z₀
    (g := fun w => (L w - L z₀) / ((a 1 : ℂ) - (a 0 : ℂ)))
    (fun w hw => by
      simpa only [mul_div_cancel_left₀ _ hsep] using
        ((hder w hw).sub_const (L z₀)).div_const ((a 1 : ℂ) - (a 0 : ℂ)))
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
    BijOn (fun z => ((a 1 : ℂ) - (a 0 : ℂ)) *
      schwarzChristoffelPrimitive a (fun _ => -1) z₀ z +
      log (((z₀ : ℂ) - (a 1 : ℂ)) / ((z₀ : ℂ) - (a 0 : ℂ))))
      upperHalfPlaneSet {w : ℂ | w.im ∈ Ioo 0 Real.pi} :=
  (bijOn_log_upperHalfPlaneSet.comp (bijOn_sub_div_sub_upperHalfPlaneSet ha)).congr
    (fun _ hz =>
      (const_mul_schwarzChristoffelPrimitive_two_neg_one_add_eq_log a (ne_of_lt ha) z₀ hz).symm)

/-- **Every horizontal strip has a two-ended Schwarz--Christoffel representation.**
For any two distinct real prevertices and any base point, an affine image of their
normalized primitive with exponents `-1` maps the upper half-plane bijectively onto
any prescribed nonempty horizontal strip. The multiplicative constant is nonzero. -/
theorem exists_bijOn_const_mul_schwarzChristoffelPrimitive_add_strip
    (a : Fin 2 → ℝ) (ha : Function.Injective a) (z₀ : UpperHalfPlane)
    {l h : ℝ} (hlh : l < h) :
    ∃ A : ℂ, A ≠ 0 ∧ ∃ B : ℂ,
      BijOn (fun z => A * schwarzChristoffelPrimitive a (fun _ => -1) z₀ z + B)
        upperHalfPlaneSet {w : ℂ | w.im ∈ Ioo l h} := by
  wlog hab : a 0 < a 1 generalizing a
  · let b : Fin 2 → ℝ := ![a 1, a 0]
    have hne : a 0 ≠ a 1 := ha.ne (by decide)
    have hb : b 0 < b 1 := lt_of_le_of_ne (le_of_not_gt hab) hne.symm
    have hbi : Function.Injective b := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [b]
    obtain ⟨A, hA, B, hB⟩ := this b hbi hb
    have heq : EqOn (schwarzChristoffelPrimitive b (fun _ => -1) z₀)
        (schwarzChristoffelPrimitive a (fun _ => -1) z₀) upperHalfPlaneSet :=
      eqOn_schwarzChristoffelPrimitive a (fun _ => -1) z₀
        (fun w hw => by
          simpa [schwarzChristoffelIntegrand_def, Fin.prod_univ_two, b, mul_comm] using
            hasDerivAt_schwarzChristoffelPrimitive b (fun _ => -1) z₀ hw)
        (schwarzChristoffelPrimitive_apply_base b (fun _ => -1) z₀)
    exact ⟨A, hA, B, hB.congr (fun z hz => by simp only [heq hz])⟩
  let s : ℝ := (h - l) / Real.pi
  have hs : 0 < s := div_pos (sub_pos.mpr hlh) Real.pi_pos
  have hspi : s * Real.pi = h - l := div_mul_cancel₀ _ Real.pi_ne_zero
  have hsC : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
  have hT := bijOn_ofReal_mul_add_horizontalStrip hs ((l : ℂ) * I) 0 Real.pi
  simp only [mul_zero, ofReal_im, ofReal_re, I_im, I_re,
    mul_one, mul_im, add_zero, zero_add, hspi, sub_add_cancel] at hT
  let c := log (((z₀ : ℂ) - (a 1 : ℂ)) / ((z₀ : ℂ) - (a 0 : ℂ)))
  refine ⟨(s : ℂ) * ((a 1 : ℂ) - (a 0 : ℂ)), mul_ne_zero hsC ?_,
    (s : ℂ) * c + (l : ℂ) * I, ?_⟩
  · exact_mod_cast (sub_pos.mpr hab).ne'
  · apply (hT.comp (bijOn_const_mul_schwarzChristoffelPrimitive_two_neg_one_add a hab z₀)).congr
    intro z _
    dsimp only [Function.comp_def, c]
    ring

end TauCeti
