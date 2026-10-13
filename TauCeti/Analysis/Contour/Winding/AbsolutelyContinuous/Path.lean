/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Winding.Number.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Path
import TauCeti.MeasureTheory.Integral.CurveIntegral.Basic

/-!
# The winding number as an ordinary path integral

For an absolutely continuous path, the existing raw winding number is the normalized ordinary
curve integral of the Cauchy kernel, away from the path's trace.
-/

public section

open MeasureTheory Set

namespace TauCeti.Contour

/-- The ordinary Cauchy-kernel 1-form is curve integrable along an absolutely continuous path
that avoids its pole. -/
theorem _root_.AbsolutelyContinuousOnInterval.curveIntegrable_inv_sub_smul_id
    {x y w : ℂ} {p : Path x y} (hp : AbsolutelyContinuousOnInterval p.extend 0 1)
    (havoid : ∀ t : Icc (0 : ℝ) 1, p t ≠ w) :
    CurveIntegrable (fun z ↦ (z - w)⁻¹ • ContinuousLinearMap.id ℂ ℂ) p := by
  have hw : w ∉ p.extend '' uIcc (0 : ℝ) 1 := by
    rintro ⟨t, ht, heq⟩
    rw [uIcc_of_le zero_le_one] at ht
    rw [Path.extend_apply p ht] at heq
    exact havoid ⟨t, ht⟩ heq
  rw [curveIntegrable_iff_intervalIntegrable_deriv]
  simpa only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul] using
    hp.intervalIntegrable_inv_sub_mul_deriv hw

/-- The winding number of an absolutely continuous path avoiding a point is its normalized
ordinary curve integral of the Cauchy kernel. -/
theorem _root_.AbsolutelyContinuousOnInterval.windingNumber_eq_two_pi_I_inv_mul_curveIntegral
    {x y w : ℂ} {p : Path x y}
    (hp : AbsolutelyContinuousOnInterval p.extend 0 1)
    (havoid : ∀ t : Icc (0 : ℝ) 1, p t ≠ w) :
    windingNumber p.extend 0 1 w =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ∫ᶜ z in p, (z - w)⁻¹ • ContinuousLinearMap.id ℂ ℂ := by
  have hw : w ∉ p.extend '' uIcc (0 : ℝ) 1 := by
    rintro ⟨t, ht, heq⟩
    rw [uIcc_of_le zero_le_one] at ht
    rw [Path.extend_apply p ht] at heq
    exact havoid ⟨t, ht⟩ heq
  rw [hp.windingNumber_eq_integral hw,
    curveIntegral_eq_intervalIntegral_deriv]
  simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]

/-- Reversing an absolutely continuous path negates its actual winding number off the trace. -/
theorem _root_.AbsolutelyContinuousOnInterval.windingNumber_path_symm
    {x y w : ℂ} {p : Path x y}
    (hp : AbsolutelyContinuousOnInterval p.extend 0 1)
    (havoid : ∀ t : Icc (0 : ℝ) 1, p t ≠ w) :
    windingNumber p.symm.extend 0 1 w = -windingNumber p.extend 0 1 w := by
  have hs : ∀ t : Icc (0 : ℝ) 1, p.symm t ≠ w := by
    intro t ht
    have hm : w ∈ range p := by
      rw [← Path.symm_range p]
      exact ⟨t, ht⟩
    obtain ⟨u, hu⟩ := hm
    exact havoid u hu
  rw [AbsolutelyContinuousOnInterval.windingNumber_eq_two_pi_I_inv_mul_curveIntegral
    (Path.absolutelyContinuousOnInterval_extend_symm hp) hs,
    hp.windingNumber_eq_two_pi_I_inv_mul_curveIntegral havoid, curveIntegral_symm, mul_neg]

/-- Concatenating absolutely continuous paths adds their actual winding numbers away from both
traces. -/
theorem _root_.AbsolutelyContinuousOnInterval.windingNumber_path_trans
    {x y z w : ℂ} {p : Path x y} {q : Path y z}
    (hp : AbsolutelyContinuousOnInterval p.extend 0 1)
    (hq : AbsolutelyContinuousOnInterval q.extend 0 1)
    (hpavoid : ∀ t : Icc (0 : ℝ) 1, p t ≠ w)
    (hqavoid : ∀ t : Icc (0 : ℝ) 1, q t ≠ w) :
    windingNumber (p.trans q).extend 0 1 w =
      windingNumber p.extend 0 1 w + windingNumber q.extend 0 1 w := by
  have ht : ∀ t : Icc (0 : ℝ) 1, (p.trans q) t ≠ w := by
    intro t ht
    have hm : w ∈ range p ∪ range q := by
      rw [← Path.trans_range p q]
      exact ⟨t, ht⟩
    rcases hm with ⟨u, hu⟩ | ⟨u, hu⟩
    · exact hpavoid u hu
    · exact hqavoid u hu
  rw [AbsolutelyContinuousOnInterval.windingNumber_eq_two_pi_I_inv_mul_curveIntegral
      (Path.absolutelyContinuousOnInterval_extend_trans hp hq) ht,
    hp.windingNumber_eq_two_pi_I_inv_mul_curveIntegral hpavoid,
    hq.windingNumber_eq_two_pi_I_inv_mul_curveIntegral hqavoid,
    curveIntegral_trans
      (hp.curveIntegrable_inv_sub_smul_id hpavoid)
      (hq.curveIntegrable_inv_sub_smul_id hqavoid), mul_add]

end TauCeti.Contour
