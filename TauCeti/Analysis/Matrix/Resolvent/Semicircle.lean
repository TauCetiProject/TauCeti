/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Resolvent.SelfConsistency
public import TauCeti.Probability.Distributions.Semicircle.ResolventTransform
public import Mathlib.Algebra.BigOperators.Expect

/-!
# Deterministic semicircle comparison for Hermitian resolvents

The mean absolute errors of the principal-minor quadratic forms control the spectral resolvent
transform's deviation from the semicircle transform at each upper-half-plane parameter.
-/

public section

noncomputable section

open MeasureTheory Matrix
open scoped BigOperators NNReal

namespace Matrix.IsHermitian

/-- The difference from the semicircle transform is controlled by the mean absolute
leave-one-out error, the principal-minor trace correction, and the mean absolute diagonal entry. -/
theorem norm_resolventTransform_spectralMeasure_sub_semicircleReal_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) {z : ℂ} (hz : 0 < z.im) (v : ℝ≥0) :
    ‖resolventTransform (A.spectralMeasure hA : Measure ℝ) z -
      resolventTransform (TauCeti.Probability.semicircleReal 0 v) z‖ ≤
      z.im⁻¹ ^ 2 * ((𝔼 i, ‖A.minorQuadraticError i z v‖) +
        3 * (v : ℝ) / ((Fintype.card ι : ℝ) * z.im) + (𝔼 i, ‖A i i‖)) := by
  let m := resolventTransform (A.spectralMeasure hA : Measure ℝ) z
  let c := 3 * (v : ℝ) / ((Fintype.card ι : ℝ) * z.im)
  have hs := TauCeti.Probability.norm_sub_resolventTransform_semicircleReal_le
    (a := 0) (v := v) hz (w := m)
    (im_resolventTransform_pos (IsProbabilityMeasure.ne_zero _) hz).le
  rw [Complex.ofReal_zero, sub_zero] at hs
  have hentry (i : ι) :
      ‖(v : ℂ) * m - star (fun j : {j // j ≠ i} ↦ A j i) ⬝ᵥ
        (A.minorResolvent i z *ᵥ fun j : {j // j ≠ i} ↦ A j i)‖ ≤
      ‖A.minorQuadraticError i z v‖ + c := by
    rw [minorQuadraticError_def, norm_sub_rev]
    refine (norm_sub_le_norm_sub_add_norm_sub _
      (((v : ℂ) / (Fintype.card ι : ℂ)) * (A.minorResolvent i z).trace) _).trans
      (add_le_add le_rfl ?_)
    rw [div_eq_mul_inv, mul_assoc, ← mul_sub, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg v.coe_nonneg]
    have h := hA.norm_inv_card_mul_trace_minorResolvent_sub_resolventTransform_le hz.ne' i
    rw [abs_of_pos hz] at h
    exact (mul_le_mul_of_nonneg_left h v.coe_nonneg).trans_eq (by unfold c; ring)
  let E (i : ι) := ‖A.minorQuadraticError i z v‖ + c + ‖A i i‖
  have hres := hA.norm_resolventTransform_spectralMeasure_quadratic_le hz (v : ℂ)
  have hbound := hres.trans (mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum fun i _ ↦ by
      rw [add_sub_assoc]
      exact (norm_add_le _ _).trans ((add_le_add le_rfl (hentry i)).trans_eq (add_comm ..)))
    (by positivity) : _ ≤ (z.im * Fintype.card ι)⁻¹ * ∑ i, E i)
  refine hs.trans ((div_le_div_of_nonneg_right hbound hz.le).trans_eq ?_)
  calc
    _ = z.im⁻¹ ^ 2 * (𝔼 i, E i) := by rw [Fintype.expect_eq_sum_div_card]; ring
    _ = _ := by simp only [E, Finset.expect_add_distrib, Fintype.expect_const, c]

end Matrix.IsHermitian
