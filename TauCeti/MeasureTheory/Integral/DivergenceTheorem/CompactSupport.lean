/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Compactly supported divergence on a vector space

This specializes Mathlib's `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable`
to a globally `C¹`, compactly supported vector field. A bounding box contains its support,
so every boundary flux vanishes and the full-space divergence integral is zero.
-/

public section

noncomputable section

open Set

namespace MeasureTheory

/-- The divergence of a globally `C¹`, compactly supported coordinate vector field is
integrable and has zero integral on the whole space. -/
theorem integral_divergence_eq_zero {n : ℕ}
    {f : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    Integrable (fun x ↦ ∑ i : Fin (n + 1), fderiv ℝ f x (Pi.single i 1) i) ∧
      (∫ x, ∑ i : Fin (n + 1), fderiv ℝ f x (Pi.single i 1) i) = 0 := by
  let D (x : Fin (n + 1) → ℝ) := ∑ i, fderiv ℝ f x (Pi.single i 1) i
  have hDc : Continuous D := continuous_finsetSum _ fun i _ ↦
    (continuous_apply i).comp ((hf.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hDcompact : HasCompactSupport D := by
    apply HasCompactSupport.of_support_subset_isCompact hc
    intro x hx
    by_contra hn
    exact hx (by simp [D, fderiv_of_notMem_tsupport ℝ hn])
  have hDi : Integrable D := hDc.integrable_of_hasCompactSupport hDcompact
  obtain ⟨R, hR, hbound⟩ := hc.isBounded.exists_pos_norm_lt
  let a : Fin (n + 1) → ℝ := fun _ ↦ -R
  let b : Fin (n + 1) → ℝ := fun _ ↦ R
  have hab : a ≤ b := fun _ ↦ neg_le_self hR.le
  have hzero {x : Fin (n + 1) → ℝ} (hn : R ≤ ‖x‖) : f x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hx ↦ (hbound x hx).not_ge hn)
  have hDzero {x : Fin (n + 1) → ℝ} (hx : x ∉ Icc a b) : D x = 0 := by
    have hn : R ≤ ‖x‖ := le_of_not_gt fun hn ↦ hx ⟨fun i ↦
      (abs_lt.mp (lt_of_le_of_lt (norm_le_pi_norm x i) hn)).1.le, fun i ↦
      (abs_lt.mp (lt_of_le_of_lt (norm_le_pi_norm x i) hn)).2.le⟩
    have ht : x ∉ tsupport f := fun hx ↦ (hbound x hx).not_ge hn
    simp [D, fderiv_of_notMem_tsupport ℝ ht]
  have hface (i : Fin (n + 1)) (t : ℝ) (ht : |t| = R) (y : Fin n → ℝ) :
      f (i.insertNth t y) i = 0 := by
    apply congrFun (hzero ?_) i
    have h := norm_le_pi_norm (i.insertNth (α := fun _ ↦ ℝ) t y) i
    simpa only [Fin.insertNth_apply_same, Real.norm_eq_abs, ht] using h
  have hdiv := integral_divergence_of_hasFDerivAt_off_countable a b hab f
    (fderiv ℝ f) ∅ countable_empty hf.continuous.continuousOn
    (fun x _ ↦ (hf.differentiable one_ne_zero x).hasFDerivAt) hDi.integrableOn
  refine ⟨hDi, ?_⟩
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ hDzero hx)]
  rw [hdiv]
  simp only [a, b, hface _ R (abs_of_pos hR),
    hface _ (-R) (by rw [abs_neg, abs_of_pos hR]), integral_zero, sub_self,
    Finset.sum_const_zero]

end MeasureTheory
