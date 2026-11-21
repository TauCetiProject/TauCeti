/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Concentration.Poincare.LogSobolev
public import Mathlib.Probability.Moments.CovarianceBilin

/-!
# Linear tests for the Poincaré inequality

A probability measure with a finite second moment and Poincaré constant `C` satisfies
`Var(⟪v, ·⟫) ≤ C * ‖v‖²`. Its centered covariance bilinear form satisfies the same
quadratic-form bound. On a nontrivial space, a measure with identity covariance therefore
has `1 ≤ C`.

The linear-test argument is adapted from the
[KLS formalization](https://github.com/human-ai-mathematics/kls-lean/blob/65810c73f9dd7945fc646ab484cb19d673f5291d/formalization/FunctionalInequalities/Poincare/SmoothTest/Linear.lean).
The variance and derivative-energy normalization agrees with Anderson, Guionnet and Zeitouni,
*An Introduction to Random Matrices*, §2.3.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ContDiff

namespace MeasureTheory.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ] {C : ℝ}

/-- Linear tests bound variance by the Poincaré constant times the squared norm of the
coefficient vector. -/
theorem PoincareInequality.variance_inner_le (hP : μ.PoincareInequality C) (v : E)
    (hv : MemLp (fun x ↦ inner ℝ v x) 2 μ) :
    variance (fun x ↦ inner ℝ v x) μ ≤ C * ‖v‖ ^ 2 := by
  have hd (x : E) : fderiv ℝ (fun y ↦ inner ℝ v y) x = innerSL ℝ v :=
    (innerSL ℝ v).hasFDerivAt.fderiv
  have hdf : MemLp (fun x ↦ ‖fderiv ℝ (fun y ↦ inner ℝ v y) x‖) 2 μ := by
    simpa only [hd, innerSL_apply_norm] using (memLp_const ‖v‖ : MemLp (fun _ : E ↦ ‖v‖) 2 μ)
  simpa only [hd, innerSL_apply_norm, integral_const, probReal_univ, one_smul] using
    hP.apply (fun x ↦ inner ℝ v x) (innerSL ℝ v).contDiff hv hdf

variable [BorelSpace E]

/-- The centered covariance quadratic form is bounded by the Poincaré constant. -/
theorem PoincareInequality.covarianceBilin_self_le [CompleteSpace E]
    (hP : μ.PoincareInequality C) (hμ : MemLp (id : E → E) 2 μ) (v : E) :
    covarianceBilin μ v v ≤ C * ‖v‖ ^ 2 := by
  rw [covarianceBilin_self hμ]
  exact hP.variance_inner_le v (hμ.const_inner v)

/-- A measure with identity covariance on a nontrivial space has Poincaré constant at least
one. -/
theorem PoincareInequality.one_le_of_covarianceBilin_self_eq [CompleteSpace E] [Nontrivial E]
    (hP : μ.PoincareInequality C) (hμ : MemLp (id : E → E) 2 μ)
    (hcov : ∀ v : E, covarianceBilin μ v v = ‖v‖ ^ 2) : 1 ≤ C := by
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have hpos : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
  have h := hP.covarianceBilin_self_le hμ v
  rw [hcov v] at h
  nlinarith

end MeasureTheory.Measure
