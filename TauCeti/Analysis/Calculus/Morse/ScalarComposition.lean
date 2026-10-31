/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Index

/-!
# Scalar reparametrization of Morse functions

A scalar change of values with nonzero derivative preserves critical points and their
nondegeneracy. At a critical point it scales the Hessian by its first derivative. Positive
scaling preserves the Morse index; negative scaling exchanges the positive and negative
indices. Thus a decreasing reparametrization changes index λ into dimension minus λ.
This is the local calculation underlying reversal of a Morse exhaustion.

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, Sections 3 and 7.
-/

public section

open Function

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : E → ℝ} {φ : ℝ → ℝ} {x : E}

/-- At a critical point, a scalar change of values scales the Hessian quadratic form. -/
theorem hessianQuadraticForm_scalar_comp (hφ : ContDiffAt ℝ 2 φ (f x))
    (hf : ContDiffAt ℝ 2 f x) (hc : fderiv ℝ f x = 0) :
    hessianQuadraticForm (φ ∘ f) x = deriv φ (f x) • hessianQuadraticForm f x := by
  ext v
  simp [hessianQuadraticForm_apply, fderiv_fderiv_scalar_comp_of_fderiv_eq_zero hφ hf hc]

/-- A scalar change of values with nonzero derivative preserves nondegenerate critical points,
including on infinite-dimensional normed spaces. -/
theorem IsNondegenerateCriticalPoint.scalar_comp (h : IsNondegenerateCriticalPoint f x)
    (hφ : ContDiffAt ℝ 2 φ (f x)) (hφ' : deriv φ (f x) ≠ 0) :
    IsNondegenerateCriticalPoint (φ ∘ f) x := by
  refine ⟨hφ.comp x h.contDiffAt,
    (fderiv_scalar_comp_eq_zero_iff (hφ.differentiableAt two_ne_zero)
      (h.contDiffAt.differentiableAt two_ne_zero) hφ').mpr h.fderiv_eq_zero, ?_⟩
  rw [fderiv_fderiv_scalar_comp_of_fderiv_eq_zero hφ h.contDiffAt h.fderiv_eq_zero]
  obtain ⟨e, he⟩ := h.isInvertible
  rw [← he]
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := (deriv φ (f x))⁻¹ • e.symm.toContinuousLinearMap)
  all_goals ext v; simp [smul_smul, hφ']

/-- An increasing scalar reparametrization preserves the Morse index at a critical point. -/
theorem morseIndex_scalar_comp_of_pos (hφ : ContDiffAt ℝ 2 φ (f x))
    (hf : ContDiffAt ℝ 2 f x) (hc : fderiv ℝ f x = 0) (hφ' : 0 < deriv φ (f x)) :
    morseIndex (φ ∘ f) x = morseIndex f x := by
  rw [morseIndex_def, morseIndex_def, hessianQuadraticForm_scalar_comp hφ hf hc]
  exact QuadraticForm.sigNeg_smul_of_pos _ hφ'

/-- A decreasing scalar reparametrization complements the Morse index at a nondegenerate
critical point. The additive statement avoids truncated natural subtraction. -/
theorem IsNondegenerateCriticalPoint.morseIndex_scalar_comp_add_morseIndex_eq_finrank
    [FiniteDimensional ℝ E] (h : IsNondegenerateCriticalPoint f x)
    (hφ : ContDiffAt ℝ 2 φ (f x)) (hφ' : deriv φ (f x) < 0) :
    morseIndex (φ ∘ f) x + morseIndex f x = Module.finrank ℝ E := by
  rw [morseIndex_def, hessianQuadraticForm_scalar_comp hφ h.contDiffAt h.fderiv_eq_zero,
    QuadraticForm.sigNeg_smul_of_neg _ hφ']
  exact h.sigPos_hessianQuadraticForm_add_morseIndex_eq_finrank

end TauCeti
