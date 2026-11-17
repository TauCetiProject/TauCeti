/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
import TauCeti.Analysis.InnerProductSpace.Positive.Definite

/-!
# Realizing positive-definite real quadratic forms on inner product spaces

Every positive-definite real quadratic form `Q` on a finite-dimensional real vector space `W`
corresponds to its symmetric polar bilinear form `QuadraticMap.associatedHom ℝ Q`. Applying
`TauCeti.exists_linearEquiv_inner_eq_of_posDef` produces a linear equivalence `e : W ≃ₗ[ℝ] E`
into any finite-dimensional real inner product space `E` of the same dimension transporting `Q`
to the squared norm `‖·‖ ^ 2` (`QuadraticMap.PosDef.exists_linearEquiv_norm_sq_eq`).

## Main results

* `QuadraticMap.PosDef.exists_linearEquiv_norm_sq_eq`: a positive-definite quadratic form on `W`
  is pulled back from `‖·‖ ^ 2` along a linear equivalence `W ≃ₗ[ℝ] E` whenever `W` and `E` are
  finite-dimensional of equal dimension.

## References

* S. Axler, *Linear Algebra Done Right*, 4th ed., Springer (2024), Chapter 6 (orthonormal bases
  and Gram--Schmidt).
-/

public section

open Module

/-- **Euclidean realization of a positive-definite real quadratic form.** If `Q` is a
positive-definite quadratic form on a finite-dimensional real vector space `W` and `E` is a
finite-dimensional real inner product space of the same dimension, there exists a linear
equivalence `e : W ≃ₗ[ℝ] E` such that `‖e x‖ ^ 2 = Q x` for every `x`. -/
theorem QuadraticMap.PosDef.exists_linearEquiv_norm_sq_eq
    {W E : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {Q : QuadraticForm ℝ W} (hQ : Q.PosDef) (hdim : finrank ℝ W = finrank ℝ E) :
    ∃ e : W ≃ₗ[ℝ] E, ∀ x, ‖e x‖ ^ 2 = Q x := by
  have hpos : (QuadraticMap.associatedHom ℝ Q).toQuadraticMap.PosDef := by
    rwa [QuadraticMap.toQuadraticMap_associated]
  obtain ⟨e, he⟩ := TauCeti.exists_linearEquiv_inner_eq_of_posDef hdim hpos
    (LinearMap.BilinForm.isSymm_iff.mpr (QuadraticForm.associated_isSymm ℝ Q))
  refine ⟨e, fun x ↦ ?_⟩
  rw [← real_inner_self_eq_norm_sq, he x x, QuadraticMap.associated_eq_self_apply]
