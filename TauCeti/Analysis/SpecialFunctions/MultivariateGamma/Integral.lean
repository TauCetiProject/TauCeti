/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.MultivariateGamma.Basic
public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Lebesgue
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# The multivariate Gamma function as a cone integral

For `(p - 1) / 2 < a` the multivariate Gamma function `TauCeti.multivariateGamma p a` is the
integral of `(det A) ^ (a - (p + 1) / 2) * exp (-trace A)` over the cone of positive-definite
symmetric `p × p` matrices, taken against `TauCeti.symmetricLebesgue p`. The normalization of
that reference measure is part of the identity, not a convention that can be changed afterwards,
which is why this file, unlike the elementary theory in
`TauCeti/Analysis/SpecialFunctions/MultivariateGamma/Basic.lean`, depends on the measure theory
of the symmetric matrices.

Only dimension zero is available so far; the positive-dimensional identity is proved in Cholesky
coordinates and waits on the Jacobian of `L ↦ L * Lᵀ`.

## Main results

* `TauCeti.integral_posDef_multivariateGamma_zero` — the cone integral in dimension zero.

## References

* M. L. Eaton, *Multivariate Statistics: A Vector Space Approach*, Chapter 5.
* R. J. Muirhead, *Aspects of Multivariate Statistical Theory*, Section 2.1.
-/

public section

noncomputable section

open MeasureTheory Real

namespace TauCeti

/-- The cone integral that characterizes `Γ_p`, in dimension zero: the symmetric `0 × 0` matrices
form a single point, which is positive definite and has determinant `1` and trace `0`, and
`symmetricLebesgue 0` is the Dirac measure there. Both sides are `1`, so unlike the
positive-dimensional identity this one needs no hypothesis on the shape parameter. -/
theorem integral_posDef_multivariateGamma_zero (a : ℝ) :
    ∫ A in {A : selfAdjoint.submodule ℝ (Matrix (Fin 0) (Fin 0) ℝ) |
        (A : Matrix (Fin 0) (Fin 0) ℝ).PosDef},
      (A : Matrix (Fin 0) (Fin 0) ℝ).det ^ (a - 1 / 2) *
        exp (-(A : Matrix (Fin 0) (Fin 0) ℝ).trace) ∂symmetricLebesgue 0 =
      multivariateGamma 0 a := by
  have hset : {A : selfAdjoint.submodule ℝ (Matrix (Fin 0) (Fin 0) ℝ) |
      (A : Matrix (Fin 0) (Fin 0) ℝ).PosDef} = Set.univ :=
    Set.eq_univ_of_forall fun A =>
      ⟨selfAdjoint.isHermitian_coe A, fun x hx => absurd (by ext i; exact i.elim0) hx⟩
  rw [hset, Measure.restrict_univ, symmetricLebesgue_zero, integral_dirac]
  simp [Matrix.det_fin_zero]

end TauCeti
