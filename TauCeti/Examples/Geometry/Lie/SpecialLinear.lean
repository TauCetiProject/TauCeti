/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Exponential.Diagonal
public import TauCeti.Geometry.Manifold.Instances.SpecialLinearGroup
public import TauCeti.Geometry.Lie.ContinuousFunctor
public import TauCeti.Geometry.Lie.Exponential.Matrix.Compatibility
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# A non-exponential element of the real special linear group

The native real group `SL₂(ℝ)` has a Lie-group exponential that misses the
explicit element `diag(-2,-1/2)`. In fact no real matrix exponentiates to that matrix, even
without a trace condition. The same element witnesses non-surjectivity for both the matrix
exponential and the native Lie-group exponential.

## Main declarations

* `TauCeti.Lie.SL2.negativeDiagonal`: the determinant-one negative diagonal.
* `TauCeti.Lie.SL2.coe_negativeDiagonal`: its underlying matrix.
* `TauCeti.Lie.SL2.exp_ne_negativeDiagonal`: exclusion from the real matrix exponential.
* `TauCeti.Lie.SL2.negativeDiagonal_ne_one`: the element is nontrivial.
* `TauCeti.Lie.SL2.lieExp_ne_negativeDiagonal`: exclusion from the native exponential.
* `TauCeti.Lie.SL2.lieExp_not_surjective`: native exponential non-surjectivity.

## References

* B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, second edition, GTM 222
  (2015), Section 3.7, Definition 3.40 and Example 3.41, for matrix-group exponentials and
  non-surjectivity. Example 3.41 uses a different, nondiagonalizable matrix.
-/

public noncomputable section

open scoped Matrix

namespace TauCeti.Lie.SL2

/-- The native special-linear element with diagonal entries `-2` and `-1/2`. -/
def negativeDiagonal : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  ⟨Matrix.diagonal ![-2, -(1 / 2)], by norm_num [Matrix.det_fin_two]⟩

/-- The underlying matrix of the negative diagonal element. -/
@[simp]
theorem coe_negativeDiagonal :
    (negativeDiagonal : Matrix (Fin 2) (Fin 2) ℝ) = Matrix.diagonal ![-2, -(1 / 2)] := by
  unfold negativeDiagonal
  rfl

/-- No real matrix exponentiates to the negative diagonal element. -/
theorem exp_ne_negativeDiagonal (A : Matrix (Fin 2) (Fin 2) ℝ) :
    NormedSpace.exp A ≠ (negativeDiagonal : Matrix (Fin 2) (Fin 2) ℝ) := by
  intro h
  have hinj : Function.Injective (![-2, -(1 / 2)] : Fin 2 → ℝ) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | rfl | norm_num at hij
  have hp := A.diag_pos_of_exp_eq_diagonal hinj (by simpa only [coe_negativeDiagonal] using h) 0
  norm_num at hp

/-- The negative diagonal element is not the identity. -/
@[simp]
theorem negativeDiagonal_ne_one : negativeDiagonal ≠ 1 := by
  intro h
  have he := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) ℝ =>
    (A : Matrix (Fin 2) (Fin 2) ℝ) 0 0) h
  norm_num [coe_negativeDiagonal] at he

section Native

open scoped Matrix.Norms.Operator ContDiff Manifold
attribute [local instance] Matrix.linftyOpTopologicalSpace
attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

/-- The actual native `SL₂(ℝ)` exponential misses the negative diagonal element. -/
theorem lieExp_ne_negativeDiagonal
    (X : LeftInvariantDerivation
      𝓘(ℝ, Matrix.SpecialLinearGroup.Model (Fin 2) ℝ)
      (Matrix.SpecialLinearGroup (Fin 2) ℝ)) :
    lieExp X ≠ negativeDiagonal := by
  intro h
  let f : Matrix.SpecialLinearGroup (Fin 2) ℝ →ₜ* Matrix.GeneralLinearGroup (Fin 2) ℝ :=
    { Matrix.SpecialLinearGroup.toGL with
      continuous_toFun := Matrix.SpecialLinearGroup.continuous_toGL }
  have hn := f.map_lieExp
    (I := 𝓘(ℝ, Matrix.SpecialLinearGroup.Model (Fin 2) ℝ))
    (I' := 𝓘(ℝ, Matrix (Fin 2) (Fin 2) ℝ)) X
  dsimp only at hn
  rw [h, lieExp_eq_expUnit] at hn
  have hm := congrArg (fun U : (Matrix (Fin 2) (Fin 2) ℝ)ˣ =>
    (U : Matrix (Fin 2) (Fin 2) ℝ)) hn
  -- The continuous homomorphism retains toGL as its underlying monoid homomorphism.
  have hf : (f negativeDiagonal : Matrix (Fin 2) (Fin 2) ℝ) =
      (negativeDiagonal : Matrix (Fin 2) (Fin 2) ℝ) :=
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix negativeDiagonal
  have he := hm.symm.trans hf
  simp only [TauCeti.expUnit_coe] at he
  apply exp_ne_negativeDiagonal _
  simpa only [Matrix.linftyOpTopologicalSpace_eq] using he

/-- The native real special-linear group has a nonsurjective exponential map. -/
theorem lieExp_not_surjective :
    ¬ Function.Surjective
      (lieExp (I := 𝓘(ℝ, Matrix.SpecialLinearGroup.Model (Fin 2) ℝ))
        (G := Matrix.SpecialLinearGroup (Fin 2) ℝ)) := by
  intro h
  obtain ⟨X, hX⟩ := h negativeDiagonal
  exact lieExp_ne_negativeDiagonal X hX

end Native
end TauCeti.Lie.SL2
