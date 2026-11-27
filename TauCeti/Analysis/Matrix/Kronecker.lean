/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Exponential.Log
import TauCeti.Topology.Instances.Matrix

/-!
# The functional calculus of Kronecker products

For square matrices `A` over `𝕜 = ℝ` or `ℂ` (any `RCLike` field), the maps `A ↦ A ⊗ₖ 1` and
`B ↦ 1 ⊗ₖ B` are continuous unital ⋆-algebra homomorphisms, so they commute with the continuous
functional calculus: `cfc f (A ⊗ₖ 1) = cfc f A ⊗ₖ 1` and `cfc f (1 ⊗ₖ B) = 1 ⊗ₖ cfc f B`. The two
factors `A ⊗ₖ 1` and `1 ⊗ₖ B` of `A ⊗ₖ B` commute, so for positive definite `A` and `B` the
logarithm of their Kronecker product splits as a sum,
`log (A ⊗ₖ B) = log A ⊗ₖ 1 + 1 ⊗ₖ log B`.

When the index `m × n` labels a basis of the tensor product of two finite quantum systems, this is
the additivity of the logarithm of a product state, which underlies the subadditivity of the von
Neumann entropy (`TauCeti/Analysis/Matrix/Entropy.lean`).

## Main results

* `Matrix.cfc_kronecker_one`, `Matrix.cfc_one_kronecker`: the functional calculus commutes with
  tensoring by the identity on either side;
* `Matrix.PosDef.cfc_log_kronecker`: `log (A ⊗ₖ B) = log A ⊗ₖ 1 + 1 ⊗ₖ log B` for positive
  definite `A` and `B`.
-/

public section

open scoped Kronecker ComplexOrder

namespace Matrix

variable {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- The functional calculus commutes with tensoring by the identity on the right. -/
@[simp]
theorem cfc_kronecker_one (f : ℝ → ℝ) (A : Matrix m m 𝕜) :
    cfc f (A ⊗ₖ (1 : Matrix n n 𝕜)) = cfc f A ⊗ₖ (1 : Matrix n n 𝕜) := by
  by_cases hA : IsSelfAdjoint A
  · simpa only [kroneckerOneStarAlgHom_apply] using
      (StarAlgHom.map_cfc (kroneckerOneStarAlgHom 𝕜 n) f A
        (A.finite_real_spectrum.continuousOn _) continuous_kroneckerOneStarAlgHom hA
        (hA.map _)).symm
  -- Off the self-adjoint matrices both sides are zero; for empty `n` there is only one matrix.
  rcases isEmpty_or_nonempty n with hn | ⟨⟨k⟩⟩
  · exact Subsingleton.elim _ _
  have hA' : ¬IsSelfAdjoint (A ⊗ₖ (1 : Matrix n n 𝕜)) := fun h ↦ hA <| by
    ext i j
    simpa [star_eq_conjTranspose, conjTranspose_kronecker] using congr_fun₂ h (i, k) (j, k)
  rw [cfc_apply_of_not_predicate A hA, cfc_apply_of_not_predicate _ hA', zero_kronecker]

/-- The functional calculus commutes with tensoring by the identity on the left. -/
@[simp]
theorem cfc_one_kronecker (f : ℝ → ℝ) (B : Matrix n n 𝕜) :
    cfc f ((1 : Matrix m m 𝕜) ⊗ₖ B) = (1 : Matrix m m 𝕜) ⊗ₖ cfc f B := by
  by_cases hB : IsSelfAdjoint B
  · simpa only [oneKroneckerStarAlgHom_apply] using
      (StarAlgHom.map_cfc (oneKroneckerStarAlgHom 𝕜 (m := m) n) f B
        (B.finite_real_spectrum.continuousOn _) continuous_oneKroneckerStarAlgHom hB
        (hB.map _)).symm
  -- Off the self-adjoint matrices both sides are zero; for empty `m` there is only one matrix.
  rcases isEmpty_or_nonempty m with hm | ⟨⟨k⟩⟩
  · exact Subsingleton.elim _ _
  have hB' : ¬IsSelfAdjoint ((1 : Matrix m m 𝕜) ⊗ₖ B) := fun h ↦ hB <| by
    ext i j
    simpa [star_eq_conjTranspose, conjTranspose_kronecker] using congr_fun₂ h (k, i) (k, j)
  rw [cfc_apply_of_not_predicate B hB, cfc_apply_of_not_predicate _ hB', kronecker_zero]

/-- The logarithm of the Kronecker product of two positive definite matrices is
`log A ⊗ₖ 1 + 1 ⊗ₖ log B`. -/
theorem PosDef.cfc_log_kronecker {A : Matrix m m 𝕜} {B : Matrix n n 𝕜} (hA : A.PosDef)
    (hB : B.PosDef) :
    cfc Real.log (A ⊗ₖ B) =
      cfc Real.log A ⊗ₖ (1 : Matrix n n 𝕜) + (1 : Matrix m m 𝕜) ⊗ₖ cfc Real.log B := by
  open scoped MatrixOrder Matrix.Norms.L2Operator in
  let : NormedAlgebra ℝ (Matrix (m × n) (m × n) 𝕜) := Matrix.l2OpNormedAlgebraReal
  have hAB : A ⊗ₖ B = (A ⊗ₖ (1 : Matrix n n 𝕜)) * ((1 : Matrix m m 𝕜) ⊗ₖ B) := by
    rw [← mul_kronecker_mul, mul_one, one_mul]
  have hcomm : Commute (A ⊗ₖ (1 : Matrix n n 𝕜)) ((1 : Matrix m m 𝕜) ⊗ₖ B) := by
    rw [Commute, SemiconjBy, ← mul_kronecker_mul, ← mul_kronecker_mul, mul_one, one_mul,
      mul_one, one_mul]
  rw [hAB, ← cfc_kronecker_one, ← cfc_one_kronecker]
  exact CFC.log_mul_of_commute hcomm (isStrictlyPositive_iff_posDef.2 (hA.kronecker .one))
    (isStrictlyPositive_iff_posDef.2 (PosDef.one.kronecker hB))

end Matrix
