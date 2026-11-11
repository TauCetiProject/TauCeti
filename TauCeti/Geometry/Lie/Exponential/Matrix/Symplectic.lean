/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import TauCeti.Algebra.Lie.Symplectic.Basic
public import TauCeti.Geometry.Lie.Exponential.OneParameter

/-!
# Matrix exponential lines in the symplectic group

This file identifies the matrices over `𝕜 = ℝ` or `ℂ` whose whole real exponential line lies in
the symplectic matrix group: they are exactly the elements of the symplectic Lie algebra
`LieAlgebra.Symplectic.sp l 𝕜`. It is the symplectic companion of the orthogonal characterization
in `TauCeti/Geometry/Lie/Exponential/Matrix/SpecialOrthogonal.lean`. Over `ℝ` this is the Lie
algebra of the real symplectic group `Sp(2n, ℝ)`; over `ℂ` it is the real Lie algebra underlying
`Sp(2n, ℂ)`, whose intersection with the skew-Hermitian matrices is the Lie algebra of the compact
symplectic group.

Both directions run through the conjugated form `Aᵀ = J * (-A) * J⁻¹` of skew-adjointness, since
that is the shape the exponential transports: it becomes `(exp A)ᵀ = J * (exp A)⁻¹ * J⁻¹`, which is
the symplectic condition. Conversely the symplectic condition holds along the whole line, so the
exponential lines of `Aᵀ` and of `J * (-A) * J⁻¹` coincide and their generators agree.

Because a symplectic matrix has determinant one (Mathlib's `SymplecticGroup.det_eq_one`), the
exponential of an element of `sp` lands in the special linear group as well.

## Main results

* `Matrix.exp_mem_symplecticGroup_of_mem_sp`: the exponential of an element of the symplectic Lie
  algebra is symplectic.
* `Matrix.det_exp_eq_one_of_mem_sp`: that exponential has determinant one.
* `Matrix.forall_exp_smul_mem_symplecticGroup_iff_mem_sp`: a matrix generates a one-parameter
  subgroup of the symplectic group exactly when it lies in the symplectic Lie algebra.
-/

public section

open NormedSpace
open scoped Matrix Matrix.Norms.Operator

noncomputable section

namespace Matrix

variable {l : Type*} [DecidableEq l] [Fintype l] {𝕜 : Type*} [RCLike 𝕜]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The matrix exponential of an element of the symplectic Lie algebra is symplectic. -/
theorem exp_mem_symplecticGroup_of_mem_sp (A : Matrix (l ⊕ l) (l ⊕ l) 𝕜)
    (hA : A ∈ LieAlgebra.Symplectic.sp l 𝕜) :
    exp A ∈ symplecticGroup l 𝕜 := by
  rw [SymplecticGroup.mem_iff']
  have hT : (exp A)ᵀ * J l 𝕜 = J l 𝕜 * exp (-A) := by
    rw [← eq_J_conj_iff_mul_J_eq, ← exp_transpose,
      (LieAlgebra.Symplectic.mem_sp_iff_transpose_eq_J_conj_neg A).mp hA,
      exp_conj _ _ (isUnit_J l 𝕜)]
  have hinv : exp (-A) * exp A = 1 := by
    rw [← exp_add_of_commute _ _ ((Commute.refl A).neg_left), neg_add_cancel, NormedSpace.exp_zero]
  rw [hT, mul_assoc, hinv, mul_one]

/-- The exponential of an element of the symplectic Lie algebra has determinant one. -/
theorem det_exp_eq_one_of_mem_sp (A : Matrix (l ⊕ l) (l ⊕ l) 𝕜)
    (hA : A ∈ LieAlgebra.Symplectic.sp l 𝕜) : (exp A).det = 1 :=
  SymplecticGroup.det_eq_one (exp_mem_symplecticGroup_of_mem_sp A hA)

/-- A matrix generates a one-parameter subgroup of the symplectic group exactly when it is
skew-adjoint for the canonical skew-symmetric matrix, that is, exactly when it lies in the
symplectic Lie algebra. The one-parameter subgroup is real, `t ↦ exp (t • A)` with `t : ℝ`, also
when `𝕜 = ℂ`. -/
@[simp]
theorem forall_exp_smul_mem_symplecticGroup_iff_mem_sp (A : Matrix (l ⊕ l) (l ⊕ l) 𝕜) :
    (∀ t : ℝ, exp (t • A) ∈ symplecticGroup l 𝕜) ↔ A ∈ LieAlgebra.Symplectic.sp l 𝕜 := by
  constructor
  · intro h
    rw [LieAlgebra.Symplectic.mem_sp_iff_transpose_eq_J_conj_neg]
    refine TauCeti.eq_of_forall_exp_smul_eq fun s => ?_
    calc exp (s • Aᵀ)
        = (exp (s • A))ᵀ := by rw [← Matrix.transpose_smul, exp_transpose]
      _ = J l 𝕜 * (exp (s • A))⁻¹ * (J l 𝕜)⁻¹ :=
          SymplecticGroup.transpose_eq_J_conj_inv (h s)
      _ = J l 𝕜 * exp (s • (-A)) * (J l 𝕜)⁻¹ := by rw [smul_neg, exp_neg]
      _ = exp (s • (J l 𝕜 * (-A) * (J l 𝕜)⁻¹)) := by
          rw [← exp_conj _ _ (isUnit_J l 𝕜)]
          congr 1
          simp only [smul_mul_assoc, mul_smul_comm]
  · intro hA t
    exact exp_mem_symplecticGroup_of_mem_sp (t • A)
      (((LieAlgebra.Symplectic.sp l 𝕜).toSubmodule.restrictScalars ℝ).smul_mem t hA)

end Matrix
