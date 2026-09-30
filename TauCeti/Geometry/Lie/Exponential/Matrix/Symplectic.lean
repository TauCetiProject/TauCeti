/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import TauCeti.Algebra.Lie.Symplectic.Basic
public import TauCeti.Geometry.Lie.Exponential.OneParameter

/-!
# Matrix exponential lines in the symplectic group

This file identifies the real matrices whose whole exponential line lies in the symplectic matrix
group: they are exactly the elements of the symplectic Lie algebra
`LieAlgebra.Symplectic.sp l ℝ`. It is the symplectic companion of the orthogonal characterization
in `TauCeti/Geometry/Lie/Exponential/Matrix/SpecialOrthogonal.lean`.

Both directions run through the conjugated forms of
`TauCeti/Algebra/Lie/Symplectic/Basic.lean`. If `A` is skew-adjoint for the canonical
skew-symmetric matrix `J`, that is `Aᵀ = J * (-A) * J⁻¹`, then `Matrix.exp_transpose` and
`Matrix.exp_conj` give `(exp A)ᵀ = J * (exp A)⁻¹ * J⁻¹`, which is the symplectic condition. In the
other direction the hypothesis is available at every time `t`, so the two exponential lines
`t ↦ exp (t • Aᵀ)` and `t ↦ exp (t • (J * (-A) * J⁻¹))` coincide; distinct generators give
distinct one-parameter subgroups (`TauCeti.expUnitHom_injective`), so the generators agree and `A`
is skew-adjoint. No derivative is taken: the injectivity of `TauCeti.expUnitHom` replaces the
usual differentiation at `t = 0`.

Because a symplectic matrix has determinant one (Mathlib's `SymplecticGroup.det_eq_one`), the
exponential of an element of `sp` lands in the special linear group as well.

## Main results

* `Matrix.exp_mem_symplecticGroup_of_mem_sp`: the exponential of an element of the symplectic Lie
  algebra is symplectic.
* `Matrix.det_exp_eq_one_of_mem_sp`: that exponential has determinant one.
* `Matrix.forall_exp_smul_mem_symplecticGroup_iff_mem_sp`: a real matrix generates a
  one-parameter subgroup of the symplectic group exactly when it lies in the symplectic Lie
  algebra.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 2, "Consequences": the matrix groups are Lie groups, with their Lie
  algebras named explicitly.
-/

public section

open NormedSpace
open scoped Matrix Matrix.Norms.Operator

noncomputable section

namespace Matrix

variable {l : Type*} [DecidableEq l] [Fintype l]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The matrix exponential of an element of the symplectic Lie algebra is symplectic. -/
theorem exp_mem_symplecticGroup_of_mem_sp (A : Matrix (l ⊕ l) (l ⊕ l) ℝ)
    (hA : A ∈ LieAlgebra.Symplectic.sp l ℝ) :
    exp A ∈ symplecticGroup l ℝ := by
  rw [SymplecticGroup.mem_iff']
  have hT : (exp A)ᵀ = J l ℝ * exp (-A) * (J l ℝ)⁻¹ := by
    rw [← exp_transpose, (LieAlgebra.Symplectic.mem_sp_iff_transpose_eq_conj A).mp hA,
      exp_conj _ _ (isUnit_J l ℝ)]
  have hinv : exp (-A) * exp A = 1 := by
    rw [← exp_add_of_commute _ _ ((Commute.refl A).neg_left), neg_add_cancel, NormedSpace.exp_zero]
  calc (exp A)ᵀ * J l ℝ * exp A
      = J l ℝ * exp (-A) * ((-J l ℝ) * J l ℝ) * exp A := by
        rw [hT, J_inv]; noncomm_ring
    _ = J l ℝ * (exp (-A) * exp A) := by
        rw [neg_mul, J_squared, neg_neg]; noncomm_ring
    _ = J l ℝ := by rw [hinv, mul_one]

/-- The exponential of an element of the symplectic Lie algebra has determinant one. -/
theorem det_exp_eq_one_of_mem_sp (A : Matrix (l ⊕ l) (l ⊕ l) ℝ)
    (hA : A ∈ LieAlgebra.Symplectic.sp l ℝ) : (exp A).det = 1 :=
  SymplecticGroup.det_eq_one (exp_mem_symplecticGroup_of_mem_sp A hA)

/-- A real matrix generates a one-parameter subgroup of the symplectic group exactly when it is
skew-adjoint for the canonical skew-symmetric matrix, that is, exactly when it lies in the
symplectic Lie algebra. -/
@[simp]
theorem forall_exp_smul_mem_symplecticGroup_iff_mem_sp (A : Matrix (l ⊕ l) (l ⊕ l) ℝ) :
    (∀ t : ℝ, exp (t • A) ∈ symplecticGroup l ℝ) ↔ A ∈ LieAlgebra.Symplectic.sp l ℝ := by
  constructor
  · intro h
    rw [LieAlgebra.Symplectic.mem_sp_iff_transpose_eq_conj]
    apply TauCeti.expUnitHom_injective (R := Matrix (l ⊕ l) (l ⊕ l) ℝ)
    apply ContinuousMonoidHom.ext
    intro t
    apply Units.ext
    rw [← ofAdd_toAdd t]
    simp only [TauCeti.expUnitHom_apply, TauCeti.expUnit_coe]
    set s : ℝ := Multiplicative.toAdd t with hs
    calc exp (s • Aᵀ)
        = (exp (s • A))ᵀ := by rw [← Matrix.transpose_smul, exp_transpose]
      _ = J l ℝ * (exp (s • A))⁻¹ * (J l ℝ)⁻¹ :=
          SymplecticGroup.transpose_eq_J_conj_inv (h s)
      _ = J l ℝ * exp (s • (-A)) * (J l ℝ)⁻¹ := by rw [smul_neg, exp_neg]
      _ = exp (s • (J l ℝ * (-A) * (J l ℝ)⁻¹)) := by
          rw [← exp_conj _ _ (isUnit_J l ℝ)]
          congr 1
          simp only [smul_mul_assoc, mul_smul_comm]
  · intro hA t
    exact exp_mem_symplecticGroup_of_mem_sp (t • A)
      ((LieAlgebra.Symplectic.sp l ℝ).smul_mem t hA)

end Matrix
