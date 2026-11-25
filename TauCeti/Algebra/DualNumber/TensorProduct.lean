/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Base change of the dual numbers

For an `R`-algebra `A` that is also, compatibly, an algebra over a commutative `R`-algebra `S`,
the dual numbers commute with base change: `A ⊗[R] R[ε] ≃ₐ[S] A[ε]`, sending `a ⊗ (r + t ε)` to
`a • (r + t ε)` with `r` and `t` mapped into `A`. The algebra `A` need not be commutative; taking
`A = S` gives the `S`-algebra isomorphism `S ⊗[R] R[ε] ≃ₐ[S] S[ε]`.

The statement and naming are modelled on Mathlib's `MvPolynomial.algebraTensorAlgEquiv`
(in `Mathlib/RingTheory/TensorProduct/MvPolynomial.lean`); as in Mathlib's `polyEquivTensor`
(in `Mathlib/RingTheory/PolynomialAlgebra.lean`), the coefficient algebra may be noncommutative.
The construction here assembles the two directions from `Algebra.TensorProduct.lift` and
`DualNumber.lift`.
-/

public section

open TensorProduct DualNumber TrivSqZeroExt

namespace TauCeti

variable (R S A : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S]
  [Semiring A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]

/-- The base change `A ⊗[R] R[ε] ≃ₐ[S] A[ε]` of the dual numbers. -/
noncomputable def dualNumberAlgebraTensorAlgEquiv : A ⊗[R] R[ε] ≃ₐ[S] A[ε] :=
  AlgEquiv.ofAlgHom
    (Algebra.TensorProduct.lift (inlAlgHom S A A)
      (lift ⟨(Algebra.ofId R A[ε], ε), eps_mul_eps, fun _ => commute_eps_left _⟩)
      fun _ _ => by
        -- the image `r + t ε` of `R[ε]` is central, as scalars from `R` and `ε` both are
        simp only [lift_apply_apply, Algebra.ofId_apply]
        exact (Algebra.commute_algebraMap_right _ _).add_right <|
          (Algebra.commute_algebraMap_right _ _).mul_right (commute_eps_right _))
    (DualNumber.lift ⟨(Algebra.TensorProduct.includeLeft (S := S), 1 ⊗ₜ ε), by simp,
      fun _ => by simp [commute_iff_eq]⟩)
    (by ext <;> simp)
    (by ext <;> simp)

variable {R S A}

/-- The scalar part of the base change of `a ⊗ x`. -/
@[simp]
theorem dualNumberAlgebraTensorAlgEquiv_tmul_fst (a : A) (x : R[ε]) :
    (dualNumberAlgebraTensorAlgEquiv R S A (a ⊗ₜ x)).fst = a * algebraMap R A x.fst := by
  simp [dualNumberAlgebraTensorAlgEquiv, lift_apply_apply, algebraMap_eq_inl']

/-- The infinitesimal part of the base change of `a ⊗ x`. -/
@[simp]
theorem dualNumberAlgebraTensorAlgEquiv_tmul_snd (a : A) (x : R[ε]) :
    (dualNumberAlgebraTensorAlgEquiv R S A (a ⊗ₜ x)).snd = a * algebraMap R A x.snd := by
  simp [dualNumberAlgebraTensorAlgEquiv, lift_apply_apply, algebraMap_eq_inl']

/-- Base change sends `a ⊗ 1` to the constant `a`. -/
@[simp]
theorem dualNumberAlgebraTensorAlgEquiv_tmul_one (a : A) :
    dualNumberAlgebraTensorAlgEquiv R S A (a ⊗ₜ 1) = inl a := by
  simp [dualNumberAlgebraTensorAlgEquiv]

/-- Base change sends `a ⊗ ε` to `a • ε`. -/
@[simp]
theorem dualNumberAlgebraTensorAlgEquiv_tmul_eps (a : A) :
    dualNumberAlgebraTensorAlgEquiv R S A (a ⊗ₜ ε) = a • ε := by
  simp [dualNumberAlgebraTensorAlgEquiv, ← inl_mul_eq_smul]

/-- The inverse of base change sends `ε` to `1 ⊗ ε`. -/
@[simp]
theorem dualNumberAlgebraTensorAlgEquiv_symm_eps :
    (dualNumberAlgebraTensorAlgEquiv R S A).symm ε = 1 ⊗ₜ ε := by
  simp [dualNumberAlgebraTensorAlgEquiv, lift_apply_apply]

end TauCeti
