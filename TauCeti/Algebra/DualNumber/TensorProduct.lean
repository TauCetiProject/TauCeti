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

For a commutative `R`-algebra `S`, the dual numbers commute with base change:
`S ⊗[R] R[ε] ≃ₐ[S] S[ε]`, sending `s ⊗ (a + b ε)` to `s • (a + b ε)` with `a` and `b`
mapped into `S`.

The statement and naming are modelled on Mathlib's `MvPolynomial.algebraTensorAlgEquiv`
(in `Mathlib/RingTheory/TensorProduct/MvPolynomial.lean`); the construction here instead
assembles the two directions from `Algebra.TensorProduct.lift` and `DualNumber.lift`.
-/

public section

open TensorProduct DualNumber TrivSqZeroExt

namespace TauCeti

variable (R S : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S]

/-- The base change `S ⊗[R] R[ε] ≃ₐ[S] S[ε]` of the dual numbers. -/
noncomputable def dualNumberAlgebraTensorAlgEquiv : S ⊗[R] R[ε] ≃ₐ[S] S[ε] :=
  AlgEquiv.ofAlgHom
    (Algebra.TensorProduct.lift (Algebra.ofId S S[ε])
      (lift ⟨(Algebra.ofId R S[ε], ε), eps_mul_eps, fun _ => commute_eps_left _⟩)
      fun _ _ => Commute.all _ _)
    (lift ⟨(Algebra.ofId S (S ⊗[R] R[ε]), 1 ⊗ₜ ε), by simp,
      fun _ => Commute.all (S := S ⊗[R] R[ε]) _ _⟩)
    (DualNumber.algHom_ext (by simp))
    (Algebra.TensorProduct.ext (by ext) (DualNumber.algHom_ext (by simp)))

variable {R S}

/-- The scalar part of the base change of `s ⊗ x`. -/
@[simp]
theorem dualNumberAlgebraTensorAlgEquiv_tmul_fst (s : S) (x : R[ε]) :
    (dualNumberAlgebraTensorAlgEquiv R S (s ⊗ₜ x)).fst = s * algebraMap R S x.fst := by
  simp [dualNumberAlgebraTensorAlgEquiv, lift_apply_apply, algebraMap_eq_inl']

/-- The infinitesimal part of the base change of `s ⊗ x`. -/
@[simp]
theorem dualNumberAlgebraTensorAlgEquiv_tmul_snd (s : S) (x : R[ε]) :
    (dualNumberAlgebraTensorAlgEquiv R S (s ⊗ₜ x)).snd = s * algebraMap R S x.snd := by
  simp [dualNumberAlgebraTensorAlgEquiv, lift_apply_apply, algebraMap_eq_inl']

/-- Base change sends `s ⊗ 1` to the constant `s`. -/
@[simp]
theorem dualNumberAlgebraTensorAlgEquiv_tmul_one (s : S) :
    dualNumberAlgebraTensorAlgEquiv R S (s ⊗ₜ 1) = algebraMap S S[ε] s := by
  simp [dualNumberAlgebraTensorAlgEquiv]

/-- Base change sends `s ⊗ ε` to `s • ε`. -/
@[simp]
theorem dualNumberAlgebraTensorAlgEquiv_tmul_eps (s : S) :
    dualNumberAlgebraTensorAlgEquiv R S (s ⊗ₜ ε) = s • ε := by
  simp [dualNumberAlgebraTensorAlgEquiv, ← Algebra.smul_def]

/-- The inverse of base change sends `ε` to `1 ⊗ ε`. -/
@[simp]
theorem dualNumberAlgebraTensorAlgEquiv_symm_eps :
    (dualNumberAlgebraTensorAlgEquiv R S).symm ε = 1 ⊗ₜ ε := by
  simp [dualNumberAlgebraTensorAlgEquiv, lift_apply_apply]

end TauCeti
