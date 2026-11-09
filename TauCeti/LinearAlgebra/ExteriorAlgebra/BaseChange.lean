/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.BaseChange

/-!
# Scalar extension of exterior algebras

Mathlib's `ExteriorAlgebra.baseChangeEquiv` identifies `A ⊗[R] ⋀ M` with `⋀ (A ⊗[R] M)` over
arbitrary commutative rings, including in characteristic two, and records its values on
`a ⊗ ι m` and on `ι (a ⊗ m)`. This file extends that API on the inverse comparison: its value on
an arbitrary generator, on wedges of pure tensors, and its naturality in the module.
No flatness or freeness assumption is needed.
-/

public section

open scoped TensorProduct

namespace ExteriorAlgebra

variable {R : Type*} (A : Type*) {M : Type*}
variable [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup M] [Module R M]

/-- The inverse base-change comparison carries an exterior generator to the scalar extension of
that generator. -/
@[simp]
theorem baseChangeEquiv_symm_ι (x : A ⊗[R] M) :
    (baseChangeEquiv R M A).symm (ι A x) = (ι R).baseChange A x := by
  induction x using TensorProduct.inductionOn with
  | tmul a m => exact baseChangeEquiv_symm_apply R M A a m
  | add x y hx hy => simp only [map_add, hx, hy]

/-- On wedges of pure tensors the scalar coefficients multiply. -/
@[simp]
theorem baseChangeEquiv_symm_ιMulti_tmul {n : ℕ} (a : Fin n → A) (m : Fin n → M) :
    (baseChangeEquiv R M A).symm (ιMulti A n fun i ↦ a i ⊗ₜ[R] m i) =
      (∏ i, a i) ⊗ₜ[R] ιMulti R n m := by
  induction n with
  | zero => simp [ιMulti_zero_apply, Algebra.TensorProduct.one_def]
  | succ n ih =>
      simp only [ιMulti_succ_apply, map_mul, baseChangeEquiv_symm_ι, LinearMap.baseChange_tmul,
        Matrix.vecTail, Function.comp_def, ih, Algebra.TensorProduct.tmul_mul_tmul,
        Fin.prod_univ_succ]

/-- The inverse base-change comparison is natural in the module. -/
@[simp]
theorem baseChangeEquiv_symm_map {N : Type*} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (x : ExteriorAlgebra A (A ⊗[R] M)) :
    (baseChangeEquiv R N A).symm (map (f.baseChange A) x) =
      Algebra.TensorProduct.map (AlgHom.id A A) (map f) ((baseChangeEquiv R M A).symm x) := by
  have h : (baseChangeEquiv R N A).symm.toAlgHom.comp (map (f.baseChange A)) =
      (Algebra.TensorProduct.map (AlgHom.id A A) (map f)).comp
        (baseChangeEquiv R M A).symm.toAlgHom := by
    apply hom_ext
    apply TensorProduct.AlgebraTensorModule.ext
    intro a m
    simp
  exact AlgHom.congr_fun h x

end ExteriorAlgebra
