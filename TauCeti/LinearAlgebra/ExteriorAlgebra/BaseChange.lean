/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.LinearAlgebra.ExteriorAlgebra.BaseChange

/-!
# Scalar extension of exterior algebras

Mathlib's `ExteriorAlgebra.baseChangeEquiv` identifies `A ⊗[R] ⋀ M` with `⋀ (A ⊗[R] M)` over
arbitrary commutative rings, including in characteristic two, and records its values on
`a ⊗ ι m` and on `ι (a ⊗ m)`. This file extends that API: on the inverse comparison, its value on
an arbitrary generator, on wedges of pure tensors, and its naturality in the module; on the
forward comparison, its intertwining of scalar-extended interior contraction with contraction by
the scalar-extended functional (`ExteriorAlgebra.baseChangeEquiv_baseChange_contractLeft`).
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

/-- `ExteriorAlgebra.baseChangeEquiv` intertwines the scalar-extended interior contraction by `d`
with interior contraction by `Module.Dual.baseChange A d`. -/
@[simp]
theorem baseChangeEquiv_baseChange_contractLeft (d : Module.Dual R M)
    (x : A ⊗[R] ExteriorAlgebra R M) :
    baseChangeEquiv R M A
        ((CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) d).baseChange A x) =
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm A (A ⊗[R] M))) (d.baseChange A)
        (baseChangeEquiv R M A x) := by
  let φ : ExteriorAlgebra R M →ₐ[R] ExteriorAlgebra A (A ⊗[R] M) :=
    ((baseChangeEquiv R M A).toAlgHom.restrictScalars R).comp Algebra.TensorProduct.includeRight
  have hφ (y : ExteriorAlgebra R M) : φ y = baseChangeEquiv R M A (1 ⊗ₜ[R] y) := rfl
  let P (y : ExteriorAlgebra R M) : Prop :=
    φ (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) d y) =
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm A (A ⊗[R] M))) (d.baseChange A) (φ y)
  have h1 : P 1 := by
    simp [P]
  have hmul (a : ExteriorAlgebra R M) : ∀ u, P u → P (a * u) := by
    induction a using ExteriorAlgebra.induction with
    | algebraMap r =>
      intro u hu
      dsimp only [P]
      rw [← Algebra.smul_def, map_smul, map_smul, map_smul, hu, ← algebraMap_smul A r (φ u),
        map_smul, algebraMap_smul]
    | ι m =>
      intro u hu
      have hφm : φ (ι R m) = ι A (1 ⊗ₜ[R] m) := baseChangeEquiv_apply R M A 1 m
      dsimp only [P] at hu ⊢
      rw [CliffordAlgebra.contractLeft_ι_mul, map_sub, map_smul, map_mul, hu, map_mul, hφm,
        CliffordAlgebra.contractLeft_ι_mul, Module.Dual.baseChange_apply_tmul, smul_one_smul]
    | mul a b ha hb =>
      intro u hu
      rw [mul_assoc]
      exact ha (b * u) (hb u hu)
    | add a b ha hb =>
      intro u hu
      dsimp only [P]
      rw [add_mul, map_add, map_add, map_add, map_add, ha u hu, hb u hu]
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ hx₁ hx₂ => simp only [map_add, hx₁, hx₂]
  | tmul a y =>
    have hay (z : ExteriorAlgebra R M) : a ⊗ₜ[R] z = a • ((1 : A) ⊗ₜ[R] z) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have hy : P y := by simpa only [mul_one] using hmul y 1 h1
    rw [LinearMap.baseChange_tmul, hay, hay y, map_smul, map_smul, map_smul, ← hφ, ← hφ]
    exact congrArg (a • ·) hy

end ExteriorAlgebra
