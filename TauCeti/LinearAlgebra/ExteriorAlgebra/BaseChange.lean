/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.ExteriorAlgebra.BaseChange
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Scalar extension of exterior algebras

Mathlib's `ExteriorAlgebra.baseChangeEquiv` identifies `A ⊗[R] ⋀ M` with `⋀ (A ⊗[R] M)` over
arbitrary commutative rings, including in characteristic two, and records its values on
`a ⊗ ι m` and on `ι (a ⊗ m)`. This file extends that API: on the inverse comparison, its value on
an arbitrary generator, on wedges of pure tensors, and its naturality in the module; and on the
forward comparison, its value on pure scalar multiples of wedge-basis elements and its
compatibility with `CliffordAlgebra.contractLeft`. No flatness or freeness assumption is needed.
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

/-- `ExteriorAlgebra.baseChangeEquiv` carries a scalar multiple of the `S`-th wedge-basis vector of
`b` to the same scalar multiple of the `S`-th wedge-basis vector of `b.baseChange A`. -/
@[simp]
theorem baseChangeEquiv_tmul_basis {I : Type*} [LinearOrder I] (b : Module.Basis I R M)
    (a : A) (S : Finset I) :
    baseChangeEquiv R M A (a ⊗ₜ[R] b.ExteriorAlgebra S) =
      a • (b.baseChange A).ExteriorAlgebra S := by
  have h1 : baseChangeEquiv R M A (1 ⊗ₜ[R] b.ExteriorAlgebra S) =
      (b.baseChange A).ExteriorAlgebra S := by
    apply (baseChangeEquiv R M A).symm.injective
    rw [AlgEquiv.symm_apply_apply, basis_apply_ofCard (b.baseChange A) (rfl : S.card = S.card),
      basis_apply_ofCard b (rfl : S.card = S.card)]
    simp only [ιMulti_family, Function.comp_def, Module.Basis.baseChange_apply,
      baseChangeEquiv_symm_ιMulti_tmul, Finset.prod_const_one]
  have ha : a ⊗ₜ[R] b.ExteriorAlgebra S = a • (1 ⊗ₜ[R] b.ExteriorAlgebra S) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [ha, map_smul, h1]

/-- If `d' : Module.Dual A (A ⊗[R] M)` extends `d : Module.Dual R M` on `1 ⊗ₜ m`, then
`ExteriorAlgebra.baseChangeEquiv` intertwines the base-changed contraction by `d` with contraction
by `d'`. -/
theorem contractLeft_baseChangeEquiv {d : Module.Dual R M} {d' : Module.Dual A (A ⊗[R] M)}
    (hd : ∀ m, d' (1 ⊗ₜ[R] m) = algebraMap R A (d m)) (t : A ⊗[R] ExteriorAlgebra R M) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm A (A ⊗[R] M))) d'
        (baseChangeEquiv R M A t) =
      baseChangeEquiv R M A
        ((CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) d).baseChange A t) := by
  let φ : ExteriorAlgebra R M →ₐ[R] ExteriorAlgebra A (A ⊗[R] M) :=
    ((baseChangeEquiv R M A).toAlgHom.restrictScalars R).comp
      Algebra.TensorProduct.includeRight
  have hφ_ι (m : M) : φ (CliffordAlgebra.ι 0 m) = ι A (1 ⊗ₜ[R] m) :=
    baseChangeEquiv_apply R M A 1 m
  have h1 (y : ExteriorAlgebra R M) :
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm A (A ⊗[R] M))) d' (φ y) =
        φ (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) d y) := by
    induction y using CliffordAlgebra.left_induction with
    | algebraMap r =>
      rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R A (ExteriorAlgebra A (A ⊗[R] M)),
        CliffordAlgebra.contractLeft_algebraMap, CliffordAlgebra.contractLeft_algebraMap, map_zero]
    | add y₁ y₂ hy₁ hy₂ => simp only [map_add, hy₁, hy₂]
    | ι_mul y' m' hy' =>
      rw [map_mul, hφ_ι, CliffordAlgebra.contractLeft_ι_mul, CliffordAlgebra.contractLeft_ι_mul,
        hy', hd, IsScalarTower.algebraMap_smul, map_sub, map_smul, map_mul, hφ_ι]
  induction t using TensorProduct.inductionOn with
  | add t₁ t₂ ht₁ ht₂ => simp only [map_add, ht₁, ht₂]
  | tmul a y =>
    have hφ (z : ExteriorAlgebra R M) :
        baseChangeEquiv R M A (a ⊗ₜ[R] z) = a • φ z := by
      have ha : a ⊗ₜ[R] z = a • (1 ⊗ₜ[R] z) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [ha, map_smul]
      rfl
    rw [LinearMap.baseChange_tmul, hφ, hφ, map_smul, h1]

end ExteriorAlgebra
