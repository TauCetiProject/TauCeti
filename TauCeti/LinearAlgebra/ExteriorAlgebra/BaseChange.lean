/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.ExteriorAlgebra.BaseChange

/-!
# Scalar extension of exterior algebras

Mathlib's `ExteriorAlgebra.baseChangeEquiv` identifies `A ⊗[R] ⋀ M` with `⋀ (A ⊗[R] M)` over
arbitrary commutative rings, including in characteristic two, and records its values on
`a ⊗ ι m` and on `ι (a ⊗ m)`. This file extends that API on the inverse comparison (its value on
an arbitrary generator, on wedges of pure tensors, and its naturality in the module) and on the
forward comparison (its action on scalars, products of `1 ⊗ x`, and scalar-extended exterior
contractions `CliffordAlgebra.contractLeft`). No flatness or freeness assumption is needed.
-/

public section

open scoped TensorProduct

namespace ExteriorAlgebra

variable {R : Type*} {M : Type*}
variable [CommRing R] [AddCommGroup M] [Module R M]

section

variable (A : Type*) [CommRing A] [Algebra R A]

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

/-- The base-change comparison is multiplicative on elements of the form `1 ⊗ x`. -/
@[simp]
theorem baseChangeEquiv_one_tmul_mul (x y : ExteriorAlgebra R M) :
    baseChangeEquiv R M A (1 ⊗ₜ[R] (x * y)) =
      baseChangeEquiv R M A (1 ⊗ₜ[R] x) * baseChangeEquiv R M A (1 ⊗ₜ[R] y) := by
  rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

end

variable {A : Type*} [CommRing A] [Algebra R A]

/-- The base-change comparison sends `a ⊗ algebraMap R _ r` to the scalar `a * algebraMap R A r`. -/
@[simp]
theorem baseChangeEquiv_tmul_algebraMap (a : A) (r : R) :
    baseChangeEquiv R M A (a ⊗ₜ[R] algebraMap R (ExteriorAlgebra R M) r) =
      algebraMap A (ExteriorAlgebra A (A ⊗[R] M)) (a * algebraMap R A r) := by
  conv_lhs =>
    rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_comm,
      ← mul_one (a * algebraMap R A r), ← smul_eq_mul, ← TensorProduct.smul_tmul',
      ← Algebra.TensorProduct.one_def, map_smul, map_one, ← Algebra.algebraMap_eq_smul_one]

/-- `ExteriorAlgebra.baseChangeEquiv` intertwines the scalar extension of left exterior contraction
by `d` with left exterior contraction by a compatible `A`-linear functional `d'`. -/
theorem baseChangeEquiv_baseChange_contractLeft {d : Module.Dual R M}
    {d' : Module.Dual A (A ⊗[R] M)} (hd : ∀ u, d' (1 ⊗ₜ[R] u) = algebraMap R A (d u))
    (x : A ⊗[R] ExteriorAlgebra R M) :
    baseChangeEquiv R M A
        ((CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) d).baseChange A x) =
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm A (A ⊗[R] M))) d'
        (baseChangeEquiv R M A x) := by
  have h1 (s : ExteriorAlgebra R M) :
      baseChangeEquiv R M A
          (1 ⊗ₜ[R] CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) d s) =
        CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm A (A ⊗[R] M))) d'
          (baseChangeEquiv R M A (1 ⊗ₜ[R] s)) := by
    have hιR (v : M) : CliffordAlgebra.ι (0 : QuadraticForm R M) v = ι R v := rfl
    have hιA (v : A ⊗[R] M) :
        CliffordAlgebra.ι (0 : QuadraticForm A (A ⊗[R] M)) v = ι A v := rfl
    induction s using CliffordAlgebra.left_induction with
    | algebraMap r =>
      rw [CliffordAlgebra.contractLeft_algebraMap, TensorProduct.tmul_zero, map_zero,
        baseChangeEquiv_tmul_algebraMap, CliffordAlgebra.contractLeft_algebraMap]
    | add s₁ s₂ hs₁ hs₂ =>
      simp only [map_add, TensorProduct.tmul_add, hs₁, hs₂]
    | ι_mul s u hs =>
      rw [CliffordAlgebra.contractLeft_ι_mul, TensorProduct.tmul_sub, TensorProduct.tmul_smul,
        map_sub, ← algebraMap_smul A, map_smul, hιR u, baseChangeEquiv_one_tmul_mul,
        baseChangeEquiv_one_tmul_mul, baseChangeEquiv_apply, ← hιA (1 ⊗ₜ[R] u),
        CliffordAlgebra.contractLeft_ι_mul, hs, hd u]
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a s =>
    rw [← mul_one a, ← smul_eq_mul, ← TensorProduct.smul_tmul', map_smul, map_smul, map_smul,
      map_smul, LinearMap.baseChange_tmul, h1]

end ExteriorAlgebra
