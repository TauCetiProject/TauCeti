/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Contraction
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Homogeneous

/-!
# Quadratic forms in symmetric algebras

Every `φ ⊗ ψ` in `M ⊗[R] M` represents a degree-`2` homogeneous element `ι φ * ι ψ` via
`TauCeti.SymmetricAlgebra.quadFormOfTensor`. For a finite projective module `V`,
`TauCeti.SymmetricAlgebra.bilinearToQuadForm B` turns `B` into a degree-`2` homogeneous
polynomial evaluating at `v` to `B v v`.

## Main definitions

* `TauCeti.SymmetricAlgebra.quadFormOfTensor`: maps `m₁ ⊗ₜ m₂` to `ι m₁ * ι m₂`.
* `TauCeti.SymmetricAlgebra.bilinearToQuadForm`: quadratic form in
  `SymmetricAlgebra R (Module.Dual R V)` attached to a bilinear form on `V`.

## Main results

* `TauCeti.SymmetricAlgebra.coe_quadFormOfTensor_tmul`: pure-tensor product rule.
* `TauCeti.SymmetricAlgebra.lift_eval_quadFormOfTensor`: evaluation agrees with `dualDistrib`.
* `TauCeti.SymmetricAlgebra.lift_eval_bilinearToQuadForm`: evaluating `bilinearToQuadForm B` at
  `v` yields `B v v`.
-/

public section

open scoped TensorProduct

namespace TauCeti.SymmetricAlgebra

variable (R : Type*) (M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The linear map sending `m₁ ⊗ₜ m₂ : M ⊗[R] M` to the degree-`2` homogeneous product
`ι m₁ * ι m₂` in `SymmetricAlgebra R M`. -/
noncomputable def quadFormOfTensor :
    M ⊗[R] M →ₗ[R] homogeneousSubmodule R M 2 :=
  TensorProduct.lift (DirectSum.gMulLHom R fun n ↦ homogeneousSubmodule R M n) ∘ₗ
    TensorProduct.map
      (homogeneousSubmoduleOneEquiv R M).symm.toLinearMap
      (homogeneousSubmoduleOneEquiv R M).symm.toLinearMap

variable {R M}

/-- On a pure tensor `m₁ ⊗ₜ m₂`, `quadFormOfTensor` evaluates to `ι m₁ * ι m₂`. -/
@[simp]
theorem coe_quadFormOfTensor_tmul (m₁ m₂ : M) :
    (quadFormOfTensor R M (m₁ ⊗ₜ[R] m₂) : _root_.SymmetricAlgebra R M) =
      _root_.SymmetricAlgebra.ι R M m₁ * _root_.SymmetricAlgebra.ι R M m₂ := by
  simp [quadFormOfTensor, DirectSum.gMulLHom_apply_apply, SetLike.coe_gMul]

/-- Evaluating the image of `z : Dual R V ⊗[R] Dual R V` under `quadFormOfTensor` at `v : V`
agrees with `TensorProduct.dualDistrib R V V z (v ⊗ₜ[R] v)`. -/
theorem lift_eval_quadFormOfTensor {V : Type*} [AddCommMonoid V] [Module R V]
    (v : V) (z : Module.Dual R V ⊗[R] Module.Dual R V) :
    _root_.SymmetricAlgebra.lift (Module.Dual.eval R V v)
        (quadFormOfTensor R (Module.Dual R V) z : _) =
      TensorProduct.dualDistrib R V V z (v ⊗ₜ[R] v) := by
  induction z using TensorProduct.inductionOn with
  | tmul φ ψ => simp
  | add x y hx hy => simp [hx, hy]

/-- The degree-`2` homogeneous element of `SymmetricAlgebra R (Module.Dual R V)` representing
`v ↦ B v v` for a bilinear form `B` on a finite projective module `V`. -/
noncomputable def bilinearToQuadForm {V : Type*} [AddCommMonoid V] [Module R V]
    [Module.Finite R V] [Module.Projective R V] (B : V →ₗ[R] V →ₗ[R] R) :
    homogeneousSubmodule R (Module.Dual R V) 2 :=
  quadFormOfTensor R (Module.Dual R V)
    ((TensorProduct.dualDistribEquiv R V V).symm (TensorProduct.lift B))

/-- Evaluating `bilinearToQuadForm B` at `v` returns the diagonal value `B v v`. -/
@[simp]
theorem lift_eval_bilinearToQuadForm {V : Type*} [AddCommMonoid V] [Module R V]
    [Module.Finite R V] [Module.Projective R V] (B : V →ₗ[R] V →ₗ[R] R) (v : V) :
    _root_.SymmetricAlgebra.lift (Module.Dual.eval R V v) (bilinearToQuadForm B : _) = B v v := by
  rw [bilinearToQuadForm, lift_eval_quadFormOfTensor,
    ← TensorProduct.toLinearMap_dualDistribEquiv, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, TensorProduct.lift.tmul]

end TauCeti.SymmetricAlgebra
