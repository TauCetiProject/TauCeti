/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Contraction
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Homogeneous

/-!
# Degree-two homogeneous elements in symmetric algebras

Every `φ ⊗ ψ` in `M ⊗[R] M` represents a degree-`2` homogeneous element `ι φ * ι ψ` via
`TauCeti.SymmetricAlgebra.homogeneousSubmoduleTwoOfTensor`. For a finite projective module `V`,
`TauCeti.SymmetricAlgebra.homogeneousSubmoduleTwoOfBilin B` turns a bilinear form `B` into a
degree-`2` homogeneous element evaluating at `v` to `B v v`.

## Main definitions

* `TauCeti.SymmetricAlgebra.homogeneousSubmoduleTwoOfTensor`: maps `m₁ ⊗ₜ m₂` to `ι m₁ * ι m₂` in
  `homogeneousSubmodule R M 2`.
* `TauCeti.SymmetricAlgebra.homogeneousSubmoduleTwoOfBilin`: degree-`2` homogeneous element in
  `SymmetricAlgebra R (Module.Dual R V)` attached to a bilinear form on `V`.

## Main results

* `TauCeti.SymmetricAlgebra.coe_homogeneousSubmoduleTwoOfTensor_tmul`: pure-tensor product rule.
* `TauCeti.SymmetricAlgebra.lift_eval_homogeneousSubmoduleTwoOfTensor`: evaluation agrees with
  `dualDistrib`.
* `TauCeti.SymmetricAlgebra.lift_eval_homogeneousSubmoduleTwoOfBilin`: evaluating
  `homogeneousSubmoduleTwoOfBilin B` at `v` yields `B v v`.
-/

public section

open scoped TensorProduct

namespace TauCeti.SymmetricAlgebra

variable (R : Type*) (M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The linear map sending `m₁ ⊗ₜ m₂ : M ⊗[R] M` to the degree-`2` homogeneous product
`ι m₁ * ι m₂` in `SymmetricAlgebra R M`. -/
noncomputable def homogeneousSubmoduleTwoOfTensor :
    M ⊗[R] M →ₗ[R] homogeneousSubmodule R M 2 :=
  homogeneousSubmoduleMul R M 1 1 ∘ₗ
    TensorProduct.map
      (homogeneousSubmoduleOneEquiv R M).symm.toLinearMap
      (homogeneousSubmoduleOneEquiv R M).symm.toLinearMap

variable {R M}

/-- On a pure tensor `m₁ ⊗ₜ m₂`, `homogeneousSubmoduleTwoOfTensor` evaluates to
`ι m₁ * ι m₂`. -/
@[simp]
theorem coe_homogeneousSubmoduleTwoOfTensor_tmul (m₁ m₂ : M) :
    (homogeneousSubmoduleTwoOfTensor R M (m₁ ⊗ₜ[R] m₂) : _root_.SymmetricAlgebra R M) =
      _root_.SymmetricAlgebra.ι R M m₁ * _root_.SymmetricAlgebra.ι R M m₂ := by
  simpa [homogeneousSubmoduleTwoOfTensor] using
    coe_homogeneousSubmoduleMul_tmul R M
      ((homogeneousSubmoduleOneEquiv R M).symm m₁)
      ((homogeneousSubmoduleOneEquiv R M).symm m₂)

/-- Evaluating the image of `z : Dual R V ⊗[R] Dual R V` under `homogeneousSubmoduleTwoOfTensor`
at `v : V` agrees with `TensorProduct.dualDistrib R V V z (v ⊗ₜ[R] v)`. -/
@[simp]
theorem lift_eval_homogeneousSubmoduleTwoOfTensor {V : Type*} [AddCommMonoid V] [Module R V]
    (v : V) (z : Module.Dual R V ⊗[R] Module.Dual R V) :
    _root_.SymmetricAlgebra.lift (Module.Dual.eval R V v)
        (homogeneousSubmoduleTwoOfTensor R (Module.Dual R V) z : _) =
      TensorProduct.dualDistrib R V V z (v ⊗ₜ[R] v) := by
  induction z using TensorProduct.inductionOn with
  | tmul φ ψ => simp
  | add x y hx hy => simp [hx, hy]

/-- The `R`-linear map sending a bilinear form `B` on a finite projective module `V` to the
degree-`2` homogeneous element of `SymmetricAlgebra R (Module.Dual R V)` representing
`v ↦ B v v`. -/
noncomputable def homogeneousSubmoduleTwoOfBilin {V : Type*} [AddCommMonoid V] [Module R V]
    [Module.Finite R V] [Module.Projective R V] :
    (V →ₗ[R] V →ₗ[R] R) →ₗ[R] homogeneousSubmodule R (Module.Dual R V) 2 :=
  homogeneousSubmoduleTwoOfTensor R (Module.Dual R V) ∘ₗ
    (TensorProduct.dualDistribEquiv R V V).symm.toLinearMap ∘ₗ
      (TensorProduct.lift.equiv (RingHom.id R) V V R).toLinearMap

/-- Evaluating `homogeneousSubmoduleTwoOfBilin B` at `v` returns the diagonal value `B v v`. -/
@[simp]
theorem lift_eval_homogeneousSubmoduleTwoOfBilin {V : Type*} [AddCommMonoid V] [Module R V]
    [Module.Finite R V] [Module.Projective R V] (B : V →ₗ[R] V →ₗ[R] R) (v : V) :
    _root_.SymmetricAlgebra.lift (Module.Dual.eval R V v)
        (homogeneousSubmoduleTwoOfBilin B : _) = B v v := by
  simp only [homogeneousSubmoduleTwoOfBilin, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, lift_eval_homogeneousSubmoduleTwoOfTensor,
    ← TensorProduct.toLinearMap_dualDistribEquiv, LinearEquiv.apply_symm_apply,
    TensorProduct.lift.equiv_apply]

end TauCeti.SymmetricAlgebra
