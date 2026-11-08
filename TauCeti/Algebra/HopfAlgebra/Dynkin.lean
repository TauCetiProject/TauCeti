/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.HopfAlgebra.Primitive
public import Mathlib.RingTheory.HopfAlgebra.Convolution
public import TauCeti.Algebra.Lie.Derivation.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Antipode convolution with a derivation

Convolving the antipode with an algebra derivation gives the Dynkin operator.
On primitive elements it equals the derivation. Multiplication on the right by
a primitive element gives a commutator recurrence, which expresses its values
on words as iterated brackets when the derivation preserves the generators.

The construction uses Mathlib's convolution of linear maps and Tau Ceti's
bundled derivations of noncommutative algebras.

Adapted from `Mei/RingTheory/HopfAlgebra/Dynkin.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei),
commit `97304cc1bd51a202db1a705709fb4763f61e190a` (Apache 2.0).
-/

public section

open scoped TensorProduct
open WithConv

namespace TauCeti.HopfAlgebra

variable {R A : Type*} [CommRing R] [Ring A] [_root_.HopfAlgebra R A]
  (Y : TauCeti.derivationLieAlgebra R A)

local notation "S" => _root_.HopfAlgebraStruct.antipode R (A := A)
local notation "μ" => LinearMap.mul' R A

/-- The convolution of the antipode with an algebra derivation. -/
noncomputable def dynkinOperator : A →ₗ[R] A :=
  (toConv S * toConv (Y : Module.End R A)).ofConv

/-- The convolution description of the Dynkin operator. -/
theorem dynkinOperator_def :
    dynkinOperator Y = (toConv S * toConv (Y : Module.End R A)).ofConv := (rfl)

/-- The Dynkin operator applies the antipode and derivation to the two coproduct factors. -/
theorem dynkinOperator_apply (a : A) :
    dynkinOperator Y a =
      μ (TensorProduct.map S (Y : Module.End R A) (Coalgebra.comul a)) := by
  rw [dynkinOperator_def]
  exact LinearMap.convMul_apply _ _ a

/-- The Dynkin operator kills the unit. -/
@[simp]
theorem dynkinOperator_one : dynkinOperator Y (1 : A) = 0 := by
  rw [dynkinOperator_apply]
  simp [Algebra.TensorProduct.one_def, TauCeti.derivationLieAlgebra.apply_one_eq_zero]

/-- On primitive elements the Dynkin operator equals its defining derivation. -/
@[simp]
theorem dynkinOperator_of_isPrimitiveElem {p : A} (hp : Bialgebra.IsPrimitiveElem R p) :
    dynkinOperator Y p = (Y : Module.End R A) p := by
  rw [dynkinOperator_apply, hp.comul_eq_tmul_add_tmul]
  simp [TauCeti.derivationLieAlgebra.apply_one_eq_zero]

private theorem tensor_dynkin_right_primitive {x : A} (hx : Bialgebra.IsPrimitiveElem R x)
    (t : A ⊗[R] A) :
    μ (TensorProduct.map S (Y : Module.End R A) (t * (1 ⊗ₜ[R] x + x ⊗ₜ[R] 1))) =
      μ (TensorProduct.map S (Y : Module.End R A) t) * x -
        x * μ (TensorProduct.map S (Y : Module.End R A) t) +
        μ (TensorProduct.map S (LinearMap.id : A →ₗ[R] A) t) * (Y : Module.End R A) x := by
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [mul_add, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      map_add, TensorProduct.map_tmul, LinearMap.mul'_apply,
      _root_.HopfAlgebra.antipode_mul_antidistrib, hx.antipode_eq_neg,
      TauCeti.derivationLieAlgebra.leibniz, LinearMap.id_apply]
    noncomm_ring
  | add t u ht hu =>
    simp only [add_mul, map_add, ht, hu]
    noncomm_ring

/-- Right multiplication by a primitive element gives the Dynkin commutator recurrence. -/
theorem dynkinOperator_mul_primitive (a : A) {x : A} (hx : Bialgebra.IsPrimitiveElem R x) :
    dynkinOperator Y (a * x) = dynkinOperator Y a * x - x * dynkinOperator Y a +
      Coalgebra.counit (R := R) a • (Y : Module.End R A) x := by
  rw [dynkinOperator_apply, Bialgebra.comul_mul, hx.comul_eq_tmul_add_tmul,
    tensor_dynkin_right_primitive Y hx, ← dynkinOperator_apply,
    ← LinearMap.rTensor_def, _root_.HopfAlgebra.mul_antipode_rTensor_comul_apply,
    Algebra.smul_def]

end TauCeti.HopfAlgebra
