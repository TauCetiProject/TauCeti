/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.Coalgebra.TensorProduct
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Base change of coalgebras

This file records formulas for the coalgebra structure on a scalar extension `A ⊗[R] H`.
Cocommutativity can be checked after faithfully flat extension of scalars, without requiring
an algebra structure on the coalgebra.

## Main declarations

* `TauCeti.Coalgebra.baseChange_comul_tmul`: the comultiplication of a scalar extension on
  pure tensors.
* `TauCeti.Coalgebra.baseChange_comul`: the comultiplication of a scalar extension is the scalar
  extension of the comultiplication, followed by `distribBaseChange`.
* `TauCeti.Coalgebra.IsCocomm.of_baseChange`: cocommutativity descends along a faithfully flat
  commutative algebra.
-/

public section

open scoped TensorProduct

namespace TauCeti.Coalgebra

universe u v w

variable {R : Type u} (A : Type v) {H : Type w}
variable [CommSemiring R] [CommSemiring A] [Algebra R A]
variable [AddCommMonoid H] [Module R H] [CoalgebraStruct R H]

/-- The comultiplication of a base-changed coalgebra on a pure tensor. -/
theorem baseChange_comul_tmul (a : A) (h : H) :
    Coalgebra.comul (R := A) (A := A ⊗[R] H) (a ⊗ₜ[R] h) =
      TensorProduct.AlgebraTensorModule.distribBaseChange R A H H
        (a ⊗ₜ[R] Coalgebra.comul (R := R) (A := H) h) := by
  rw [TensorProduct.comul_tmul, CommSemiring.comul_apply]
  induction Coalgebra.comul (R := R) (A := H) h using TensorProduct.inductionOn with
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | tmul g k =>
      simp only [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
        TensorProduct.AlgebraTensorModule.distribBaseChange_tmul]
      rw [TensorProduct.tmul_eq_smul_one_tmul a g,
        TensorProduct.tmul_eq_smul_one_tmul a k, TensorProduct.tmul_smul]
      exact TensorProduct.smul_tmul' a (1 ⊗ₜ[R] g) (1 ⊗ₜ[R] k)

/-- The comultiplication of a base-changed coalgebra is the base change of the comultiplication,
followed by `distribBaseChange`. -/
theorem baseChange_comul :
    Coalgebra.comul (R := A) (A := A ⊗[R] H) =
      (TensorProduct.AlgebraTensorModule.distribBaseChange R A H H).toLinearMap ∘ₗ
        (Coalgebra.comul (R := R) (A := H)).baseChange A := by
  ext h
  simp only [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    LinearMap.coe_restrictScalars, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearMap.baseChange_tmul]
  exact baseChange_comul_tmul A 1 h

end TauCeti.Coalgebra

namespace TauCeti.Coalgebra.IsCocomm

universe u v w

variable {k : Type u} {K : Type v} {H : Type w} [CommRing k] [CommRing K] [Algebra k K]
  [Module.FaithfullyFlat k K] [AddCommGroup H] [Module k H] [_root_.Coalgebra k H]

/-- Cocommutativity descends along a faithfully flat commutative algebra. -/
theorem of_baseChange [h : _root_.Coalgebra.IsCocomm K (K ⊗[k] H)] :
    _root_.Coalgebra.IsCocomm k H := by
  constructor
  ext x
  apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := k) (B := K) (H ⊗[k] H)
  let e := TensorProduct.AlgebraTensorModule.distribBaseChange k K H H
  apply e.injective
  have he_comul :
      e (1 ⊗ₜ[k] Coalgebra.comul (R := k) x) =
        Coalgebra.comul (R := K) (1 ⊗ₜ[k] x) :=
    (TauCeti.Coalgebra.baseChange_comul_tmul K 1 x).symm
  have he_comm :
      e (1 ⊗ₜ[k] TensorProduct.comm k H H (Coalgebra.comul (R := k) x)) =
        TensorProduct.comm K (K ⊗[k] H) (K ⊗[k] H)
          (e (1 ⊗ₜ[k] Coalgebra.comul (R := k) x)) := by
    induction Coalgebra.comul (R := k) x using TensorProduct.inductionOn with
    | add a b ha hb => simp only [map_add, TensorProduct.tmul_add, ha, hb]
    | tmul a b => simp [e]
  simpa only [TensorProduct.mk_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, he_comul,
    Coalgebra.comm_comul]
    using he_comm

end TauCeti.Coalgebra.IsCocomm
