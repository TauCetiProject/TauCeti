/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Torsion in tensor products

An annihilator of either factor annihilates its tensor product with an arbitrary module.
Similarly, the tensor product of a torsion abelian group with any abelian group is torsion.
No flatness or finite generation is required. These facts supply the tensor closure properties
used in Hurewicz theorems modulo a class of abelian groups.

## References

* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953).
-/

public section

open scoped TensorProduct

namespace TauCeti

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module R N]

/-- An annihilator for a commuting scalar action on the left factor annihilates the tensor
product. This includes integer annihilators of modules over any commutative ring. -/
theorem isTorsionBy_tensorProduct_left {S : Type*} [Semiring S] [Module S M]
    [SMulCommClass R S M] {r : S} (h : Module.IsTorsionBy S M r) :
    Module.IsTorsionBy S (M ⊗[R] N) r := by
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul x y => rw [TensorProduct.smul_tmul', h (x := x), TensorProduct.zero_tmul]
  | add x y hx hy => simp [smul_add, hx, hy]

/-- An annihilator of the right factor annihilates the tensor product when the scalar action
can be moved between its factors. -/
theorem isTorsionBy_tensorProduct_right {S : Type*} [CommSemiring S] [Module S M]
    [Module S N] [SMulCommClass R S M] [TensorProduct.CompatibleSMul R S M N] {r : S}
    (h : Module.IsTorsionBy S N r) : Module.IsTorsionBy S (M ⊗[R] N) r := by
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul x y => rw [← TensorProduct.tmul_smul, h (x := y), TensorProduct.tmul_zero]
  | add x y hx hy => simp [smul_add, hx, hy]

/-- Tensoring a torsion abelian group on the left with any abelian group gives a torsion group. -/
theorem isAddTorsion_tensorProduct_left {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module R A] [Module R B] (h : IsAddTorsion A) : IsAddTorsion (A ⊗[R] B) := by
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul x y => exact ((TensorProduct.mk R A B).flip y).toAddMonoidHom.isOfFinAddOrder (h x)
  | add x y hx hy => exact hx.add hy

/-- Tensoring a torsion abelian group on the right with any abelian group gives a torsion group. -/
theorem isAddTorsion_tensorProduct_right {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module R A] [Module R B] (h : IsAddTorsion B) : IsAddTorsion (A ⊗[R] B) :=
  IsAddTorsion.of_surjective (TensorProduct.comm R B A).surjective
    (isAddTorsion_tensorProduct_left h)

end TauCeti
