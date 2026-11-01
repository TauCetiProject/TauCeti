/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Torsion in tensor products

An annihilator of either factor annihilates its tensor product with an arbitrary module.
Similarly, the tensor product of commutative additive monoids is torsion if either factor is
torsion.
No flatness or finite generation is required. These facts supply the tensor closure properties
used in Hurewicz theorems modulo a class of abelian groups.

If an ideal `I` kills one factor and the other factor `X` satisfies `I • X = X`, the tensor
product vanishes. This is how modules killed by an idempotent ideal `m` are seen to be killed by
`m ⊗ -` in almost mathematics.

## References

* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953).
* O. Gabber, L. Ramero, *Almost ring theory*, Lecture Notes in Math. 1800, Springer (2003),
  Remark 2.1.4(i).
-/

public section

open scoped TensorProduct Pointwise

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
theorem isTorsionBy_tensorProduct_right {S : Type*} [Semiring S] [Module S M]
    [Module S N] [SMulCommClass R S M] [TensorProduct.CompatibleSMul R S M N] {r : S}
    (h : Module.IsTorsionBy S N r) : Module.IsTorsionBy S (M ⊗[R] N) r := by
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul x y => rw [← TensorProduct.tmul_smul, h (x := y), TensorProduct.tmul_zero]
  | add x y hx hy => simp [smul_add, hx, hy]

/-- Tensoring a torsion commutative additive monoid on the left with any commutative additive
monoid gives a torsion monoid. -/
theorem isAddTorsion_tensorProduct_left {A B : Type*} [AddCommMonoid A] [AddCommMonoid B]
    [Module R A] [Module R B] (h : IsAddTorsion A) : IsAddTorsion (A ⊗[R] B) := by
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul x y => exact ((TensorProduct.mk R A B).flip y).toAddMonoidHom.isOfFinAddOrder (h x)
  | add x y hx hy => exact hx.add hy

/-- Tensoring a torsion commutative additive monoid on the right with any commutative additive
monoid gives a torsion monoid. -/
theorem isAddTorsion_tensorProduct_right {A B : Type*} [AddCommMonoid A] [AddCommMonoid B]
    [Module R A] [Module R B] (h : IsAddTorsion B) : IsAddTorsion (A ⊗[R] B) := fun t ↦ by
  obtain ⟨u, rfl⟩ := (TensorProduct.comm R B A).surjective t
  exact (TensorProduct.comm R B A).toAddMonoidHom.isOfFinAddOrder
    (isAddTorsion_tensorProduct_left h u)

/-- If `I • X = X` and `I` kills `K`, then `X ⊗ K = 0`: for `i ∈ I` one has
`(i • x) ⊗ k = x ⊗ (i • k) = 0`. -/
theorem subsingleton_tensorProduct_of_isTorsionBySet_right {I : Ideal R}
    (hM : I • (⊤ : Submodule R M) = ⊤) (hN : Module.IsTorsionBySet R N I) :
    Subsingleton (M ⊗[R] N) := by
  refine subsingleton_of_forall_eq 0 fun t ↦ ?_
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
    have hx : x ∈ I • (⊤ : Submodule R M) := by rw [hM]; exact Submodule.mem_top
    refine Submodule.smul_induction_on (p := fun x ↦ x ⊗ₜ[R] y = 0) hx (fun r hr n _ ↦ ?_)
      fun x y hx hy ↦ by rw [TensorProduct.add_tmul, hx, hy, add_zero]
    rw [TensorProduct.smul_tmul, hN (a := ⟨r, hr⟩), TensorProduct.tmul_zero]
  | add x y hx hy => rw [hx, hy, add_zero]

/-- If `I` kills `M` and `I • X = X`, then `M ⊗ X = 0`. -/
theorem subsingleton_tensorProduct_of_isTorsionBySet_left {I : Ideal R}
    (hM : Module.IsTorsionBySet R M I) (hN : I • (⊤ : Submodule R N) = ⊤) :
    Subsingleton (M ⊗[R] N) :=
  have := subsingleton_tensorProduct_of_isTorsionBySet_right hN hM
  (TensorProduct.comm R M N).toEquiv.subsingleton

end TauCeti
