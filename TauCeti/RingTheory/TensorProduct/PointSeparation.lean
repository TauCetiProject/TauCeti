/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Separating tensors by algebra-valued points

Separating families of field-valued points on two algebras also separate their tensor product.
This lets one check equations on products of dense families of rational points, without any
finite-type or algebraic-closedness hypothesis.

The coefficient argument follows the proof of
`TauCeti.instIsReducedTensorProductOfIsAlgClosed` in
`TauCeti.RingTheory.FiniteType.Tensor.Product`, using Mathlib's `Module.Basis.baseChange`.
-/

public section

open scoped TensorProduct

namespace TauCeti

/-- Products of separating families of rational points separate the tensor product. -/
theorem tensorProduct_eq_zero_of_forall_productMap_eq_zero
    {k A B ι κ : Type*} [Field k] [Ring A] [Algebra k A]
    [Ring B] [Algebra k B]
    (f : ι → A →ₐ[k] k) (g : κ → B →ₐ[k] k)
    (hf : ∀ a, (∀ i, f i a = 0) → a = 0)
    (hg : ∀ b, (∀ j, g j b = 0) → b = 0)
    (x : A ⊗[k] B) (hx : ∀ i j, Algebra.TensorProduct.productMap (f i) (g j) x = 0) :
    x = 0 := by
  classical
  let b := Module.Free.chooseBasis k B
  let c := b.baseChange A
  apply c.repr.injective
  ext l
  simp only [map_zero, Finsupp.zero_apply]
  apply hf
  intro i
  let F : A ⊗[k] B →ₐ[k] B := (Algebra.TensorProduct.lid k B).toAlgHom.comp
    (Algebra.TensorProduct.map (f i) (AlgHom.id k B))
  have hF : F x = 0 := by
    apply hg
    intro j
    have hcomp : (g j).comp F = Algebra.TensorProduct.productMap (f i) (g j) := by
      ext : 1 <;> ext d <;> simp [F, AlgHom.comp_apply]
    exact (DFunLike.congr_fun hcomp x).trans (hx i j)
  have hcoord (z : A ⊗[k] B) : b.repr (F z) l = f i (c.repr z l) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z z' hz hz' => simp [hz, hz']
    | tmul a d => simp [F, c, mul_comm]
  simpa [hF] using (hcoord x).symm

end TauCeti
