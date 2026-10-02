/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Reduced tensor products over finite fields

The tensor product of two reduced algebras over a finite field is reduced, with no
finite-generation hypothesis on either factor. The cardinality-power Frobenius is linear
over the ground field. Its injectivity on the two factors therefore gives injectivity on
the tensor product. In particular every reduced algebra over a finite field is geometrically
reduced. This supplies the reduced tensor square needed to form reductions of affine groups.

## References

* The Stacks Project, [Tag 030U](https://stacks.math.columbia.edu/tag/030U),
  reduced algebras after separable field extension.

The proof uses Mathlib's `FiniteField.frobeniusAlgHom` and
`TensorProduct.map_injective_of_flat_flat`.
-/

public section

open scoped TensorProduct

namespace TauCeti

variable (k : Type*) [Field k] [Finite k]

/-- The tensor product of reduced algebras over a finite field is reduced. Neither factor
needs to be finitely generated. -/
instance instIsReducedTensorProductOfFiniteField
    (A B : Type*) [CommRing A] [Algebra k A] [IsReduced A]
    [CommRing B] [Algebra k B] [IsReduced B] : IsReduced (A ⊗[k] B) := by
  classical
  let := Fintype.ofFinite k
  let fA := (FiniteField.frobeniusAlgHom k A).toLinearMap
  let fB := (FiniteField.frobeniusAlgHom k B).toLinearMap
  have hA : Function.Injective fA := by
    apply (injective_iff_map_eq_zero _).mpr
    intro x hx
    exact IsReduced.eq_zero x ⟨Fintype.card k, hx⟩
  have hB : Function.Injective fB := by
    apply (injective_iff_map_eq_zero _).mpr
    intro x hx
    exact IsReduced.eq_zero x ⟨Fintype.card k, hx⟩
  have hinj := TensorProduct.map_injective_of_flat_flat fA fB hA hB
  have hmap (x : A ⊗[k] B) :
      TensorProduct.map fA fB x = FiniteField.frobeniusAlgHom k (A ⊗[k] B) x := by
    induction x using TensorProduct.inductionOn with
    | tmul a b => simp [fA, fB, Algebra.TensorProduct.tmul_pow]
    | add x y hx hy => simp only [map_add, hx, hy]
  apply (isReduced_iff_pow_one_lt (Fintype.card k) (Fintype.one_lt_card)).mpr
  intro x hx
  apply hinj
  simpa only [hmap, map_zero, FiniteField.coe_frobeniusAlgHom] using hx

/-- A reduced algebra over a finite field is geometrically reduced, without a
finite-generation hypothesis. -/
instance instIsGeometricallyReducedOfFiniteField
    (A : Type*) [CommRing A] [Algebra k A] [IsReduced A] :
    Algebra.IsGeometricallyReduced k A := by
  rw [Algebra.isGeometricallyReduced_field_iff]
  infer_instance

end TauCeti
