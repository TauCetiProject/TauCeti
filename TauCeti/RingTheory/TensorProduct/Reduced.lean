/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Etale.Field
import TauCeti.RingTheory.FiniteType.Tensor.Product
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# Reduced tensor products over perfect fields

Every reduced algebra over a perfect field is geometrically reduced.
The tensor product of two reduced algebras over a perfect field is therefore reduced, with
no finite-generation hypothesis on either factor.
This supplies the reduced tensor square needed to form reductions of affine groups.

## References

* The Stacks Project, [Tag 030U](https://stacks.math.columbia.edu/tag/030U),
  reduced algebras after separable field extension.

-/

public section

open scoped TensorProduct

namespace TauCeti

variable (k : Type*) [Field k] [PerfectField k]

/-- A reduced algebra over a perfect field is geometrically reduced, without a
finite-generation hypothesis. -/
instance instIsGeometricallyReducedOfPerfectField
    (A : Type*) [CommRing A] [Algebra k A] [IsReduced A] :
    Algebra.IsGeometricallyReduced k A := by
  -- Finite subextensions of the algebraic closure are étale, so their scalar extensions
  -- preserve reducedness. Use Mathlib's `IsReduced.tensorProduct_of_flat_of_forall_fg`
  -- and `Algebra.FormallyEtale.of_isSeparable`, together with `TauCeti.isReduced_of_smooth`.
  rw [Algebra.isGeometricallyReduced_field_iff]
  have : IsReduced (A ⊗[k] AlgebraicClosure k) := by
    apply IsReduced.tensorProduct_of_flat_of_forall_fg
    intro B hB
    let : Field B := (Subalgebra.isField_of_algebraic B).toField
    have : Algebra.FiniteType k B := ⟨B.fg_top.mpr hB⟩
    have : Algebra.IsAlgebraic k B :=
      Algebra.IsAlgebraic.of_injective B.val Subtype.val_injective
    have : Algebra.FormallyEtale k B := Algebra.FormallyEtale.of_isSeparable k B
    have : Algebra.Etale k B := ⟨inferInstance,
      Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
    exact isReduced_of_smooth A (A ⊗[k] B)
  exact isReduced_of_injective (Algebra.TensorProduct.comm k (AlgebraicClosure k) A)
    (Algebra.TensorProduct.comm k (AlgebraicClosure k) A).injective

/-- The tensor product of reduced algebras over a perfect field is reduced. Neither factor
needs to be finitely generated. -/
instance instIsReducedTensorProductOfPerfectField
    (A B : Type*) [CommRing A] [Algebra k A] [IsReduced A]
    [CommRing B] [Algebra k B] [IsReduced B] : IsReduced (A ⊗[k] B) := by
  -- Extend scalars to the algebraic closure and apply the reduced tensor-product result
  -- there to finitely generated subalgebras, via `TauCeti.instIsReducedTensorProductOfIsAlgClosed`.
  apply IsReduced.tensorProduct_of_flat_of_forall_fg
  intro C hC
  have : Algebra.FiniteType k C := ⟨C.fg_top.mpr hC⟩
  have : IsReduced C := isReduced_of_injective C.val Subtype.val_injective
  let L := AlgebraicClosure k
  have : IsReduced ((L ⊗[k] C) ⊗[L] (L ⊗[k] A)) := inferInstance
  have : IsReduced ((L ⊗[k] C) ⊗[k] A) :=
    isReduced_of_injective
      (Algebra.TensorProduct.cancelBaseChange k L L (L ⊗[k] C) A).symm
      (Algebra.TensorProduct.cancelBaseChange k L L (L ⊗[k] C) A).symm.injective
  have : IsReduced (L ⊗[k] (C ⊗[k] A)) :=
    isReduced_of_injective (Algebra.TensorProduct.assoc k k L L C A).symm
      (Algebra.TensorProduct.assoc k k L L C A).symm.injective
  have : IsReduced (C ⊗[k] A) :=
    isReduced_of_injective
      (Algebra.TensorProduct.includeRight : C ⊗[k] A →ₐ[k] L ⊗[k] (C ⊗[k] A))
      (Algebra.TensorProduct.includeRight_injective (algebraMap k L).injective)
  exact isReduced_of_injective (Algebra.TensorProduct.comm k A C)
    (Algebra.TensorProduct.comm k A C).injective

end TauCeti
