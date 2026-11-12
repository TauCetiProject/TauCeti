/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.PolynomialAlgebra
import TauCeti.RingTheory.FiniteType.Tensor.Product
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# Reduced tensor products after separable field extensions

Extending the scalars of a reduced algebra by a separable algebraic field extension gives a reduced
algebra, since the finite subextensions are étale. Consequently, if `F / E` is a separable algebraic
extension of fields over `k` and `E ⊗[k] A` is reduced, then so is `F ⊗[k] A`.
In particular, every reduced algebra over a perfect field is geometrically reduced.
Localizing the first factor of a reduced tensor product keeps it reduced, so `RatFunc k ⊗[k] A` is
reduced for every reduced `k`-algebra `A`.
The tensor product of two reduced algebras over a perfect field is therefore reduced, with
no finite-generation hypothesis on either factor.
This supplies the reduced tensor square needed to form reductions of affine groups.

Over an arbitrary field `k`, an algebra `A` is geometrically reduced as soon as `L ⊗[k] A` is
reduced for one algebraically closed field `L` over `k`, since the algebraic closure of `k` embeds
in `L` and the tensor product over a field preserves injections.

## References

* The Stacks Project, [Tag 030U](https://stacks.math.columbia.edu/tag/030U),
  reduced algebras after separable field extension.

-/

public section

open scoped TensorProduct

namespace Algebra.IsGeometricallyReduced

/-- A `k`-algebra `A` is geometrically reduced as soon as `L ⊗[k] A` is reduced for one
algebraically closed field `L` over `k`. -/
theorem of_isReduced_tensorProduct {k A : Type*} [Field k] [Ring A] [Algebra k A]
    (L : Type*) [Field L] [Algebra k L] [IsAlgClosed L] [IsReduced (L ⊗[k] A)] :
    IsGeometricallyReduced k A := by
  rw [isGeometricallyReduced_field_iff]
  exact isReduced_of_injective
    (Algebra.TensorProduct.map (IsAlgClosed.lift : AlgebraicClosure k →ₐ[k] L) 1)
    (Module.Flat.rTensor_preserves_injective_linearMap _ (RingHom.injective _))

end Algebra.IsGeometricallyReduced

namespace TauCeti

/-- Extending the scalars of a reduced algebra by a separable algebraic field extension gives a
reduced algebra. Neither factor needs to be finite or finitely generated. -/
instance isReduced_tensorProduct_of_isSeparable {k : Type*} [Field k] {A L : Type*} [CommRing A]
    [Algebra k A] [IsReduced A] [Field L] [Algebra k L] [Algebra.IsSeparable k L] :
    IsReduced (A ⊗[k] L) := by
  -- Finitely generated subalgebras of `L` are finite separable field extensions, hence étale,
  -- so their scalar extensions preserve reducedness (`TauCeti.isReduced_of_smooth`).
  apply IsReduced.tensorProduct_of_flat_of_forall_fg
  intro B hB
  let : Field B := (Subalgebra.isField_of_algebraic B).toField
  have : Algebra.FiniteType k B := ⟨B.fg_top.mpr hB⟩
  have : Algebra.IsSeparable k B := Algebra.IsSeparable.of_algHom (E' := L) (f := B.val)
  have : Algebra.FormallyEtale k B := Algebra.FormallyEtale.of_isSeparable k B
  have : Algebra.Etale k B := ⟨inferInstance,
    Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  exact isReduced_of_smooth A (A ⊗[k] B)

/-- Let `F / E` be a separable algebraic extension of fields over `k`. If `E ⊗[k] A` is reduced,
then so is `F ⊗[k] A`. -/
theorem isReduced_tensorProduct_of_isReduced_of_isSeparable (k : Type*) [CommRing k] {E F : Type*}
    [Field E] [Field F] [Algebra k E] [Algebra E F] [Algebra k F] [IsScalarTower k E F]
    [Algebra.IsSeparable E F] (A : Type*) [CommRing A] [Algebra k A] [hE : IsReduced (E ⊗[k] A)] :
    IsReduced (F ⊗[k] A) := by
  -- `F ⊗[k] A = (E ⊗[k] A) ⊗[E] F`
  let e := (Algebra.TensorProduct.cancelBaseChange k E E F A).symm.trans
    (Algebra.TensorProduct.comm E F (E ⊗[k] A))
  exact isReduced_of_injective e e.injective

/-- Let `B` be a localization of the `k`-algebra `A`. If `A ⊗[k] L` is reduced, then so is
`B ⊗[k] L`. -/
theorem isReduced_tensorProduct_of_isLocalization {k : Type*} [CommRing k] {A : Type*} [CommRing A]
    [Algebra k A] (M : Submonoid A) (B : Type*) [CommRing B] [Algebra k B] [Algebra A B]
    [IsScalarTower k A B] [IsLocalization M B] (L : Type*) [CommRing L] [Algebra k L]
    [IsReduced (A ⊗[k] L)] : IsReduced (B ⊗[k] L) := by
  -- `B ⊗[k] L` is the localization of `A ⊗[k] L` at the image of `M`
  let φ : A ⊗[k] L →ₐ[k] B ⊗[k] L :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom k A B) (AlgHom.id k L)
  algebraize [φ.toRingHom]
  have : IsScalarTower A (A ⊗[k] L) (B ⊗[k] L) := .of_algebraMap_eq fun a ↦ by
    simp [RingHom.algebraMap_toAlgebra, φ]
  have := IsLocalization.tensorProduct_tensorProduct k L M B
    (by ext; simp [RingHom.algebraMap_toAlgebra, φ])
  -- `isReduced_localizationPreserves` needs both rings in one universe, so pass through the
  -- `Localization` instance instead
  let e := IsLocalization.algEquiv (Algebra.algebraMapSubmonoid (A ⊗[k] L) M) (B ⊗[k] L)
    (Localization (Algebra.algebraMapSubmonoid (A ⊗[k] L) M))
  exact isReduced_of_injective e e.injective

/-- The tensor product of a reduced algebra over a domain `k` with the rational function field
`RatFunc k` is reduced. -/
instance isReduced_ratFunc_tensorProduct {k : Type*} [CommRing k] [IsDomain k] {A : Type*}
    [CommRing A] [IsReduced A] [Algebra k A] : IsReduced (RatFunc k ⊗[k] A) := by
  -- `k[X] ⊗[k] A = A[X]` is reduced, and `RatFunc k` is a localization of `k[X]`
  have : IsReduced (Polynomial A) :=
    isReduced_of_injective (MvPolynomial.uniqueAlgEquiv A Unit).symm
      (MvPolynomial.uniqueAlgEquiv A Unit).symm.injective
  have : IsReduced (Polynomial k ⊗[k] A) :=
    let e := (Algebra.TensorProduct.comm k _ A).trans (polyEquivTensor k A).symm
    isReduced_of_injective e e.injective
  exact isReduced_tensorProduct_of_isLocalization (nonZeroDivisors (Polynomial k)) _ A

variable (k : Type*) [Field k] [PerfectField k]

/-- A reduced algebra over a perfect field is geometrically reduced, without a
finite-generation hypothesis. -/
instance instIsGeometricallyReducedOfPerfectField
    (A : Type*) [CommRing A] [Algebra k A] [IsReduced A] :
    Algebra.IsGeometricallyReduced k A := by
  rw [Algebra.isGeometricallyReduced_field_iff]
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
