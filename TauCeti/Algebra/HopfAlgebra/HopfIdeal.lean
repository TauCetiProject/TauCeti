/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Ideal.Maps

/-!
# Hopf ideals

This file defines Hopf ideals in a Hopf algebra over a commutative semiring. A Hopf ideal is
an ideal `I` whose comultiplication lands in `I ⊗ H + H ⊗ I`, whose counit vanishes on `I`,
and which is stable under the antipode.

This is a small Layer 3 prerequisite for the reductive-groups roadmap target
"Hopf ideals ↔ closed subgroup schemes": closed subgroup schemes of an affine group scheme
are represented on coordinate rings by quotient Hopf algebras, and the ideal being quotiented
must satisfy exactly these Hopf-ideal closure conditions.

## Main definitions

* `TauCeti.HopfIdeal`: a Hopf ideal in a Hopf algebra over a commutative semiring.
* `TauCeti.HopfIdeal.leftTensorIdeal` and `TauCeti.HopfIdeal.rightTensorIdeal`: the two
  summands `I ⊗ H` and `H ⊗ I` inside `H ⊗ H`.
* `⊥ : HopfIdeal R H`: the zero Hopf ideal.

## References

This follows the standard Hopf-algebra definition of a Hopf ideal; see Sweedler,
*Hopf Algebras*, Chapter 1. The formalization uses Mathlib's Hopf-algebra and tensor-product
ideal API.
-/

open scoped TensorProduct

namespace TauCeti

universe u v

section TensorIdeals

variable (R : Type u) (H : Type v)
variable [CommSemiring R] [Semiring H] [Algebra R H]

namespace HopfIdeal

/-- The image of an ideal `I ≤ H` under the left inclusion `H → H ⊗[R] H`, representing
`I ⊗ H` inside the tensor product algebra. -/
def leftTensorIdeal (I : Ideal H) : Ideal (H ⊗[R] H) :=
  Ideal.map (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := H) (B := H)).toRingHom I

/-- The image of an ideal `I ≤ H` under the right inclusion `H → H ⊗[R] H`, representing
`H ⊗ I` inside the tensor product algebra. -/
def rightTensorIdeal (I : Ideal H) : Ideal (H ⊗[R] H) :=
  Ideal.map (Algebra.TensorProduct.includeRight (R := R) (A := H) (B := H)).toRingHom I

@[simp]
theorem leftTensorIdeal_def (I : Ideal H) :
    leftTensorIdeal (R := R) (H := H) I =
      Ideal.map
        (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := H) (B := H)).toRingHom
        I :=
  rfl

@[simp]
theorem rightTensorIdeal_def (I : Ideal H) :
    rightTensorIdeal (R := R) (H := H) I =
      Ideal.map
        (Algebra.TensorProduct.includeRight (R := R) (A := H) (B := H)).toRingHom I :=
  rfl

/-- The left tensor inclusion sends elements of `I` into `I ⊗ H`. -/
theorem includeLeft_mem_leftTensorIdeal {I : Ideal H} {x : H} (hx : x ∈ I) :
    Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := H) (B := H) x ∈
      leftTensorIdeal (R := R) (H := H) I :=
  Ideal.mem_map_of_mem _ hx

/-- The right tensor inclusion sends elements of `I` into `H ⊗ I`. -/
theorem includeRight_mem_rightTensorIdeal {I : Ideal H} {x : H} (hx : x ∈ I) :
    Algebra.TensorProduct.includeRight (R := R) (A := H) (B := H) x ∈
      rightTensorIdeal (R := R) (H := H) I :=
  Ideal.mem_map_of_mem _ hx

/-- A pure tensor `x ⊗ₜ y` with `x ∈ I` lies in `I ⊗ H`. -/
theorem tmul_mem_leftTensorIdeal {I : Ideal H} {x : H} (hx : x ∈ I) (y : H) :
    x ⊗ₜ[R] y ∈ leftTensorIdeal (R := R) (H := H) I := by
  have h : x ⊗ₜ[R] y =
      Algebra.TensorProduct.includeRight (R := R) (A := H) (B := H) y *
        Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := H) (B := H) x := by
    rw [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [h]
  exact Ideal.mul_mem_left _ _ (includeLeft_mem_leftTensorIdeal (R := R) (H := H) hx)

/-- A pure tensor `x ⊗ₜ y` with `y ∈ I` lies in `H ⊗ I`. -/
theorem tmul_mem_rightTensorIdeal {I : Ideal H} (x : H) {y : H} (hy : y ∈ I) :
    x ⊗ₜ[R] y ∈ rightTensorIdeal (R := R) (H := H) I := by
  have h : x ⊗ₜ[R] y =
      Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := H) (B := H) x *
        Algebra.TensorProduct.includeRight (R := R) (A := H) (B := H) y := by
    rw [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [h]
  exact Ideal.mul_mem_left _ _ (includeRight_mem_rightTensorIdeal (R := R) (H := H) hy)

theorem mem_leftTensorIdeal {I : Ideal H} {x : H ⊗[R] H} :
    x ∈ leftTensorIdeal (R := R) (H := H) I ↔
      x ∈ Ideal.map
        (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := H) (B := H)).toRingHom
        I :=
  Iff.rfl

theorem mem_rightTensorIdeal {I : Ideal H} {x : H ⊗[R] H} :
    x ∈ rightTensorIdeal (R := R) (H := H) I ↔
      x ∈ Ideal.map
        (Algebra.TensorProduct.includeRight (R := R) (A := H) (B := H)).toRingHom I :=
  Iff.rfl

theorem leftTensorIdeal_le_iff {I : Ideal H} {J : Ideal (H ⊗[R] H)} :
    leftTensorIdeal (R := R) (H := H) I ≤ J ↔
      I ≤ Ideal.comap
        (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := H) (B := H)).toRingHom
        J := by
  exact Ideal.map_le_iff_le_comap

theorem rightTensorIdeal_le_iff {I : Ideal H} {J : Ideal (H ⊗[R] H)} :
    rightTensorIdeal (R := R) (H := H) I ≤ J ↔
      I ≤ Ideal.comap
        (Algebra.TensorProduct.includeRight (R := R) (A := H) (B := H)).toRingHom J := by
  exact Ideal.map_le_iff_le_comap

theorem le_leftTensorIdeal_iff {I : Ideal H} {J : Ideal (H ⊗[R] H)} :
    J ≤ leftTensorIdeal (R := R) (H := H) I ↔
      J ≤ Ideal.map
        (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := H) (B := H)).toRingHom
        I :=
  Iff.rfl

theorem le_rightTensorIdeal_iff {I : Ideal H} {J : Ideal (H ⊗[R] H)} :
    J ≤ rightTensorIdeal (R := R) (H := H) I ↔
      J ≤ Ideal.map
        (Algebra.TensorProduct.includeRight (R := R) (A := H) (B := H)).toRingHom I :=
  Iff.rfl

end HopfIdeal

end TensorIdeals

variable (R : Type u) (H : Type v)
variable [CommSemiring R] [Semiring H] [HopfAlgebra R H]

/-- A Hopf ideal in a Hopf algebra over a commutative semiring.

The comultiplication condition is stated in the ambient tensor product algebra as
`Δ(I) ⊆ I ⊗ H + H ⊗ I`. The quotient Hopf algebra will be added separately once the needed
quotient coalgebra API is available. -/
structure HopfIdeal where
  /-- The underlying ideal. -/
  carrier : Ideal H
  /-- The underlying ideal is two-sided. -/
  isTwoSided' : carrier.IsTwoSided
  /-- The comultiplication of an element of the ideal lies in `I ⊗ H + H ⊗ I`. -/
  comul_mem' :
    ∀ ⦃x : H⦄, x ∈ carrier →
      Coalgebra.comul (R := R) x ∈
        HopfIdeal.leftTensorIdeal (R := R) (H := H) carrier ⊔
          HopfIdeal.rightTensorIdeal (R := R) (H := H) carrier
  /-- The counit vanishes on the ideal. -/
  counit_eq_zero' : ∀ ⦃x : H⦄, x ∈ carrier → Coalgebra.counit (R := R) x = 0
  /-- The antipode preserves the ideal. -/
  antipode_mem' :
    ∀ ⦃x : H⦄, x ∈ carrier → HopfAlgebra.antipode R x ∈ carrier

namespace HopfIdeal

variable {R H}

instance : SetLike (HopfIdeal R H) H where
  coe I := I.carrier
  coe_injective' I J h := by
    cases I with
    | mk carrier htwo hcomul hcounit hantipode =>
    cases J with
    | mk carrier' htwo' hcomul' hcounit' hantipode' =>
    congr
    exact SetLike.ext' h

instance : AddSubmonoidClass (HopfIdeal R H) H where
  add_mem {I} := I.carrier.add_mem
  zero_mem I := I.carrier.zero_mem

instance : SMulMemClass (HopfIdeal R H) H H where
  smul_mem {I} h {_} hx := I.carrier.mul_mem_left h hx

instance : PartialOrder (HopfIdeal R H) :=
  .ofSetLike (HopfIdeal R H) H

/-- The underlying ideal of a Hopf ideal. -/
def toIdeal (I : HopfIdeal R H) : Ideal H :=
  I.carrier

instance (I : HopfIdeal R H) : I.toIdeal.IsTwoSided :=
  I.isTwoSided'

@[simp]
theorem mem_carrier {I : HopfIdeal R H} {x : H} : x ∈ I.carrier ↔ x ∈ I :=
  Iff.rfl

@[simp]
theorem mem_toIdeal {I : HopfIdeal R H} {x : H} : x ∈ I.toIdeal ↔ x ∈ I :=
  Iff.rfl

@[simp]
theorem toIdeal_carrier (I : HopfIdeal R H) : I.toIdeal = I.carrier :=
  rfl

theorem le_def {I J : HopfIdeal R H} : I ≤ J ↔ ∀ ⦃x : H⦄, x ∈ I → x ∈ J :=
  Iff.rfl

theorem toIdeal_le_toIdeal {I J : HopfIdeal R H} :
    I.toIdeal ≤ J.toIdeal ↔ I ≤ J :=
  Iff.rfl

/-- Two Hopf ideals are equal when they contain the same elements. -/
@[ext]
theorem ext {I J : HopfIdeal R H} (h : ∀ x : H, x ∈ I ↔ x ∈ J) : I = J :=
  SetLike.ext h

/-- Constructor from an ideal and the three Hopf-ideal closure conditions. -/
def ofIdeal (I : Ideal H) [I.IsTwoSided]
    (hcomul :
      ∀ ⦃x : H⦄, x ∈ I →
        Coalgebra.comul (R := R) x ∈
          leftTensorIdeal (R := R) (H := H) I ⊔ rightTensorIdeal (R := R) (H := H) I)
    (hcounit : ∀ ⦃x : H⦄, x ∈ I → Coalgebra.counit (R := R) x = 0)
    (hantipode : ∀ ⦃x : H⦄, x ∈ I → HopfAlgebra.antipode R x ∈ I) :
    HopfIdeal R H where
  carrier := I
  isTwoSided' := inferInstance
  comul_mem' := hcomul
  counit_eq_zero' := hcounit
  antipode_mem' := hantipode

@[simp]
theorem ofIdeal_carrier (I : Ideal H) [I.IsTwoSided] (hcomul hcounit hantipode) :
    (ofIdeal (R := R) (H := H) I hcomul hcounit hantipode).carrier = I :=
  rfl

@[simp]
theorem mem_ofIdeal {I : Ideal H} [I.IsTwoSided] {hcomul hcounit hantipode} {x : H} :
    x ∈ ofIdeal (R := R) (H := H) I hcomul hcounit hantipode ↔ x ∈ I :=
  Iff.rfl

/-- The comultiplication of an element of a Hopf ideal lies in `I ⊗ H + H ⊗ I`. -/
theorem comul_mem (I : HopfIdeal R H) {x : H} (hx : x ∈ I) :
    Coalgebra.comul (R := R) x ∈
      leftTensorIdeal (R := R) (H := H) I.toIdeal ⊔
        rightTensorIdeal (R := R) (H := H) I.toIdeal :=
  I.comul_mem' hx

/-- The counit vanishes on a Hopf ideal. -/
theorem counit_eq_zero (I : HopfIdeal R H) {x : H} (hx : x ∈ I) :
    Coalgebra.counit (R := R) x = 0 :=
  I.counit_eq_zero' hx

/-- The antipode preserves a Hopf ideal. -/
theorem antipode_mem (I : HopfIdeal R H) {x : H} (hx : x ∈ I) :
    HopfAlgebra.antipode R x ∈ I :=
  I.antipode_mem' hx

/-- A Hopf ideal absorbs multiplication on the right as well as on the left. -/
theorem mul_mem_right (I : HopfIdeal R H) {x : H} (hx : x ∈ I) (y : H) :
    x * y ∈ I :=
  I.toIdeal.mul_mem_right y hx

/-- The zero ideal as a Hopf ideal. -/
instance instBot : Bot (HopfIdeal R H) where
  bot :=
    { carrier := ⊥
      isTwoSided' := inferInstance
      comul_mem' := by
        intro x hx
        rw [Ideal.mem_bot] at hx
        subst x
        simp
      counit_eq_zero' := by
        intro x hx
        rw [Ideal.mem_bot] at hx
        subst x
        simp
      antipode_mem' := by
        intro x hx
        rw [Ideal.mem_bot] at hx
        subst x
        simp }

@[simp]
theorem bot_toIdeal : (⊥ : HopfIdeal R H).toIdeal = (⊥ : Ideal H) :=
  rfl

@[simp]
theorem mem_bot {x : H} : x ∈ (⊥ : HopfIdeal R H) ↔ x = 0 :=
  Ideal.mem_bot

/-- The zero Hopf ideal is contained in every Hopf ideal. -/
instance : OrderBot (HopfIdeal R H) where
  bot := ⊥
  bot_le I x hx := by
    rw [mem_bot] at hx
    rw [hx]
    exact zero_mem I

end HopfIdeal

end TauCeti
