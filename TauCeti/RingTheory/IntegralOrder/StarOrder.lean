/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Rat
public import Mathlib.Algebra.Star.Subalgebra
public import Mathlib.Data.Matrix.Basis
public import TauCeti.RingTheory.IntegralOrder.Basic

/-!
# Star-orders

Let `B` be a `ℚ`-algebra with an involution `x ↦ star x`, for instance a finite-dimensional
semisimple `ℚ`-algebra with a positive involution as in the PEL data of Shimura varieties. A
*star-order* in `B` is a `ℤ`-order `O` in `B` (in the sense of `TauCeti.IntegralOrder.IsOrder`)
which is stable under the involution, `star O = O`. It inherits the involution, and every
statement about overorders or maximality is made about the underlying `ℤ`-subalgebra.

## Main definitions

* `TauCeti.StarOrder B`: a star-stable `ℤ`-subalgebra of `B` which is a `ℤ`-order in `B`.
* `TauCeti.StarOrder.toSubring`: the underlying subring of a star-order.
* `TauCeti.StarOrder.orderEquiv`: star-orders are the same as `ℤ`-subalgebras of `B` which are
  orders and are star-stable; both directions retain the carrier.
* `TauCeti.StarOrder.ofTrivialStar`: in an algebra with trivial involution every order is a
  star-order.
* `TauCeti.StarOrder.int`: the integer order `ℤ ⊆ ℚ` with the identity involution.
* `TauCeti.StarOrder.matrix n`: the star-order `M_n(ℤ)` of `M_n(ℚ)` with the transpose involution.

## Main results

* `TauCeti.StarOrder.toSubalgebra_le_toSubalgebra`: inclusions of star-orders are inclusions of
  the underlying subalgebras.
* `TauCeti.StarOrder.mem_int`: the integer order of `ℚ` consists of the integers.
* `TauCeti.StarOrder.single_mem_matrix`: `M_n(ℤ)` contains the standard matrix units.

## References

* K.-W. Lan, *Arithmetic compactifications of PEL-type Shimura varieties*, Definitions 1.1.1.2
  to 1.1.1.4 and §1.2.1.
* R. Kottwitz, *Points on some Shimura varieties over finite fields*, §5.
-/

public section

namespace TauCeti

open IntegralOrder

variable (B : Type*) [Ring B] [StarRing B] [Algebra ℚ B]

/-- A *star-order* in a `ℚ`-algebra `B` with involution: a `ℤ`-subalgebra of `B` which is stable
under the involution and is a `ℤ`-order in `B` (finitely generated over `ℤ` and spanning `B` over
`ℚ`). -/
structure StarOrder extends StarSubalgebra ℤ B where
  /-- The underlying `ℤ`-subalgebra is a `ℤ`-order in `B`. -/
  isOrder : IsOrder ℚ toSubalgebra

namespace StarOrder

variable {B}

instance instSetLike : SetLike (StarOrder B) B where
  coe O := O.carrier
  coe_injective O O' h := by
    obtain ⟨O, _⟩ := O
    obtain ⟨O', _⟩ := O'
    congr
    exact SetLike.coe_injective h

instance instPartialOrder : PartialOrder (StarOrder B) := .ofSetLike (StarOrder B)

instance instSubringClass : SubringClass (StarOrder B) B where
  add_mem {O} := O.add_mem'
  mul_mem {O} := O.mul_mem'
  one_mem {O} := O.one_mem'
  zero_mem {O} := O.zero_mem'
  neg_mem {O} _ hx := neg_mem (s := O.toSubalgebra) hx

instance instStarMemClass : StarMemClass (StarOrder B) B where
  star_mem {O} := O.star_mem'

variable (O O' : StarOrder B)

/-- Membership in the underlying star subalgebra is membership in the star-order. -/
@[simp]
theorem mem_toStarSubalgebra {x : B} : x ∈ O.toStarSubalgebra ↔ x ∈ O :=
  Iff.rfl

/-- Membership in the underlying subalgebra is membership in the star-order. -/
theorem mem_toSubalgebra {x : B} : x ∈ O.toSubalgebra ↔ x ∈ O :=
  Iff.rfl

/-- The carrier of the underlying star subalgebra is the carrier of the star-order. -/
@[simp]
theorem coe_toStarSubalgebra : (O.toStarSubalgebra : Set B) = O :=
  rfl

/-- The underlying subring of a star-order. -/
def toSubring : Subring B :=
  O.toSubalgebra.toSubring

/-- Membership in the underlying subring is membership in the star-order. -/
@[simp]
theorem mem_toSubring {x : B} : x ∈ O.toSubring ↔ x ∈ O :=
  Iff.rfl

/-- A star-order is determined by its underlying subalgebra. -/
theorem toSubalgebra_injective :
    Function.Injective (fun O : StarOrder B => O.toSubalgebra) := fun _ _ h =>
  SetLike.coe_injective (congrArg ((↑) : Subalgebra ℤ B → Set B) h)

/-- Two star-orders with the same elements are equal. -/
@[ext]
theorem ext {O O' : StarOrder B} (h : ∀ x, x ∈ O ↔ x ∈ O') : O = O' :=
  SetLike.ext h

/-- Inclusions of star-orders are inclusions of the underlying `ℤ`-subalgebras. -/
@[simp]
theorem toSubalgebra_le_toSubalgebra : O.toSubalgebra ≤ O'.toSubalgebra ↔ O ≤ O' :=
  Iff.rfl

/-- The underlying subalgebra of a star-order is star-stable. -/
@[simp]
theorem star_toSubalgebra : star O.toSubalgebra = O.toSubalgebra :=
  SetLike.ext fun _ => (Subalgebra.mem_star_iff _ _).trans (_root_.star_mem_iff (s := O))

/-- A star-order inherits the involution of the ambient algebra. -/
instance instStarRing : StarRing O :=
  StarSubalgebra.starRing O.toStarSubalgebra

/-- A star-stable `ℤ`-subalgebra which is an order is a star-order. -/
def ofSubalgebra (Λ : Subalgebra ℤ B) (h : IsOrder ℚ Λ) (hstar : star Λ = Λ) : StarOrder B where
  toSubalgebra := Λ
  star_mem' {x} hx := by
    rwa [Subalgebra.mem_carrier, ← Subalgebra.mem_star_iff, hstar]
  isOrder := h

/-- The star-order built from a star-stable order has that order as its underlying subalgebra. -/
@[simp]
theorem toSubalgebra_ofSubalgebra (Λ : Subalgebra ℤ B) (h : IsOrder ℚ Λ) (hstar : star Λ = Λ) :
    (ofSubalgebra Λ h hstar).toSubalgebra = Λ :=
  (rfl)

/-- **Star-orders as star-stable orders.** A star-order is the same as a `ℤ`-subalgebra of `B`
which is a `ℤ`-order and is star-stable. Both directions retain the carrier. -/
def orderEquiv : StarOrder B ≃ {Λ : Subalgebra ℤ B // IsOrder ℚ Λ ∧ star Λ = Λ} where
  toFun O := ⟨O.toSubalgebra, O.isOrder, O.star_toSubalgebra⟩
  invFun Λ := ofSubalgebra Λ.val Λ.property.1 Λ.property.2
  left_inv _ := rfl
  right_inv _ := rfl

/-- `StarOrder.orderEquiv` forgets the star structure to the underlying subalgebra. -/
@[simp]
theorem coe_orderEquiv_apply : (orderEquiv O : Subalgebra ℤ B) = O.toSubalgebra :=
  (rfl)

/-- The inverse of `StarOrder.orderEquiv` retains the given subalgebra. -/
@[simp]
theorem toSubalgebra_orderEquiv_symm (Λ : {Λ : Subalgebra ℤ B // IsOrder ℚ Λ ∧ star Λ = Λ}) :
    (orderEquiv.symm Λ).toSubalgebra = Λ.val :=
  (rfl)

/-- In an algebra with trivial involution, every `ℤ`-order is a star-order. -/
def ofTrivialStar [TrivialStar B] (Λ : Subalgebra ℤ B) (h : IsOrder ℚ Λ) : StarOrder B :=
  ofSubalgebra Λ h <| SetLike.ext fun x => by rw [Subalgebra.mem_star_iff, star_trivial]

/-- The star-order of an order with trivial involution has that order as underlying subalgebra. -/
@[simp]
theorem toSubalgebra_ofTrivialStar [TrivialStar B] (Λ : Subalgebra ℤ B) (h : IsOrder ℚ Λ) :
    (ofTrivialStar Λ h).toSubalgebra = Λ :=
  (rfl)

/-! ### Examples -/

/-- The integer order `ℤ ⊆ ℚ`, a star-order for the identity involution of `ℚ`. -/
def int : StarOrder ℚ :=
  ofTrivialStar ⊥ isOrder_bot

/-- The integer order of `ℚ` consists of the images of the integers. -/
@[simp]
theorem mem_int {x : ℚ} : x ∈ int ↔ ∃ m : ℤ, (m : ℚ) = x := by
  refine (Algebra.mem_bot (R := ℤ) (A := ℚ)).trans ?_
  simp only [Set.mem_range, eq_intCast]

/-- `StarOrder.orderEquiv` sends the integer order of `ℚ` to the scalar order `⊥`. -/
theorem orderEquiv_int : (orderEquiv int : Subalgebra ℤ ℚ) = ⊥ :=
  (rfl)

/-- The integer order of `ℚ` contains `2`. -/
theorem two_mem_int : (2 : ℚ) ∈ int :=
  mem_int.2 ⟨2, by simp⟩

/-- The integer order of `ℚ` does not contain `1 / 2`. -/
theorem half_notMem_int : (1 / 2 : ℚ) ∉ int := fun h => by
  obtain ⟨m, hm⟩ := mem_int.1 h
  have hden := congrArg Rat.den hm
  rw [Rat.den_intCast] at hden
  norm_num at hden

section Matrix

variable (n : Type*) [Fintype n] [DecidableEq n]

/-- The star-order `M_n(ℤ)` in `M_n(ℚ)`, where the involution of `M_n(ℚ)` is the conjugate
transpose, which is the transpose since the involution of `ℚ` is trivial. -/
def matrix : StarOrder (Matrix n n ℚ) where
  toSubalgebra := (Algebra.ofId ℤ ℚ).mapMatrix.range
  star_mem' {x} := by
    rintro ⟨y, rfl⟩
    exact ⟨y.transpose, by ext i j; simp [Matrix.star_apply]⟩
  isOrder := by
    refine isOrder_iff.2 ⟨.of_surjective ((Algebra.ofId ℤ ℚ).mapMatrix.rangeRestrict.toLinearMap)
      (AlgHom.rangeRestrict_surjective _), eq_top_iff.2 fun x _ => ?_⟩
    rw [Matrix.matrix_eq_sum_single x]
    refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
    rw [← mul_one (x i j), ← smul_eq_mul, ← Matrix.smul_single]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Matrix.single i j 1, by simp⟩)

variable {n}

/-- A matrix lies in `M_n(ℤ)` exactly when all of its entries are integers. -/
@[simp]
theorem mem_matrix {x : Matrix n n ℚ} : x ∈ matrix n ↔ ∀ i j, ∃ m : ℤ, (m : ℚ) = x i j := by
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨y, rfl⟩ i j
    exact ⟨y i j, by simp⟩
  · choose y hy using h
    exact ⟨Matrix.of y, by ext i j; simp [hy]⟩

/-- The star-order `M_n(ℤ)` contains the standard matrix units. -/
theorem single_mem_matrix (i j : n) : Matrix.single i j (1 : ℚ) ∈ matrix n :=
  ⟨Matrix.single i j 1, by simp⟩

end Matrix

end StarOrder

end TauCeti
