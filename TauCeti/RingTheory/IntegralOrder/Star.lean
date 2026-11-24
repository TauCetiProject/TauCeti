/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Subalgebra
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import TauCeti.RingTheory.IntegralOrder.Basic

/-!
# Star-stable orders

Let `R` be a domain with fraction field `F` and `E` an `F`-algebra carrying an involution
`x ↦ star x`. A *star-order* is an `R`-order `O` in `E` (`TauCeti.IntegralOrder.IsOrder`) which is
stable under the involution, `star O = O`; the involution of `E` then restricts to `O`. Star-orders
in a finite-dimensional semisimple `ℚ`-algebra with positive involution are the coefficient rings of
PEL data: the order `O` acts on a lattice `L`, and the symplectic pairing on `L` makes the action
of `b ∈ O` adjoint to that of `star b`. Allowing a general `R` covers the `ℤ_(p)`-orders of
`p`-integral data as well as the `ℤ`-orders of integral data.

A star-order is a bundled structure, but it carries no data beyond its underlying subalgebra:
`TauCeti.IntegralOrder.StarOrder.orderEquiv` identifies star-orders, ordered by inclusion, with the
`R`-subalgebras of `E` which are star-stable orders. Overorders and maximality are those of the
underlying subalgebras (`TauCeti.IntegralOrder.IsMaximalOrder`), and are not required to respect
the involution.

## Main definitions

* `TauCeti.IntegralOrder.StarOrder R F E`: the star-stable `R`-orders in `E`.
* `TauCeti.IntegralOrder.StarOrder.toSubalgebra`, `TauCeti.IntegralOrder.StarOrder.toSubring`: the
  underlying subalgebra and subring.
* `TauCeti.IntegralOrder.StarOrder.orderEquiv`: star-orders are the star-stable orders among the
  `R`-subalgebras of `E`.
* `TauCeti.IntegralOrder.StarOrder.bot`: the image of `R` is a star-order in `F`.
* `TauCeti.IntegralOrder.StarOrder.matrix`: if `O` is a star-order in `E`, then the matrices with
  entries in `O` form a star-order in `Matrix n n E` with the conjugate-transpose involution.

## Main results

* `TauCeti.IntegralOrder.StarOrder.star_toSubalgebra`: the pointwise star of the underlying
  subalgebra of a star-order is itself.

## References

* K.-W. Lan, *Arithmetic compactifications of PEL-type Shimura varieties*, Definitions 1.1.1.2 to
  1.1.1.4 and §1.2.1.
* R. E. Kottwitz, *Points on some Shimura varieties over finite fields*, §5.
-/

public section

namespace TauCeti.IntegralOrder

variable (R F E : Type*) [CommRing R] [CommRing F] [Ring E] [StarRing E] [Algebra F E]
  [Algebra R E]

/-- A *star-order* in an `F`-algebra `E` with involution: an `R`-order in `E`, in the sense of
`TauCeti.IntegralOrder.IsOrder`, which is stable under the involution of `E`. -/
structure StarOrder extends Subalgebra R E where
  /-- The involution maps the order into itself. -/
  star_mem' {x : E} : x ∈ carrier → star x ∈ carrier
  /-- The underlying subalgebra is an `R`-order in `E`. -/
  isOrder' : IsOrder F toSubalgebra

/-- Forgetting that a star-order is star-stable and an order. -/
add_decl_doc StarOrder.toSubalgebra

namespace StarOrder

variable {R F E}

theorem toSubalgebra_injective :
    Function.Injective (toSubalgebra : StarOrder R F E → Subalgebra R E) := by
  rintro ⟨O, _, _⟩ ⟨P, _, _⟩ (rfl : O = P)
  rfl

instance : SetLike (StarOrder R F E) E where
  coe O := O.toSubalgebra
  coe_injective _ _ h := toSubalgebra_injective (SetLike.coe_injective h)

instance : PartialOrder (StarOrder R F E) := .ofSetLike (StarOrder R F E)

instance : SubringClass (StarOrder R F E) E where
  mul_mem {O} := O.toSubalgebra.mul_mem
  one_mem O := O.toSubalgebra.one_mem
  add_mem {O} := O.toSubalgebra.add_mem
  zero_mem O := O.toSubalgebra.zero_mem
  neg_mem {O} := O.toSubalgebra.neg_mem

instance : SMulMemClass (StarOrder R F E) R E where
  smul_mem {O} r _ hm := O.toSubalgebra.smul_mem hm r

instance : StarMemClass (StarOrder R F E) E where
  star_mem {O} := O.star_mem'

variable {O P : StarOrder R F E} {x : E}

@[simp]
theorem mem_toSubalgebra : x ∈ O.toSubalgebra ↔ x ∈ O :=
  Iff.rfl

@[simp]
theorem coe_toSubalgebra (O : StarOrder R F E) : (O.toSubalgebra : Set E) = O :=
  rfl

@[ext]
theorem ext (h : ∀ x, x ∈ O ↔ x ∈ P) : O = P :=
  SetLike.ext h

@[simp]
theorem toSubalgebra_inj : O.toSubalgebra = P.toSubalgebra ↔ O = P :=
  toSubalgebra_injective.eq_iff

/-- Inclusions of star-orders are inclusions of their underlying subalgebras. -/
@[simp]
theorem toSubalgebra_le_toSubalgebra : O.toSubalgebra ≤ P.toSubalgebra ↔ O ≤ P :=
  Iff.rfl

@[simp]
theorem toSubalgebra_lt_toSubalgebra : O.toSubalgebra < P.toSubalgebra ↔ O < P :=
  Iff.rfl

/-- The underlying subalgebra of a star-order is an `R`-order. -/
theorem isOrder (O : StarOrder R F E) : IsOrder F O.toSubalgebra :=
  O.isOrder'

/-- Every element of a star-order is integral over `R`. -/
theorem isIntegral (hx : x ∈ O) : IsIntegral R x :=
  O.isOrder.isIntegral hx

/-- The underlying subring of a star-order. -/
def toSubring (O : StarOrder R F E) : Subring E :=
  O.toSubalgebra.toSubring

@[simp]
theorem mem_toSubring : x ∈ O.toSubring ↔ x ∈ O :=
  Iff.rfl

@[simp]
theorem coe_toSubring (O : StarOrder R F E) : (O.toSubring : Set E) = O :=
  (rfl)

/-- Two star-orders with the same underlying subring are equal. -/
theorem toSubring_injective :
    Function.Injective (toSubring : StarOrder R F E → Subring E) := fun _ _ h =>
  SetLike.coe_injective (congrArg ((↑) : Subring E → Set E) h)

/-- A subalgebra which is an order and stable under the involution, viewed as a star-order. -/
def ofSubalgebra (Λ : Subalgebra R E) (hΛ : IsOrder F Λ) (hstar : ∀ x ∈ Λ, star x ∈ Λ) :
    StarOrder R F E where
  toSubalgebra := Λ
  star_mem' := hstar _
  isOrder' := hΛ

@[simp]
theorem ofSubalgebra_toSubalgebra (Λ : Subalgebra R E) (hΛ : IsOrder F Λ)
    (hstar : ∀ x ∈ Λ, star x ∈ Λ) : (ofSubalgebra Λ hΛ hstar).toSubalgebra = Λ :=
  (rfl)

@[simp]
theorem mem_ofSubalgebra {Λ : Subalgebra R E} {hΛ : IsOrder F Λ}
    {hstar : ∀ x ∈ Λ, star x ∈ Λ} : x ∈ ofSubalgebra Λ hΛ hstar ↔ x ∈ Λ :=
  Iff.rfl

variable (R F E) in
/-- **Star-orders as star-stable orders.** A star-order is the same as an `R`-subalgebra of `E`
which is an `R`-order in `E` and is stable under the involution; the identification preserves the
underlying subalgebras, so it is an isomorphism for the inclusion orders. -/
def orderEquiv :
    StarOrder R F E ≃o {Λ : Subalgebra R E // IsOrder F Λ ∧ ∀ x ∈ Λ, star x ∈ Λ} where
  toFun O := ⟨O.toSubalgebra, O.isOrder, fun _ => O.star_mem'⟩
  invFun Λ := ofSubalgebra Λ.val Λ.property.1 Λ.property.2
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

@[simp]
theorem coe_orderEquiv_apply (O : StarOrder R F E) :
    (orderEquiv R F E O : Subalgebra R E) = O.toSubalgebra :=
  (rfl)

@[simp]
theorem orderEquiv_symm_apply (Λ : {Λ : Subalgebra R E // IsOrder F Λ ∧ ∀ x ∈ Λ, star x ∈ Λ}) :
    (orderEquiv R F E).symm Λ = ofSubalgebra Λ.val Λ.property.1 Λ.property.2 :=
  (rfl)

section StarModule

variable [StarRing R] [StarModule R E]


/-- The pointwise image of the underlying subalgebra of a star-order under the involution is the
same subalgebra: `O* = O`. -/
@[simp]
theorem star_toSubalgebra (O : StarOrder R F E) : star O.toSubalgebra = O.toSubalgebra :=
  Subalgebra.ext fun x => ⟨fun hx => by simpa using star_mem (S := StarOrder R F E) hx,
    fun hx => by simpa using star_mem (S := StarOrder R F E) hx⟩

/-- The star-subalgebra underlying a star-order. -/
def toStarSubalgebra (O : StarOrder R F E) : StarSubalgebra R E where
  toSubalgebra := O.toSubalgebra
  star_mem' := star_mem (S := StarOrder R F E)

@[simp]
theorem toStarSubalgebra_toSubalgebra (O : StarOrder R F E) :
    O.toStarSubalgebra.toSubalgebra = O.toSubalgebra :=
  (rfl)

@[simp]
theorem mem_toStarSubalgebra : x ∈ O.toStarSubalgebra ↔ x ∈ O :=
  Iff.rfl

end StarModule

section Bot

variable [Algebra R F] [StarRing R] [StarRing F] [StarModule R F]

variable (R F) in
/-- The image of `R` is a star-order in `F`. -/
def bot : StarOrder R F F :=
  ofSubalgebra ⊥ isOrder_bot fun x hx => by
    obtain ⟨r, rfl⟩ := Algebra.mem_bot.1 hx
    exact Algebra.mem_bot.2 ⟨star r, algebraMap_star_comm r⟩

@[simp]
theorem bot_toSubalgebra : (bot R F).toSubalgebra = ⊥ :=
  (rfl)

@[simp]
theorem mem_bot {x : F} : x ∈ bot R F ↔ x ∈ Set.range (algebraMap R F) :=
  Algebra.mem_bot

end Bot

section Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Matrix star-orders.** The matrices with entries in a star-order `O` in `E` form a star-order
in `Matrix n n E`, whose involution is the conjugate transpose. For `O = ℤ` in `ℚ` this is
`M_n(ℤ)` in `M_n(ℚ)` with the transpose. -/
def matrix (O : StarOrder R F E) : StarOrder R F (Matrix n n E) :=
  ofSubalgebra O.toSubalgebra.matrix O.isOrder.matrix fun M hM i j => by
    simpa [Matrix.star_apply] using star_mem (S := StarOrder R F E) (hM j i)

@[simp]
theorem matrix_toSubalgebra (O : StarOrder R F E) :
    (O.matrix : StarOrder R F (Matrix n n E)).toSubalgebra = O.toSubalgebra.matrix :=
  (rfl)

@[simp]
theorem mem_matrix {M : Matrix n n E} : M ∈ O.matrix ↔ ∀ i j, M i j ∈ O :=
  Iff.rfl

end Matrix

end StarOrder

end TauCeti.IntegralOrder
