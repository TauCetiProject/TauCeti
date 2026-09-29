/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Orders.Basic
public import TauCeti.NumberTheory.NumberField.TotallyPositive

/-!
# Morphisms of number-field orders

A morphism of orders includes a map of their ambient number fields. This lets it act on
denominators of fractional ideals. Its restriction to the orders is a ring homomorphism, and
it carries totally positive generators to totally positive generators. These are the two
ingredients needed for maps on wide and narrow Picard groups.

## References

* G. S. Kopp and J. C. Lagarias, *Class Field Theory for Orders of Number Fields*, §2.
-/

public section
noncomputable section

open NumberField

namespace TauCeti.GlobalNumberFields

namespace NumberFieldOrder

universe u v w z

/-- A morphism of number-field orders: a homomorphism of their ambient fields that maps the
source order into the target order. The ambient map is part of the data so that it can also map
elements with denominators. -/
structure Hom {K : Type u} [Field K] [NumberField K]
    {L : Type v} [Field L] [NumberField L]
    (O : NumberFieldOrder K) (O' : NumberFieldOrder L) where
  /-- The map on ambient number fields. -/
  fieldHom : K →+* L
  /-- The ambient map carries the source order into the target order. -/
  map_mem' : ∀ ⦃x : K⦄, x ∈ O.toSubalgebra → fieldHom x ∈ O'.toSubalgebra

namespace Hom

variable {K : Type u} [Field K] [NumberField K]
variable {L : Type v} [Field L] [NumberField L]
variable {M : Type w} [Field M] [NumberField M]
variable {N : Type z} [Field N] [NumberField N]
variable {O : NumberFieldOrder K} {O' : NumberFieldOrder L}
variable {O'' : NumberFieldOrder M}
variable {O''' : NumberFieldOrder N}

instance : CoeFun (Hom O O') (fun _ => K → L) := ⟨fun f => f.fieldHom⟩

/-- An order morphism maps elements of the source order into the target order. -/
theorem map_mem (f : Hom O O') {x : K} (hx : x ∈ O.toSubalgebra) :
    f x ∈ O'.toSubalgebra :=
  f.map_mem' hx

@[simp]
theorem map_zero (f : Hom O O') : f (0 : K) = 0 :=
  f.fieldHom.map_zero

@[simp]
theorem map_one (f : Hom O O') : f (1 : K) = 1 :=
  f.fieldHom.map_one

@[simp]
theorem map_add (f : Hom O O') (x y : K) : f (x + y) = f x + f y :=
  f.fieldHom.map_add x y

@[simp]
theorem map_mul (f : Hom O O') (x y : K) : f (x * y) = f x * f y :=
  f.fieldHom.map_mul x y

theorem map_inv (f : Hom O O') (x : K) : f x⁻¹ = (f x)⁻¹ :=
  map_inv₀ f.fieldHom x

theorem map_div (f : Hom O O') (x y : K) : f (x / y) = f x / f y :=
  map_div₀ f.fieldHom x y

/-- Restrict an order morphism to a ring homomorphism of its two orders. -/
def toOrderHom (f : Hom O O') : O.toSubalgebra →+* O'.toSubalgebra :=
  f.fieldHom.restrict O.toSubalgebra O'.toSubalgebra (fun _ hx => f.map_mem hx)

@[simp]
theorem toOrderHom_apply (f : Hom O O') (x : O.toSubalgebra) :
    ((f.toOrderHom x : O'.toSubalgebra) : L) = f (x : K) :=
  by simp [toOrderHom]

/-- Two order morphisms agreeing on the ambient field are equal. -/
@[ext]
theorem ext {f g : Hom O O'} (h : ∀ x : K, f x = g x) : f = g := by
  cases f with
  | mk ff hf =>
    cases g with
    | mk fg hg =>
      have heq : ff = fg := RingHom.ext h
      subst heq
      rfl

/-- The identity morphism of an order. -/
def id (O : NumberFieldOrder K) : Hom O O where
  fieldHom := RingHom.id K
  map_mem' := fun {_x} hx => hx

/-- Composition of order morphisms, including their maps on ambient fields. -/
def comp (g : Hom O' O'') (f : Hom O O') : Hom O O'' where
  fieldHom := g.fieldHom.comp f.fieldHom
  map_mem' := fun {x} hx => g.map_mem' (f.map_mem' (x := x) hx)

@[simp]
theorem id_apply (O : NumberFieldOrder K) (x : K) : (Hom.id O) x = x := by
  simp [id]

@[simp]
theorem comp_apply (g : Hom O' O'') (f : Hom O O') (x : K) :
    (g.comp f) x = g (f x) := by
  simp [comp]

/-- Restriction to the orders respects composition. -/
@[simp]
theorem toOrderHom_comp (g : Hom O' O'') (f : Hom O O') :
    (g.comp f).toOrderHom = g.toOrderHom.comp f.toOrderHom := by
  ext x
  rfl

/-- Restricting the identity morphism gives the identity on the order. -/
@[simp]
theorem toOrderHom_id (O : NumberFieldOrder K) :
    (Hom.id O).toOrderHom = RingHom.id O.toSubalgebra := by
  ext x
  rfl

@[simp]
theorem id_comp (f : Hom O O') : (Hom.id O').comp f = f := by ext x; rfl

@[simp]
theorem comp_id (f : Hom O O') : f.comp (Hom.id O) = f := by ext x; rfl

/-- Composition of order morphisms is associative. -/
theorem comp_assoc (h : Hom O'' O''') (g : Hom O' O'') (f : Hom O O') :
    (h.comp g).comp f = h.comp (g.comp f) := by
  ext x
  rfl

/-- Restricting a real place of the target field along an order morphism gives a real place
of the source field. -/
theorem isReal_comap (f : Hom O O') {w : InfinitePlace L} (hw : w.IsReal) :
    (w.comap f.fieldHom).IsReal :=
  hw.comap f.fieldHom

/-- A morphism of orders preserves total positivity in the ambient number fields. In
particular it takes generators of narrowly principal fractional ideals to positive generators. -/
theorem pos_of_totallyPos (f : Hom O O') {x : K} (hx : IsTotallyPositive x) :
    IsTotallyPositive (f x) :=
  hx.map f.fieldHom

/-- Inclusion between orders of the same field is an order morphism. -/
def ofLE {O O' : NumberFieldOrder K} (h : O.toSubalgebra ≤ O'.toSubalgebra) :
    Hom O O' where
  fieldHom := RingHom.id K
  map_mem' := fun {_x} hx => h hx

@[simp]
theorem ofLE_apply {O O' : NumberFieldOrder K}
    (h : O.toSubalgebra ≤ O'.toSubalgebra) (x : K) :
    ofLE h x = x := by simp [ofLE]

end Hom

end NumberFieldOrder

end TauCeti.GlobalNumberFields
