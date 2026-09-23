/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Prod

/-!
# Homomorphisms out of a product of monoids and additive equivalences of products

A product of two monoids is their coproduct in commutative monoids: a homomorphism
`M × N →* P` with `P` commutative is the same data as a pair of homomorphisms `M →* P` and
`N →* P`, recovered by restricting along the two inclusions. Mathlib has the two directions
separately, as `MonoidHom.coprod` and composition with `MonoidHom.inl` and `MonoidHom.inr`,
together with the fact that they are mutually inverse; this file packages them as the
corresponding equivalence.

The file also provides an additive equivalence between functions into a product and pairs of
function spaces, packaging the underlying `Equiv` with pointwise addition.

## Main definitions

* `MonoidHom.coprodEquiv`: the multiplicative equivalence `((M →* P) × (N →* P)) ≃* (M × N →* P)`
  for `P` a commutative monoid.
-/

public section

namespace MonoidHom

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [CommMonoid P]

/-- Homomorphisms from a product of two monoids to a commutative monoid `P` are pairs of
homomorphisms out of the factors: the forward map is `MonoidHom.coprod` and the inverse
restricts along `MonoidHom.inl` and `MonoidHom.inr`. -/
@[to_additive /-- Homomorphisms from a product of two additive monoids to a commutative
additive monoid `P` are pairs of homomorphisms out of the factors: the forward map is
`AddMonoidHom.coprod` and the inverse restricts along `AddMonoidHom.inl` and
`AddMonoidHom.inr`. -/]
def coprodEquiv : ((M →* P) × (N →* P)) ≃* (M × N →* P) where
  toFun f := f.1.coprod f.2
  invFun f := (f.comp (inl M N), f.comp (inr M N))
  left_inv f := by ext x <;> simp
  right_inv f := coprod_unique f
  map_mul' f g := by ext x; simp [mul_mul_mul_comm]

@[to_additive (attr := simp) /-- The homomorphism attached to a pair of homomorphisms out of the
factors is their coproduct. -/]
theorem coprodEquiv_apply (f : (M →* P) × (N →* P)) (x : M × N) :
    coprodEquiv f x = f.1 x.1 * f.2 x.2 := (rfl)

@[to_additive (attr := simp) /-- The pair of homomorphisms attached to a homomorphism out of a
product restricts it along the two inclusions. -/]
theorem coprodEquiv_symm_apply (f : M × N →* P) :
    coprodEquiv.symm f = (f.comp (inl M N), f.comp (inr M N)) := (rfl)

end MonoidHom

namespace TauCeti

namespace AddEquiv

/-- Functions into products are additively equivalent to products of function spaces. -/
def piProd {ι : Type*} (B C : ι → Type*)
    [∀ i, AddMonoid (B i)] [∀ i, AddMonoid (C i)] :
    (∀ i, B i × C i) ≃+ (∀ i, B i) × (∀ i, C i) :=
  { Equiv.arrowProdEquivProdArrow ι B C with map_add' := fun _ _ ↦ rfl }

/-- `piProd` maps a function to its two component functions. -/
@[simp]
theorem piProd_apply (B C : ι → Type*) [∀ i, AddMonoid (B i)] [∀ i, AddMonoid (C i)]
    (f : ∀ i, B i × C i) : piProd B C f = (fun i ↦ (f i).1, fun i ↦ (f i).2) :=
  Equiv.arrowProdEquivProdArrow_apply ι B C f

/-- The inverse of `piProd` pairs component functions pointwise. -/
@[simp]
theorem piProd_symm_apply (B C : ι → Type*) [∀ i, AddMonoid (B i)]
    [∀ i, AddMonoid (C i)] (f : (∀ i, B i) × (∀ i, C i)) :
    (piProd B C).symm f = fun i ↦ (f.1 i, f.2 i) :=
  by
    apply funext
    intro i
    exact Equiv.arrowProdEquivProdArrow_symm_apply ι B C f i

end AddEquiv

end TauCeti
