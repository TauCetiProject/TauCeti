/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Prod

/-!
# Homomorphisms out of a product of monoids, and products of isomorphisms

A product of two monoids is their coproduct in commutative monoids: a homomorphism
`M × N →* P` with `P` commutative is the same data as a pair of homomorphisms `M →* P` and
`N →* P`, recovered by restricting along the two inclusions. Mathlib has the two directions
separately, as `MonoidHom.coprod` and composition with `MonoidHom.inl` and `MonoidHom.inr`,
together with the fact that they are mutually inverse; this file packages them as the
corresponding equivalence.

The file also records the value and the inverse of a product `MulEquiv.prodCongr` of two
multiplicative isomorphisms, which Mathlib states only for the underlying `Equiv.prodCongr`, and
recognizes a commutative monoid with projections and inclusions satisfying the biproduct
identities as the product of the two factors.

## Main definitions

* `MonoidHom.coprodEquiv`: the multiplicative equivalence `((M →* P) × (N →* P)) ≃* (M × N →* P)`
  for `P` a commutative monoid.
* `MulEquiv.ofProdCoprod`: the multiplicative equivalence `P ≃* A × B` determined by
  projections `P →* A`, `P →* B` and inclusions `A →* P`, `B →* P` satisfying the biproduct
  identities.
* `MulEquiv.prodCongr_apply`, `MulEquiv.prodCongr_symm`: the product of two isomorphisms acts
  componentwise, and its inverse is the product of the inverses.
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

namespace MulEquiv

variable {M N M' N' : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass M'] [MulOneClass N']

/-- The product of two multiplicative isomorphisms acts componentwise. -/
@[to_additive (attr := simp) prodCongr_apply
/-- The product of two additive isomorphisms acts componentwise. -/]
theorem prodCongr_apply (f : M ≃* M') (g : N ≃* N') (x : M × N) :
    f.prodCongr g x = (f x.1, g x.2) := (rfl)

/-- The inverse of a product of two multiplicative isomorphisms is the product of the inverses. -/
@[to_additive (attr := simp) prodCongr_symm
/-- The inverse of a product of two additive isomorphisms is the product of the inverses. -/]
theorem prodCongr_symm (f : M ≃* M') (g : N ≃* N') :
    (f.prodCongr g).symm = f.symm.prodCongr g.symm := (rfl)

section ofProdCoprod

variable {P A B : Type*} [CommMonoid P] [MulOneClass A] [MulOneClass B]
  (fst : P →* A) (snd : P →* B) (inl : A →* P) (inr : B →* P)
  (h : (inl.coprod inr).comp (fst.prod snd) = MonoidHom.id P)
  (fst_inl : fst.comp inl = MonoidHom.id A) (fst_inr : fst.comp inr = 1)
  (snd_inl : snd.comp inl = 1) (snd_inr : snd.comp inr = MonoidHom.id B)

/-- A commutative monoid `P` with projections `fst : P →* A`, `snd : P →* B` and inclusions
`inl : A →* P`, `inr : B →* P` satisfying the biproduct identities is the product `A × B`: the
forward map is `fst.prod snd` and the inverse is `inl.coprod inr`. -/
@[to_additive ofProdCoprod
/-- An additive commutative monoid `P` with projections `fst : P →+ A`,
`snd : P →+ B` and inclusions `inl : A →+ P`, `inr : B →+ P` satisfying the biproduct identities
is the product `A × B`: the forward map is `fst.prod snd` and the inverse is
`inl.coprod inr`. -/]
def ofProdCoprod : P ≃* A × B where
  toFun := fst.prod snd
  invFun := inl.coprod inr
  map_mul' := map_mul _
  left_inv x := DFunLike.congr_fun h x
  right_inv := fun ⟨x, y⟩ => by
    apply Prod.ext
    · simpa using congrArg₂ (· * ·)
        (DFunLike.congr_fun fst_inl x) (DFunLike.congr_fun fst_inr y)
    · simpa using congrArg₂ (· * ·)
        (DFunLike.congr_fun snd_inl x) (DFunLike.congr_fun snd_inr y)

/-- The equivalence `MulEquiv.ofProdCoprod` is given by the two projections. -/
@[to_additive (attr := simp) ofProdCoprod_apply
/-- The equivalence `AddEquiv.ofProdCoprod` is given by the two projections. -/]
theorem ofProdCoprod_apply (x : P) :
    ofProdCoprod fst snd inl inr h fst_inl fst_inr snd_inl snd_inr x = (fst x, snd x) := (rfl)

/-- The inverse of `MulEquiv.ofProdCoprod` multiplies the two inclusions. -/
@[to_additive (attr := simp) ofProdCoprod_symm_apply
/-- The inverse of `AddEquiv.ofProdCoprod` adds the two inclusions. -/]
theorem ofProdCoprod_symm_apply (x : A × B) :
    (ofProdCoprod fst snd inl inr h fst_inl fst_inr snd_inl snd_inr).symm x =
      inl x.1 * inr x.2 := (rfl)

end ofProdCoprod

end MulEquiv
