/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Group.TypeTags.Hom

/-!
# Characters of a free commutative monoid

The free commutative monoid on an index type `σ` is modelled as `Multiplicative (σ →₀ ℕ)`: its
underlying additive monoid `σ →₀ ℕ` is the free `ℕ`-module on `σ`. This file records its
universal property in the form most useful for the functor of points of an affine semigroup: a
homomorphism `Multiplicative (σ →₀ ℕ) →* M` to a commutative monoid `M` is the same data as a
family `σ → M`.

The equivalence sends a homomorphism `χ` to its values `i ↦ χ (ofAdd (single i 1))` on the
standard generators, and a family `c : σ → M` to the unique homomorphism extending it. This is
the many-generator version of Mathlib's `powersHom : M ≃ (Multiplicative ℕ →* M)` (the case of
one generator), and the monoid counterpart of `TauCeti.freeAbelianCharEquiv` in
`TauCeti.Algebra.Group.FreeAbelianCharacter`: no invertibility is imposed on the values. The two
appear together whenever a semigroup splits as a product of a free commutative monoid and a free
abelian group, as the dual semigroup of a smooth cone does; the values of a character on the free
monoid factor may vanish, while those on the free abelian factor are units.

## Main definitions

* `TauCeti.freeCommMonoidCharEquiv`: the multiplicative equivalence
  `(Multiplicative (σ →₀ ℕ) →* M) ≃* (σ → M)`.

## Implementation notes

The equivalence is not exposed: `TauCeti.freeCommMonoidCharEquiv_apply` and
`TauCeti.freeCommMonoidCharEquiv_symm_apply_ofAdd` characterise both of its directions, so
nothing downstream needs to unfold it. The first is proved by the parenthesised `(rfl)`, which
elaborates against the definition itself; a bare `rfl` in an exported theorem would demand that
the definition be `@[expose]`d.

## References

The construction reuses Mathlib's group-algebra-free toolkit: the `Finsupp.liftAddHom`
universal property of `σ →₀ ℕ`, the `ℕ`-power homomorphism `multiplesHom`, and the type-tag
adjunction `AddMonoidHom.toMultiplicativeLeft` from `Mathlib.Algebra.Group.TypeTags.Hom`.
-/

public section

namespace TauCeti

variable {σ : Type*} {M : Type*} [CommMonoid M]

/-- The universal property of the free commutative monoid `Multiplicative (σ →₀ ℕ)`: a
homomorphism to a commutative monoid `M` is the same data as a family `σ → M`. The forward map
reads off the values on the standard generators `ofAdd (single i 1)`; the inverse extends a
family to the unique homomorphism through `Finsupp.liftAddHom` and the `ℕ`-power
homomorphism. -/
noncomputable def freeCommMonoidCharEquiv :
    (Multiplicative (σ →₀ ℕ) →* M) ≃* (σ → M) where
  toFun χ i := χ (Multiplicative.ofAdd (Finsupp.single i 1))
  invFun c := AddMonoidHom.toMultiplicativeLeft
    (Finsupp.liftAddHom fun i => (multiplesHom (Additive M)) (Additive.ofMul (c i)))
  map_mul' _ _ := rfl
  right_inv c := by
    funext i
    simp
  left_inv χ := by
    apply Multiplicative.monoidHom_ext
    apply Finsupp.addHom_ext'
    intro x
    apply AddMonoidHom.ext_nat
    simp

/-- The forward direction of `freeCommMonoidCharEquiv` evaluates a character on the standard
generator indexed by `i`. -/
@[simp]
theorem freeCommMonoidCharEquiv_apply (χ : Multiplicative (σ →₀ ℕ) →* M) (i : σ) :
    freeCommMonoidCharEquiv χ i = χ (Multiplicative.ofAdd (Finsupp.single i 1)) :=
  (rfl)

/-- The inverse of `freeCommMonoidCharEquiv` evaluates a finitely supported family of natural
exponents as the corresponding product of powers of the chosen coordinates. -/
@[simp]
theorem freeCommMonoidCharEquiv_symm_apply_ofAdd (c : σ → M) (m : σ →₀ ℕ) :
    (freeCommMonoidCharEquiv (M := M)).symm c (Multiplicative.ofAdd m) =
      m.prod fun i n => c i ^ n := by
  simp [freeCommMonoidCharEquiv, Finsupp.liftAddHom_apply, Finsupp.sum, Finsupp.prod,
    toMul_sum, multiplesHom_apply]

end TauCeti
