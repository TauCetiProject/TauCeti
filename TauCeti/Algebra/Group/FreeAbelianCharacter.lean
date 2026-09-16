/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Group.TypeTags.Hom
public import Mathlib.Data.Int.Cast.Lemmas

/-!
# Characters of a free abelian group and of a free commutative monoid

The free abelian group on an index type `σ` is modelled as `Multiplicative (σ →₀ ℤ)`: its
underlying additive group `σ →₀ ℤ` is the free `ℤ`-module on `σ`. This file records its
universal property in the form most useful for the functor of points of a split torus: a
homomorphism `Multiplicative (σ →₀ ℤ) →* M` to a commutative group `M` is the same data as a
family `σ → M`, naturally and multiplicatively.

Replacing the integers by the natural numbers gives the free commutative monoid
`Multiplicative (σ →₀ ℕ)` on `σ` and the same universal property with `M` only a commutative
monoid. The two appear together whenever a semigroup splits as a product of a free commutative
monoid and a free abelian group, as the dual semigroup of a smooth cone does; the values of a
character on the free monoid factor may vanish, while those on the free abelian factor are
units.

Each equivalence sends a homomorphism `χ` to its values `i ↦ χ (ofAdd (single i 1))` on the
standard generators, and a family `c : σ → M` to the unique homomorphism extending it. They are
the many-generator versions of Mathlib's `zpowersHom : M ≃ (Multiplicative ℤ →* M)` and
`powersHom : M ≃ (Multiplicative ℕ →* M)` (the case of one generator).

## Main definitions

* `TauCeti.freeAbelianCharEquiv`: the multiplicative equivalence
  `(Multiplicative (σ →₀ ℤ) →* M) ≃* (σ → M)`.
* `TauCeti.freeCommMonoidCharEquiv`: the multiplicative equivalence
  `(Multiplicative (σ →₀ ℕ) →* M) ≃* (σ → M)`.

## References

The construction reuses Mathlib's group-algebra-free toolkit: the `Finsupp.liftAddHom`
universal property of `σ →₀ ℤ` and of `σ →₀ ℕ`, the power homomorphisms `zmultiplesHom` and
`multiplesHom`, and the type-tag adjunction `AddMonoidHom.toMultiplicativeLeft` from
`Mathlib.Algebra.Group.TypeTags.Hom`.

The additive shadow of this equivalence is the `R = ℤ` case of Mathlib's
`Finsupp.lift : (σ → M) ≃+ ((σ →₀ ℤ) →ₗ[ℤ] M)`, transported across `addMonoidHomLequivInt` and
the `Multiplicative`/`Additive` type-tag adjunctions. We build it directly from the same
underlying pieces (`Finsupp.liftAddHom` and `zmultiplesHom`) rather than transporting that
chain of isomorphisms so that the forward map is *definitionally* generator evaluation
`χ ↦ fun i => χ (ofAdd (single i 1))`. That keeps `freeAbelianCharEquiv_apply`, `map_mul'`, and
`freeAbelianCharEquiv_comp` true by `rfl`; a transported equivalence would route every
evaluation through the composite transport maps and lose that defeq.
-/

public section

namespace TauCeti

variable {σ : Type*} {M : Type*} [CommGroup M]

/-- The universal property of the free abelian group `Multiplicative (σ →₀ ℤ)`: a homomorphism
to a commutative group `M` is the same data as a family `σ → M`. The forward map reads off the
values on the standard generators `ofAdd (single i 1)`; the inverse extends a family to the
unique homomorphism through `Finsupp.liftAddHom` and the `ℤ`-power homomorphism. -/
@[expose] noncomputable def freeAbelianCharEquiv : (Multiplicative (σ →₀ ℤ) →* M) ≃* (σ → M) where
  toFun χ i := χ (Multiplicative.ofAdd (Finsupp.single i 1))
  invFun c := AddMonoidHom.toMultiplicativeLeft
    (Finsupp.liftAddHom fun i => (zmultiplesHom (Additive M)) (Additive.ofMul (c i)))
  map_mul' _ _ := rfl
  right_inv c := by
    funext i
    simp
  left_inv χ := by
    apply Multiplicative.monoidHom_ext
    apply Finsupp.addHom_ext'
    intro x
    apply AddMonoidHom.ext_int
    simp

/-- The forward direction of `freeAbelianCharEquiv` evaluates a character on the standard
generator indexed by `i`. -/
@[simp]
theorem freeAbelianCharEquiv_apply (χ : Multiplicative (σ →₀ ℤ) →* M) (i : σ) :
    freeAbelianCharEquiv χ i = χ (Multiplicative.ofAdd (Finsupp.single i 1)) :=
  rfl

/-- The inverse of `freeAbelianCharEquiv` sends the standard generator indexed by `i` to the
chosen coordinate `c i`. -/
theorem freeAbelianCharEquiv_symm_apply_ofAdd_single (c : σ → M) (i : σ) :
    (freeAbelianCharEquiv (M := M)).symm c (Multiplicative.ofAdd (Finsupp.single i 1)) = c i := by
  simp [freeAbelianCharEquiv]

/-- The inverse of `freeAbelianCharEquiv` evaluates an arbitrary finitely supported integer
combination as the corresponding product of powers of the chosen coordinates. -/
@[simp]
theorem freeAbelianCharEquiv_symm_apply_ofAdd (c : σ → M) (m : σ →₀ ℤ) :
    (freeAbelianCharEquiv (M := M)).symm c (Multiplicative.ofAdd m) =
      m.prod fun i n => c i ^ n := by
  simp [freeAbelianCharEquiv, Finsupp.liftAddHom_apply, Finsupp.sum, Finsupp.prod,
    toMul_sum, zmultiplesHom_apply]

/-- Reading off generator values is natural in the target group: post-composing with a
homomorphism `ψ : M →* N` commutes with `freeAbelianCharEquiv`. -/
@[simp]
theorem freeAbelianCharEquiv_comp {N : Type*} [CommGroup N] (ψ : M →* N)
    (χ : Multiplicative (σ →₀ ℤ) →* M) (i : σ) :
    freeAbelianCharEquiv (ψ.comp χ) i = ψ (freeAbelianCharEquiv χ i) :=
  rfl

section CommMonoid

variable {M : Type*} [CommMonoid M]

/-- The universal property of the free commutative monoid `Multiplicative (σ →₀ ℕ)`: a
homomorphism to a commutative monoid `M` is the same data as a family `σ → M`. This is the
monoid counterpart of `TauCeti.freeAbelianCharEquiv`, with no invertibility imposed on the
values; the forward map again reads off the values on the standard generators
`ofAdd (single i 1)`. -/
@[expose] noncomputable def freeCommMonoidCharEquiv :
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
  rfl

/-- The inverse of `freeCommMonoidCharEquiv` evaluates a finitely supported family of natural
exponents as the corresponding product of powers of the chosen coordinates. -/
@[simp]
theorem freeCommMonoidCharEquiv_symm_apply_ofAdd (c : σ → M) (m : σ →₀ ℕ) :
    (freeCommMonoidCharEquiv (M := M)).symm c (Multiplicative.ofAdd m) =
      m.prod fun i n => c i ^ n := by
  simp [freeCommMonoidCharEquiv, Finsupp.liftAddHom_apply, Finsupp.sum, Finsupp.prod,
    toMul_sum, multiplesHom_apply]

end CommMonoid

end TauCeti
