/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Group.TypeTags.Hom
public import Mathlib.Data.Int.Cast.Lemmas

/-!
# Characters of a free abelian group

The free abelian group on an index type `σ` is modelled as `Multiplicative (σ →₀ ℤ)`: its
underlying additive group `σ →₀ ℤ` is the free `ℤ`-module on `σ`. This file records its
universal property in the form most useful for the functor of points of a split torus: a
homomorphism `Multiplicative (σ →₀ ℤ) →* M` to a commutative group `M` is the same data as a
family `σ → M`, naturally and multiplicatively.

The equivalence sends a homomorphism `χ` to its values `i ↦ χ (ofAdd (single i 1))` on the
standard generators, and a family `c : σ → M` to the unique homomorphism extending it. This is
the many-generator version of Mathlib's `zpowersHom : M ≃ (Multiplicative ℤ →* M)` (the case of
one generator).

## Main definitions

* `TauCeti.freeAbelianCharEquiv`: the multiplicative equivalence
  `(Multiplicative (σ →₀ ℤ) →* M) ≃* (σ → M)`.

## References

The construction reuses Mathlib's group-algebra-free toolkit: the `Finsupp.liftAddHom`
universal property of `σ →₀ ℤ`, the `ℤ`-power homomorphism `zmultiplesHom`, and the type-tag
adjunction `AddMonoidHom.toMultiplicativeLeft` from `Mathlib.Algebra.Group.TypeTags.Hom`.

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
@[expose] noncomputable def freeAbelianCharEquiv :
    (Multiplicative (σ →₀ ℤ) →* M) ≃* (σ → M) where
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
@[simp]
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

end TauCeti
