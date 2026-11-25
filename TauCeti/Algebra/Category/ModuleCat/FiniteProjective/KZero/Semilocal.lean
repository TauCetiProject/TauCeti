/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.StableEquivalent
public import TauCeti.Algebra.Module.Projective.Semilocal

/-!
# Classes in the projective `K₀` of a semilocal ring

Over a commutative semilocal ring `R`, a ring with finitely many maximal ideals, finitely
generated projective modules cancel free summands and are classified by their rank functions
(`TauCeti/Algebra/Module/Projective/Semilocal.lean`). In the split Grothendieck group of finitely
generated projective `R`-modules, equality of classes is stable equivalence, so here two modules
have the same class exactly when they are isomorphic, and exactly when they have the same rank at
every prime.

The rank comparison is the injectivity half of the classification of the `K₀` of a commutative
semilocal ring by its locally constant ranks: a class `[P] - [Q]` with `P` and `Q` of the same
rank at every prime is zero. The hypothesis cannot be dropped: over the Dedekind domain
`ℤ[√-5]`, the prime `(2, 1 + √-5)` and the ring itself have rank one everywhere but different
classes.

## Main results

* `TauCeti.SplitK0.of_eq_of_iff_nonempty_linearEquiv`: over a semilocal ring, two finitely
  generated projective modules have the same class if and only if they are isomorphic.
* `TauCeti.SplitK0.of_eq_of_iff_rankAtStalk_eq`: over a semilocal ring, two finitely generated
  projective modules have the same class if and only if they have the same rank at every prime.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II, §2,
  Exercise 2.6, p. 79.
-/

public section

namespace TauCeti.SplitK0

universe u

variable {R : Type u} [CommRing R] [Finite (MaximalSpectrum R)]
  {P Q : (finiteProjectiveModules R).FullSubcategory}

/-- **Classes in the projective `K₀` of a semilocal ring are isomorphism classes.** If `R` has
finitely many maximal ideals, two finitely generated projective `R`-modules have the same class
in split `K₀` if and only if they are isomorphic. -/
theorem of_eq_of_iff_nonempty_linearEquiv :
    of.{u} P = of.{u} Q ↔ Nonempty (P.obj ≃ₗ[R] Q.obj) := by
  rw [of_eq_of_iff_stableEquivalent]
  exact ⟨StableEquivalent.nonempty_linearEquiv_of_finite_maximalSpectrum,
    fun ⟨e⟩ ↦ .of_equiv e⟩

/-- **Rank detects classes in the projective `K₀` of a semilocal ring.** If `R` has finitely
many maximal ideals, two finitely generated projective `R`-modules have the same class in split
`K₀` if and only if they have the same rank at every prime. -/
theorem of_eq_of_iff_rankAtStalk_eq :
    of.{u} P = of.{u} Q ↔
      Module.rankAtStalk (R := R) P.obj = Module.rankAtStalk (R := R) Q.obj := by
  rw [of_eq_of_iff_nonempty_linearEquiv, Module.nonempty_linearEquiv_iff_rankAtStalk_eq]

end TauCeti.SplitK0
