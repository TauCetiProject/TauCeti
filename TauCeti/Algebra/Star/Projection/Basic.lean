/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Algebra.Star.Unitary
public import TauCeti.Algebra.Algebra.Unitization
import Mathlib.Algebra.Star.UnitaryStarAlgAut

/-!
# Reflections and unitary conjugates of star projections

For a star projection `p` in a star ring, the reflection `1 - 2 * p` is the negative of the
symmetry `2 * p - 1` in Mathlib's `IsStarProjection.two_mul_sub_one_mem_unitary`, so it is
self-adjoint and lies in `unitary A`. We also record the witness identities for `u * p` used
when descending unitary conjugacy of projections to Murray–von Neumann equivalence, together with
the `inr`-projection conjugation lemmas in `Unitization`.

## Main declarations

* `IsStarProjection.isSelfAdjoint_one_sub_two_mul`: `1 - 2 * p` is self-adjoint.
* `IsStarProjection.one_sub_two_mul_mem_unitary`: `1 - 2 * p ∈ unitary A`.
* `IsStarProjection.mul_star_mul_eq_mul_mul_star`: `(x * p) * star (x * p) = x * p * star x`.
* `IsStarProjection.star_mul_mul_self_of_mem_unitary`: `star (u * p) * (u * p) = p` for `u`
  unitary.
* `Unitization.inr_snd_conj`, `Unitization.isStarProjection_snd_conj`: conjugating an `inr`-image
  star projection by a unitary in `Unitization R M` stays in `M` and remains a star projection.

## References

* M. Rørdam, F. Larsen, and N. Laustsen, *An Introduction to K-Theory for C⋆-Algebras*, Chapter 2,
  Lemma 2.1.4.
-/

public section

namespace IsStarProjection

section Semigroup

variable {A : Type*} [Semigroup A] [StarMul A] {p : A}

/-- For a star projection `p` and any `x`, `(x * p) * star (x * p) = x * p * star x`. -/
theorem mul_star_mul_eq_mul_mul_star (hp : IsStarProjection p) (x : A) :
    x * p * star (x * p) = x * p * star x := by
  rw [star_mul, hp.isSelfAdjoint.star_eq, mul_assoc x p, ← mul_assoc p p (star x),
    hp.isIdempotentElem.eq, ← mul_assoc]

end Semigroup

section Monoid

variable {A : Type*} [Monoid A] [StarMul A] {p u : A}

/-- For a star projection `p` and a unitary `u`, `star (u * p) * (u * p) = p`. -/
theorem star_mul_mul_self_of_mem_unitary (hp : IsStarProjection p) (hu : u ∈ unitary A) :
    star (u * p) * (u * p) = p := by
  rw [star_mul, hp.isSelfAdjoint.star_eq, mul_assoc p (star u) (u * p),
    ← mul_assoc (star u) u p, Unitary.star_mul_self_of_mem hu, one_mul, hp.isIdempotentElem.eq]

end Monoid

section NonAssocStarRing

variable {A : Type*} [NonAssocRing A] [StarRing A] {p : A}

/-- For a star projection `p`, the reflection `1 - 2 * p` is self-adjoint. -/
theorem isSelfAdjoint_one_sub_two_mul (hp : IsStarProjection p) : IsSelfAdjoint (1 - 2 * p) := by
  rw [two_mul]
  exact .sub (.one A) (hp.isSelfAdjoint.add hp.isSelfAdjoint)

end NonAssocStarRing

section StarRing

variable {A : Type*} [Ring A] [StarRing A] {p : A}

/-- For a star projection `p`, the reflection `1 - 2 * p` is a unitary element. -/
theorem one_sub_two_mul_mem_unitary (hp : IsStarProjection p) : 1 - 2 * p ∈ unitary A := by
  rw [← neg_sub (2 * p) 1, ← Unitary.coe_neg ⟨2 * p - 1, hp.two_mul_sub_one_mem_unitary⟩]
  exact SetLike.coe_mem _

end StarRing

end IsStarProjection

namespace Unitization

variable {R M : Type*} [CommSemiring R] [StarRing R] [NonUnitalSemiring M] [StarRing M]
  [Module R M]

/-- Conjugating `(x : Unitization R M)` by any `u : Unitization R M` has zero scalar part, so it
equals the `inr` image of its `.snd` component. -/
theorem inr_snd_conj (u : Unitization R M) (x : M) :
    ((u * (x : Unitization R M) * star u).snd : Unitization R M) =
      u * (x : Unitization R M) * star u :=
  inr_snd_of_fst_eq_zero (by simp [fst_mul, fst_inr])

/-- Conjugating an `inr`-embedded star projection `x` by a unitary `u` in `Unitization R M`
yields a star projection in `M` at `.snd`. -/
theorem isStarProjection_snd_conj [IsScalarTower R M M] [SMulCommClass R M M] [StarModule R M]
    {x : M} (hx : IsStarProjection x) {u : Unitization R M} (hu : u ∈ unitary (Unitization R M)) :
    IsStarProjection (u * (x : Unitization R M) * star u).snd := by
  have hprojU : IsStarProjection (u * (x : Unitization R M) * star u) := by
    have h := hx.inr.map (Unitary.conjStarAlgAut R (Unitization R M) ⟨u, hu⟩)
    rw [Unitary.conjStarAlgAut_apply] at h
    exact h
  rw [← inr_snd_conj u x] at hprojU
  exact hprojU.of_inr

end Unitization
