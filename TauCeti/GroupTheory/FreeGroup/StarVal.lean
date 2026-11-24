/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Basic
public import TauCeti.GroupTheory.FreeGroup.Substitution

/-!
# Values of signed words in a monoid with involution

The signed words `List (α × Bool)` over an alphabet `α` form the free monoid with involution on
`α`: the involution is `FreeGroup.invRev`, which reverses a word and flips the signs, and the
morphisms into another such monoid are the letter-by-letter substitutions
`w.flatMap (FreeGroup.substituteLetter ψ)`.

A map `ρ : α → N` into a monoid `N` with an involution `star` extends to the signed words by
sending a negative letter to the `star` of the value of its generator (`FreeGroup.starVal`);
when `star` reverses products this is the morphism of monoids with involution extending `ρ`.
Values in a finite monoid with involution are how regular constraints on the words assigned to
the variables of an equation are recorded in [DJP16, §1.1]: a constraint becomes a condition on
the value of the word for a suitable `ρ`.

## Main definitions

* `FreeGroup.starVal`: the value of a signed word for a valuation of the generators.

## Main results

* `FreeGroup.starVal_invRev`: the value of the formal inverse is the `star` of the value.
* `FreeGroup.starVal_unique`: `starVal ρ` is the only map on signed words respecting the empty
  word, concatenation and formal inverses that sends each positive letter to the value of its
  generator.
* `FreeGroup.starVal_flatMap_substituteLetter`: values are compatible with substitution.
* `FreeGroup.starVal_eq_lift_mk`: in a group, for values whose `star` is their inverse, the
  value of a signed word is the image of the element of the free group it represents.

## References

* [DJP16] V. Diekert, A. Jez, W. Plandowski, *Finding all solutions of equations in free groups
  and monoids with involution*, Inform. and Comput. 251 (2016), 263–286; arXiv:1405.5133.
-/

public section

namespace FreeGroup

variable {α β N : Type*}

/-- The value of a signed word in a monoid with a `star` operation (an involution in the
intended applications), for a valuation `ρ` of the generators: a positive letter has the value of
its generator, a negative letter the `star` of that value, and a word the product of the values of
its letters. -/
def starVal [Monoid N] [Star N] (ρ : α → N) (w : List (α × Bool)) : N :=
  (w.map fun p => bif p.2 then ρ p.1 else star (ρ p.1)).prod

section Monoid

variable [Monoid N] [Star N] (ρ : α → N)

/-- The value of a signed word is the product of the values of its letters. -/
theorem starVal_def (w : List (α × Bool)) :
    starVal ρ w = (w.map fun p => bif p.2 then ρ p.1 else star (ρ p.1)).prod :=
  (rfl)

/-- The empty word has value `1`. -/
@[simp] theorem starVal_nil : starVal ρ ([] : List (α × Bool)) = 1 := by
  simp [starVal]

/-- The value of a concatenation is the product of the values. -/
@[simp] theorem starVal_append (u w : List (α × Bool)) :
    starVal ρ (u ++ w) = starVal ρ u * starVal ρ w := by
  simp [starVal]

/-- The value of a word beginning with a letter is the value of that letter times the value of
the rest of the word. -/
@[simp] theorem starVal_cons (p : α × Bool) (w : List (α × Bool)) :
    starVal ρ (p :: w) = (bif p.2 then ρ p.1 else star (ρ p.1)) * starVal ρ w := by
  simp [starVal]

/-- A positive letter has the value of its generator. -/
theorem starVal_singleton_true (a : α) : starVal ρ [(a, true)] = ρ a := by
  simp [starVal]

/-- A negative letter has the `star` of the value of its generator. -/
theorem starVal_singleton_false (a : α) : starVal ρ [(a, false)] = star (ρ a) := by
  simp [starVal]

variable {ρ} in
/-- Uniqueness of the value map: a map on signed words that sends the empty word to `1`,
concatenations to products, formal inverses to `star`s and each positive letter to the value of
its generator is `starVal ρ`. -/
theorem starVal_unique (f : List (α × Bool) → N) (hnil : f [] = 1)
    (happend : ∀ u w, f (u ++ w) = f u * f w) (hinvRev : ∀ w, f (invRev w) = star (f w))
    (htrue : ∀ a, f [(a, true)] = ρ a) : f = starVal ρ := by
  funext w
  induction w with
  | nil => simp [hnil]
  | cons p w ih =>
    rw [← List.singleton_append, happend, ih, starVal_append]
    obtain ⟨a, _ | _⟩ := p
    · simpa [invRev, htrue] using congrArg (· * starVal ρ w) (hinvRev [(a, true)])
    · simp [htrue]

end Monoid

section StarMul

variable [Monoid N] [StarMul N] (ρ : β → N)

/-- The value of the formal inverse of a word is the `star` of its value. -/
@[simp] theorem starVal_invRev (w : List (β × Bool)) :
    starVal ρ (invRev w) = star (starVal ρ w) := by
  induction w with
  | nil => simp
  | cons p w ih =>
    rw [invRev_cons, starVal_append, ih, starVal_cons, star_mul]
    obtain ⟨a, _ | _⟩ := p <;> simp [invRev]

/-- The value of a substituted word is the value of the word for the valuation that sends a
generator to the value of the word substituted for it. -/
theorem starVal_flatMap_substituteLetter (ψ : α → List (β × Bool)) (w : List (α × Bool)) :
    starVal ρ (w.flatMap (substituteLetter ψ)) = starVal (fun a => starVal ρ (ψ a)) w := by
  induction w with
  | nil => simp
  | cons p w ih =>
    obtain ⟨a, _ | _⟩ := p <;> simp [ih]

end StarMul

/-- For a valuation in a group whose values have their inverses as `star` (for instance when the
involution of the group is inversion), the value of a signed word is the image, under the
homomorphism from the free group extending the valuation, of the element of the free group that
the word represents. -/
theorem starVal_eq_lift_mk {G : Type*} [Group G] [Star G] {ρ : α → G}
    (hρ : ∀ a, star (ρ a) = (ρ a)⁻¹) (w : List (α × Bool)) : starVal ρ w = lift ρ (mk w) := by
  simp [starVal, lift_mk, hρ]

end FreeGroup
