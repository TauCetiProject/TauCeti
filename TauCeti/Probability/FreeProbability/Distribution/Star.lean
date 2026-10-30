/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Pi
public import TauCeti.Algebra.Star.StarPolynomial
public import TauCeti.Probability.FreeProbability.Distribution.Basic

/-!
# Joint *-distributions

The *-distribution of a family `a : ι → A` in a star algebra with a linear functional `φ` is the
functional on noncommutative *-polynomials obtained by evaluation,
`p ↦ φ (StarPolynomial.lift a p)`. It records every ordered moment of the family and its adjoints,
`φ (b₁ ⋯ bₙ)` with each `bⱼ` some `a i` or `star (a i)`, and not only the moments of the algebraic
joint distribution, which never sees an adjoint.

Through the letters `StarPolynomial.letter a`, which list the family together with its adjoints,
the *-distribution is the algebraic joint distribution of the doubled family `letter a`. Equality
of *-distributions is therefore equivalent to equality of all ordered *-moments, including the
empty word, and the families may live in different star algebras. The transport formulas cover
star algebra homomorphisms, relabeling and subfamilies, adjoints, and arbitrary *-polynomial
substitutions; in particular, equal *-distributions remain equal after applying the same family of
*-polynomials. For two functionals on the same algebra, equality of *-distributions is equivalent
to agreement on the generated unital star subalgebra.

A *-distribution restricts to the joint distribution on the polynomials without adjoints. For
selfadjoint families the two carry the same information. Positivity `0 ≤ φ (star x * x)` and
traciality of `φ` are inherited by the *-distribution; normalization is separate, as the value on
`1` is `φ 1`.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 4.
-/

public section

namespace TauCeti

open StarPolynomial

variable {R A B ι κ : Type*} [CommSemiring R] [StarRing R]
  [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]
  [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]

/-- The joint *-distribution of `a` with respect to `φ`: evaluate a noncommutative *-polynomial
at `a`, then apply `φ`. Normalization, positivity and traciality are separate conditions. -/
noncomputable def starDistribution (φ : A →ₗ[R] R) (a : ι → A) :
    StarPolynomial R ι →ₗ[R] R :=
  φ.comp (lift a).toLinearMap

/-- A *-distribution is the pullback of the functional along *-polynomial evaluation. -/
theorem starDistribution_def (φ : A →ₗ[R] R) (a : ι → A) :
    starDistribution φ a = φ.comp (lift a).toLinearMap := (rfl)

@[simp]
theorem starDistribution_apply (φ : A →ₗ[R] R) (a : ι → A) (p : StarPolynomial R ι) :
    starDistribution φ a p = φ (lift a p) := (rfl)

/-- The *-distribution of `a` is the joint distribution of its letters, the family `a`
together with its adjoints, read through the identification of the star polynomials with the free
algebra on the letters. -/
theorem starDistribution_eq_comp_toFreeAlgebra (φ : A →ₗ[R] R) (a : ι → A) :
    starDistribution φ a =
      (jointDistribution φ (letter a)).comp (toFreeAlgebra R ι).toLinearMap := by
  ext p
  simp [lift_apply]

/-- Evaluating the *-distribution on a word in the generators and their adjoints gives its
ordered moment. For the empty word this is `φ 1`. -/
theorem starDistribution_list_prod_letter (φ : A →ₗ[R] R) (a : ι → A) (w : List (ι × Bool)) :
    starDistribution φ a (w.map (letter X)).prod = φ (w.map (letter a)).prod := by
  simp [map_list_prod, List.map_map, Function.comp_def]

/-- Two families have the same *-distribution exactly when their letters, the families together
with their adjoints, have the same joint distribution. -/
theorem starDistribution_eq_iff_jointDistribution_letter_eq {φ : A →ₗ[R] R} {ψ : B →ₗ[R] R}
    {a : ι → A} {b : ι → B} :
    starDistribution φ a = starDistribution ψ b ↔
      jointDistribution φ (letter a) = jointDistribution ψ (letter b) := by
  rw [starDistribution_eq_comp_toFreeAlgebra, starDistribution_eq_comp_toFreeAlgebra]
  exact (LinearMap.cancel_right (toFreeAlgebra R ι).surjective).trans Iff.rfl

/-- A *-distribution is determined by all its ordered *-moments, including the empty word.
The two families may live in different star algebras. -/
theorem starDistribution_eq_iff {φ : A →ₗ[R] R} {ψ : B →ₗ[R] R} {a : ι → A} {b : ι → B} :
    starDistribution φ a = starDistribution ψ b ↔
      ∀ w : List (ι × Bool), φ (w.map (letter a)).prod = ψ (w.map (letter b)).prod := by
  rw [starDistribution_eq_iff_jointDistribution_letter_eq, jointDistribution_eq_iff]

/-- Evaluating the formal generators recovers the original *-polynomial functional. -/
@[simp]
theorem starDistribution_X (φ : StarPolynomial R ι →ₗ[R] R) :
    starDistribution φ X = φ := by
  ext p
  simp

/-- Pulling a functional back along a star algebra homomorphism is equivalent to mapping the
family forward. This also gives transport along star algebra equivalences. -/
theorem starDistribution_map (φ : B →ₗ[R] R) (f : A →⋆ₐ[R] B) (a : ι → A) :
    starDistribution (φ.comp f.toLinearMap) a = starDistribution φ (f ∘ a) := by
  ext p
  simpa using congrArg φ (DFunLike.congr_fun (comp_lift f a) p)

/-- The *-distribution of a family of *-polynomials in `a` is obtained by applying the same
substitution to the *-distribution of `a`. -/
theorem starDistribution_subst (φ : A →ₗ[R] R) (a : ι → A) (p : κ → StarPolynomial R ι) :
    starDistribution φ (fun j ↦ lift a (p j)) = starDistribution (starDistribution φ a) p :=
  (starDistribution_map φ (lift a) p).symm

/-- Relabeling, including restriction to a subfamily, is pullback by the corresponding map of
star polynomials. The label map need not be injective. -/
theorem starDistribution_comp (φ : A →ₗ[R] R) (a : ι → A) (r : κ → ι) :
    starDistribution φ (a ∘ r) = starDistribution (starDistribution φ a) (X ∘ r) := by
  simpa [Function.comp_def] using starDistribution_subst φ a (X ∘ r)

/-- The *-distribution of the adjoint family is obtained from that of the family by substituting
the formal adjoints for the generators. -/
theorem starDistribution_star (φ : A →ₗ[R] R) (a : ι → A) :
    starDistribution φ (star a) =
      starDistribution (starDistribution φ a) (star (X (R := R))) := by
  simpa [Pi.star_def] using starDistribution_subst φ a (star X)

/-- Equality of *-distributions is preserved by evaluating any family of *-polynomials. -/
theorem starDistribution_subst_eq {φ : A →ₗ[R] R} {ψ : B →ₗ[R] R} {a : ι → A} {b : ι → B}
    (h : starDistribution φ a = starDistribution ψ b) (p : κ → StarPolynomial R ι) :
    starDistribution φ (fun j ↦ lift a (p j)) = starDistribution ψ (fun j ↦ lift b (p j)) := by
  rw [starDistribution_subst, starDistribution_subst, h]

/-- Equal *-distributions have equal *-distributions on every relabeled family, including every
subfamily. -/
theorem starDistribution_comp_eq {φ : A →ₗ[R] R} {ψ : B →ₗ[R] R} {a : ι → A} {b : ι → B}
    (h : starDistribution φ a = starDistribution ψ b) (r : κ → ι) :
    starDistribution φ (a ∘ r) = starDistribution ψ (b ∘ r) := by
  rw [starDistribution_comp φ a r, starDistribution_comp ψ b r, h]

/-- A surjective relabeling loses no information about the *-distribution. -/
theorem starDistribution_comp_eq_iff {φ : A →ₗ[R] R} {ψ : B →ₗ[R] R} {a : ι → A} {b : ι → B}
    {r : κ → ι} (hr : Function.Surjective r) :
    starDistribution φ (a ∘ r) = starDistribution ψ (b ∘ r) ↔
      starDistribution φ a = starDistribution ψ b := by
  classical
  refine ⟨fun h ↦ ?_, fun h ↦ starDistribution_comp_eq h r⟩
  have h' := starDistribution_comp_eq h (Function.surjInv hr)
  simpa [Function.comp_def, Function.surjInv_eq] using h'

/-- Two families have the same *-distribution exactly when their adjoint families do. -/
theorem starDistribution_star_eq_iff {φ : A →ₗ[R] R} {ψ : B →ₗ[R] R} {a : ι → A} {b : ι → B} :
    starDistribution φ (star a) = starDistribution ψ (star b) ↔
      starDistribution φ a = starDistribution ψ b := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [starDistribution_star φ a, starDistribution_star ψ b, h]⟩
  rw [← star_star a, ← star_star b, starDistribution_star φ (star a),
    starDistribution_star ψ (star b), h]

/-- Two functionals have the same *-distribution on a family exactly when they agree on the
unital star subalgebra generated by that family. -/
theorem starDistribution_eq_iff_eqOn_adjoin {φ ψ : A →ₗ[R] R} {a : ι → A} :
    starDistribution φ a = starDistribution ψ a ↔
      Set.EqOn φ ψ (StarAlgebra.adjoin R (Set.range a)) := by
  rw [← range_lift]
  constructor
  · rintro h _ ⟨p, rfl⟩
    exact LinearMap.congr_fun h p
  · intro h
    ext p
    exact h ⟨p, rfl⟩

/-- On the polynomials without adjoints, a *-distribution is the joint distribution. -/
@[simp]
theorem starDistribution_comp_ofFreeAlgebra (φ : A →ₗ[R] R) (a : ι → A) :
    (starDistribution φ a).comp (ofFreeAlgebra R ι).toLinearMap = jointDistribution φ a := by
  ext p
  simp

/-- Equal *-distributions have equal joint distributions. -/
theorem jointDistribution_eq_of_starDistribution_eq {φ : A →ₗ[R] R} {ψ : B →ₗ[R] R}
    {a : ι → A} {b : ι → B} (h : starDistribution φ a = starDistribution ψ b) :
    jointDistribution φ a = jointDistribution ψ b := by
  rw [← starDistribution_comp_ofFreeAlgebra, h, starDistribution_comp_ofFreeAlgebra]

/-- For selfadjoint families the *-distribution carries no more information than the joint
distribution. -/
theorem starDistribution_eq_iff_jointDistribution_eq {φ : A →ₗ[R] R} {ψ : B →ₗ[R] R}
    {a : ι → A} {b : ι → B} (ha : ∀ i, IsSelfAdjoint (a i)) (hb : ∀ i, IsSelfAdjoint (b i)) :
    starDistribution φ a = starDistribution ψ b ↔ jointDistribution φ a = jointDistribution ψ b :=
  ⟨jointDistribution_eq_of_starDistribution_eq, fun h ↦ by
    rw [starDistribution_eq_iff_jointDistribution_letter_eq, letter_eq_comp_fst ha,
      letter_eq_comp_fst hb]
    exact jointDistribution_comp_eq h Prod.fst⟩

/-- The *-distribution of a positive functional is positive. -/
theorem starDistribution_star_mul_self_nonneg [PartialOrder R] {φ : A →ₗ[R] R}
    (hφ : ∀ x, 0 ≤ φ (star x * x)) (a : ι → A) (p : StarPolynomial R ι) :
    0 ≤ starDistribution φ a (star p * p) := by
  rw [starDistribution_apply, map_mul, map_star]
  exact hφ (lift a p)

/-- The *-distribution of a tracial functional is tracial. -/
theorem starDistribution_mul_comm {φ : A →ₗ[R] R} (hφ : ∀ x y, φ (x * y) = φ (y * x))
    (a : ι → A) (p q : StarPolynomial R ι) :
    starDistribution φ a (p * q) = starDistribution φ a (q * p) := by
  simpa using hφ (lift a p) (lift a q)

end TauCeti
