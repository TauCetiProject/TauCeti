/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Star.StarPolynomial
public import TauCeti.Probability.FreeProbability.Distribution.Basic

/-!
# Star distributions

The star distribution of a family `a` in a star algebra with a linear functional `φ` is the
functional `p ↦ φ (p(a))` on noncommutative star polynomials. It records the moments of all
ordered words in the variables and their adjoints, and it is exactly the joint algebraic
distribution of the doubled family `StarPolynomial.withStar a` of the variables and their
adjoints. Equality of star distributions is therefore equivalent to equality of all these word
moments, including the empty word.

The transport formulas parallel those for joint distributions: star algebra homomorphisms,
relabeling and subfamilies, and substitution of star polynomials. In particular, equal star
distributions remain equal after evaluating the same family of star polynomials. The star
distribution determines the joint algebraic distribution, and for two functionals on the same
algebra it is equivalent to agreement on the generated star subalgebra.

No positivity is built in: a functional that commutes with `star`, or is nonnegative on
elements `star x * x`, transfers that property to its star distributions.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 1.
-/

public section

namespace TauCeti

open StarPolynomial

variable {R A B ι κ : Type*} [CommSemiring R] [StarRing R]
  [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]
  [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]

/-- The star distribution of `a` with respect to `φ`: evaluate a star polynomial at `a`, then
apply `φ`. Normalization and positivity are separate conditions. -/
noncomputable def starDistribution (φ : A →ₗ[R] R) (a : ι → A) :
    StarPolynomial R ι →ₗ[R] R :=
  φ.comp (lift (R := R) a : StarPolynomial R ι →ₐ[R] A).toLinearMap

/-- A star distribution is the pullback of the functional along star polynomial evaluation. -/
theorem starDistribution_def (φ : A →ₗ[R] R) (a : ι → A) :
    starDistribution φ a =
      φ.comp (lift (R := R) a : StarPolynomial R ι →ₐ[R] A).toLinearMap :=
  (rfl)

@[simp]
theorem starDistribution_apply (φ : A →ₗ[R] R) (a : ι → A) (p : StarPolynomial R ι) :
    starDistribution φ a p = φ (lift a p) := (rfl)

/-- The star distribution of `a` is the joint algebraic distribution of the variables and their
adjoints, read through the identification of star polynomials with the free algebra. -/
theorem starDistribution_eq_jointDistribution_comp (φ : A →ₗ[R] R) (a : ι → A) :
    starDistribution φ a =
      (jointDistribution φ (withStar a)).comp (toFreeAlgebra R ι).toLinearMap := by
  ext p
  simp [lift_apply]

/-- Evaluating the star distribution on a word in the generators gives the ordered moment of
the corresponding word in the variables and their adjoints. For the empty word this is
`φ 1`. -/
theorem starDistribution_list_prod (φ : A →ₗ[R] R) (a : ι → A) (w : List (ι × Bool)) :
    starDistribution φ a (w.map (withStar (X (R := R)))).prod = φ (w.map (withStar a)).prod := by
  simp [map_list_prod, List.map_map, Function.comp_def]

/-- A star distribution is determined by the moments of all words in the variables and their
adjoints, including the empty word. The two families may live in different algebras. -/
theorem starDistribution_eq_iff {φ : A →ₗ[R] R} {ψ : B →ₗ[R] R} {a : ι → A} {b : ι → B} :
    starDistribution φ a = starDistribution ψ b ↔
      ∀ w : List (ι × Bool), φ (w.map (withStar a)).prod = ψ (w.map (withStar b)).prod := by
  rw [starDistribution_eq_jointDistribution_comp, starDistribution_eq_jointDistribution_comp,
    (toFreeAlgebra R ι).surjective.injective_linearMapComp_right.eq_iff,
    jointDistribution_eq_iff]

/-- Evaluating the formal variables recovers the original functional on star polynomials. -/
@[simp]
theorem starDistribution_X (φ : StarPolynomial R ι →ₗ[R] R) :
    starDistribution φ (X (R := R) (ι := ι)) = φ := by
  ext p
  simp

/-- Pulling a functional back along a star algebra homomorphism is equivalent to mapping the
family forward. -/
theorem starDistribution_map (φ : B →ₗ[R] R) (f : A →⋆ₐ[R] B) (a : ι → A) :
    starDistribution (φ.comp (f : A →ₐ[R] B).toLinearMap) a = starDistribution φ (f ∘ a) := by
  ext p
  simp [← comp_lift f a]

/-- The star distribution of a family obtained by evaluating star polynomials is obtained by
applying the same substitution to the star distribution. -/
theorem starDistribution_subst (φ : A →ₗ[R] R) (a : ι → A) (p : κ → StarPolynomial R ι) :
    starDistribution φ (fun j => lift a (p j)) =
      starDistribution (starDistribution φ a) p := by
  simpa only [starDistribution_def, Function.comp_def] using
    (starDistribution_map φ (lift a) p).symm

/-- Relabeling, including restriction to a subfamily, is pullback by the corresponding
substitution of variables. The label map need not be injective. -/
theorem starDistribution_comp (φ : A →ₗ[R] R) (a : ι → A) (r : κ → ι) :
    starDistribution φ (a ∘ r) = starDistribution (starDistribution φ a) (X ∘ r) := by
  simpa [Function.comp_def] using starDistribution_subst φ a (X ∘ r)

/-- Equality of star distributions is preserved by evaluating any family of star
polynomials. -/
theorem starDistribution_subst_eq {φ : A →ₗ[R] R} {ψ : B →ₗ[R] R} {a : ι → A} {b : ι → B}
    (h : starDistribution φ a = starDistribution ψ b) (p : κ → StarPolynomial R ι) :
    starDistribution φ (fun j => lift a (p j)) =
      starDistribution ψ (fun j => lift b (p j)) := by
  rw [starDistribution_subst, starDistribution_subst, h]

/-- Equal star distributions have equal star distributions on every relabeled family,
including every subfamily. -/
theorem starDistribution_comp_eq {φ : A →ₗ[R] R} {ψ : B →ₗ[R] R} {a : ι → A} {b : ι → B}
    (h : starDistribution φ a = starDistribution ψ b) (r : κ → ι) :
    starDistribution φ (a ∘ r) = starDistribution ψ (b ∘ r) := by
  rw [starDistribution_comp φ a r, starDistribution_comp ψ b r, h]

/-- The joint algebraic distribution is the restriction of the star distribution to
polynomials without adjoints. -/
theorem jointDistribution_eq_starDistribution_comp (φ : A →ₗ[R] R) (a : ι → A) :
    jointDistribution φ a =
      (starDistribution φ a).comp (ofFreeAlgebra R ι).toLinearMap := by
  ext p
  simp

/-- Equal star distributions have equal joint algebraic distributions. -/
theorem jointDistribution_eq_of_starDistribution_eq {φ : A →ₗ[R] R} {ψ : B →ₗ[R] R}
    {a : ι → A} {b : ι → B} (h : starDistribution φ a = starDistribution ψ b) :
    jointDistribution φ a = jointDistribution ψ b := by
  rw [jointDistribution_eq_starDistribution_comp, jointDistribution_eq_starDistribution_comp, h]

/-- Two functionals have the same star distribution on a family exactly when they agree on the
star subalgebra generated by that family. -/
theorem starDistribution_eq_iff_eqOn_adjoin {φ ψ : A →ₗ[R] R} {a : ι → A} :
    starDistribution φ a = starDistribution ψ a ↔
      Set.EqOn φ ψ (StarAlgebra.adjoin R (Set.range a)) := by
  rw [← range_lift (R := R)]
  constructor
  · rintro h x ⟨p, rfl⟩
    simpa using LinearMap.congr_fun h p
  · intro h
    ext p
    simpa using h ⟨p, rfl⟩

/-- A functional commuting with `star` has star distributions commuting with `star`. -/
theorem starDistribution_star {φ : A →ₗ[R] R} (hφ : ∀ x, φ (star x) = star (φ x))
    (a : ι → A) (p : StarPolynomial R ι) :
    starDistribution φ a (star p) = star (starDistribution φ a p) := by
  simp [map_star, hφ]

/-- A functional that is nonnegative on every `star x * x` has star distributions with the
same property. -/
theorem starDistribution_star_mul_self_nonneg [PartialOrder R] {φ : A →ₗ[R] R}
    (hφ : ∀ x, 0 ≤ φ (star x * x)) (a : ι → A) (p : StarPolynomial R ι) :
    0 ≤ starDistribution φ a (star p * p) := by
  simpa [map_star] using hφ (lift a p)

end TauCeti
