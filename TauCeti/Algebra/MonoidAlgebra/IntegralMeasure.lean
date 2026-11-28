/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Analysis.Complex.Basic

/-!
# Integral measures on complex characters

A function on a set of characters is an integral measure if one finitely supported element of
`MonoidAlgebra R G` represents the function by evaluation at every character in the set.
When the coefficient subring is closed under complex conjugation and the characters are unitary,
conjugating coefficients and inverting basis elements represents complex conjugation.

## Main declarations

* `MonoidAlgebra.characterEval` evaluates a monoid-algebra element at a complex character.
* `MonoidAlgebra.IsIntegralMeasure` is closed under algebra operations, conjugation, and squared
  modulus.

## References

The integral-measure argument follows [ShortProof](https://github.com/lsernau/grh-lean) at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, in
`grh/src/New/OneLift/HeckeValues/AlgebraicPartIntegrality.lean`.
-/

public noncomputable section

namespace MonoidAlgebra

/-- Evaluate an `R`-coefficient monoid algebra at a unit-valued character. -/
def characterEval (R : Subring ℂ) {G : Type*} [Monoid G] (χ : G →* ℂˣ) :
    MonoidAlgebra R G →ₐ[R] ℂ :=
  MonoidAlgebra.lift R ℂ G ((Units.coeHom ℂ).comp χ)

/-- Evaluating one basis term multiplies its coefficient by the character value. -/
@[simp]
theorem characterEval_single (R : Subring ℂ) {G : Type*} [Monoid G]
    (χ : G →* ℂˣ) (g : G) (c : R) :
    characterEval R χ (MonoidAlgebra.single g c) = (c : ℂ) * (χ g : ℂ) := by
  rw [characterEval, MonoidAlgebra.lift_single, Algebra.smul_def]
  rfl

/-- Character evaluation is the sum of the weighted character values over the support. -/
theorem characterEval_apply (R : Subring ℂ) {G : Type*} [Monoid G]
    (χ : G →* ℂˣ) (μ : MonoidAlgebra R G) :
    characterEval R χ μ = μ.coeff.sum (fun g c ↦ (c : ℂ) * (χ g : ℂ)) :=
  MonoidAlgebra.lift_apply' _ _

/-- A character function is an integral measure if it is the evaluation of one integral
monoid-algebra element throughout `S`. -/
def IsIntegralMeasure (R : Subring ℂ) {G : Type*} [Monoid G]
    (S : Set (G →* ℂˣ)) (F : (G →* ℂˣ) → ℂ) : Prop :=
  ∃ μ : MonoidAlgebra R G, ∀ ϑ ∈ S, F ϑ = characterEval R ϑ μ

/-- An integral measure is represented by one monoid-algebra element on all of `S`. -/
theorem isIntegralMeasure_iff {R : Subring ℂ} {G : Type*} [Monoid G]
    {S : Set (G →* ℂˣ)} {F : (G →* ℂˣ) → ℂ} :
    IsIntegralMeasure R S F ↔
      ∃ μ : MonoidAlgebra R G, ∀ ϑ ∈ S, F ϑ = characterEval R ϑ μ :=
  (Iff.rfl)

/-- The zero character function is evaluation of the zero measure. -/
theorem IsIntegralMeasure.zero (R : Subring ℂ) {G : Type*} [Monoid G]
    (S : Set (G →* ℂˣ)) : IsIntegralMeasure R S 0 :=
  ⟨0, by intros; simp⟩

/-- The constant one character function is evaluation of the identity measure. -/
theorem IsIntegralMeasure.one (R : Subring ℂ) {G : Type*} [Monoid G]
    (S : Set (G →* ℂˣ)) : IsIntegralMeasure R S 1 :=
  ⟨1, by intros; simp⟩

/-- The sum of two integral measures is an integral measure. -/
theorem IsIntegralMeasure.add {R : Subring ℂ} {G : Type*} [Monoid G]
    {S : Set (G →* ℂˣ)} {F F' : (G →* ℂˣ) → ℂ}
    (hF : IsIntegralMeasure R S F) (hF' : IsIntegralMeasure R S F') :
    IsIntegralMeasure R S (F + F') := by
  obtain ⟨μ, hμ⟩ := hF
  obtain ⟨ν, hν⟩ := hF'
  refine ⟨μ + ν, fun ϑ hϑ ↦ ?_⟩
  rw [Pi.add_apply, hμ ϑ hϑ, hν ϑ hϑ, map_add]

/-- The negative of an integral measure is an integral measure. -/
theorem IsIntegralMeasure.neg {R : Subring ℂ} {G : Type*} [Monoid G]
    {S : Set (G →* ℂˣ)} {F : (G →* ℂˣ) → ℂ}
    (hF : IsIntegralMeasure R S F) : IsIntegralMeasure R S (-F) := by
  obtain ⟨μ, hμ⟩ := hF
  refine ⟨-μ, fun ϑ hϑ ↦ ?_⟩
  rw [Pi.neg_apply, hμ ϑ hϑ, map_neg]

/-- The difference of two integral measures is an integral measure. -/
theorem IsIntegralMeasure.sub {R : Subring ℂ} {G : Type*} [Monoid G]
    {S : Set (G →* ℂˣ)} {F F' : (G →* ℂˣ) → ℂ}
    (hF : IsIntegralMeasure R S F) (hF' : IsIntegralMeasure R S F') :
    IsIntegralMeasure R S (F - F') := by
  simpa only [sub_eq_add_neg] using hF.add hF'.neg

/-- The pointwise product of integral measures is an integral measure. -/
theorem IsIntegralMeasure.mul {R : Subring ℂ} {G : Type*} [Monoid G]
    {S : Set (G →* ℂˣ)} {F F' : (G →* ℂˣ) → ℂ}
    (hF : IsIntegralMeasure R S F) (hF' : IsIntegralMeasure R S F') :
    IsIntegralMeasure R S (F * F') := by
  obtain ⟨μ, hμ⟩ := hF
  obtain ⟨ν, hν⟩ := hF'
  refine ⟨μ * ν, fun ϑ hϑ ↦ ?_⟩
  rw [Pi.mul_apply, hμ ϑ hϑ, hν ϑ hϑ, map_mul]

/-- A natural power of an integral measure is an integral measure. -/
theorem IsIntegralMeasure.pow {R : Subring ℂ} {G : Type*} [Monoid G]
    {S : Set (G →* ℂˣ)} {F : (G →* ℂˣ) → ℂ}
    (hF : IsIntegralMeasure R S F) (n : ℕ) : IsIntegralMeasure R S (F ^ n) := by
  obtain ⟨μ, hμ⟩ := hF
  refine ⟨μ ^ n, fun ϑ hϑ ↦ ?_⟩
  rw [Pi.pow_apply, hμ ϑ hϑ, map_pow]

/-- A finite sum of integral measures is an integral measure. -/
theorem IsIntegralMeasure.sum {R : Subring ℂ} {G : Type*} [Monoid G]
    {S : Set (G →* ℂˣ)} {ι : Type*} (t : Finset ι)
    {F : ι → (G →* ℂˣ) → ℂ} (hF : ∀ i ∈ t, IsIntegralMeasure R S (F i)) :
    IsIntegralMeasure R S (∑ i ∈ t, F i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using IsIntegralMeasure.zero R S
  | @insert a t ha ih =>
    rw [Finset.sum_insert ha]
    exact (hF a (Finset.mem_insert_self a t)).add
      (ih fun i hi ↦ hF i (Finset.mem_insert_of_mem hi))

/-- A finite product of integral measures is an integral measure. -/
theorem IsIntegralMeasure.prod {R : Subring ℂ} {G : Type*} [Monoid G]
    {S : Set (G →* ℂˣ)} {ι : Type*} (t : Finset ι)
    {F : ι → (G →* ℂˣ) → ℂ} (hF : ∀ i ∈ t, IsIntegralMeasure R S (F i)) :
    IsIntegralMeasure R S (∏ i ∈ t, F i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using IsIntegralMeasure.one R S
  | @insert a t ha ih =>
    rw [Finset.prod_insert ha]
    exact (hF a (Finset.mem_insert_self a t)).mul
      (ih fun i hi ↦ hF i (Finset.mem_insert_of_mem hi))

/-- Conjugate the coefficients and invert the basis elements of a group-algebra element. -/
private def conjugateMeasure {G : Type*} [Group G] (R : Subring ℂ)
    (hR : ∀ z ∈ R, star z ∈ R) (μ : MonoidAlgebra R G) : MonoidAlgebra R G :=
  MonoidAlgebra.mapDomain (Equiv.inv G)
    (MonoidAlgebra.mapRingHom G ((starRingEnd ℂ).restrict R R hR) μ)

/-- Evaluation of the conjugated measure is the conjugate of evaluation on unitary characters. -/
private theorem characterEval_conjugateMeasure {G : Type*} [Group G]
    (R : Subring ℂ) (hR : ∀ z ∈ R, star z ∈ R) (χ : G →* ℂˣ)
    (hχ : ∀ u, ‖(χ u : ℂ)‖ = 1) (μ : MonoidAlgebra R G) :
    characterEval R χ (conjugateMeasure R hR μ) = star (characterEval R χ μ) := by
  induction μ using MonoidAlgebra.induction_linear with
  | zero => simp [conjugateMeasure]
  | add μ ν hμ hν =>
    have hadd : conjugateMeasure R hR (μ + ν) =
        conjugateMeasure R hR μ + conjugateMeasure R hR ν := by
      simp [conjugateMeasure, MonoidAlgebra.mapDomain_add]
    rw [hadd]
    simp only [map_add, hμ, hν, Complex.star_def]
  | single g c =>
    simp [conjugateMeasure, map_inv, Complex.inv_eq_conj (hχ g)]

/-- Conjugation of an integral measure is an integral measure on unitary characters. -/
theorem IsIntegralMeasure.conj {R : Subring ℂ} {G : Type*} [Group G]
    {S : Set (G →* ℂˣ)} {F : (G →* ℂˣ) → ℂ}
    (hR : ∀ z ∈ R, star z ∈ R) (hS : ∀ ϑ ∈ S, ∀ u, ‖(ϑ u : ℂ)‖ = 1)
    (hF : IsIntegralMeasure R S F) : IsIntegralMeasure R S (star F) := by
  obtain ⟨μ, hμ⟩ := hF
  refine ⟨conjugateMeasure R hR μ, fun ϑ hϑ ↦ ?_⟩
  rw [Pi.star_apply, hμ ϑ hϑ, characterEval_conjugateMeasure R hR ϑ (hS ϑ hϑ)]

/-- Squared modulus of an integral measure is an integral measure on unitary characters. -/
theorem IsIntegralMeasure.norm_sq {R : Subring ℂ} {G : Type*} [Group G]
    {S : Set (G →* ℂˣ)} {F : (G →* ℂˣ) → ℂ}
    (hR : ∀ z ∈ R, star z ∈ R) (hS : ∀ ϑ ∈ S, ∀ u, ‖(ϑ u : ℂ)‖ = 1)
    (hF : IsIntegralMeasure R S F) :
    IsIntegralMeasure R S (fun ϑ ↦ (‖F ϑ‖ : ℂ) ^ 2) := by
  obtain ⟨μ, hμ⟩ := hF
  refine ⟨μ * conjugateMeasure R hR μ, fun ϑ hϑ ↦ ?_⟩
  rw [map_mul, characterEval_conjugateMeasure R hR ϑ (hS ϑ hϑ), ← hμ ϑ hϑ]
  simpa only [Complex.star_def] using (Complex.mul_conj' (F ϑ)).symm

end MonoidAlgebra
