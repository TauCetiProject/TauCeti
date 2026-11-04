/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.D.TripledWeight

/-!
# Raising induction on the tripled D₄ weight diagram

If two tripled weights differ by a nonnegative integral combination of simple roots, a sequence
of simple raising steps joins the lower weight to the higher one. Consequently every predicate
stable under those steps is upward closed for the root order. The integrality condition matters:
weights in different minuscule summands must not be compared using the rational root cone alone.

This finite weight-diagram calculation lets raising-stable coordinate flags exclude all negative
root directions, not just negative simple-root directions.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §13.4.
-/

public section

open scoped Matrix

namespace TauCeti.DynkinType

-- This relation describes the three eight-vertex diagrams, each a chain with a middle diamond.
private def tripledRaisingPrecedes (a b : Fin 24) : Prop :=
  a.val / 8 = b.val / 8 ∧ b.val ≤ a.val ∧ ¬ (a.val % 8 = 4 ∧ b.val % 8 = 3)

private instance (a b : Fin 24) : Decidable (tripledRaisingPrecedes a b) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ ¬ (_ ∧ _)))

-- Twice the inverse Cartan matrix detects both positivity and membership in the root lattice.
private def twiceInverse : Matrix (Fin 4) (Fin 4) ℤ :=
  !![2, 2, 1, 1; 2, 4, 2, 2; 1, 2, 2, 1; 1, 2, 1, 2]

private theorem cartan_mul_twiceInverse : CartanMatrix.D 4 * twiceInverse = 2 • 1 := by
  rw [CartanMatrix.D_four]
  decide

private theorem vecMul_cartan_twiceInverse (c : Fin 4 → ℤ) :
    (c ᵥ* CartanMatrix.D 4) ᵥ* twiceInverse = 2 • c := by
  rw [Matrix.vecMul_vecMul, cartan_mul_twiceInverse, Matrix.vecMul_smul, Matrix.vecMul_one]

private theorem tripledRaisingPrecedes_of_sub_eq (a b : Fin 24) (c : Fin 4 → ℤ)
    (hc : ∀ i, 0 ≤ c i)
    (hab : d4TripledWeight b - d4TripledWeight a = c ᵥ* CartanMatrix.D 4) :
    tripledRaisingPrecedes a b := by
  have hcertificate : ∀ a b : Fin 24,
      (∀ i, 0 ≤ ((d4TripledWeight b - d4TripledWeight a) ᵥ* twiceInverse) i ∧
        ((d4TripledWeight b - d4TripledWeight a) ᵥ* twiceInverse) i % 2 = 0) →
      tripledRaisingPrecedes a b := by
    decide +kernel
  apply hcertificate a b
  rw [hab, vecMul_cartan_twiceInverse]
  intro i
  have hi : 0 ≤ c i + c i ∧ (c i + c i) % 2 = 0 := by
    have := hc i
    omega
  simpa only [Pi.smul_apply, two_smul] using hi

private theorem exists_raising_step (a b : Fin 24) (hab : tripledRaisingPrecedes a b)
    (hne : a ≠ b) :
    ∃ i : Fin 4, d4TripledWeight a i = -1 ∧
      tripledRaisingPrecedes (d4TripledReflection i a) b ∧
      (d4TripledReflection i a).val < a.val := by
  have hcertificate : ∀ a b : Fin 24, tripledRaisingPrecedes a b → a ≠ b →
      ∃ i : Fin 4, d4TripledWeight a i = -1 ∧
        tripledRaisingPrecedes (d4TripledReflection i a) b ∧
        (d4TripledReflection i a).val < a.val := by
    decide +kernel
  exact hcertificate a b hab hne

/-- A predicate on the tripled D₄ weights stable under simple raising steps is upward closed
under nonnegative integral combinations of the Bourbaki simple roots. -/
theorem d4TripledWeight_dominance_induction {P : Fin 24 → Prop}
    (hstep : ∀ (i : Fin 4) (a : Fin 24), d4TripledWeight a i = -1 →
      P a → P (d4TripledReflection i a))
    (a b : Fin 24) (c : Fin 4 → ℤ) (hc : ∀ i, 0 ≤ c i)
    (hab : d4TripledWeight b - d4TripledWeight a = c ᵥ* CartanMatrix.D 4)
    (ha : P a) : P b := by
  have hreach := tripledRaisingPrecedes_of_sub_eq a b c hc hab
  suffices ∀ a : Fin 24, tripledRaisingPrecedes a b → P a → P b from this a hreach ha
  intro a
  induction a using WellFoundedLT.induction with
  | ind a ih =>
    intro hab ha
    by_cases heq : a = b
    · exact heq ▸ ha
    · obtain ⟨i, hi, hib, hia⟩ := exists_raising_step a b hab heq
      exact ih (d4TripledReflection i a) hia hib (hstep i a hi ha)

end TauCeti.DynkinType
