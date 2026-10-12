/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.Passport.Count
public import TauCeti.Combinatorics.PermutationTriple.Passport.Stabilizer

/-!
# The normalizer formula for passport size

The normalizer of a passport's reference monodromy group acts on its generating triples.
Every stabilizer is the centralizer, so every orbit has the same size. Counting the generating
triples by orbits gives an exact division formula for the number of isomorphism classes in the
passport in terms of the finite set of generating triples. The divisibility statement makes the
natural-number quotient meaningful. A separate generating-triple count can evaluate the
finite-set cardinality to obtain a formula in terms of cycle data.

## References

* S. K. Lando, A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, §1.5.
* M. Musty, S. Schiavone, J. Sijsling, J. Voight, *A database of Belyi maps*, §2.
-/

open Equiv MulAction

public section

namespace TauCeti

namespace PassportSpec

variable {n : ℕ} (P : PassportSpec n)

/-- Counting generating triples orbit by orbit: the number of normalizer orbits times the
normalizer order equals the number of generating triples times the centralizer order. -/
theorem
  card_generatingTripleOrbits_mul_card_normalizer_eq_card_generatingTriple_mul_card_centralizer :
    Nat.card (orbitRel.Quotient
        (Subgroup.normalizer (P.G : Set (Perm (Fin n)))) P.GeneratingTriple) *
      Nat.card (Subgroup.normalizer (P.G : Set (Perm (Fin n)))) =
      Nat.card P.GeneratingTriple *
        Nat.card (Subgroup.centralizer (P.G : Set (Perm (Fin n)))) := by
  classical
  let N := Subgroup.normalizer (P.G : Set (Perm (Fin n)))
  let C := Subgroup.centralizer (P.G : Set (Perm (Fin n)))
  let Ω := orbitRel.Quotient N P.GeneratingTriple
  let _ : Fintype Ω := Fintype.ofFinite Ω
  let _ : Fintype P.GeneratingTriple := Fintype.ofFinite P.GeneratingTriple
  have horbit (ω : Ω) : Nat.card (orbit N ω.out) * Nat.card C = Nat.card N :=
    P.card_orbit_generatingTriple_mul_card_centralizer_eq_card_normalizer ω.out
  have hsum : Nat.card P.GeneratingTriple =
      ∑ ω : Ω, Nat.card (orbit N ω.out) := by
    calc
      Nat.card P.GeneratingTriple =
          Nat.card (Σ ω : Ω, orbit N ω.out) :=
        Nat.card_congr (selfEquivSigmaOrbits N P.GeneratingTriple)
      _ = ∑ ω : Ω, Nat.card (orbit N ω.out) := by
        simp only [Nat.card_eq_fintype_card, Fintype.card_sigma]
  rw [hsum]
  simp only [Nat.card_eq_fintype_card] at *
  rw [Finset.sum_mul]
  -- Expose the local names for the normalizer and centralizer so the pointwise formula matches.
  change Fintype.card Ω * Fintype.card N =
    ∑ ω : Ω, Fintype.card (orbit N ω.out) * Fintype.card C
  simp only [horbit, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp

/-- Counting generating triples orbit by orbit: the number of passport classes times the
normalizer order equals the number of generating triples times the centralizer order. -/
theorem passportSize_mul_card_normalizer_eq_card_generatingTriple_mul_card_centralizer
    (hn : n ≠ 0)
    (hG : IsPretransitive P.G (Fin n)) :
    P.passportSize * Nat.card (Subgroup.normalizer (P.G : Set (Perm (Fin n)))) =
      Nat.card P.GeneratingTriple *
        Nat.card (Subgroup.centralizer (P.G : Set (Perm (Fin n)))) := by
  rw [P.passportSize_eq_card_generatingTripleOrbits hn hG]
  exact
    P.card_generatingTripleOrbits_mul_card_normalizer_eq_card_generatingTriple_mul_card_centralizer

/-- The normalizer order divides the product of the generating-triple count and the
centralizer order. -/
theorem card_normalizer_dvd_card_generatingTriple_mul_card_centralizer :
    Nat.card (Subgroup.normalizer (P.G : Set (Perm (Fin n)))) ∣
      Nat.card P.GeneratingTriple *
        Nat.card (Subgroup.centralizer (P.G : Set (Perm (Fin n)))) := by
  refine ⟨Nat.card (orbitRel.Quotient
    (Subgroup.normalizer (P.G : Set (Perm (Fin n)))) P.GeneratingTriple), ?_⟩
  have h :=
    P.card_generatingTripleOrbits_mul_card_normalizer_eq_card_generatingTriple_mul_card_centralizer
  simpa only [mul_comm] using h.symm

/-- The passport-size formula in terms of the generating-triple finset: its elements form equal
normalizer orbits, each having normalizer order divided by centralizer order elements. -/
theorem passportSize_eq_card_generatingTriples_mul_card_centralizer_div_card_normalizer
    (hn : n ≠ 0)
    (hG : IsPretransitive P.G (Fin n)) :
    P.passportSize =
      P.generatingTriples.card *
        Nat.card (Subgroup.centralizer (P.G : Set (Perm (Fin n)))) /
          Nat.card (Subgroup.normalizer (P.G : Set (Perm (Fin n)))) := by
  rw [← P.card_generatingTriples]
  rw [← P.passportSize_mul_card_normalizer_eq_card_generatingTriple_mul_card_centralizer
    hn hG]
  exact (Nat.mul_div_cancel P.passportSize
    (Nat.card_pos (α := Subgroup.normalizer (P.G : Set (Perm (Fin n)))))).symm

end PassportSpec

end TauCeti
