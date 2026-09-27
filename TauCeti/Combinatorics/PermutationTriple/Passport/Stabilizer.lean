/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.Passport.Count

/-!
# Stabilizers of generating triples

The normalizer of a passport's reference monodromy group acts on its generating triples.
Every generating triple has the same stabilizer: the centralizer of that reference group,
viewed as a subgroup of the normalizer. This identifies the common factor in the
orbit count used to compute passport sizes from generating-triple counts.

The result uses only the fact that the first two permutations generate the reference group;
no connectedness or admissibility hypothesis is needed.

## References

* S. K. Lando, A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, §1.5.
* M. Musty, S. Schiavone, J. Sijsling, J. Voight, *A database of Belyi maps*, §2.
-/

open Equiv MulAction

public section

namespace TauCeti

namespace PermutationTriple

variable {n : ℕ}

/-- The stabilizer of a triple under the normalizer of its monodromy group is the
centralizer of that group, regarded as a subgroup of the normalizer. -/
theorem stabilizer_normalizer (t : PermutationTriple n) :
    MulAction.stabilizer
        (Subgroup.normalizer (t.monodromyGroup : Set (Perm (Fin n)))) t =
      (Subgroup.centralizer (t.monodromyGroup : Set (Perm (Fin n)))).subgroupOf
        (Subgroup.normalizer (t.monodromyGroup : Set (Perm (Fin n)))) := by
  ext τ
  simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
  rw [← t.automorphismGroup_eq_centralizer_monodromyGroup]
  rw [PermutationTriple.mem_automorphismGroup_iff]
  simp only [Subgroup.smul_def]
  constructor
  · intro hfix
    exact ⟨by rw [← PermutationTriple.smul_σ0, hfix],
      by rw [← PermutationTriple.smul_σ1, hfix]⟩
  · intro hfix
    exact PermutationTriple.ext_of_two
      (by rw [PermutationTriple.smul_σ0, hfix.1])
      (by rw [PermutationTriple.smul_σ1, hfix.2])

end PermutationTriple

namespace PassportSpec

variable {n : ℕ} (P : PassportSpec n)

/-- The stabilizer of any generating triple under the normalizer action is the centralizer
of the reference monodromy group, regarded as a subgroup of its normalizer. -/
@[simp]
theorem stabilizer_generatingTriple (g : P.GeneratingTriple) :
    MulAction.stabilizer (Subgroup.normalizer (P.G : Set (Perm (Fin n)))) g =
      (Subgroup.centralizer (P.G : Set (Perm (Fin n)))).subgroupOf
        (Subgroup.normalizer (P.G : Set (Perm (Fin n)))) := by
  have h := g.1.stabilizer_normalizer
  rw [g.2.monodromyGroup_eq] at h
  rw [← h]
  ext τ
  simp only [MulAction.mem_stabilizer_iff]
  simpa only [GeneratingTriple.coe_smul, Subgroup.smul_def] using
    (Subtype.ext_iff : τ • g = g ↔ (τ • g).1 = g.1)

/-- Orbit-stabilizer for a generating triple, with its stabilizer expressed as the
centralizer of the reference monodromy group. -/
theorem card_orbit_generatingTriple_mul_card_centralizer (g : P.GeneratingTriple) :
    Nat.card (MulAction.orbit (Subgroup.normalizer (P.G : Set (Perm (Fin n)))) g) *
      Nat.card (Subgroup.centralizer (P.G : Set (Perm (Fin n)))) =
        Nat.card (Subgroup.normalizer (P.G : Set (Perm (Fin n)))) := by
  classical
  let N := Subgroup.normalizer (P.G : Set (Perm (Fin n)))
  let C := Subgroup.centralizer (P.G : Set (Perm (Fin n)))
  let : Fintype N := Fintype.ofFinite N
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group N g
  have hcard : Nat.card (C.subgroupOf N) = Nat.card C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.centralizer_le_normalizer
      (P.G : Set (Perm (Fin n))))).toEquiv
  have hstab : Nat.card (MulAction.stabilizer N g) = Nat.card C := by
    calc
      _ = Nat.card (C.subgroupOf N) :=
        congrArg (fun H : Subgroup N => Nat.card H) (stabilizer_generatingTriple P g)
      _ = Nat.card C := hcard
  have h' : Nat.card (MulAction.orbit N g) * Nat.card (MulAction.stabilizer N g) =
      Nat.card N := by simpa only [Nat.card_eq_fintype_card] using h
  simpa only [hstab] using h'

/-- The number of generating triples times the centralizer order equals the number of
normalizer orbits times the normalizer order. This is the exact division behind the
passport-size formula, independently of how the generating triples are counted. -/
theorem card_generatingTriple_mul_card_centralizer :
    Nat.card P.GeneratingTriple *
      Nat.card (Subgroup.centralizer (P.G : Set (Perm (Fin n)))) =
        Nat.card (MulAction.orbitRel.Quotient
          (Subgroup.normalizer (P.G : Set (Perm (Fin n)))) P.GeneratingTriple) *
          Nat.card (Subgroup.normalizer (P.G : Set (Perm (Fin n)))) := by
  classical
  let N := Subgroup.normalizer (P.G : Set (Perm (Fin n)))
  let Q := MulAction.orbitRel.Quotient N P.GeneratingTriple
  let : Fintype Q := Fintype.ofFinite Q
  have hdec : Nat.card P.GeneratingTriple =
      ∑ q : Q, Nat.card (MulAction.orbit N q.out) := by
    rw [Nat.card_congr (MulAction.selfEquivSigmaOrbits N P.GeneratingTriple), Nat.card_sigma]
  calc
    Nat.card P.GeneratingTriple * _ =
        (∑ q : Q, Nat.card (MulAction.orbit N q.out)) * _ := by rw [hdec]
    _ = ∑ q : Q, Nat.card N := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q _
      exact card_orbit_generatingTriple_mul_card_centralizer P q.out
    _ = Nat.card Q * Nat.card N := by simp

/-- The passport-size equation before division: each normalizer orbit has the same
centralizer stabilizer. -/
theorem passportSize_mul_card_normalizer (hn : n ≠ 0)
    (hG : IsPretransitive P.G (Fin n)) :
    P.passportSize * Nat.card (Subgroup.normalizer (P.G : Set (Perm (Fin n)))) =
      P.generatingTriples.card *
        Nat.card (Subgroup.centralizer (P.G : Set (Perm (Fin n)))) := by
  rw [P.passportSize_eq_card_generatingTripleOrbits hn hG,
    ← P.card_generatingTriples]
  exact P.card_generatingTriple_mul_card_centralizer.symm

/-- The normalizer order divides the number of generating triples weighted by the
centralizer order. -/
theorem card_normalizer_dvd_card_generatingTriples_mul_card_centralizer
    (hn : n ≠ 0) (hG : IsPretransitive P.G (Fin n)) :
    Nat.card (Subgroup.normalizer (P.G : Set (Perm (Fin n)))) ∣
      P.generatingTriples.card *
        Nat.card (Subgroup.centralizer (P.G : Set (Perm (Fin n)))) := by
  refine ⟨P.passportSize, ?_⟩
  simpa only [mul_comm] using (P.passportSize_mul_card_normalizer hn hG).symm

/-- The size of a passport is the number of generating triples, weighted by their
common centralizer stabilizer and divided by the order of the normalizer. -/
theorem passportSize_eq_card_generatingTriples_mul_card_centralizer_div_card_normalizer
    (hn : n ≠ 0) (hG : IsPretransitive P.G (Fin n)) :
    P.passportSize =
      P.generatingTriples.card *
        Nat.card (Subgroup.centralizer (P.G : Set (Perm (Fin n)))) /
          Nat.card (Subgroup.normalizer (P.G : Set (Perm (Fin n)))) := by
  have hN : 0 < Nat.card (Subgroup.normalizer (P.G : Set (Perm (Fin n)))) :=
    Nat.card_pos
  rw [← P.passportSize_mul_card_normalizer hn hG]
  simpa only [mul_comm] using (Nat.mul_div_cancel_left P.passportSize hN).symm

end PassportSpec

end TauCeti
