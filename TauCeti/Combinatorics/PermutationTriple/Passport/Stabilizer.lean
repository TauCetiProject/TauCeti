/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.Passport.Normalizer

/-!
# Stabilizers of generating triples

The normalizer of a passport's reference monodromy group acts on its generating triples.
Every generating triple has the same stabilizer: the centralizer of that reference group,
viewed as a subgroup of the normalizer. Orbit-stabilizer then gives the size of each orbit.
This per-orbit equation uses no total generating-triple count.

The result uses only the fact that the first two permutations generate the reference group;
no connectedness or admissibility hypothesis is needed.

## References

* S. K. Lando, A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, §1.5.
* M. Musty, S. Schiavone, J. Sijsling, J. Voight, *A database of Belyi maps*, §2.
-/

open Equiv MulAction

public section

namespace TauCeti

namespace PassportSpec

variable {n : ℕ} (P : PassportSpec n)

/-- The stabilizer of any generating triple under the normalizer action is the centralizer
of the reference monodromy group, regarded as a subgroup of its normalizer. -/
@[simp]
theorem stabilizer_generatingTriple_eq_centralizer_subgroupOf (g : P.GeneratingTriple) :
    MulAction.stabilizer (Subgroup.normalizer (P.G : Set (Perm (Fin n)))) g =
      (Subgroup.centralizer (P.G : Set (Perm (Fin n)))).subgroupOf
        (Subgroup.normalizer (P.G : Set (Perm (Fin n)))) := by
  have h := g.1.stabilizer_normalizer_eq_centralizer_subgroupOf
  rw [g.2.monodromyGroup_eq] at h
  rw [← h]
  ext τ
  simp only [MulAction.mem_stabilizer_iff]
  simpa only [GeneratingTriple.coe_smul, Subgroup.smul_def] using
    (Subtype.ext_iff : τ • g = g ↔ (τ • g).1 = g.1)

/-- Orbit-stabilizer for a generating triple, with its stabilizer expressed as the
centralizer of the reference monodromy group. -/
theorem card_orbit_generatingTriple_mul_card_centralizer_eq_card_normalizer
    (g : P.GeneratingTriple) :
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
        congrArg (fun H : Subgroup N => Nat.card H)
          (stabilizer_generatingTriple_eq_centralizer_subgroupOf P g)
      _ = Nat.card C := hcard
  have h' : Nat.card (MulAction.orbit N g) * Nat.card (MulAction.stabilizer N g) =
      Nat.card N := by simpa only [Nat.card_eq_fintype_card] using h
  simpa only [hstab] using h'

end PassportSpec

end TauCeti
