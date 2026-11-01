/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.Passport.Stabilizer

/-!
# Burnside's formula for passport size

The normalizer of a passport's reference monodromy group acts on its generating triples.
An element of the normalizer fixes a generating triple exactly when it centralizes the
reference group. Thus it fixes every generating triple or none of them. This evaluates
every summand in Burnside's formula and gives an independent fixed-point interpretation
of the normalizer formula for passport size.

No admissibility hypothesis is needed to evaluate the fixed-point sets. Identifying the
normalizer orbits with passport classes requires nonzero degree and transitivity of the
reference group. In particular the fixed-point statements also apply when no generating
triple has the prescribed cycle data.

## References

* S. K. Lando, A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, §1.5.
* M. Musty, S. Schiavone, J. Sijsling, J. Voight, *A database of Belyi maps*, §2.
-/

public section

open Equiv MulAction

namespace TauCeti.PassportSpec

variable {n : ℕ} (P : PassportSpec n)

/-- A normalizer element fixes a generating triple exactly when it centralizes the
reference monodromy group. -/
@[simp]
theorem smul_generatingTriple_eq_self_iff
    (τ : Subgroup.normalizer (P.G : Set (Perm (Fin n)))) (g : P.GeneratingTriple) :
    τ • g = g ↔
      (τ : Perm (Fin n)) ∈ Subgroup.centralizer (P.G : Set (Perm (Fin n))) := by
  rw [← mem_stabilizer_iff,
    P.stabilizer_generatingTriple_eq_centralizer_subgroupOf]
  rfl

open Classical in
/-- A normalizer element fixes all generating triples if it belongs to the centralizer,
and fixes none otherwise. This includes the case of an empty generating-triple type. -/
theorem fixedBy_generatingTriple_eq
    (τ : Subgroup.normalizer (P.G : Set (Perm (Fin n)))) :
    fixedBy P.GeneratingTriple τ =
      if (τ : Perm (Fin n)) ∈ Subgroup.centralizer (P.G : Set (Perm (Fin n)))
      then Set.univ else ∅ := by
  apply Set.ext
  intro g
  rw [mem_fixedBy, P.smul_generatingTriple_eq_self_iff]
  split <;> simp_all

open Classical in
/-- The fixed-point count contributing to Burnside's formula is the full generating count
for an element of the centralizer, and zero for every other normalizer element. -/
@[simp]
theorem ncard_fixedBy_generatingTriple
    (τ : Subgroup.normalizer (P.G : Set (Perm (Fin n)))) :
    (fixedBy P.GeneratingTriple τ).ncard =
      if (τ : Perm (Fin n)) ∈ Subgroup.centralizer (P.G : Set (Perm (Fin n)))
      then Nat.card P.GeneratingTriple else 0 := by
  rw [P.fixedBy_generatingTriple_eq]
  split <;> simp

open Classical in
/-- The total fixed-point count is the number of generating triples times the order of
the centralizer. Only the centralizer's elements contribute to the sum. -/
theorem sum_ncard_fixedBy_generatingTriple :
    (∑ τ : Subgroup.normalizer (P.G : Set (Perm (Fin n))),
      (fixedBy P.GeneratingTriple τ).ncard) =
      Nat.card P.GeneratingTriple *
        Nat.card (Subgroup.centralizer (P.G : Set (Perm (Fin n)))) := by
  classical
  let N := Subgroup.normalizer (P.G : Set (Perm (Fin n)))
  let C := Subgroup.centralizer (P.G : Set (Perm (Fin n)))
  have hcard : Nat.card (C.subgroupOf N) = Nat.card C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (Subgroup.centralizer_le_normalizer (P.G : Set (Perm (Fin n))))).toEquiv
  simp_rw [P.ncard_fixedBy_generatingTriple]
  rw [← hcard]
  rw [← Finset.sum_filter]
  simp [Nat.card_eq_fintype_card, Fintype.card_subtype, Subgroup.mem_subgroupOf, N, C,
    mul_comm]

open Classical in
/-- **Burnside's formula for a passport**, without division: the total fixed-point count
is the number of passport classes times the normalizer order. -/
theorem sum_ncard_fixedBy_eq_passportSize_mul_card_normalizer
    (hn : n ≠ 0) (hG : IsPretransitive P.G (Fin n)) :
    (∑ τ : Subgroup.normalizer (P.G : Set (Perm (Fin n))),
      (fixedBy P.GeneratingTriple τ).ncard) =
      P.passportSize * Nat.card (Subgroup.normalizer (P.G : Set (Perm (Fin n)))) := by
  classical
  let N := Subgroup.normalizer (P.G : Set (Perm (Fin n)))
  let Ω := orbitRel.Quotient N P.GeneratingTriple
  let _ : Fintype Ω := Fintype.ofFinite Ω
  let _ : Fintype P.GeneratingTriple := Fintype.ofFinite P.GeneratingTriple
  have h := sum_card_fixedBy_eq_card_orbits_mul_card_group N P.GeneratingTriple
  simp only [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] at h
  rw [P.passportSize_eq_card_generatingTripleOrbits hn hG]
  exact h

open Classical in
/-- The number of passport classes is the average number of generating triples fixed by
an element of the normalizer, not by an element of the reference monodromy group. -/
theorem passportSize_eq_sum_ncard_fixedBy_div_card_normalizer
    (hn : n ≠ 0) (hG : IsPretransitive P.G (Fin n)) :
    P.passportSize =
      (∑ τ : Subgroup.normalizer (P.G : Set (Perm (Fin n))),
        (fixedBy P.GeneratingTriple τ).ncard) /
          Nat.card (Subgroup.normalizer (P.G : Set (Perm (Fin n)))) := by
  rw [P.sum_ncard_fixedBy_eq_passportSize_mul_card_normalizer hn hG]
  exact (Nat.mul_div_cancel _ (Nat.card_pos
    (α := Subgroup.normalizer (P.G : Set (Perm (Fin n)))))).symm

end TauCeti.PassportSpec
