/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.Passport.Stabilizer

/-!
# Burnside fixed-point counts for passports

The normalizer of a passport's reference monodromy group acts on its generating triples.
An element of the normalizer fixes a generating triple exactly when it centralizes the
reference group. Thus it fixes every generating triple or none of them. This evaluates
every summand in Burnside's formula and their sum. The results concern fixed-point
counts, not the identification of normalizer orbits with passport classes.

No admissibility, nonzero-degree or transitivity hypothesis is needed to evaluate the
fixed-point sets. In particular the statements also apply when no generating triple has
the prescribed cycle data.

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
  exact Subgroup.mem_subgroupOf

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
  simp_rw [P.ncard_fixedBy_generatingTriple]
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (Subgroup.centralizer_le_normalizer (P.G : Set (Perm (Fin n))))).toEquiv]
  rw [← Finset.sum_filter]
  simp [Nat.card_eq_fintype_card, Fintype.card_subtype, Subgroup.mem_subgroupOf, mul_comm]

end TauCeti.PassportSpec
