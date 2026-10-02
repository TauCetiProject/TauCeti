/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Determined
public import TauCeti.RepresentationTheory.Induction.Permutation
-- Non-public: Burnside's lemma is what turns an equality of fixed-point counts into an equality of
-- orbit counts.
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Permutation representations in characteristic zero are classified by fixed-point counts

Let `G` be a finite group acting on finite types `X` and `Y`, and let `k` be a field of
characteristic zero. The character of the permutation representation `k[X]` at `g` is the number
of points of `X` fixed by `g`, cast into `k` (`TauCeti.char_ofMulAction`), and over a field of
characteristic zero a representation is determined by its character
(`Representation.nonempty_equiv_of_character_eq`). Characteristic zero makes the cast injective,
so the two statements combine into an exact criterion:

`k[X] ≃ k[Y]` as representations of `G` **if and only if** `#X^g = #Y^g` for every `g : G`.

Both directions need the characteristic-zero hypothesis, for different reasons. Without it the
fixed-point counts are only visible modulo the characteristic, so an isomorphism says less; and
without it a representation is not determined by its character at all.

The criterion is strictly weaker than an equivalence of `G`-sets: an equivariant equivalence
`X ≃ Y` gives an equivalence of permutation representations
(`TauCeti.ofMulActionEquivCongr`), but the converse fails, and the subgroup form below is exactly
where it fails. Taking `X = G ⧸ H` and `Y = G ⧸ K` for subgroups `H` and `K`, the criterion says
that the trivial representations of `H` and of `K` induce to equivalent representations of `G`
precisely when every element of `G` fixes as many cosets of `H` as of `K` — the classical condition
of Gassmann, satisfied by non-conjugate subgroups, so that `G ⧸ H` and `G ⧸ K` need not be
isomorphic `G`-sets. Nothing about Gassmann's examples is proved here; what is proved is the
criterion they are examples for.

Numerical consequences are recorded along the way. Equivalent permutation representations come from
`G`-sets of the same size (read the criterion at `g = 1`) and with the same number of orbits (sum
the criterion over `G` and apply Burnside's lemma); in the subgroup form the first of these is the
equality of the two indices.

## Main statements

* `TauCeti.natCard_fixedBy_eq_of_nonempty_equiv_ofMulAction`: equivalent permutation representations
  have equal fixed-point counts.
* `TauCeti.nonempty_equiv_ofMulAction_iff_forall_natCard_fixedBy_eq`: **the classification** —
  over a field of characteristic zero, two permutation representations of a finite group are
  equivalent exactly when the fixed-point counts of the underlying `G`-sets agree.
* `TauCeti.natCard_eq_of_nonempty_equiv_ofMulAction` and
  `TauCeti.natCard_orbitRelQuotient_eq_of_nonempty_equiv_ofMulAction`: the cardinalities and the
  orbit counts agree.
* `TauCeti.nonempty_iso_repOfMulAction_iff_forall_natCard_fixedBy_eq`: the same classification,
  read on the objects of `Rep k G`.
* `TauCeti.nonempty_equiv_ind_trivial_iff_forall_natCard_fixedBy_eq`: the subgroup form, for the
  representations induced from the trivial representations of two subgroups, with
  `TauCeti.index_eq_of_nonempty_equiv_ind_trivial` its numerical consequence.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Springer GTM 42 (1977), Part I, §2.3
  (characters determine representations) and §3.3 (permutation representations).
* F. Gassmann, *Bemerkungen zur vorstehenden Arbeit von Hurwitz*, Math. Z. **25** (1926), 665–675,
  for the subgroup condition the last statement characterizes.

This supplies the rational half of Step 2 in Layer 4 of
`TauCetiRoadmap/RepresentationTheory/ModularInduction/README.md`, whose `Suggested.lean` pins it as
`nonempty_equiv_ofMulAction_rat`; the proof uses nothing about `ℚ` beyond its characteristic, so it
is stated over an arbitrary field of characteristic zero and `ℚ` is the instance that layer takes.
-/

public section

open MulAction Representation

namespace TauCeti

universe u v w

variable (k : Type u) [Field k] {G : Type v} [Group G] [Finite G]

section Classification

variable {X Y : Type w} [MulAction G X] [MulAction G Y] [Finite X] [Finite Y]

omit [Finite G] in
/-- **Equivalent permutation representations have equal fixed-point counts.** Equivalent
representations have equal characters, the character of `k[X]` at `g` is `#X^g` cast into `k`, and
in characteristic zero that cast is injective. -/
theorem natCard_fixedBy_eq_of_nonempty_equiv_ofMulAction [CharZero k]
    (h : Nonempty ((ofMulAction k G X).Equiv (ofMulAction k G Y))) (g : G) :
    Nat.card (fixedBy X g) = Nat.card (fixedBy Y g) := by
  obtain ⟨φ⟩ := h
  have hchar := congrFun (Representation.char_iso φ) g
  rw [char_ofMulAction, char_ofMulAction] at hchar
  exact Nat.cast_injective hchar

/-- **Permutation representations in characteristic zero are classified by fixed-point counts.**
For a finite group `G` acting on finite types `X` and `Y` and a field `k` of characteristic zero,
the permutation representations `k[X]` and `k[Y]` are equivalent exactly when `g` fixes as many
points of `X` as of `Y`, for every `g : G`.

The forward direction is `TauCeti.natCard_fixedBy_eq_of_nonempty_equiv_ofMulAction`; the backward
one reads the fixed-point counts as the permutation characters and appeals to
`Representation.nonempty_equiv_of_character_eq`. -/
theorem nonempty_equiv_ofMulAction_iff_forall_natCard_fixedBy_eq [CharZero k] :
    Nonempty ((ofMulAction k G X).Equiv (ofMulAction k G Y)) ↔
      ∀ g : G, Nat.card (fixedBy X g) = Nat.card (fixedBy Y g) := by
  refine ⟨fun h g ↦ natCard_fixedBy_eq_of_nonempty_equiv_ofMulAction k h g, fun h ↦ ?_⟩
  refine Representation.nonempty_equiv_of_character_eq _ _ (funext fun g ↦ ?_)
  rw [char_ofMulAction, char_ofMulAction]
  exact congrArg Nat.cast (h g)

omit [Finite G] in
/-- **Equivalent permutation representations come from `G`-sets of the same size**: the
classification read at `g = 1`, where every point is fixed. -/
theorem natCard_eq_of_nonempty_equiv_ofMulAction [CharZero k]
    (h : Nonempty ((ofMulAction k G X).Equiv (ofMulAction k G Y))) :
    Nat.card X = Nat.card Y := by
  have hone := natCard_fixedBy_eq_of_nonempty_equiv_ofMulAction k h 1
  rwa [fixedBy_one_eq_univ, fixedBy_one_eq_univ, Nat.card_univ, Nat.card_univ] at hone

/-- **Equivalent permutation representations come from `G`-sets with the same number of orbits.**
Summing the fixed-point counts over `G` and applying Burnside's lemma expresses `|G|` times the
number of orbits in terms of data the classification equates; `|G|` is nonzero, so the orbit counts
agree. -/
theorem natCard_orbitRelQuotient_eq_of_nonempty_equiv_ofMulAction [CharZero k]
    (h : Nonempty ((ofMulAction k G X).Equiv (ofMulAction k G Y))) :
    Nat.card (orbitRel.Quotient G X) = Nat.card (orbitRel.Quotient G Y) := by
  classical
  have _ : Fintype G := Fintype.ofFinite G
  have _ : Fintype X := Fintype.ofFinite X
  have _ : Fintype Y := Fintype.ofFinite Y
  have _ : Fintype (orbitRel.Quotient G X) := Fintype.ofFinite _
  have _ : Fintype (orbitRel.Quotient G Y) := Fintype.ofFinite _
  have hsum : ∑ g : G, Fintype.card (fixedBy X g) = ∑ g : G, Fintype.card (fixedBy Y g) :=
    Finset.sum_congr rfl fun g _ ↦ by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
      exact natCard_fixedBy_eq_of_nonempty_equiv_ofMulAction k h g
  rw [sum_card_fixedBy_eq_card_orbits_mul_card_group,
    sum_card_fixedBy_eq_card_orbits_mul_card_group] at hsum
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Nat.eq_of_mul_eq_mul_right Fintype.card_pos hsum

/-- **The classification in `Rep k G`.** The permutation representations of two finite `G`-sets are
isomorphic as objects of `Rep k G`, over a field of characteristic zero, exactly when the
fixed-point counts agree. This is
`TauCeti.nonempty_equiv_ofMulAction_iff_forall_natCard_fixedBy_eq` read through `Rep.mkIso` and
`Representation.equivOfIso`, which identify the two notions of sameness on the objects
`Rep.of ρ`. -/
theorem nonempty_iso_repOfMulAction_iff_forall_natCard_fixedBy_eq [CharZero k] :
    Nonempty (Rep.ofMulAction k G X ≅ Rep.ofMulAction k G Y) ↔
      ∀ g : G, Nat.card (fixedBy X g) = Nat.card (fixedBy Y g) := by
  rw [← nonempty_equiv_ofMulAction_iff_forall_natCard_fixedBy_eq k]
  refine ⟨fun ⟨i⟩ ↦ ⟨?_⟩, fun ⟨e⟩ ↦ ⟨Rep.mkIso e⟩⟩
  have e := Representation.equivOfIso i
  rwa [Rep.of_ρ, Rep.of_ρ] at e

end Classification

section Subgroup

variable [CharZero k] (H K : Subgroup G)

/-- **The subgroup form of the classification.** The trivial representations of two subgroups `H`
and `K` of a finite group induce to equivalent representations of `G`, over a field of
characteristic zero, exactly when every `g : G` fixes as many cosets of `H` as of `K`.

The induced representations are the permutation representations on the coset spaces
(`TauCeti.indTrivialEquiv`), so this is
`TauCeti.nonempty_equiv_ofMulAction_iff_forall_natCard_fixedBy_eq` at `X = G ⧸ H` and
`Y = G ⧸ K`. -/
theorem nonempty_equiv_ind_trivial_iff_forall_natCard_fixedBy_eq :
    Nonempty (((Representation.trivial k H k).ind H.subtype).Equiv
        ((Representation.trivial k K k).ind K.subtype)) ↔
      ∀ g : G, Nat.card (fixedBy (G ⧸ H) g) = Nat.card (fixedBy (G ⧸ K) g) := by
  refine Iff.trans ?_
    (nonempty_equiv_ofMulAction_iff_forall_natCard_fixedBy_eq (X := G ⧸ H) (Y := G ⧸ K) k)
  exact ⟨fun ⟨φ⟩ ↦ ⟨((indTrivialEquiv k H).symm.trans φ).trans (indTrivialEquiv k K)⟩,
    fun ⟨φ⟩ ↦ ⟨((indTrivialEquiv k H).trans φ).trans (indTrivialEquiv k K).symm⟩⟩

/-- **Equivalently induced trivial representations force equal indices.** The coset space `G ⧸ H`
has cardinality `H.index`, so this is
`TauCeti.natCard_eq_of_nonempty_equiv_ofMulAction` on the coset spaces, read through
`Subgroup.index = Nat.card (G ⧸ ·)`. It is the one numerical condition on `H` and `K` that is
visible without any character computation. -/
theorem index_eq_of_nonempty_equiv_ind_trivial
    (h : Nonempty (((Representation.trivial k H k).ind H.subtype).Equiv
      ((Representation.trivial k K k).ind K.subtype))) :
    H.index = K.index := by
  rw [Subgroup.index_eq_card, Subgroup.index_eq_card]
  refine natCard_eq_of_nonempty_equiv_ofMulAction (G := G) (X := G ⧸ H) (Y := G ⧸ K) k ?_
  obtain ⟨φ⟩ := h
  exact ⟨((indTrivialEquiv k H).symm.trans φ).trans (indTrivialEquiv k K)⟩

end Subgroup

end TauCeti
