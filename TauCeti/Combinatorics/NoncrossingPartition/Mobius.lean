/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import TauCeti.Combinatorics.Enumerative.IncidenceAlgebra
public import TauCeti.Combinatorics.NoncrossingPartition.Interval
import Mathlib.Algebra.BigOperators.Fin
import TauCeti.Algebra.BigOperators.Finset.Range

/-!
# The Möbius function of the lattice of noncrossing partitions

The free cumulants of a word are obtained from its block moments by Möbius inversion on the
lattice `NC(s)` of noncrossing partitions, so the values of its Möbius function `μ` are the
coefficients expressing cumulants through moments. This file computes the values `μ(0̂, π)`.

First, `μ(0̂, π)` is multiplicative: the lower interval `[0̂, π]` is the product of the lattices
`NC(B)` over the parts `B` of `π`, and accordingly `μ(0̂, π) = ∏_{B ∈ π} μ_{NC(B)}(0̂, 1̂)`.

Second, on the noncrossing partitions of `n` positions, `μ(0̂, 1̂) = (-1)^(n-1) C_(n-1)`, with
`C_k` the Catalan numbers. The proof applies Weisner's theorem to the atom joining the two first
positions `m₁ < m₂`: the noncrossing partitions other than `1̂` whose join with this atom is `1̂`
are exactly the partitions into the positions after `m₁` up to some position `y` and the remaining
positions. Together with multiplicativity this gives the recurrence
`μ_n = -∑_{0 < i < n} μ_i μ_(n-i)`, which is the recurrence of the signed Catalan numbers.

## Main results

* `TauCeti.NoncrossingPartition.mu_bot_eq_prod_mu` — `μ(0̂, π) = ∏_{B ∈ π} μ_{NC(B)}(0̂, 1̂)`.
* `TauCeti.NoncrossingPartition.mu_bot_top` — `μ(0̂, 1̂) = (-1)^(|s|-1) C_(|s|-1)` on `NC(s)`, and
  `TauCeti.NoncrossingPartition.mu_bot_top_fin` — `μ(0_n, 1_n) = (-1)^(n-1) C_(n-1)` on `NC(n)`.
* `TauCeti.NoncrossingPartition.mu_bot_eq_prod` — the blockwise formula
  `μ(0̂, π) = ∏_{B ∈ π} (-1)^(|B|-1) C_(|B|-1)`.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 10
  (Proposition 10.15).
* G. Kreweras, *Sur les partitions non croisées d'un cycle*, Discrete Math. 1 (1972), 333–350.
* L. Weisner, *Abstract theory of inversion of finite series*, Trans. Amer. Math. Soc. 38 (1935),
  474–484.
-/

public section

open Finset IncidenceAlgebra

namespace TauCeti.NoncrossingPartition

variable {α 𝕜 : Type*} [LinearOrder α] [CommRing 𝕜] {s : Finset α}

/-- *Multiplicativity of the Möbius function* of `NC(s)` on lower intervals: `μ(0̂, π)` is the
product over the parts `B` of `π` of the values `μ(0̂, 1̂)` on the lattices `NC(B)`. -/
theorem mu_bot_eq_prod_mu (π : NoncrossingPartition s) :
    mu 𝕜 ⊥ π = ∏ B ∈ π.1.parts, mu 𝕜 (⊥ : NoncrossingPartition B) ⊤ := by
  induction hn : #s using Nat.strong_induction_on generalizing s with
  | _ n ih =>
  subst hn
  induction π using WellFoundedLT.induction with
  | _ π ihπ =>
  by_cases hbot : π = ⊥
  · subst hbot
    rw [mu_self, eq_comm]
    refine prod_eq_one fun B hB => ?_
    obtain ⟨i, -, rfl⟩ := Finpartition.mem_bot_iff.1 hB
    rw [Subsingleton.elim (⊥ : NoncrossingPartition {i}) ⊤, mu_self]
  by_cases htop : π = ⊤
  · subst htop
    have hs : s ≠ ∅ := fun hs => hbot (eq_bot_of_eq_empty hs _)
    rw [coe_top, Finpartition.parts_top hs, prod_singleton]
  -- Each part of `π` has fewer positions than `s`, and some part has at least two.
  have hlt : ∀ B ∈ π.1.parts, #B < #s := fun B hB => card_lt_card <|
    (π.1.le hB).ssubset_of_ne fun h =>
      htop (Subtype.ext (Finpartition.eq_top_of_mem_parts (h ▸ hB)))
  obtain ⟨B, hB, hB1⟩ : ∃ B ∈ π.1.parts, 1 < #B := by
    by_contra! h
    refine hbot (le_bot_iff.1 fun B hB => ?_)
    obtain ⟨i, rfl⟩ :=
      card_eq_one.1 (le_antisymm (h B hB) (π.1.nonempty_of_mem_parts hB).card_pos)
    exact ⟨{i}, Finpartition.mem_bot_iff.2 ⟨i, π.1.le hB (mem_singleton_self i), rfl⟩, le_rfl⟩
  have hsum : ∑ σ ∈ Iic π, ∏ C ∈ σ.1.parts, mu 𝕜 (⊥ : NoncrossingPartition C) ⊤ = 0 := by
    rw [sum_Iic_prod_parts_eq_prod_sum]
    refine prod_eq_zero hB ?_
    rw [sum_congr rfl fun τ _ => (ih #B (hlt B hB) τ rfl).symm, ← Icc_bot_top,
      sum_Icc_mu_right, ite_eq_right (bot_ne_top_of_one_lt_card hB1)]
  rw [Iic_eq_cons_Iio, sum_cons, add_eq_zero_iff_eq_neg] at hsum
  rw [hsum, mu_eq_neg_sum_Ico_of_ne (Ne.symm hbot), Ico_bot]
  exact congrArg _ (sum_congr rfl fun σ hσ => ihπ σ (mem_Iio.1 hσ))

section Atom

/-! ### Weisner's theorem at the atom joining the two smallest positions -/

variable {i j : α}

/-- The partition of `s` with the part `{i, j}`, all other positions forming singletons. -/
private noncomputable def pairPartition (s : Finset α) (i j : α) (hij : {i, j} ⊆ s) :
    Finpartition s :=
  (⊥ : Finpartition (s \ {i, j})).extend (insert_ne_empty i {j}) sdiff_disjoint
    (sdiff_union_of_subset hij)

private theorem mem_parts_pairPartition {hij : {i, j} ⊆ s} {B : Finset α} :
    B ∈ (pairPartition s i j hij).parts ↔ B = {i, j} ∨ ∃ k ∈ s \ {i, j}, {k} = B := by
  rw [pairPartition, Finpartition.extend_parts, mem_insert, Finpartition.mem_bot_iff]

/-- A part of `pairPartition s i j` with two different positions is `{i, j}`. -/
private theorem eq_pair_of_mem_parts_pairPartition {hij : {i, j} ⊆ s} {B : Finset α}
    (hB : B ∈ (pairPartition s i j hij).parts) {a c : α} (ha : a ∈ B) (hc : c ∈ B)
    (hac : a < c) : B = {i, j} := by
  obtain h | ⟨k, -, rfl⟩ := mem_parts_pairPartition.1 hB
  · exact h
  · rw [mem_singleton] at ha hc
    exact absurd hac (by rw [ha, hc]; exact lt_irrefl k)

private theorem isNoncrossing_pairPartition (hij : {i, j} ⊆ s) :
    (pairPartition s i j hij).IsNoncrossing :=
  Finpartition.isNoncrossing_iff.2 fun _ hB _ hC _ ha _ hb _ hc _ hd hab hbc hcd =>
    (eq_pair_of_mem_parts_pairPartition hB ha hc (hab.trans hbc)).trans
      (eq_pair_of_mem_parts_pairPartition hC hb hd (hbc.trans hcd)).symm

private theorem part_pairPartition (hij : {i, j} ⊆ s) :
    (pairPartition s i j hij).part i = {i, j} :=
  Finpartition.part_eq_of_mem _ (mem_parts_pairPartition.2 (Or.inl rfl)) (mem_insert_self i _)

/-- A partition in which `i` and `j` share a part is coarser than `pairPartition s i j`. -/
private theorem pairPartition_le {hij : {i, j} ⊆ s} {R : Finpartition s} (hR : j ∈ R.part i) :
    pairPartition s i j hij ≤ R := by
  have hi : i ∈ s := hij (mem_insert_self i _)
  refine fun B hB => ?_
  obtain rfl | ⟨k, hk, rfl⟩ := mem_parts_pairPartition.1 hB
  · refine ⟨R.part i, R.part_mem.2 hi, fun z hz => ?_⟩
    rcases mem_insert.1 hz with rfl | hz
    exacts [R.mem_part_self.2 hi, mem_singleton.1 hz ▸ hR]
  · exact ⟨R.part k, R.part_mem.2 (sdiff_subset hk),
      singleton_subset_iff.2 (R.mem_part_self.2 (sdiff_subset hk))⟩

private theorem pairPartition_ne_bot {hij : {i, j} ⊆ s} (hne : i ≠ j) :
    pairPartition s i j hij ≠ ⊥ := fun h => by
  have h' : {i, j} ∈ (pairPartition s i j hij).parts := mem_parts_pairPartition.2 (Or.inl rfl)
  rw [h, Finpartition.mem_bot_iff] at h'
  obtain ⟨k, -, hk⟩ := h'
  exact hne ((mem_singleton.1 (hk ▸ mem_insert_self i _)).trans
    (mem_singleton.1 (hk ▸ mem_insert_of_mem (mem_singleton_self j))).symm)

/-- Let `i ≤ j` be positions of `s` with no position of `s` strictly between them. A noncrossing
partition `x` joins with `pairPartition s i j` to the partition into one part exactly when the
parts of `x` through `i` and `j` cover `s`. -/
private theorem sup_pairPartition_eq_top_iff (hij : {i, j} ⊆ s) (hle : i ≤ j)
    (hadj : ∀ z ∈ s, z ≤ i ∨ j ≤ z) (x : NoncrossingPartition s) :
    x ⊔ ⟨pairPartition s i j hij, isNoncrossing_pairPartition hij⟩ = ⊤ ↔
      x.1.part i ∪ x.1.part j = s := by
  have hi : i ∈ s := hij (mem_insert_self i _)
  have hj : j ∈ s := hij (mem_insert_of_mem (mem_singleton_self j))
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · -- Merging the parts of `x` through `i` and `j` gives an upper bound of `x` and the atom.
    obtain ⟨Q, hQ, hxQ, hQi⟩ := x.2.exists_part_eq_union hi hj hle hadj
    have hsup : x ⊔ ⟨pairPartition s i j hij, isNoncrossing_pairPartition hij⟩ ≤ ⟨Q, hQ⟩ :=
      sup_le (Subtype.coe_le_coe.1 hxQ)
        (pairPartition_le (hij := hij) (hQi ▸ mem_union_right _ (x.1.mem_part_self.2 hj)))
    rw [hx, top_le_iff] at hsup
    exact hQi.symm.trans ((congrArg (fun P : NoncrossingPartition s => P.1.part i) hsup).trans
      (Finpartition.part_top hi))
  · set R := x ⊔ ⟨pairPartition s i j hij, isNoncrossing_pairPartition hij⟩
    have hjR : j ∈ R.1.part i := Finpartition.part_mono (le_sup_right : _ ≤ R) i
      (by rw [part_pairPartition]; exact mem_insert_of_mem (mem_singleton_self j))
    have hsR : s ⊆ R.1.part i := calc
      s = x.1.part i ∪ x.1.part j := hx.symm
      _ ⊆ R.1.part i ∪ R.1.part j := union_subset_union
        (Finpartition.part_mono (le_sup_left : x ≤ R) i)
        (Finpartition.part_mono (le_sup_left : x ≤ R) j)
      _ = R.1.part i := by rw [(R.1.mem_part_iff_part_eq_part hj hi).1 hjR, union_self]
    have hR := R.1.part_mem.2 hi
    rw [(R.1.part_subset i).antisymm hsR] at hR
    exact Subtype.ext (Finpartition.eq_top_of_mem_parts hR)

end Atom

section Split

/-! ### Partitions into two parts, one of them convex -/

variable {C : Finset α}

/-- The partition of `s` into a nonempty part `C ⊆ s` and the rest `s \ C`. -/
private noncomputable def splitPartition (s C : Finset α) (hC : C.Nonempty) (hCs : C ⊆ s) :
    Finpartition s :=
  (⊤ : Finpartition (s \ C)).extend hC.ne_empty sdiff_disjoint (sdiff_union_of_subset hCs)

variable {hC : C.Nonempty} {hCs : C ⊆ s}

private theorem parts_splitPartition (hsC : (s \ C).Nonempty) :
    (splitPartition s C hC hCs).parts = {C, s \ C} := by
  rw [splitPartition, Finpartition.extend_parts, Finpartition.parts_top hsC.ne_empty]

private theorem part_splitPartition_of_mem {z : α} (hz : z ∈ C) :
    (splitPartition s C hC hCs).part z = C :=
  Finpartition.part_eq_of_mem _ (by simp [splitPartition]) hz

private theorem part_splitPartition_of_notMem {z : α} (hz : z ∈ s) (hzC : z ∉ C) :
    (splitPartition s C hC hCs).part z = s \ C := by
  have hzsC : z ∈ s \ C := mem_sdiff.2 ⟨hz, hzC⟩
  exact Finpartition.part_eq_of_mem _
    (by rw [parts_splitPartition ⟨z, hzsC⟩]; exact mem_insert_of_mem (mem_singleton_self _)) hzsC

/-- Splitting off a part `C` that contains every position of `s` between two of its elements
gives a noncrossing partition. -/
private theorem isNoncrossing_splitPartition
    (hconv : ∀ a ∈ C, ∀ c ∈ C, ∀ b ∈ s, a < b → b < c → b ∈ C) :
    (splitPartition s C hC hCs).IsNoncrossing := by
  refine Finpartition.isNoncrossing_iff_part.2 fun a ha b hb c hc d hd hab hbc hcd => ?_
  by_cases haC : a ∈ C <;> by_cases hbC : b ∈ C
  · rw [part_splitPartition_of_mem haC, part_splitPartition_of_mem hbC]
  · rw [part_splitPartition_of_mem haC] at hc
    exact absurd (hconv a haC c hc b hb hab hbc) hbC
  · rw [part_splitPartition_of_mem hbC] at hd
    rw [part_splitPartition_of_notMem ha haC] at hc
    exact absurd (hconv b hbC d hd c (mem_sdiff.1 hc).1 hbc hcd) (mem_sdiff.1 hc).2
  · rw [part_splitPartition_of_notMem ha haC, part_splitPartition_of_notMem hb hbC]

end Split

section Recurrence

/-! ### The noncrossing partitions joining the two smallest positions with everything -/

variable {m₁ m₂ : α}

/-- If the first position of `s` is `m₁`, then the positions of `s` other than `m₁` up to `y`
contain every position of `s` between two of them. -/
private theorem mem_filter_le_of_lt_of_lt (hmin₁ : ∀ z ∈ s, m₁ ≤ z) {y : α} :
    ∀ a ∈ {z ∈ s.erase m₁ | z ≤ y}, ∀ c ∈ {z ∈ s.erase m₁ | z ≤ y}, ∀ b ∈ s, a < b → b < c →
      b ∈ {z ∈ s.erase m₁ | z ≤ y} := by
  intro a ha c hc b hb hab hbc
  simp only [mem_filter, mem_erase] at ha hc ⊢
  exact ⟨⟨((hmin₁ a ha.1.2).trans_lt hab).ne', hb⟩, hbc.le.trans hc.2⟩

variable (hm₁ : m₁ ∈ s) (hm₂ : m₂ ∈ s.erase m₁) {x : NoncrossingPartition s}
  (hx : x.1.part m₁ ∪ x.1.part m₂ = s) (hne : x.1.part m₁ ≠ x.1.part m₂)
include hm₁ hm₂ hx hne

/-- If the parts through `m₁` and `m₂` are different and cover `s`, they are complementary. -/
private theorem part_eq_sdiff_part : x.1.part m₁ = s \ x.1.part m₂ := by
  have hm₂s := mem_of_mem_erase hm₂
  ext w
  refine ⟨fun hw => mem_sdiff.2 ⟨x.1.part_subset m₁ hw, fun hw₂ => hne ?_⟩, fun hw => ?_⟩
  · rw [← (x.1.mem_part_iff_part_eq_part (x.1.part_subset m₁ hw) hm₁).1 hw,
      (x.1.mem_part_iff_part_eq_part (x.1.part_subset m₁ hw) hm₂s).1 hw₂]
  · exact (mem_union.1 (hx.symm ▸ (mem_sdiff.1 hw).1)).resolve_right (mem_sdiff.1 hw).2

variable (hmin₁ : ∀ z ∈ s, m₁ ≤ z) (hmin₂ : ∀ z ∈ s.erase m₁, m₂ ≤ z)
include hmin₁ hmin₂

/-- Let `m₁ < m₂` be the two first positions of `s`. If the parts of a noncrossing partition
through `m₁` and `m₂` are different and cover `s`, then the part through `m₂` consists of the
positions of `s` other than `m₁` up to its last element. -/
private theorem filter_le_max'_eq_part :
    {z ∈ s.erase m₁ | z ≤ (x.1.part m₂).max' ⟨m₂, x.1.mem_part_self.2 (mem_of_mem_erase hm₂)⟩} =
      x.1.part m₂ := by
  have hm₂s := mem_of_mem_erase hm₂
  have hm₁C : m₁ ∉ x.1.part m₂ := fun h => hne ((x.1.mem_part_iff_part_eq_part hm₁ hm₂s).1 h)
  set y := (x.1.part m₂).max' ⟨m₂, x.1.mem_part_self.2 hm₂s⟩
  have hyC : y ∈ x.1.part m₂ := max'_mem _ _
  have hys : y ∈ s := x.1.part_subset m₂ hyC
  ext z
  simp only [mem_filter, mem_erase]
  refine ⟨fun ⟨⟨hz₁, hzs⟩, hzy⟩ => by_contra fun hzC => ?_,
    fun hz => ⟨⟨fun h => hm₁C (h ▸ hz), x.1.part_subset m₂ hz⟩, le_max' _ _ hz⟩⟩
  -- Otherwise `m₁ < m₂ < z < y` with `m₁, z` in one part and `m₂, y` in another.
  have hzB : z ∈ x.1.part m₁ := (mem_union.1 (hx.symm ▸ hzs)).resolve_right hzC
  have h₁₂ : m₁ < m₂ := (hmin₁ m₂ hm₂s).lt_of_ne (ne_of_mem_erase hm₂).symm
  have h₂z : m₂ < z := (hmin₂ z (mem_erase.2 ⟨hz₁, hzs⟩)).lt_of_ne
    fun h => hzC (h ▸ x.1.mem_part_self.2 hm₂s)
  have hzy' : z < y := hzy.lt_of_ne fun h => hzC (h ▸ hyC)
  exact hne (x.2.part_eq_part hm₁ hm₂s ((x.1.mem_part_iff_part_eq_part hzs hm₁).1 hzB).symm
    ((x.1.mem_part_iff_part_eq_part hys hm₂s).1 hyC).symm h₁₂ h₂z hzy')

omit hm₁ hm₂ hx hne hmin₁ hmin₂ in
/-- Let `m₁ < m₂` be the two first positions of `s`. Removing the partition into one part, the
noncrossing partitions whose join with the part `{m₁, m₂}` is the partition into one part are the
partitions into the positions of `s` other than `m₁` up to some `y` and the remaining positions;
summing `μ(⊥, x)` over them gives a sum over `y` of products of Möbius functions of smaller
lattices. -/
private theorem sum_erase_top_mu_bot (hpair : {m₁, m₂} ⊆ s) (hmin₁ : ∀ z ∈ s, m₁ ≤ z)
    (hm₂ : m₂ ∈ s.erase m₁) (hmin₂ : ∀ z ∈ s.erase m₁, m₂ ≤ z) :
    ∑ x ∈ ({x | x ⊔ ⟨pairPartition s m₁ m₂ hpair, isNoncrossing_pairPartition hpair⟩ = ⊤} :
        Finset (NoncrossingPartition s)).erase ⊤,
      mu 𝕜 ⊥ x =
    ∑ y ∈ s.erase m₁, mu 𝕜 (⊥ : NoncrossingPartition {z ∈ s.erase m₁ | z ≤ y}) ⊤ *
      mu 𝕜 (⊥ : NoncrossingPartition (s \ {z ∈ s.erase m₁ | z ≤ y})) ⊤ := by
  have hm₁ : m₁ ∈ s := hpair (mem_insert_self _ _)
  have hm₂s := mem_of_mem_erase hm₂
  have hle : m₁ ≤ m₂ := hmin₁ m₂ hm₂s
  have hadj (z : α) (hz : z ∈ s) : z ≤ m₁ ∨ m₂ ≤ z :=
    if h : z = m₁ then Or.inl h.le else Or.inr (hmin₂ z (mem_erase.2 ⟨h, hz⟩))
  have hC {y : α} (hy : y ∈ s.erase m₁) : y ∈ {z ∈ s.erase m₁ | z ≤ y} := mem_filter.2 ⟨hy, le_rfl⟩
  have hm₂C {y : α} (hy : y ∈ s.erase m₁) : m₂ ∈ {z ∈ s.erase m₁ | z ≤ y} :=
    mem_filter.2 ⟨hm₂, hmin₂ y hy⟩
  have hCs (y : α) : {z ∈ s.erase m₁ | z ≤ y} ⊆ s := (filter_subset _ _).trans (erase_subset _ _)
  have hm₁C (y : α) : m₁ ∉ {z ∈ s.erase m₁ | z ≤ y} :=
    fun h => ne_of_mem_erase (mem_filter.1 h).1 rfl
  have hX (x : NoncrossingPartition s) (hx : x ∈ ({x | x ⊔ ⟨pairPartition s m₁ m₂ hpair,
      isNoncrossing_pairPartition hpair⟩ = ⊤} : Finset (NoncrossingPartition s)).erase ⊤) :
      x.1.part m₁ ∪ x.1.part m₂ = s ∧ x.1.part m₁ ≠ x.1.part m₂ := by
    obtain ⟨hxtop, hxa⟩ := mem_erase.1 hx
    have hu := (sup_pairPartition_eq_top_iff hpair hle hadj x).1 (mem_filter.1 hxa).2
    refine ⟨hu, fun h => hxtop (Subtype.ext (Finpartition.eq_top_of_mem_parts ?_))⟩
    rw [← h, union_self] at hu
    have hpart := x.1.part_mem.2 hm₁
    rwa [hu] at hpart
  -- Biject `y` with the partition splitting off the positions after `m₁` up to `y`; the inverse
  -- sends `x` to the last position of its part through `m₂`.
  symm
  refine sum_bij'
    (fun y hy => ⟨splitPartition s _ (nonempty_of_ne_empty (ne_empty_of_mem (hC hy))) (hCs y),
      isNoncrossing_splitPartition (mem_filter_le_of_lt_of_lt hmin₁)⟩)
    (fun x _ => (x.1.part m₂).max' ⟨m₂, x.1.mem_part_self.2 hm₂s⟩)
    (fun y hy => ?_) (fun x hx => ?_) (fun y hy => ?_) (fun x hx => ?_) (fun y hy => ?_)
  · -- The split partition joins with the atom to the top, and is not the top itself.
    rw [mem_erase, mem_filter, sup_pairPartition_eq_top_iff hpair hle hadj]
    dsimp only
    rw [part_splitPartition_of_mem (hm₂C hy), part_splitPartition_of_notMem hm₁ (hm₁C y)]
    refine ⟨fun h => ?_, mem_univ _, sdiff_union_of_subset (hCs y)⟩
    have h₁ := congrArg (fun P : NoncrossingPartition s => P.1.part m₁) h
    dsimp only at h₁
    rw [part_splitPartition_of_notMem hm₁ (hm₁C y), coe_top, Finpartition.part_top hm₁] at h₁
    have hy' : y ∈ s \ {z ∈ s.erase m₁ | z ≤ y} := h₁.symm ▸ hCs y (hC hy)
    exact (mem_sdiff.1 hy').2 (hC hy)
  · -- The last position of the part through `m₂` is not `m₁`.
    obtain ⟨hu, hne⟩ := hX x hx
    have hmax := max'_mem (x.1.part m₂) ⟨m₂, x.1.mem_part_self.2 hm₂s⟩
    refine mem_erase.2 ⟨fun h => hne ?_, x.1.part_subset m₂ hmax⟩
    exact (x.1.mem_part_iff_part_eq_part hm₁ hm₂s).1 (h ▸ hmax)
  · -- The last position of the split-off part is `y`.
    dsimp only
    simp only [part_splitPartition_of_mem (hm₂C hy)]
    exact le_antisymm (max'_le _ _ _ fun z hz => (mem_filter.1 hz).2) (le_max' _ _ (hC hy))
  · -- A partition `x` is the split at the last position of its part through `m₂`.
    obtain ⟨hu, hne⟩ := hX x hx
    have hCx := filter_le_max'_eq_part hm₁ hm₂ hu hne hmin₁ hmin₂
    refine Subtype.ext (Finpartition.ext_of_part fun z hz => ?_)
    dsimp only
    by_cases hzC : z ∈ x.1.part m₂
    · rw [part_splitPartition_of_mem (hCx.symm ▸ hzC), hCx,
        (x.1.mem_part_iff_part_eq_part hz hm₂s).1 hzC]
    · rw [part_splitPartition_of_notMem hz (hCx.symm ▸ hzC), hCx,
        ← part_eq_sdiff_part hm₁ hm₂ hu hne,
        (x.1.mem_part_iff_part_eq_part hz hm₁).1
          ((mem_union.1 (hu.symm ▸ hz)).resolve_right hzC)]
  · -- The Möbius function at the split partition is a product over its two parts.
    have hsC : m₁ ∈ s \ {z ∈ s.erase m₁ | z ≤ y} := mem_sdiff.2 ⟨hm₁, hm₁C y⟩
    conv_rhs => rw [mu_bot_eq_prod_mu]
    dsimp only
    rw [parts_splitPartition (nonempty_of_ne_empty (ne_empty_of_mem hsC)),
      prod_pair fun h : {z ∈ s.erase m₁ | z ≤ y} = _ => hm₁C y (h ▸ hsC)]

end Recurrence

/-- The Catalan identity behind `mu_bot_top`:
`∑_{i ≤ k} (-1)^i C_i (-1)^(k-i) C_(k-i) = (-1)^k C_(k+1)`. -/
private theorem sum_range_neg_one_pow_mul_catalan (k : ℕ) :
    ∑ i ∈ range (k + 1),
        (-1 : 𝕜) ^ i * catalan i * ((-1) ^ (k + 1 - 1 - i) * catalan (k + 1 - 1 - i)) =
      (-1) ^ k * catalan (k + 1) := by
  rw [catalan_succ, ← sum_range fun i => catalan i * catalan (k - i),
    Nat.cast_sum, mul_sum, Nat.add_sub_cancel]
  refine sum_congr rfl fun i hi => ?_
  rw [← Nat.add_sub_cancel' (Nat.lt_succ_iff.1 (mem_range.1 hi)), pow_add, Nat.add_sub_cancel_left]
  push_cast
  ring

/-- **The Möbius function of the lattice of noncrossing partitions**: on the noncrossing
partitions of a set `s` of `n` positions, `μ(0̂, 1̂) = (-1)^(n-1) C_(n-1)`, where `C_k` is the
`k`-th Catalan number. For `n = 0` both sides are `1`. -/
@[simp]
theorem mu_bot_top (s : Finset α) :
    mu 𝕜 (⊥ : NoncrossingPartition s) ⊤ = (-1) ^ (#s - 1) * catalan (#s - 1) := by
  induction hn : #s using Nat.strong_induction_on generalizing s with
  | _ n ih =>
  subst hn
  by_cases hs1 : #s ≤ 1
  · rw [bot_eq_top_iff_card_le_one.2 hs1, mu_self, Nat.sub_eq_zero_of_le hs1, pow_zero,
      catalan_zero, Nat.cast_one, one_mul]
  obtain ⟨k, hk⟩ : ∃ k, #s = k + 2 := ⟨#s - 2, by omega⟩
  -- The two first positions `m₁ < m₂` of `s`.
  obtain ⟨m₁, hm₁, hmin₁⟩ : ∃ m ∈ s, ∀ z ∈ s, m ≤ z :=
    have hs : s.Nonempty := card_pos.1 (by omega)
    ⟨s.min' hs, min'_mem s hs, fun z hz => min'_le s z hz⟩
  have hcard : #(s.erase m₁) = k + 1 := by rw [card_erase_of_mem hm₁, hk]; rfl
  obtain ⟨m₂, hm₂, hmin₂⟩ : ∃ m ∈ s.erase m₁, ∀ z ∈ s.erase m₁, m ≤ z :=
    have ht : (s.erase m₁).Nonempty := card_pos.1 (by omega)
    ⟨_, min'_mem _ ht, fun z hz => min'_le _ z hz⟩
  have hpair : {m₁, m₂} ⊆ s :=
    insert_subset hm₁ (singleton_subset_iff.2 (mem_of_mem_erase hm₂))
  -- Weisner's theorem at the atom joining `m₁` and `m₂`.
  have hW := sum_filter_sup_eq_top_mu_bot_eq_zero (𝕜 := 𝕜)
    (a := ⟨pairPartition s _ _ hpair, isNoncrossing_pairPartition hpair⟩)
    fun h => pairPartition_ne_bot (hij := hpair) (ne_of_mem_erase hm₂).symm
      (congrArg Subtype.val h)
  have htop : (⊤ : NoncrossingPartition s) ∈ ({x | x ⊔ ⟨pairPartition s _ _ hpair,
      isNoncrossing_pairPartition hpair⟩ = ⊤} : Finset (NoncrossingPartition s)) := by simp
  rw [Icc_bot_top, ← add_sum_erase _ _ htop, sum_erase_top_mu_bot hpair hmin₁ hm₂ hmin₂] at hW
  -- By induction, each summand is a product of signed Catalan numbers.
  have hterm (y : α) (hy : y ∈ s.erase m₁) :
      mu 𝕜 (⊥ : NoncrossingPartition {z ∈ s.erase m₁ | z ≤ y}) ⊤ *
        mu 𝕜 (⊥ : NoncrossingPartition (s \ {z ∈ s.erase m₁ | z ≤ y})) ⊤ =
      (-1) ^ #{z ∈ s.erase m₁ | z < y} * catalan #{z ∈ s.erase m₁ | z < y} *
        ((-1) ^ #{z ∈ s.erase m₁ | y < z} * catalan #{z ∈ s.erase m₁ | y < z}) := by
    have hle : #{z ∈ s.erase m₁ | z ≤ y} = #{z ∈ s.erase m₁ | z < y} + 1 := by
      rw [← card_insert_of_notMem (by simp : y ∉ {z ∈ s.erase m₁ | z < y})]
      congr 1
      ext z
      simp only [mem_filter, mem_insert]
      grind
    have hsplit : #{z ∈ s.erase m₁ | z ≤ y} + #{z ∈ s.erase m₁ | y < z} = k + 1 := by
      rw [← hcard, ← card_filter_add_card_filter_not (s := s.erase m₁) (p := fun z => z ≤ y)]
      simp only [not_le]
    have hsdiff : #(s \ {z ∈ s.erase m₁ | z ≤ y}) = #{z ∈ s.erase m₁ | y < z} + 1 := by
      rw [card_sdiff_of_subset ((filter_subset _ _).trans (erase_subset _ _))]
      omega
    rw [ih _ (by omega) _ rfl, ih _ (by omega) _ rfl, hle, hsdiff, Nat.add_sub_cancel,
      Nat.add_sub_cancel]
  rw [sum_congr rfl hterm, sum_card_filter_lt_card_filter_gt (s.erase m₁)
    (fun i j => (-1 : 𝕜) ^ i * catalan i * ((-1) ^ j * catalan j)), hcard,
    sum_range_neg_one_pow_mul_catalan] at hW
  rw [eq_neg_of_add_eq_zero_left hW, hk, show k + 2 - 1 = k + 1 by omega, pow_succ]
  ring

/-- The Möbius function of `NC(n)`: `μ(0_n, 1_n) = (-1)^(n-1) C_(n-1)` on the noncrossing
partitions of the `n` ordered positions of `Fin n`. -/
theorem mu_bot_top_fin (n : ℕ) :
    mu 𝕜 (⊥ : NoncrossingPartition (univ : Finset (Fin n))) ⊤ =
      (-1) ^ (n - 1) * catalan (n - 1) := by
  rw [mu_bot_top, card_univ, Fintype.card_fin]

/-- The blockwise formula for the Möbius function of `NC(s)`: `μ(0̂, π)` is the product over the
parts `B` of `π` of `(-1)^(|B|-1) C_(|B|-1)`. -/
theorem mu_bot_eq_prod (π : NoncrossingPartition s) :
    mu 𝕜 ⊥ π = ∏ B ∈ π.1.parts, (-1) ^ (#B - 1) * (catalan (#B - 1) : 𝕜) := by
  rw [mu_bot_eq_prod_mu]
  exact prod_congr rfl fun B _ => mu_bot_top B

end TauCeti.NoncrossingPartition
