/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import TauCeti.RepresentationTheory.DiscreteSeries.BlockRule
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith

/-!
# Inserting a block into a discrete-series parameter

Along a chain of theta lifts between unitary groups, the doubled Harish-Chandra parameters are
built from a fixed stem by inserting blocks of consecutive entries of one parity, one block for
each lift. This file gives a combinatorial criterion under which a parameter and the same
parameter with one more block satisfy the block rule `TauCeti.DiscreteSeries.IsBlockRule`, the
correspondence of discrete-series parameters under the theta lift (Li).

A center system `TauCeti.DiscreteSeries.CenterSystem` at one infinite place consists of centers
`c` with integer values `e_c`, lengths `l_c` and kinds (up or down), and a finite set `S` of doubled
stem entries. For a finite set `B` of centers:

* the doubled entries `λ⁺_B` (`CenterSystem.entries`) are the stem together with the doubled
  blocks `2e_c + 2[l_c]` of the centers `c ∈ B`, and the rank (`CenterSystem.rank`) is
  `|S| + ∑_{c ∈ B} l_c`;
* the sign of an entry `y` (`CenterSystem.sign`) is `(-1)` to the number of centers outside `B`
  that are down with `y < 2e_c` or up with `2e_c < y` (`CenterSystem.Flips`);
* the parameter `λ_B` is `λ⁺_B` lowered by `½`, that is, by `1` in doubled coordinates
  (`CenterSystem.lowering`), when `|S|` and `|B|` are both odd;
* a doubled parameter `l` with signs `s` is `λ_B` with sign `σ` (`CenterSystem.IsParam`) if it
  lists the entries of `λ_B`, each with `σ` times the sign of its entry of `λ⁺_B`.

The system is separated with bound `h` (`CenterSystem.IsSeparated`) if the lengths have the parity
of `|S|`, the stem entries the parity of `|S| + 1`, and every doubled center `2e_c` is at distance
at least `h + l_c` from the stem and from the blocks of the other centers. Then every `λ_B` has the
gap `h`, and inserting one more center `c ∉ B` satisfies the block rule: between `λ_B` and
`λ_{B ∪ {c}}` if `c` is down, between their negatives if `c` is up. After the shift by the center,
the entries after the insertion are those before it together with the block of `c`, and since
this block is far from the others, the only sign that changes is the one of the inserted center.

## Main definitions and results

* `TauCeti.DiscreteSeries.CenterSystem`, with `CenterSystem.entries`, `CenterSystem.rank`,
  `CenterSystem.lowering`, `CenterSystem.sign`: center systems and the parameters `λ_B`.
* `TauCeti.DiscreteSeries.CenterSystem.IsSeparated`, `TauCeti.DiscreteSeries.CenterSystem.IsParam`:
  separated systems and the doubled parameters that are `λ_B` with a given sign.
* `TauCeti.DiscreteSeries.CenterSystem.IsParam.hasGap`: in a separated system with bound `h`,
  `λ_B` has the gap `h`.
* `TauCeti.DiscreteSeries.CenterSystem.IsParam.isBlockRule_insert`: inserting a down center `c`
  into `λ_B` satisfies the block rule for the shifts `e_c + ⌊n/2⌋`, `e_c + ⌊n'/2⌋`.
* `TauCeti.DiscreteSeries.CenterSystem.IsParam.isBlockRule_neg_insert`: inserting an up center `c`
  into `λ_B` satisfies the block rule between the negated parameters for the shifts
  `-e_c + ⌈n/2⌉`, `-e_c + ⌈n'/2⌉`.

## References

* J.-S. Li, *Theta lifting for unitary representations with nonzero cohomology*,
  Duke Math. J. 61 (1990).
* The statements and the method of proof follow grh-lean (https://github.com/lsernau/grh-lean,
  Apache 2.0, Copyright 2026 Anthropic, PBC), `New/UpperBound/Objects/InsertBlock.lean`:
  `New.CentreSystem.IsParam.isBlockRule_insert_of_down`,
  `New.CentreSystem.IsParam.isBlockRule_neg_insert_of_up` and `New.CentreSystem.IsParam.hasGap`.
-/

public section

open Finset Fintype

namespace TauCeti.DiscreteSeries

/-- The two kinds of centers of a `TauCeti.DiscreteSeries.CenterSystem`. -/
inductive CenterKind
  /-- An up center outside the inserted blocks reverses the signs of the entries above it. -/
  | up
  /-- A down center outside the inserted blocks reverses the signs of the entries below it. -/
  | down
  deriving DecidableEq

/-- A center system at one infinite place: centers `c : C`, each with an integer value
`center c`, a block length `length c` and a kind `kind c`, together with a finite set `stem` of
doubled stem entries. -/
structure CenterSystem (C : Type*) where
  /-- The integer value `e_c` of the center `c`, the center of its block. -/
  center : C → ℤ
  /-- The length `l_c` of the block of the center `c`. -/
  length : C → ℕ
  /-- The kind of the center `c`. -/
  kind : C → CenterKind
  /-- The doubled stem entries. -/
  stem : Finset ℤ

namespace CenterSystem

variable {C : Type*} (K : CenterSystem C)

/-- The doubled entries `λ⁺_B` of the parameter with the blocks of the centers of `B`: the stem
together with the doubled blocks `2e_c + 2[l_c]` of the centers `c ∈ B`. -/
def entries (B : Finset C) : Finset ℤ :=
  K.stem ∪ B.biUnion fun c ↦ centeredBlock (K.center c) (K.length c)

/-- The rank `|S| + ∑_{c ∈ B} l_c` of the parameter with the blocks of the centers of `B`. -/
def rank (B : Finset C) : ℕ := #K.stem + ∑ c ∈ B, K.length c

/-- The lowering, in doubled coordinates, of the parameter with the blocks of the centers of `B`:
`1` if the stem and `B` both have odd cardinality, `0` otherwise. -/
def lowering (B : Finset C) : ℕ := if Odd #K.stem ∧ Odd #B then 1 else 0

/-- The center `c` reverses the sign of the doubled entry `y`: `y` lies above `2e_c` if `c` is up,
below `2e_c` if `c` is down. -/
def Flips (c : C) (y : ℤ) : Prop :=
  K.kind c = .up ∧ 2 * K.center c < y ∨ K.kind c = .down ∧ y < 2 * K.center c

instance (c : C) (y : ℤ) : Decidable (K.Flips c y) :=
  inferInstanceAs <| Decidable <|
    K.kind c = .up ∧ 2 * K.center c < y ∨ K.kind c = .down ∧ y < 2 * K.center c

/-- An integer lies in `K.entries B` iff it is a stem entry or lies in the block of a center
of `B`. -/
@[simp] theorem mem_entries {B : Finset C} {y : ℤ} :
    y ∈ K.entries B ↔ y ∈ K.stem ∨ ∃ c ∈ B, y ∈ centeredBlock (K.center c) (K.length c) := by
  simp only [entries, mem_union, mem_biUnion]

/-- Without blocks, the entries are the stem. -/
@[simp] theorem entries_empty : K.entries ∅ = K.stem := by simp [entries]

/-- Inserting a center adds its block to the entries. -/
@[simp] theorem entries_insert [DecidableEq C] (c : C) (B : Finset C) :
    K.entries (insert c B) = K.entries B ∪ centeredBlock (K.center c) (K.length c) := by
  ext y
  simp only [entries, biUnion_insert, mem_union]
  tauto

/-- Without blocks, the rank is the number of stem entries. -/
@[simp] theorem rank_empty : K.rank ∅ = #K.stem := by simp [rank]

/-- Inserting a center `c ∉ B` raises the rank by its length. -/
theorem rank_insert [DecidableEq C] {c : C} {B : Finset C} (hc : c ∉ B) :
    K.rank (insert c B) = K.rank B + K.length c := by
  rw [rank, rank, sum_insert hc]
  omega

/-- When every length of a center of `B` has the parity of `|S|`, the rank has the parity of
`|S| (|B| + 1)`. -/
theorem rank_mod_two {B : Finset C} (hlen : ∀ c ∈ B, Even (K.length c + #K.stem)) :
    K.rank B % 2 = (#K.stem * #B + #K.stem) % 2 := by
  classical
  induction B using Finset.induction_on with
  | empty => simp
  | insert c B hc ih =>
    have hc' := Nat.even_iff.1 (hlen c (mem_insert_self c B))
    have ih' := ih fun c' hc' ↦ hlen c' (mem_insert_of_mem hc')
    rw [K.rank_insert hc, card_insert_of_notMem hc, Nat.mul_add_one]
    omega

/-- Without blocks, there is no lowering. -/
@[simp] theorem lowering_empty : K.lowering ∅ = 0 := by simp [lowering]

/-- The lowering is the parity of `|S| |B|`. -/
theorem lowering_eq_mod_two (B : Finset C) : K.lowering B = #K.stem * #B % 2 := by
  rw [lowering]
  split_ifs with h
  · exact (Nat.odd_iff.1 (Nat.odd_mul.2 h)).symm
  · exact (Nat.even_iff.1 (Nat.not_odd_iff_even.1 (h ∘ Nat.odd_mul.1))).symm

/-- Unfolding of `TauCeti.DiscreteSeries.CenterSystem.Flips`. -/
theorem flips_iff {c : C} {y : ℤ} :
    K.Flips c y ↔ K.kind c = .up ∧ 2 * K.center c < y ∨ K.kind c = .down ∧ y < 2 * K.center c :=
  Iff.rfl

/-- An up center reverses the signs of the entries above it. -/
theorem flips_iff_of_kind_eq_up {c : C} (hc : K.kind c = .up) {y : ℤ} :
    K.Flips c y ↔ 2 * K.center c < y := by
  simp [flips_iff, hc]

/-- A down center reverses the signs of the entries below it. -/
theorem flips_iff_of_kind_eq_down {c : C} (hc : K.kind c = .down) {y : ℤ} :
    K.Flips c y ↔ y < 2 * K.center c := by
  simp [flips_iff, hc]

/-- The center system is separated with bound `h`: the lengths have the parity of the number
`|S|` of stem entries, the stem entries the parity of `|S| + 1`, and every doubled center `2e_c` is
at distance at least `h + l_c` from the stem and from the blocks of the other centers. -/
structure IsSeparated (h : ℕ) : Prop where
  /-- Every length has the parity of the number of stem entries. -/
  even_length_add_card : ∀ c, Even (K.length c + #K.stem)
  /-- Every stem entry has the parity of the number of stem entries plus one. -/
  odd_add_card : ∀ y ∈ K.stem, Odd (y + #K.stem)
  /-- Every doubled center `2e_c` is at distance at least `h + l_c` from the stem. -/
  le_abs_sub_of_mem_stem : ∀ c, ∀ y ∈ K.stem, (h + K.length c : ℤ) ≤ |y - 2 * K.center c|
  /-- Every doubled center `2e_c` is at distance at least `h + l_c` from the blocks of the other
  centers. -/
  le_abs_sub_of_mem_centeredBlock : ∀ c c', c ≠ c' →
    ∀ y ∈ centeredBlock (K.center c') (K.length c'), (h + K.length c : ℤ) ≤ |y - 2 * K.center c|

variable {K} {h : ℕ}

/-- In a separated system, every doubled center `2e_c` of a center outside `B` is at distance at
least `h + l_c` from the entries of `λ⁺_B`. -/
theorem IsSeparated.le_abs_sub_of_mem_entries (hK : K.IsSeparated h) {B : Finset C} {c : C}
    (hc : c ∉ B) {y : ℤ} (hy : y ∈ K.entries B) : (h + K.length c : ℤ) ≤ |y - 2 * K.center c| := by
  rcases K.mem_entries.1 hy with hy | ⟨c', hc', hy⟩
  · exact hK.le_abs_sub_of_mem_stem c y hy
  · exact hK.le_abs_sub_of_mem_centeredBlock c c' (ne_of_mem_of_not_mem hc' hc).symm y hy

/-- In a separated system, the entries of `λ⁺_B` have the parity of `|S| + 1`. -/
theorem IsSeparated.odd_add_card_of_mem_entries (hK : K.IsSeparated h) {B : Finset C} {y : ℤ}
    (hy : y ∈ K.entries B) : Odd (y + #K.stem) := by
  rcases K.mem_entries.1 hy with hy | ⟨c, -, hy⟩
  · exact hK.odd_add_card y hy
  · have hlen := Nat.even_iff.1 (hK.even_length_add_card c)
    have hpar := Int.even_iff.1 (mem_doubledBlock.1 (mem_centeredBlock.1 hy)).2
    rw [Int.odd_iff]
    omega

/-- In a separated system, the stem and the blocks of the centers of `B` are pairwise disjoint,
so `λ⁺_B` has as many entries as its rank. -/
theorem IsSeparated.card_entries (hK : K.IsSeparated h) (B : Finset C) :
    #(K.entries B) = K.rank B := by
  -- An integer at distance at least `h + l_c` from `2e_c` is not in the block of `c`.
  have hnot {c : C} {y : ℤ} (hy : (h + K.length c : ℤ) ≤ |y - 2 * K.center c|) :
      y ∉ centeredBlock (K.center c) (K.length c) := fun hmem ↦ by
    linarith [(mem_doubledBlock.1 (mem_centeredBlock.1 hmem)).1, Nat.cast_nonneg (α := ℤ) h]
  rw [entries, card_union_of_disjoint, card_biUnion, rank]
  · simp only [card_centeredBlock]
  · intro c _ c' _ hne
    exact disjoint_left.2 fun y hy hy' ↦
      hnot (hK.le_abs_sub_of_mem_centeredBlock c c' hne y hy') hy
  · refine disjoint_left.2 fun y hy hy' ↦ ?_
    obtain ⟨c, -, hc⟩ := mem_biUnion.1 hy'
    exact hnot (hK.le_abs_sub_of_mem_stem c y hy) hc

section Sign

variable [Fintype C] [DecidableEq C]

variable (K) in
/-- The sign of the doubled entry `y` for the parameter with the blocks of the centers of `B`:
`(-1)` to the number of centers outside `B` that reverse the sign of `y`. -/
def sign (B : Finset C) (y : ℤ) : ℤˣ := (-1) ^ #{c ∈ Bᶜ | K.Flips c y}

/-- Inserting a center `c ∉ B` reverses the signs of the entries that `c` flips. -/
theorem sign_insert {c : C} {B : Finset C} (hc : c ∉ B) (y : ℤ) :
    K.sign (insert c B) y = if K.Flips c y then -K.sign B y else K.sign B y := by
  have hcompl : Bᶜ = insert c (insert c B)ᶜ := by
    rw [compl_insert, insert_erase (mem_compl.2 hc)]
  have hnot : c ∉ {c' ∈ (insert c B)ᶜ | K.Flips c' y} := by simp
  rw [sign, sign, hcompl, filter_insert]
  split_ifs
  · rw [card_insert_of_notMem hnot, pow_succ, mul_neg_one, neg_neg]
  · rfl

/-- Inserting a center `c ∉ B` changes the sign of `y` iff `c` flips `y`. -/
theorem sign_insert_ne_iff {c : C} {B : Finset C} (hc : c ∉ B) {y : ℤ} :
    K.sign (insert c B) y ≠ K.sign B y ↔ K.Flips c y := by
  rw [sign_insert hc]
  split_ifs with hf
  · exact iff_of_true (Int.units_ne_iff_eq_neg.2 rfl) hf
  · exact iff_of_false (not_not.2 rfl) hf

/-- In a separated system with bound `h`, entries of `λ⁺_B` with different signs are at least
`2h` apart. -/
theorem IsSeparated.two_mul_le_abs_sub_of_sign_ne (hK : K.IsSeparated h) {B : Finset C}
    {y y' : ℤ} (hy : y ∈ K.entries B) (hy' : y' ∈ K.entries B) (hne : K.sign B y ≠ K.sign B y') :
    2 * (h : ℤ) ≤ |y - y'| := by
  by_contra hlt
  -- Otherwise no center outside `B` lies between `y` and `y'`, so they have the same sign.
  have hflips : ∀ c ∈ Bᶜ, K.Flips c y ↔ K.Flips c y' := fun c hc ↦ by
    have h₁ := le_abs'.1 (hK.le_abs_sub_of_mem_entries (mem_compl.1 hc) hy)
    have h₂ := le_abs'.1 (hK.le_abs_sub_of_mem_entries (mem_compl.1 hc) hy')
    have h₃ := abs_lt.1 (not_le.1 hlt)
    cases hk : K.kind c
    · rw [K.flips_iff_of_kind_eq_up hk, K.flips_iff_of_kind_eq_up hk]
      omega
    · rw [K.flips_iff_of_kind_eq_down hk, K.flips_iff_of_kind_eq_down hk]
      omega
  exact hne (by rw [sign, sign, filter_congr hflips])

end Sign

/-- A doubled parameter `l` with signs `s` is `λ_B` with sign `σ`: its rank is that of `λ_B`, its
entries raised by the lowering are the entries of `λ⁺_B`, and each sign is `σ` times the sign of
the raised entry. -/
structure IsParam [Fintype C] [DecidableEq C] {ι : Type*} [Fintype ι] (K : CenterSystem C)
    (B : Finset C) (σ : ℤˣ) (s : ι → ℤˣ) (l : ι → ℤ) : Prop where
  /-- The rank of the parameter is that of `λ_B`. -/
  card_eq : card ι = K.rank B
  /-- The entries raised by the lowering are the entries of `λ⁺_B`. -/
  image_eq : univ.image (fun i ↦ l i + K.lowering B) = K.entries B
  /-- Each sign is `σ` times the sign of the raised entry. -/
  sign_eq : ∀ i, s i = σ * K.sign B (l i + K.lowering B)

section IsParam

variable [Fintype C] [DecidableEq C] {ι ι' : Type*} [Fintype ι] [Fintype ι'] {B : Finset C}
  {c : C} {σ : ℤˣ} {s : ι → ℤˣ} {l : ι → ℤ} {s' : ι' → ℤˣ} {l' : ι' → ℤ}

/-- In a separated system with bound `h`, every parameter `λ_B` has the gap `h`. -/
theorem IsParam.hasGap (hK : K.IsSeparated h) (hl : K.IsParam B σ s l) : HasGap h s l where
  injective i j hij := by
    have hinj : Set.InjOn (fun i ↦ l i + K.lowering B) (univ : Finset ι) := by
      rw [← card_image_iff, hl.image_eq, hK.card_entries, card_univ, hl.card_eq]
    exact hinj (mem_coe.2 (mem_univ i)) (mem_coe.2 (mem_univ j))
      (congrArg (· + (K.lowering B : ℤ)) hij)
  parity i := by
    have hy := Int.odd_iff.1 (hK.odd_add_card_of_mem_entries
      (hl.image_eq ▸ mem_image_of_mem (fun i ↦ l i + K.lowering B) (mem_univ i)))
    have hr := K.rank_mod_two (B := B) fun c _ ↦ hK.even_length_add_card c
    have hδ := K.lowering_eq_mod_two B
    rw [hl.card_eq, Int.even_iff]
    generalize #K.stem * #B = P at hr hδ
    omega
  gap_le i j hne := by
    have hmem (i : ι) : l i + K.lowering B ∈ K.entries B :=
      hl.image_eq ▸ mem_image_of_mem (fun i ↦ l i + K.lowering B) (mem_univ i)
    simpa using hK.two_mul_le_abs_sub_of_sign_ne (hmem i) (hmem j)
      fun heq ↦ hne (by rw [hl.sign_eq, hl.sign_eq, heq])

/-- Inserting a center `c` adds its block to the raised entries of the parameter. -/
theorem IsParam.image_eq_union_centeredBlock {σ' : ℤˣ} (hl : K.IsParam B σ s l)
    (hl' : K.IsParam (insert c B) σ' s' l') :
    univ.image (fun r ↦ l' r + K.lowering (insert c B)) =
      univ.image (fun i ↦ l i + K.lowering B) ∪ centeredBlock (K.center c) (K.length c) := by
  rw [hl.image_eq, hl'.image_eq, entries_insert]

/-- Inserting a center `c ∉ B` with the same sign `σ` changes the sign of a common raised entry
iff `c` flips it. -/
theorem IsParam.ne_iff_flips (hl : K.IsParam B σ s l) (hl' : K.IsParam (insert c B) σ s' l')
    (hc : c ∉ B) {i : ι} {r : ι'}
    (heq : l i + K.lowering B = l' r + K.lowering (insert c B)) :
    s i ≠ s' r ↔ K.Flips c (l i + K.lowering B) := by
  rw [hl.sign_eq, hl'.sign_eq, ← heq, ne_eq, mul_right_inj, ← ne_eq, ne_comm,
    sign_insert_ne_iff hc]

/-- The ranks of the parameters before and after inserting a center `c ∉ B` into a separated
system, and their parities: the parity of each rank is the lowering of the other parameter. -/
private theorem IsParam.card_insert (hK : K.IsSeparated h) (hc : c ∉ B)
    (hl : K.IsParam B σ s l) (hl' : K.IsParam (insert c B) σ s' l') :
    card ι' = card ι + K.length c ∧ card ι % 2 = K.lowering (insert c B) ∧
      card ι' % 2 = K.lowering B := by
  have hr := K.rank_mod_two (B := B) fun c _ ↦ hK.even_length_add_card c
  have hr' := K.rank_mod_two (B := insert c B) fun c _ ↦ hK.even_length_add_card c
  have hδ := K.lowering_eq_mod_two B
  have hδ' := K.lowering_eq_mod_two (insert c B)
  rw [K.rank_insert hc, card_insert_of_notMem hc, Nat.mul_add_one] at hr'
  rw [card_insert_of_notMem hc, Nat.mul_add_one] at hδ'
  rw [hl.card_eq, hl'.card_eq, K.rank_insert hc]
  generalize #K.stem * #B = P at hr hr' hδ hδ'
  omega

/-- Inserting a down center: in a separated system with bound `h`, if `l` is `λ_B` and `l'` is
`λ_{B ∪ {c}}` with the same sign, for a down center `c ∉ B`, then `l` and `l'` satisfy the block
rule with every gap `gap ≤ h` (in particular `500 (n + n')³` when `h ≥ 500 (n + n')³`) for the
character shifts `e_c + ⌊n/2⌋` and `e_c + ⌊n'/2⌋`, where `n`, `n'` are the ranks. -/
theorem IsParam.isBlockRule_insert {gap : ℕ} (hK : K.IsSeparated h) (hc : c ∉ B)
    (hdown : K.kind c = .down) (hgap : gap ≤ h) (hl : K.IsParam B σ s l)
    (hl' : K.IsParam (insert c B) σ s' l') :
    IsBlockRule gap s s' (K.center c + (card ι / 2 : ℕ)) (K.center c + (card ι' / 2 : ℕ)) l l' := by
  obtain ⟨hcard, hδ, hδ'⟩ := hl.card_insert hK hc hl'
  rw [isBlockRule_iff_of_floor _ (by omega), hδ, hδ', show card ι' - card ι = K.length c by omega]
  refine ⟨⟨(hl.hasGap hK).mono hgap, (hl'.hasGap hK).mono hgap⟩,
    hl.image_eq_union_centeredBlock hl', fun i r heq ↦ ?_⟩
  rw [hl.ne_iff_flips hl' hc heq, K.flips_iff_of_kind_eq_down hdown]

/-- Lowering the negation of `f` by `d` negates the entries of `f` raised by `d`. -/
private theorem image_neg_sub {κ : Type*} [Fintype κ] (f : κ → ℤ) (d : ℕ) :
    univ.image (fun r ↦ (-f) r - d) = (univ.image fun r ↦ f r + d).image Neg.neg := by
  rw [image_image]
  congr 1
  funext r
  simp only [Pi.neg_apply, Function.comp_apply]
  omega

/-- Inserting an up center: in a separated system with bound `h`, if `l` is `λ_B` and `l'` is
`λ_{B ∪ {c}}` with the same sign, for an up center `c ∉ B`, then `-l` and `-l'` satisfy the block
rule with every gap `gap ≤ h` (in particular `500 (n + n')³` when `h ≥ 500 (n + n')³`) for the
character shifts `-e_c + ⌈n/2⌉` and `-e_c + ⌈n'/2⌉`, where `n`, `n'` are the ranks. -/
theorem IsParam.isBlockRule_neg_insert {gap : ℕ} (hK : K.IsSeparated h) (hc : c ∉ B)
    (hup : K.kind c = .up) (hgap : gap ≤ h) (hl : K.IsParam B σ s l)
    (hl' : K.IsParam (insert c B) σ s' l') :
    IsBlockRule gap s s' (-K.center c + ((card ι + 1) / 2 : ℕ))
      (-K.center c + ((card ι' + 1) / 2 : ℕ)) (-l) (-l') := by
  obtain ⟨hcard, hδ, hδ'⟩ := hl.card_insert hK hc hl'
  rw [isBlockRule_iff_of_ceil _ (by omega), hδ, hδ', show card ι' - card ι = K.length c by omega]
  refine ⟨⟨(hl.hasGap hK).neg.mono hgap, (hl'.hasGap hK).neg.mono hgap⟩, ?_, fun i r heq ↦ ?_⟩
  · rw [image_neg_sub, image_neg_sub, hl.image_eq_union_centeredBlock hl', image_union,
      image_neg_centeredBlock]
  · simp only [Pi.neg_apply] at heq ⊢
    rw [hl.ne_iff_flips hl' hc (by omega), K.flips_iff_of_kind_eq_up hup]
    omega

end IsParam

end CenterSystem

end TauCeti.DiscreteSeries
