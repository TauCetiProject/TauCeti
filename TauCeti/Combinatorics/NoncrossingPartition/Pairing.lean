/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.NoncrossingPartition.Catalan
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Weighted sums over noncrossing pairings

In a noncrossing pairing of a nonempty finite set `s` of positions in a linear order, the first
position `m = s.min' hs` is paired with some position `x ∈ s` strictly after `m`, and no arc joins
an interior position `m < y < x` to a position after `x`. Weighting each two-element part or each
directed arc `(i, j)` (`i < j`) multiplicatively therefore gives a quadratic recurrence by the
partner `x` of `m`:

`∑_{P ∈ NC₂(s)} ∏_{(i, j) ∈ P} w i j =`
`  ∑_{x ∈ s, m < x} w m x * (∑_{M ∈ NC₂(s ∩ (m, x))} ∏ M) * (∑_{R ∈ NC₂(s_{>x})} ∏ R)`.

This is the combinatorial recurrence underlying both the Fock-space vacuum Wick formula for sums
of creation and annihilation operators and the moment formula for semicircular systems, where a
directed arc `(i, j)` with `i < j` carries a possibly nonsymmetric covariance `w i j`.

The recurrence is deduced by applying the general first-block weighted recurrence
`TauCeti.NoncrossingPartition.sum_mul_prod_eq_sum_mul_sum` twice—first on `s`, then on
`{y ∈ s | y < x}`—with weights supported on blocks of size two.

## Main results

* `TauCeti.NoncrossingPartition.sum_prod_ite_card_eq_two_eq_sum_isPairing` — a multiplicative sum
  over `NC(s)` whose block weights vanish off blocks of size two reduces to `NC₂(s)`.
* `TauCeti.NoncrossingPartition.sum_prod_eq_sum_isPairing_prod_orderedPairs` — a multiplicative
  sum over `NC(s)` whose block weights vanish off size-two blocks and equal `w i j` on `{i, j}`
  (`i < j`) reduces to the directed-arc sum over `NC₂(s)`.
* `TauCeti.NoncrossingPartition.sum_isPairing_prod_eq_sum` and
  `TauCeti.NoncrossingPartition.sum_isPairing_prod_orderedPairs_eq_sum` — the weighted recurrence
  of noncrossing pairings by the partner of the first position, for block weights and directed-arc
  weights.
* `TauCeti.NoncrossingPartition.sum_isPairing_eq_zero` — any sum over `NC₂(s)` vanishes when `#s`
  is odd.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lectures 7–9.
-/

public section

open Finset

namespace TauCeti.NoncrossingPartition

variable {α M : Type*} [LinearOrder α] {s : Finset α}

/-- The empty partition is the unique noncrossing pairing of `∅`. -/
instance instUniqueIsPairingEmpty :
    Unique {P : NoncrossingPartition (∅ : Finset α) // P.val.IsPairing} where
  default := ⟨⊥, Finpartition.isPairing_iff.2 fun B hB => by simp at hB⟩
  uniq P := Subtype.ext (Subsingleton.elim P.val ⊥)

/-- A finite set of odd size has no noncrossing pairing. -/
theorem isEmpty_isPairing (hs : Odd #s) :
    IsEmpty {P : NoncrossingPartition s // P.val.IsPairing} :=
  ⟨fun P => Nat.not_even_iff_odd.2 hs P.property.even_card⟩

/-- Any sum over the noncrossing pairings of a set of odd size vanishes. -/
theorem sum_isPairing_eq_zero [AddCommMonoid M] (hs : Odd #s)
    (f : {P : NoncrossingPartition s // P.val.IsPairing} → M) :
    ∑ P, f P = 0 := by
  have := isEmpty_isPairing hs
  simp

/-- On the empty set, the sum over noncrossing pairings of any empty product of block weights is
`1`. -/
theorem sum_isPairing_prod_empty [AddCommMonoid M] [CommMonoid M] (F : Finset α → M) :
    (∑ P : {P : NoncrossingPartition (∅ : Finset α) // P.val.IsPairing},
        ∏ B ∈ P.val.val.parts, F B) = 1 := by
  rw [univ_unique, sum_singleton]
  have hbot : (default : {P : NoncrossingPartition (∅ : Finset α) // P.val.IsPairing}).val = ⊥
      := rfl
  simp [hbot]

/-- On the empty set, the sum over noncrossing pairings of any empty product of directed-arc
weights is `1`. -/
theorem sum_isPairing_prod_orderedPairs_empty [AddCommMonoid M] [CommMonoid M] (w : α → α → M) :
    (∑ P : {P : NoncrossingPartition (∅ : Finset α) // P.val.IsPairing},
        ∏ p ∈ P.val.val.orderedPairs, w p.1 p.2) = 1 := by
  rw [univ_unique, sum_singleton]
  have hbot : (default : {P : NoncrossingPartition (∅ : Finset α) // P.val.IsPairing}).val = ⊥
      := rfl
  simp [hbot]

variable [CommSemiring M]

/-- Weighting blocks of size two by `F` and all other blocks by `0`, only the noncrossing pairings
contribute to the sum over `NC(s)`. -/
theorem sum_prod_ite_card_eq_two_eq_sum_isPairing (s : Finset α) (F : Finset α → M) :
    (∑ P : NoncrossingPartition s, ∏ B ∈ P.val.parts, if #B = 2 then F B else 0) =
      ∑ P : {P : NoncrossingPartition s // P.val.IsPairing}, ∏ B ∈ P.val.val.parts, F B := by
  have hterm (P : NoncrossingPartition s) :
      (∏ B ∈ P.val.parts, if #B = 2 then F B else 0) =
        if P.val.IsPairing then ∏ B ∈ P.val.parts, F B else 0 := by
    by_cases hP : P.val.IsPairing
    · simp only [hP, ↓reduceIte]
      exact prod_congr rfl fun B hB => ite_eq_left (Finpartition.isPairing_iff.1 hP B hB)
    · simp only [hP, ↓reduceIte]
      rw [Finpartition.isPairing_iff, not_forall] at hP
      obtain ⟨B, hB, hcard⟩ := by simpa only [not_imp] using hP
      exact prod_eq_zero hB (ite_eq_right hcard)
  simp_rw [hterm, ← sum_filter]
  exact sum_subtype _ (p := fun P : NoncrossingPartition s => P.val.IsPairing)
    (fun _ => by simp) fun P => ∏ B ∈ P.val.parts, F B

/-- If a block weight `κ` on subsets of `s` vanishes on every nonempty block of size other than two
and agrees with `w i j` on `{i, j}` whenever `i < j`, then the multiplicative sum of `κ` over
`NC(s)` equals the directed-arc sum of `w` over `NC₂(s)`. -/
theorem sum_prod_eq_sum_isPairing_prod_orderedPairs {κ : Finset α → M} (w : α → α → M)
    (hpair : ∀ {i j}, i ∈ s → j ∈ s → i < j → κ {i, j} = w i j)
    (hne : ∀ B ⊆ s, B.Nonempty → #B ≠ 2 → κ B = 0) :
    (∑ P : NoncrossingPartition s, ∏ B ∈ P.val.parts, κ B) =
      ∑ P : {P : NoncrossingPartition s // P.val.IsPairing},
        ∏ p ∈ P.val.val.orderedPairs, w p.1 p.2 := by
  have hκ (P : NoncrossingPartition s) :
      ∏ B ∈ P.val.parts, κ B =
        ∏ B ∈ P.val.parts, if #B = 2 then κ B else 0 :=
    prod_congr rfl fun B hB => by
      split_ifs with hcard
      · rfl
      · exact hne B (P.val.le hB) (P.val.nonempty_of_mem_parts hB) hcard
  simp_rw [hκ]
  rw [sum_prod_ite_card_eq_two_eq_sum_isPairing]
  refine sum_congr rfl fun P _ => ?_
  rw [← P.property.prod_orderedPairs]
  exact prod_congr rfl fun p hp =>
    hpair (Finpartition.fst_mem_of_mem_orderedPairs hp)
      (Finpartition.snd_mem_of_mem_orderedPairs hp) (Finpartition.lt_of_mem_orderedPairs hp)

/-- Evaluating the first-block recurrence on `{y ∈ s | y < x}` for weights supported on blocks of
size two leaves only the partner `z = s.min' hs`, since any `m < z < x` puts at least the three
positions `m`, `z`, `x` in the first block. -/
private theorem sum_lt_partner_eq (hs : s.Nonempty) {x : α} (hmx : s.min' hs < x)
    (F : Finset α → M) :
    (∑ L : NoncrossingPartition {y ∈ s | y < x},
        (if #(insert x (L.val.part (s.min' hs))) = 2 then F (insert x (L.val.part
            (s.min' hs))) else 0)
          * ∏ B ∈ L.val.parts with s.min' hs ∉ B, if #B = 2 then F B else 0) =
      F {s.min' hs, x} *
        ∑ M : {M : NoncrossingPartition {y ∈ s | s.min' hs < y ∧ y < x} // M.val.IsPairing},
          ∏ B ∈ M.val.val.parts, F B := by
  set m := s.min' hs
  set F' : Finset α → M := fun B => if #B = 2 then F B else 0
  set t := {y ∈ s | y < x}
  have hmt : m ∈ t := mem_filter.2 ⟨s.min'_mem hs, hmx⟩
  have ht : t.Nonempty := ⟨m, hmt⟩
  have htmin : t.min' ht = m :=
    le_antisymm (t.min'_le m hmt) (s.min'_le _ (mem_filter.1 (t.min'_mem ht)).1)
  have hrec := sum_mul_prod_eq_sum_mul_sum ht (fun C => F' (insert x C)) F'
  rw [htmin] at hrec
  rw [hrec, sum_eq_single m]
  · -- At `z = m`, `{y ∈ t | y < m}` is empty, so `A = ⊥` is its unique partition.
    have hempty : {y ∈ t | y < m} = ∅ := eq_empty_of_forall_notMem fun y hy =>
      (s.min'_le y (mem_filter.1 (mem_filter.1 hy).1).1).not_gt (mem_filter.1 hy).2
    have hA : (∑ A : NoncrossingPartition {y ∈ t | y < m},
        F' (insert x (insert m (A.val.part m))) * ∏ B ∈ A.val.parts with m ∉ B, F' B) = F {m, x}
            := by
      rw [sum_eq_single ⊥ _ (fun h => absurd (mem_univ ⊥) h)]
      · have hpart : ((⊥ : Finpartition {y ∈ t | y < m}).part m) = ∅ :=
          Finpartition.part_eq_empty _ |>.2 (by simp [hempty])
        simp [F', coe_bot, hpart, hempty, pair_comm x m, card_pair hmx.ne]
      · exact fun A _ hA => absurd (eq_bot_of_eq_empty hempty A) hA
    have hmid : {y ∈ t | m < y} = {y ∈ s | m < y ∧ y < x} := by
      ext y
      simp only [t, mem_filter]
      tauto
    have hM : (∑ M : NoncrossingPartition {y ∈ t | m < y}, ∏ B ∈ M.val.parts, F' B) =
        ∑ M : NoncrossingPartition {y ∈ s | m < y ∧ y < x}, ∏ B ∈ M.val.parts, F' B :=
      congrArg (fun u : Finset α => ∑ M : NoncrossingPartition u, ∏ B ∈ M.val.parts, F' B) hmid
    rw [hA, hM, sum_prod_ite_card_eq_two_eq_sum_isPairing]
  · -- Any `z ∈ t` with `z ≠ m` satisfies `m < z < x`, putting three distinct elements in the block.
    intro z hz hzm
    have hmz : m < z := (s.min'_le z (mem_filter.1 hz).1).lt_of_ne (Ne.symm hzm)
    have hzx : z < x := (mem_filter.1 hz).2
    have hzero : (∑ A : NoncrossingPartition {y ∈ t | y < z},
        F' (insert x (insert z (A.val.part m))) * ∏ B ∈ A.val.parts with m ∉ B, F' B) = 0 := by
      refine sum_eq_zero fun A _ => ?_
      have hmA : m ∈ A.val.part m := A.val.mem_part_self.2 (mem_filter.2 ⟨hmt, hmz⟩)
      have hcard : 2 < #(insert x (insert z (A.val.part m))) :=
        Finset.two_lt_card_iff.2 ⟨m, z, x,
          mem_insert_of_mem (mem_insert_of_mem hmA),
          mem_insert_of_mem (mem_insert_self _ _),
          mem_insert_self _ _, hmz.ne, hmx.ne, hzx.ne⟩
      simp [F', hcard.ne']
    rw [hzero, zero_mul]
  · exact fun hm => absurd hmt hm

/-- *Weighted recurrence of noncrossing pairings* (block-weight form): summing a multiplicative
block weight `F` over the noncrossing pairings of a nonempty set `s` decomposes by the partner
`x > m` of `m = s.min' hs` into `F {m, x}` times the pairing sums strictly between `m` and `x` and
strictly after `x`. -/
theorem sum_isPairing_prod_eq_sum (hs : s.Nonempty) (F : Finset α → M) :
    (∑ P : {P : NoncrossingPartition s // P.val.IsPairing}, ∏ B ∈ P.val.val.parts, F B) =
      ∑ x ∈ s with s.min' hs < x,
        F {s.min' hs, x} *
          (∑ M : {M : NoncrossingPartition {y ∈ s | s.min' hs < y ∧ y < x} // M.val.IsPairing},
            ∏ B ∈ M.val.val.parts, F B) *
          ∑ R : {R : NoncrossingPartition {y ∈ s | x < y} // R.val.IsPairing},
            ∏ B ∈ R.val.val.parts, F B := by
  set m := s.min' hs
  let F' : Finset α → M := fun B => if #B = 2 then F B else 0
  rw [← sum_prod_ite_card_eq_two_eq_sum_isPairing,
    sum_congr rfl fun P _ => P.val.prod_parts_eq_mul_prod_filter_notMem (s.min'_mem hs) F',
    sum_mul_prod_eq_sum_mul_sum hs F' F', sum_filter]
  refine sum_congr rfl fun x hx => ?_
  split_ifs with hmx
  · rw [sum_lt_partner_eq hs hmx F, sum_prod_ite_card_eq_two_eq_sum_isPairing]
  · -- When `¬ m < x`, `x = m` and `insert m (L.1.part m) = {m}` has size `1 ≠ 2`.
    obtain rfl : x = m := le_antisymm (not_lt.1 hmx) (s.min'_le x hx)
    have hzero : (∑ L : NoncrossingPartition {y ∈ s | y < m},
        F' (insert m (L.val.part m)) * ∏ B ∈ L.val.parts with m ∉ B, F' B) = 0 := by
      refine sum_eq_zero fun L _ => ?_
      have hpart : L.val.part m = ∅ := L.val.part_eq_empty.2 fun h => (mem_filter.1 h).2.false
      simp [F', hpart]
    rw [hzero, zero_mul]

/-- *Weighted recurrence of noncrossing pairings* (directed-arc form): for any two-argument weight
`w : α → α → M`, the sum over `NC₂(s)` of `∏_{(i, j) ∈ P} w i j` decomposes by the partner `x > m`
of `m = s.min' hs`. -/
theorem sum_isPairing_prod_orderedPairs_eq_sum (hs : s.Nonempty) (w : α → α → M) :
    (∑ P : {P : NoncrossingPartition s // P.val.IsPairing},
        ∏ p ∈ P.val.val.orderedPairs, w p.1 p.2) =
      ∑ x ∈ s with s.min' hs < x,
        w (s.min' hs) x *
          (∑ M : {M : NoncrossingPartition {y ∈ s | s.min' hs < y ∧ y < x} // M.val.IsPairing},
            ∏ p ∈ M.val.val.orderedPairs, w p.1 p.2) *
          ∑ R : {R : NoncrossingPartition {y ∈ s | x < y} // R.val.IsPairing},
            ∏ p ∈ R.val.val.orderedPairs, w p.1 p.2 := by
  let F : Finset α → M := fun B => if h : B.Nonempty then w (B.min' h) (B.max' h) else 1
  have hF {a b : α} (hab : a < b) : F {a, b} = w a b := by
    have hne : ({a, b} : Finset α).Nonempty := insert_nonempty a {b}
    have hmin : ({a, b} : Finset α).min' hne = a := by
      refine le_antisymm (min'_le _ _ (mem_insert_self _ _)) (le_min' _ _ _ fun y hy => ?_)
      rcases mem_insert.1 hy with rfl | hy
      · exact le_rfl
      · exact (mem_singleton.1 hy ▸ hab).le
    have hmax : ({a, b} : Finset α).max' hne = b := by
      refine le_antisymm (max'_le _ _ _ fun y hy => ?_)
        (le_max' _ _ (mem_insert_of_mem (mem_singleton_self _)))
      rcases mem_insert.1 hy with rfl | hy
      · exact hab.le
      · exact (mem_singleton.1 hy).le
    simp [F, hne, hmin, hmax]
  have hprod {t : Finset α} (P : {P : NoncrossingPartition t // P.val.IsPairing}) :
      (∏ p ∈ P.val.val.orderedPairs, w p.1 p.2) = ∏ B ∈ P.val.val.parts, F B := by
    rw [← P.property.prod_orderedPairs]
    exact prod_congr rfl fun p hp => (hF (Finpartition.lt_of_mem_orderedPairs hp)).symm
  simp_rw [hprod]
  rw [sum_isPairing_prod_eq_sum hs F]
  exact sum_congr rfl fun x hx => by rw [hF (mem_filter.1 hx).2]

end TauCeti.NoncrossingPartition
