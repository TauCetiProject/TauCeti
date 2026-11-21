/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.Rotate
public import Mathlib.Data.Nat.ModEq

import TauCeti.Data.List.Infix

/-!
# Commuting and conjugate words

Elementary combinatorics of words (lists) under concatenation, after Lyndon and Schützenberger:
these are the free-monoid lemmas on which their solution of the equation `a^M = b^N c^P` in a free
group rests. Write `wⁿ` for the concatenation `(replicate n w).flatten` of `n` copies of `w`.

* A solution of the conjugacy equation `a ++ b = b ++ c` with `a ≠ []` has the form
  `a = u ++ v`, `b = (u ++ v)ᵏ ++ u`, `c = v ++ u` (`List.exists_flatten_replicate_of_append_eq`).
* Two words that commute, `a ++ b = b ++ a`, are powers of a common word
  (`List.exists_eq_flatten_replicate_of_append_comm`).
* If powers of `a` and of `b` have a common prefix of length `|a| + |b|`, then `a` and `b`
  commute (`List.append_comm_of_prefix_flatten_replicate`); this is a weak form of the
  periodicity lemma of Fine and Wilf (`List.HasPeriod.gcd`). In particular `aᵐ = bⁿ` with
  `m ≠ 0` forces `a` and `b` to commute (`List.append_comm_of_flatten_replicate_eq`).
* A word `l` that is not a power `uⁿ` of a word with `n ≥ 2` is fixed by no nontrivial rotation:
  `l.rotate k = l` only when `|l|` divides `k` (`List.rotate_eq_self_iff_length_dvd`), so that its
  rotations by `i` and by `j` agree exactly when `i ≡ j` modulo `|l|`
  (`List.rotate_eq_rotate_iff_modEq`). Hence a word at least as long as `l` occurs in the powers of
  `l` only at positions in a single residue class modulo `|l|`
  (`List.modEq_of_prefix_drop_flatten_replicate`).

## References

* R. C. Lyndon, M. P. Schützenberger, *The equation `a^M = b^N c^P` in a free group*, Michigan
  Math. J. 9 (1962), 289–298, §2, Lemmas 2–4 and Corollary 4.1.
* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §5.4, before Lemma 20 (uniqueness of the cut), and §7.1, proof of Lemma 57 (a word
  fixed by a nontrivial cyclic shift is a proper power).
* N. J. Fine, H. S. Wilf, *Uniqueness theorems for periodic functions*, Proc. Amer. Math. Soc. 16
  (1965), 109–114.
-/

public section

namespace List

variable {α : Type*}

/-- **The conjugacy equation for words.** If `a ++ b = b ++ c` with `a ≠ []`, then `a = u ++ v`,
`c = v ++ u` and `b = (u ++ v)ᵏ ++ u` for some words `u`, `v` and some `k`. -/
theorem exists_flatten_replicate_of_append_eq {a b c : List α} (h : a ++ b = b ++ c)
    (ha : a ≠ []) : ∃ u v : List α, ∃ k : ℕ, a = u ++ v ∧ c = v ++ u ∧
      b = (replicate k (u ++ v)).flatten ++ u := by
  induction hn : b.length using Nat.strong_induction_on generalizing b with
  | _ n ih =>
    obtain ⟨b', rfl, hb'⟩ | ⟨v, rfl, rfl⟩ := append_eq_append_iff.1 h
    · obtain ⟨u, v, k, rfl, rfl, rfl⟩ := ih _ (by simp [← hn, length_pos_iff, ha]) hb' rfl
      exact ⟨u, v, k + 1, rfl, rfl, by simp [replicate_succ]⟩
    · exact ⟨b, v, 0, rfl, rfl, by simp⟩

/-- **Commuting words are powers of a common word.** If `a ++ b = b ++ a`, then `a = wⁱ` and
`b = wʲ` for a single word `w`. -/
theorem exists_eq_flatten_replicate_of_append_comm {a b : List α} (h : a ++ b = b ++ a) :
    ∃ w : List α, ∃ i j : ℕ, a = (replicate i w).flatten ∧ b = (replicate j w).flatten := by
  induction hn : a.length + b.length using Nat.strong_induction_on generalizing a b with
  | _ n ih =>
    rcases eq_or_ne a [] with rfl | ha
    · exact ⟨b, 0, 1, by simp, by simp⟩
    rcases eq_or_ne b [] with rfl | hb
    · exact ⟨a, 1, 0, by simp, by simp⟩
    obtain ⟨b', rfl, hb'⟩ | ⟨a', rfl, ha'⟩ := append_eq_append_iff.1 h
    · obtain ⟨w, i, j, rfl, rfl⟩ := ih _ (by simp [← hn, length_pos_iff, ha]) hb' rfl
      exact ⟨w, i, i + j, rfl, by rw [replicate_add, flatten_append]⟩
    · obtain ⟨w, i, j, rfl, rfl⟩ := ih _ (by simp [← hn, length_pos_iff, hb]) ha' rfl
      exact ⟨w, i + j, i, by rw [replicate_add, flatten_append], rfl⟩

/-- If a power of `a` and a power of `b` have a common prefix of length at least
`|a| + |b|`, then `a` and `b` commute. With the optimal length `|a| + |b| - gcd(|a|, |b|)` in
place of `|a| + |b|` this follows from the periodicity lemma of Fine and Wilf
(`List.HasPeriod.gcd`). -/
theorem append_comm_of_prefix_flatten_replicate {a b x : List α} {m n : ℕ}
    (ha : x <+: (replicate m a).flatten) (hb : x <+: (replicate n b).flatten)
    (hx : a.length + b.length ≤ x.length) : a ++ b = b ++ a := by
  -- A prefix `x` of a power of `c` is also a prefix of `c ++ x`, and `c` is a prefix of `x` once
  -- `x` is at least as long as `c`.
  have key {c : List α} {k : ℕ} (hc : x <+: (replicate k c).flatten) : x <+: c ++ x := by
    have : x <+: c ++ (replicate k c).flatten := by
      simpa [replicate_succ] using hc.trans (flatten_replicate_prefix_flatten_replicate c k.le_succ)
    exact prefix_of_prefix_length_le this ((prefix_append_right_inj c).2 hc) (by simp)
  have hax : a <+: x := prefix_of_prefix_length_le (prefix_append a x) (key ha) (by lia)
  have hbx : b <+: x := prefix_of_prefix_length_le (prefix_append b x) (key hb) (by lia)
  -- Hence `a ++ b` and `b ++ a` are prefixes of `x` of the same length.
  have hlen : (a ++ b).length = (b ++ a).length := by simp [Nat.add_comm]
  have h₁ : a ++ b <+: x :=
    prefix_of_prefix_length_le ((prefix_append_right_inj a).2 hbx) (key ha) (by simpa using hx)
  have h₂ : b ++ a <+: x := prefix_of_prefix_length_le ((prefix_append_right_inj b).2 hax)
    (key hb) (by simpa [Nat.add_comm] using hx)
  exact (prefix_of_prefix_length_le h₁ h₂ hlen.le).eq_of_length hlen

/-- Words with a common nonzero power commute: `aᵐ = bⁿ` with `m ≠ 0` gives
`a ++ b = b ++ a`. For `m = n = 0` both powers are `[]` and nothing follows. -/
theorem append_comm_of_flatten_replicate_eq {a b : List α} {m n : ℕ} (hm : m ≠ 0)
    (h : (replicate m a).flatten = (replicate n b).flatten) : a ++ b = b ++ a := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp_all
  have hlen : m * a.length = n * b.length := by simpa using congrArg length h
  refine append_comm_of_prefix_flatten_replicate (x := (replicate (m + m) a).flatten)
    (m := m + m) (n := n + n) prefix_rfl ?_ ?_
  · rw [replicate_add, flatten_append, h, ← flatten_append, ← replicate_add]
  · have : (replicate (m + m) a).flatten.length = m * a.length + m * a.length := by
      simp [Nat.add_mul]
    have := Nat.le_mul_of_pos_left a.length (Nat.pos_of_ne_zero hm)
    have := Nat.le_mul_of_pos_left b.length hn
    lia

/-- A word that is not a power `uⁿ` of a word `u` with `n ≥ 2` is nonempty, since `[] = []²`. -/
theorem ne_nil_of_not_exists_eq_flatten_replicate {l : List α}
    (hl : ¬∃ u n, 2 ≤ n ∧ l = (replicate n u).flatten) : l ≠ [] := by
  rintro rfl
  exact hl ⟨[], 2, le_rfl, by simp⟩

/-- **A word that is not a power is fixed by no nontrivial rotation** ([IFT], §7.1, proof of
Lemma 57). If `l` is not a power `uⁿ` of a word `u` with `n ≥ 2`, then rotating `l` by `k` gives
`l` back exactly when `|l|` divides `k`. -/
theorem rotate_eq_self_iff_length_dvd {l : List α}
    (hl : ¬∃ u n, 2 ≤ n ∧ l = (replicate n u).flatten) {k : ℕ} :
    l.rotate k = l ↔ l.length ∣ k := by
  refine ⟨fun hk => ?_, fun ⟨c, hc⟩ => by rw [hc, rotate_length_mul]⟩
  have hpos := length_pos_iff.2 (ne_nil_of_not_exists_eq_flatten_replicate hl)
  have hlt := Nat.mod_lt k hpos
  rw [← rotate_mod, rotate_eq_drop_append_take hlt.le] at hk
  rw [Nat.dvd_iff_mod_eq_zero]
  by_contra hr
  -- the two pieces of `l` cut at `k % |l|` commute, hence are powers of a common word
  obtain ⟨u, i, j, hi, hj⟩ := exists_eq_flatten_replicate_of_append_comm
    (a := l.take (k % l.length)) (b := l.drop (k % l.length)) (by rw [take_append_drop, hk])
  have hi0 : i ≠ 0 := by rintro rfl; simpa [hpos.ne', hr] using congrArg length hi
  have hj0 : j ≠ 0 := by rintro rfl; have := congrArg length hj; simp at this; lia
  exact hl ⟨u, i + j, by lia, by
    rw [← take_append_drop (k % l.length) l, hi, hj, replicate_add, flatten_append]⟩

/-- Let `l` be a word that is not a power `uⁿ` of a word with `n ≥ 2`. Its rotations by amounts
that are not congruent modulo `|l|` are distinct: rotating `l` by `i` and by `j` gives the same
word exactly when `i ≡ j` modulo `|l|`. -/
theorem rotate_eq_rotate_iff_modEq {l : List α}
    (hl : ¬∃ u n, 2 ≤ n ∧ l = (replicate n u).flatten) {i j : ℕ} :
    l.rotate i = l.rotate j ↔ i ≡ j [MOD l.length] := by
  refine ⟨fun h => ?_, fun h => by rw [← rotate_mod l i, h, rotate_mod]⟩
  wlog hij : i ≤ j generalizing i j
  · exact (this h.symm (by lia)).symm
  -- cancel the common rotation by `i`
  rw [← Nat.sub_add_cancel hij, ← rotate_rotate, rotate_eq_rotate, eq_comm,
    rotate_eq_self_iff_length_dvd hl] at h
  exact (Nat.modEq_iff_dvd' hij).2 h

/-- **Uniqueness of the cut** ([IFT], §5.4, before Lemma 20). Let `l` be a word that is not a power
`uⁿ` of a word with `n ≥ 2`. If a word `w` at least as long as `l` occurs in the concatenation of
copies of `l` at the positions `o` and `o'` (of possibly different numbers of copies), then
`o ≡ o'` modulo `|l|`. -/
theorem modEq_of_prefix_drop_flatten_replicate {w l : List α}
    (hl : ¬∃ u n, 2 ≤ n ∧ l = (replicate n u).flatten) (hw : l.length ≤ w.length) {m m' o o' : ℕ}
    (h : w <+: ((replicate m l).flatten).drop o)
    (h' : w <+: ((replicate m' l).flatten).drop o') : o ≡ o' [MOD l.length] := by
  rw [← rotate_eq_rotate_iff_modEq hl, ← take_eq_rotate_of_prefix_drop_flatten_replicate h hw,
    take_eq_rotate_of_prefix_drop_flatten_replicate h' hw]

/-- The cut is not unique for a power: the word `[0, 0] = [0]²` occurs in its square at the
positions `0` and `1`, which are not congruent modulo `2`. -/
example : [0, 0] = (replicate 2 [0]).flatten ∧
    [0, 0] <+: ((replicate 2 [0, 0]).flatten).drop 0 ∧
    [0, 0] <+: ((replicate 2 [0, 0]).flatten).drop 1 ∧ ¬0 ≡ 1 [MOD [0, 0].length] := by
  decide

end List
