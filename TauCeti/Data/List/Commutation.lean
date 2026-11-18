/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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

## References

* R. C. Lyndon, M. P. Schützenberger, *The equation `a^M = b^N c^P` in a free group*, Michigan
  Math. J. 9 (1962), 289–298, §2, Lemmas 2–4 and Corollary 4.1.
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

end List
