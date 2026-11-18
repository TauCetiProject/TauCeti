/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.PeriodicityLemma
public import Mathlib.Data.List.Rotate

import Mathlib.Data.List.Flatten
import TauCeti.Data.List.Infix

/-!
# Periods of powers of a list

Write `lⁿ` for the concatenation `(replicate n l).flatten` of `n` copies of a list `l`. A power
`lⁿ` has the period `|l|` (`List.HasPeriod`), and conversely a list with a period `d > 0` is
`A^r A₁` with `A` its prefix of length `d`, `r` the quotient of its length by `d` and `A₁` a prefix
of `A`. The factors of the powers of `l` that are at least as long as `l` begin with a rotation of
`l`: the factor of `lᵐ` starting at position `o` begins with `l.rotate o`. Every factor of a power
of a nonempty list `l` also occurs in that power at a position `o < |l|`, and a power of a rotation
of `l` is a factor of a power of `l`.

These are the combinatorial facts behind periodic words in free groups
(`TauCeti/GroupTheory/FreeGroup/Periodic.lean`), where they are combined with the
Fine–Wilf periodicity lemma (`List.HasPeriod.gcd`).

## Main results

* `List.hasPeriod_flatten_replicate`: `lⁿ` has period `|l|`.
* `List.HasPeriod.flatten_replicate_take_append_take`: a list with a period `d` is `A^r A₁`, with
  `A` its prefix of length `d`.
* `List.take_eq_rotate_of_prefix_drop_flatten_replicate`: a factor of `lᵐ` starting at position `o`,
  at least as long as `l`, begins with `l.rotate o`.
* `List.IsInfix.exists_prefix_drop_flatten_replicate`: a factor of a power of a nonempty `l`
  occurs in it at a position `o < |l|`.
* `List.IsInfix.take_isRotated_of_flatten_replicate`: a factor of a power of `l`, at least as long
  as `l`, begins with a rotation of `l`.
* `List.IsRotated.flatten_replicate_infix`: a power of a rotation of `l` is a factor of a power
  of `l`.
-/

public section

namespace List

variable {α : Type*}

/-- The concatenation of `n` copies of `l` has the period `|l|`. -/
theorem hasPeriod_flatten_replicate (l : List α) (n : ℕ) :
    ((replicate n l).flatten).HasPeriod l.length := by
  cases n with
  | zero => simp
  | succ n =>
    simpa [HasPeriod, replicate_succ] using flatten_replicate_prefix_flatten_replicate l n.le_succ

/-- **The form `A^r A₁` of a periodic list.** A list with a period `d` is the concatenation of
`|l| / d` copies of its prefix `A` of length `d`, followed by the prefix of length `|l| % d`, which
is a proper prefix of `A` when `0 < d ≤ |l|`. -/
theorem HasPeriod.flatten_replicate_take_append_take {l : List α} {d : ℕ} (h : l.HasPeriod d) :
    (replicate (l.length / d) (l.take d)).flatten ++ l.take (l.length % d) = l := by
  induction hn : l.length using Nat.strong_induction_on generalizing l with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos d with rfl | hd0
    · simp [← hn]
    rcases lt_or_ge n d with hlt | hle
    · rw [Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt, ← hn]
      simp
    -- peel off the first block: `drop d l` keeps the period and is a prefix of `l`
    have hdrop := ih (n - d) (by lia) (h.infix (drop_suffix d l).isInfix) (by simp [hn])
    have htake {k : ℕ} (hk : k ≤ n - d) : (l.drop d).take k = l.take k :=
      ((h.drop_prefix d).take k).eq_of_length (by simp [hn]; lia)
    have hrep : (replicate ((n - d) / d) ((l.drop d).take d)).flatten =
        (replicate ((n - d) / d) (l.take d)).flatten := by
      rcases lt_or_ge (n - d) d with h' | h'
      · simp [Nat.div_eq_of_lt h']
      · rw [htake h']
    rw [Nat.div_eq_sub_div hd0 hle, Nat.mod_eq_sub_mod hle, replicate_succ, flatten_cons,
      append_assoc, ← hrep, ← htake (k := (n - d) % d) (Nat.mod_le _ _), hdrop, take_append_drop]

/-- The factor of the concatenation of `m` copies of `l` that starts at position `o` and is at
least as long as `l` begins with the rotation of `l` by `o`. -/
theorem take_eq_rotate_of_prefix_drop_flatten_replicate {w l : List α} {m o : ℕ}
    (h : w <+: ((replicate m l).flatten).drop o) (hl : l.length ≤ w.length) :
    w.take l.length = l.rotate o := by
  rcases eq_or_ne l [] with rfl | hl0
  · simp
  obtain ⟨t, ht⟩ := h
  have hlen := congrArg length ht
  simp only [length_append, length_drop, length_flatten, map_replicate, sum_replicate_nat] at hlen
  have := length_pos_iff.2 hl0
  rw [← take_drop_flatten_replicate l (m := m) (by lia), ← ht, take_append_of_le_length hl]

/-- A factor of the concatenation of `n` copies of a nonempty list `l` also occurs in it at a
position `o < |l|`. -/
theorem IsInfix.exists_prefix_drop_flatten_replicate {w l : List α} {n : ℕ}
    (h : w <:+: (replicate n l).flatten) (hl : l ≠ []) :
    ∃ o < l.length, w <+: ((replicate n l).flatten).drop o := by
  obtain ⟨s, t, hst⟩ := h
  have hpos := length_pos_iff.2 hl
  have hlen := congrArg length hst
  simp only [length_append, length_flatten, map_replicate, sum_replicate_nat] at hlen
  set q := s.length / l.length with hq_def
  have hq : q ≤ n := Nat.div_le_of_le_mul (by lia)
  refine ⟨s.length % l.length, Nat.mod_lt _ hpos, IsPrefix.trans ⟨t, ?_⟩
    ((flatten_replicate_prefix_flatten_replicate l (Nat.sub_le n q)).drop _)⟩
  -- the position `|s|` is `q` whole copies of `l` followed by `|s| % |l|` letters
  have hsplit : (replicate n l).flatten =
      (replicate q l).flatten ++ (replicate (n - q) l).flatten := by
    rw [← flatten_append, ← replicate_add, Nat.add_sub_cancel' hq]
  have hq' : s.length = ((replicate q l).flatten).length + s.length % l.length := by
    simp [hq_def, Nat.div_add_mod']
  rw [← drop_length_add_append (l₁ := (replicate q l).flatten), ← hq', ← hsplit, ← hst,
    append_assoc, drop_left]

/-- A factor of a concatenation of copies of `l`, at least as long as `l`, begins with a rotation
of `l`. -/
theorem IsInfix.take_isRotated_of_flatten_replicate {w l : List α} {n : ℕ}
    (h : w <:+: (replicate n l).flatten) (hl : l.length ≤ w.length) : w.take l.length ~r l := by
  obtain ⟨s, t, hst⟩ := h
  rw [take_eq_rotate_of_prefix_drop_flatten_replicate (m := n) (o := s.length)
    ⟨t, by rw [← hst, append_assoc, drop_left]⟩ hl]
  exact IsRotated.forall l _

/-- If `l` is a rotation of `l'`, the concatenation of `n` copies of `l` is a factor of the
concatenation of `n + 1` copies of `l'`. -/
theorem IsRotated.flatten_replicate_infix {l l' : List α} (h : l ~r l') (n : ℕ) :
    (replicate n l).flatten <:+: (replicate (n + 1) l').flatten := by
  obtain ⟨k, hk, rfl⟩ := isRotated_iff_mod.1 h.symm
  rw [rotate_eq_drop_append_take hk]
  -- `(x ++ y)ⁿ⁺¹ = x ++ (y ++ x)ⁿ ++ y` with `x = l'.take k` and `y = l'.drop k`
  refine ⟨l'.take k, l'.drop k, ?_⟩
  have := append_flatten_map_append (replicate n (l'.drop k)) (l'.take k)
  simp only [map_replicate] at this
  rw [this, replicate_succ', flatten_append, flatten_singleton, append_assoc, take_append_drop]

end List
