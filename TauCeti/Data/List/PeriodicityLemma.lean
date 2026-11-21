/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.PeriodicityLemma
public import Mathlib.Data.List.Rotate

import TauCeti.Data.List.Commutation
import TauCeti.Data.List.Infix
import TauCeti.Data.List.Rotate

/-!
# Periods of powers of a list

Write `lⁿ` for the concatenation `(replicate n l).flatten` of `n` copies of a list `l`. A power
`lⁿ` has the period `|l|` (`List.HasPeriod`), and conversely a list `l` with a period `d > 0` is
`A^r A₁` with `A = l.take d` (of length `min d |l|`), `r = |l| / d` and `A₁` the prefix of `l` of
length `|l| % d`, a prefix of `A`. Consequently a list `l` that is not a power `uⁿ` of a list with
`n ≥ 2` has no period properly dividing its length, and, combined with the periodicity lemma of
Fine and Wilf (`List.HasPeriod.gcd`): if `l` and `l'` are two such lists and a common factor of a
power of `l` and a power of `l'` has length at least `|l| + |l'| - gcd(|l|, |l'|)`, then `l'` is a
rotation of `l`.

## Main results

* `List.hasPeriod_flatten_replicate`: `lⁿ` has period `|l|`.
* `List.HasPeriod.flatten_replicate_take_append_take`: a list `l` with a period `d` is `A^r A₁`,
  with `A = l.take d`.
* `List.eq_length_of_hasPeriod_of_dvd`: a list that is not a power `uⁿ`, `n ≥ 2`, has no period
  properly dividing its length.
* `List.isRotated_of_infix_flatten_replicate`: overlapping periodicities.

## References

* N. J. Fine, H. S. Wilf, *Uniqueness theorems for periodic functions*, Proc. Amer. Math. Soc. 16
  (1965), 109–114.
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

/-- **The form `A^r A₁` of a periodic list.** A list `l` with a period `d` is the concatenation of
`|l| / d` copies of `A = l.take d` followed by the prefix of `l` of length `|l| % d`, which is a
proper prefix of `A` when `0 < d ≤ |l|`. -/
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

/-- A list `l` that is not a power `uⁿ` of a list with `n ≥ 2` has no period properly dividing its
length: a period `d` of `l` that divides `|l|` is `|l|` itself. -/
theorem eq_length_of_hasPeriod_of_dvd {l : List α}
    (hl : ¬∃ u n, 2 ≤ n ∧ l = (replicate n u).flatten) {d : ℕ} (h : l.HasPeriod d)
    (hd : d ∣ l.length) : d = l.length := by
  have hpos := length_pos_iff.2 (ne_nil_of_not_exists_eq_flatten_replicate hl)
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd hpos
  obtain ⟨k, hk⟩ := hd
  by_contra hne
  -- otherwise `l` is the power `(l.take d)ᵏ` with `k ≥ 2`
  refine hl ⟨l.take d, k, ?_, ?_⟩
  · rcases k with _ | _ | k <;> simp_all
  · have := h.flatten_replicate_take_append_take
    rw [hk, Nat.mul_mod_right, take_zero, append_nil, Nat.mul_div_cancel_left k hd0] at this
    exact this.symm

/-- **Overlapping periodicities.** Let `l` and `l'` be lists that are not powers `uⁿ` of lists with
`n ≥ 2`. If a list `w` of length at least `|l| + |l'| - gcd(|l|, |l'|)` is a factor of a
concatenation of copies of `l` and of a concatenation of copies of `l'`, then `l'` is a rotation
of `l`. -/
theorem isRotated_of_infix_flatten_replicate {w l l' : List α}
    (hl : ¬∃ u n, 2 ≤ n ∧ l = (replicate n u).flatten)
    (hl' : ¬∃ u n, 2 ≤ n ∧ l' = (replicate n u).flatten) {m m' : ℕ}
    (h : w <:+: (replicate m l).flatten) (h' : w <:+: (replicate m' l').flatten)
    (hw : l.length + l'.length - l.length.gcd l'.length ≤ w.length) : l' ~r l := by
  have hg := ((hasPeriod_flatten_replicate l m).infix h).gcd
    ((hasPeriod_flatten_replicate l' m').infix h') hw
  have hle : l.length ≤ w.length ∧ l'.length ≤ w.length := by
    have := Nat.gcd_le_left l'.length
      (length_pos_iff.2 (ne_nil_of_not_exists_eq_flatten_replicate hl))
    have := Nat.gcd_le_right l.length
      (length_pos_iff.2 (ne_nil_of_not_exists_eq_flatten_replicate hl'))
    lia
  -- the prefix of `w` of length `|x|`, a rotation of `x`, has the period `gcd(|l|, |l'|)`
  have key {x : List α} {k : ℕ} (hx : ¬∃ u n, 2 ≤ n ∧ x = (replicate n u).flatten)
      (hwx : w <:+: (replicate k x).flatten) (hxw : x.length ≤ w.length)
      (hdvd : l.length.gcd l'.length ∣ x.length) : l.length.gcd l'.length = x.length := by
    have hlen : (w.take x.length).length = x.length := by simpa using hxw
    rw [← hlen] at hdvd ⊢
    exact eq_length_of_hasPeriod_of_dvd
      ((hwx.take_isRotated_of_flatten_replicate hxw).exists_eq_flatten_replicate_iff.not.2 hx)
      (hg.infix (take_prefix _ _).isInfix) hdvd
  have hlen : l'.length = l.length := (key hl' h' hle.2 (Nat.gcd_dvd_right _ _)).symm.trans
    (key hl h hle.1 (Nat.gcd_dvd_left _ _))
  have h₂ := h'.take_isRotated_of_flatten_replicate hle.2
  rw [hlen] at h₂
  exact h₂.symm.trans (h.take_isRotated_of_flatten_replicate hle.1)

end List
