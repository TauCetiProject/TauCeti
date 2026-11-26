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
length `|l| % d`, a prefix of `A`. Hence, for `l` nonempty, the factors of the powers of `l` that
are at least as long as `l` are the lists with the period `|l|` that begin with a rotation of `l`,
and they are the lists `A^r A₁` with `A` a rotation of `l`, `r ≥ 1` and `A₁` a proper prefix of
`A`.

A list `l` that is not a power `uⁿ` of a list with `n ≥ 2` has no period properly dividing its
length. Combined with the periodicity lemma of Fine and Wilf (`List.HasPeriod.gcd`): two periods
`p` and `q` of a list `w` of length at least `p + q - gcd(p, q)` whose prefixes of lengths `p` and
`q` are not such powers agree, and if `l` and `l'` are two such lists and a common factor of a
power of `l` and a power of `l'` has length at least `|l| + |l'| - gcd(|l|, |l'|)`, then `l'` is a
rotation of `l`.

## Main results

* `List.hasPeriod_flatten_replicate`: `lⁿ` has period `|l|`.
* `List.HasPeriod.flatten_replicate_take_append_take`: a list `l` with a period `d` is `A^r A₁`,
  with `A = l.take d`.
* `List.length_le_and_exists_infix_flatten_replicate_iff` and
  `List.length_le_and_exists_infix_flatten_replicate_iff_exists_eq_flatten_replicate_append`: the
  factors of the powers of a nonempty `l` that are at least as long as `l`.
* `List.eq_length_of_hasPeriod_of_dvd`: a list that is not a power `uⁿ`, `n ≥ 2`, has no period
  properly dividing its length.
* `List.HasPeriod.eq_of_hasPeriod`: two periods with such prefixes agree on a long enough list.
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
    -- the quotient by `d` drops by one and the remainder is unchanged
    have hdiv : n / d = (n - d) / d + 1 := Nat.div_eq_sub_div hd0 hle
    have hmod : n % d = (n - d) % d := Nat.mod_eq_sub_mod hle
    calc (replicate (n / d) (l.take d)).flatten ++ l.take (n % d)
        = l.take d ++ ((replicate ((n - d) / d) ((l.drop d).take d)).flatten ++
            (l.drop d).take ((n - d) % d)) := by
          rw [hrep, htake (Nat.mod_le _ _), hdiv, hmod]
          simp only [replicate_succ, flatten_cons, append_assoc]
      _ = l := by rw [hdrop, take_append_drop]

/-- For a nonempty list `l`, a list `w` is at least as long as `l` and a factor of a concatenation
of copies of `l` exactly when it has the period `|l|` and begins with a rotation of `l`. -/
theorem length_le_and_exists_infix_flatten_replicate_iff {w l : List α} (hl : l ≠ []) :
    (l.length ≤ w.length ∧ ∃ n, w <:+: (replicate n l).flatten) ↔
      w.HasPeriod l.length ∧ w.take l.length ~r l := by
  refine ⟨fun ⟨hlw, n, hw⟩ => ⟨(hasPeriod_flatten_replicate l n).infix hw,
    hw.take_isRotated_of_flatten_replicate hlw⟩, fun ⟨hp, hr⟩ => ?_⟩
  -- `w = A^r A₁` with `A = w.take |l|` is a prefix of `A^(r + 1)`, a factor of `l^(r + 2)`
  have hA : (replicate (w.length / l.length) (w.take l.length)).flatten ++
      w.take (w.length % l.length) <+:
        (replicate (w.length / l.length + 1) (w.take l.length)).flatten := by
    simpa [replicate_succ'] using
      take_prefix_take_left (l := w) (Nat.mod_lt _ (length_pos_iff.2 hl)).le
  rw [hp.flatten_replicate_take_append_take] at hA
  exact ⟨by simpa using hr.perm.length_eq, _, hA.isInfix.trans (hr.flatten_replicate_infix _)⟩

/-- **The form `A^r A₁` of a factor of a power.** For a nonempty list `l`, a list `w` is at least
as long as `l` and a factor of a concatenation of copies of `l` exactly when `w = A^r A₁` for a
rotation `A` of `l`, some `r ≥ 1` and a proper prefix `A₁` of `A`. -/
theorem length_le_and_exists_infix_flatten_replicate_iff_exists_eq_flatten_replicate_append
    {w l : List α} (hl : l ≠ []) :
    (l.length ≤ w.length ∧ ∃ n, w <:+: (replicate n l).flatten) ↔ ∃ A r A₁, A ~r l ∧ 0 < r ∧
      A₁ <+: A ∧ A₁.length < A.length ∧ w = (replicate r A).flatten ++ A₁ := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨hp, hr⟩ := (length_le_and_exists_infix_flatten_replicate_iff hl).1 h
    have hpos := length_pos_iff.2 hl
    refine ⟨w.take l.length, w.length / l.length, w.take (w.length % l.length), hr,
      Nat.div_pos h.1 hpos, take_prefix_take_left (Nat.mod_lt _ hpos).le, ?_,
      hp.flatten_replicate_take_append_take.symm⟩
    have := Nat.mod_lt w.length hpos
    have := h.1
    simp only [length_take]
    lia
  · rintro ⟨A, r, A₁, hA, hr, hA₁, -, rfl⟩
    -- `A^r A₁` is a prefix of `A^(r + 1)`, a factor of `l^(r + 2)`
    refine ⟨?_, r + 2, (IsPrefix.isInfix ?_).trans (hA.flatten_replicate_infix (r + 1))⟩
    · have := Nat.le_mul_of_pos_left A.length hr
      simp only [length_append, length_flatten, map_replicate, sum_replicate_nat,
        ← hA.perm.length_eq]
      lia
    · simpa [replicate_succ'] using hA₁

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
  · calc l = (replicate (l.length / d) (l.take d)).flatten ++ l.take (l.length % d) :=
          h.flatten_replicate_take_append_take.symm
      _ = (replicate k (l.take d)).flatten := by simp [hk, Nat.mul_div_cancel_left k hd0]

/-- **Two periods agree.** If a list `w` has the periods `p` and `q`, its prefixes of lengths `p`
and `q` are not powers `uⁿ` of lists with `n ≥ 2`, and `p + q - gcd(p, q) ≤ |w|`, then `p = q`.
This is a consequence of the periodicity lemma of Fine and Wilf. -/
theorem HasPeriod.eq_of_hasPeriod {w : List α} {p q : ℕ} (hp : w.HasPeriod p)
    (hq : w.HasPeriod q) (hp' : ¬∃ u n, 2 ≤ n ∧ w.take p = (replicate n u).flatten)
    (hq' : ¬∃ u n, 2 ≤ n ∧ w.take q = (replicate n u).flatten)
    (hw : p + q - p.gcd q ≤ w.length) : p = q := by
  have hg := hp.gcd hq hw
  -- both prefixes are nonempty, so `0 < p, q ≤ |w|`
  have hp0 : p ≠ 0 := fun h0 => ne_nil_of_not_exists_eq_flatten_replicate hp' (by simp [h0])
  have hq0 : q ≠ 0 := fun h0 => ne_nil_of_not_exists_eq_flatten_replicate hq' (by simp [h0])
  have hpw : p ≤ w.length := by have := Nat.gcd_le_right p (Nat.pos_of_ne_zero hq0); lia
  have hqw : q ≤ w.length := by have := Nat.gcd_le_left q (Nat.pos_of_ne_zero hp0); lia
  -- the prefix of length `x ∈ {p, q}` has the period `gcd(p, q)`, which divides `x`
  have key {x : ℕ} (hx : ¬∃ u n, 2 ≤ n ∧ w.take x = (replicate n u).flatten)
      (hxw : x ≤ w.length) (hdvd : p.gcd q ∣ x) : p.gcd q = x := by
    have hlen : (w.take x).length = x := by simpa using hxw
    rw [← hlen] at hdvd ⊢
    exact eq_length_of_hasPeriod_of_dvd hx (hg.infix (take_prefix _ _).isInfix) hdvd
  exact (key hp' hpw (Nat.gcd_dvd_left _ _)).symm.trans (key hq' hqw (Nat.gcd_dvd_right _ _))

/-- **Overlapping periodicities.** Let `l` and `l'` be lists that are not powers `uⁿ` of lists with
`n ≥ 2`. If a list `w` of length at least `|l| + |l'| - gcd(|l|, |l'|)` is a factor of a
concatenation of copies of `l` and of a concatenation of copies of `l'`, then `l'` is a rotation
of `l`. -/
theorem isRotated_of_infix_flatten_replicate {w l l' : List α}
    (hl : ¬∃ u n, 2 ≤ n ∧ l = (replicate n u).flatten)
    (hl' : ¬∃ u n, 2 ≤ n ∧ l' = (replicate n u).flatten) {m m' : ℕ}
    (h : w <:+: (replicate m l).flatten) (h' : w <:+: (replicate m' l').flatten)
    (hw : l.length + l'.length - l.length.gcd l'.length ≤ w.length) : l' ~r l := by
  have hle : l.length ≤ w.length ∧ l'.length ≤ w.length := by
    have := Nat.gcd_le_left l'.length
      (length_pos_iff.2 (ne_nil_of_not_exists_eq_flatten_replicate hl))
    have := Nat.gcd_le_right l.length
      (length_pos_iff.2 (ne_nil_of_not_exists_eq_flatten_replicate hl'))
    lia
  -- the prefixes of `w` of lengths `|l|` and `|l'|` are rotations of `l` and of `l'`
  have hr := h.take_isRotated_of_flatten_replicate hle.1
  have hr' := h'.take_isRotated_of_flatten_replicate hle.2
  have hlen := ((hasPeriod_flatten_replicate l m).infix h).eq_of_hasPeriod
    ((hasPeriod_flatten_replicate l' m').infix h') (hr.exists_eq_flatten_replicate_iff.not.2 hl)
    (hr'.exists_eq_flatten_replicate_iff.not.2 hl') hw
  rw [← hlen] at hr'
  exact hr'.symm.trans hr

end List
