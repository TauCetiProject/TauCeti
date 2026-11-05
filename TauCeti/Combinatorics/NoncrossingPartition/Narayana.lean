/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.NoncrossingPartition.Catalan
import Mathlib.Algebra.Polynomial.Coeff
import TauCeti.Algebra.BigOperators.Finset.Range
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# Narayana numbers: noncrossing partitions counted by their number of parts

The noncrossing partitions of `n` ordered positions with `j` parts are counted by the Narayana
number `N(n, j) = (1/n) C(n, j) C(n, j - 1)`. In the form without division this reads
`n * N(n, j) = C(n, j) * C(n, j - 1)`; for `n = 4` and `j = 2` it gives `6`. Summing over `j`
recovers the Catalan numbers.

Let `q_n(t) = ∑_{π ∈ NC(n)} t ^ |π|` be the generating polynomial of the number of parts. The
recurrence of noncrossing partitions by the part containing the first position
(`TauCeti.NoncrossingPartition.sum_mul_prod_eq_sum_mul_sum`), with every part weighted by `t`,
shows that `A(z) = ∑_{n ≥ 1} q_n(t) z ^ n` satisfies `A = z (t + A) (1 + A)`. Multiplying this by
`A ^ (k - 1)` gives a three-term recurrence for the coefficients of the powers `A ^ k`, and the
closed form `[z ^ n] A ^ k = (k / n) ∑_j C(n, j) C(n, j - k) t ^ j` for `n ≥ 1` is proved by
induction from it: the induction step is the Pascal rule for the binomial coefficients combined
with `(r + 1) C(n, r + 1) = (n - r) C(n, r)`. The case `k = 1` is the claim.

## Main results

* `TauCeti.NoncrossingPartition.card_mul_card_parts_eq` — for a finite set `s` of positions in a
  linear order, `|s| * #{π ∈ NC(s) | |π| = j + 1} = C(|s|, j + 1) * C(|s|, j)`.
* `TauCeti.NoncrossingPartition.card_parts_eq_div` — the same count as the quotient
  `C(|s|, j + 1) * C(|s|, j) / |s|`.
* `TauCeti.NoncrossingPartition.card_fin_mul_card_parts_eq` — the multiplied form
  `n * #{π ∈ NC(Fin n) | |π| = j + 1} = C(n, j + 1) * C(n, j)` for `Fin n`.
* `TauCeti.NoncrossingPartition.card_filter_card_parts_eq_zero` — only the empty set has a
  noncrossing partition without parts.
* `TauCeti.NoncrossingPartition.sum_comp_card_parts_eq_sum_range` — a sum over `NC(s)` of a
  function of the number of parts, grouped by the number of parts.
* `TauCeti.NoncrossingPartition.sum_comp_card_parts_eq_of_card_eq` — a sum over `NC(s)` of a
  function of the number of parts depends only on `|s|`.
* `TauCeti.NoncrossingPartition.sum_prod_mul_pow_card` — weighting each part `B` by `r * c ^ |B|`,
  the noncrossing partitions of `s` have total weight `c ^ |s| * ∑_{π ∈ NC(|s|)} r ^ |π|`, the
  moments of a free Poisson element.

## References

* P. Narayana, *Sur les treillis formés par les partitions d'un entier et leurs applications à la
  théorie des probabilités*, C. R. Acad. Sci. Paris 240 (1955), 1188–1189.
* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 9.
-/

public section

open Finset

namespace TauCeti.NoncrossingPartition

variable {α : Type*} [LinearOrder α] {s : Finset α}

/-- The polynomial variable `t` marking the parts of a partition. -/
local notation "τ" => (Polynomial.X : Polynomial ℚ)

/-! ### Rational binomial coefficients with an integer lower index -/

/-- The binomial coefficient `C(n, r)` as a rational number, for an integer `r`; it is `0` for
negative `r`. -/
private def bin (n : ℕ) (r : ℤ) : ℚ :=
  if 0 ≤ r then (n.choose r.toNat : ℚ) else 0

private theorem bin_natCast (n m : ℕ) : bin n (m : ℤ) = n.choose m := by
  simp [bin]

private theorem bin_of_neg (n : ℕ) {r : ℤ} (hr : r < 0) : bin n r = 0 := by
  simp [bin, not_le.2 hr]

/-- The Pascal rule for `bin`. -/
private theorem bin_succ (n : ℕ) (r : ℤ) : bin (n + 1) r = bin n r + bin n (r - 1) := by
  rcases lt_or_ge r 0 with h | h
  · rw [bin_of_neg _ h, bin_of_neg _ h, bin_of_neg _ (by omega)]
    simp
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
    cases m with
    | zero => simp [bin]
    | succ m =>
      have : ((m + 1 : ℕ) : ℤ) - 1 = m := by push_cast; ring
      rw [this, bin_natCast, bin_natCast, bin_natCast, Nat.choose_succ_succ', add_comm]
      push_cast
      ring

/-- The identity `(r + 1) C(n, r + 1) = (n - r) C(n, r)` for `bin`. -/
private theorem bin_ratio (n : ℕ) (r : ℤ) :
    ((r : ℚ) + 1) * bin n (r + 1) = ((n : ℚ) - r) * bin n r := by
  rcases lt_or_ge r (-1) with h | h
  · rw [bin_of_neg _ (by omega), bin_of_neg _ (by omega)]
    simp
  · rcases eq_or_lt_of_le h with rfl | h
    · rw [bin_of_neg n (by omega : (-1 : ℤ) < 0)]
      simp
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ r)
      have : ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [this, bin_natCast, bin_natCast]
      rcases le_or_gt m n with hmn | hmn
      · have h := congrArg (Nat.cast (R := ℚ)) (Nat.choose_succ_right_eq n m)
        push_cast [Nat.cast_sub hmn] at h
        push_cast
        linarith
      · rw [Nat.choose_eq_zero_of_lt hmn, Nat.choose_eq_zero_of_lt (by omega)]
        simp

/-- The algebraic identity behind the recurrence for the coefficients of the powers of the
generating series. -/
private theorem key_identity (n : ℕ) (hn : 1 ≤ n) (K : ℕ) (M : ℤ) :
    (K : ℚ) / (n + 1) * bin (n + 1) M * bin (n + 1) (M - K) =
      ((K : ℚ) - 1) / n * bin n (M - 1) * bin n (M - K) + K / n * bin n M * bin n (M - K) +
        K / n * bin n (M - 1) * bin n (M - K - 1) + (K + 1) / n * bin n M * bin n (M - K - 1) := by
  have hn0 : (n : ℚ) ≠ 0 := by positivity
  have hn1 : (n : ℚ) + 1 ≠ 0 := by positivity
  have R1 := bin_ratio n (M - 1)
  have R2 := bin_ratio n (M - K - 1)
  rw [sub_add_cancel] at R1
  rw [sub_add_cancel] at R2
  push_cast at R1 R2
  rw [bin_succ n M, bin_succ n (M - K)]
  have hD : (n : ℚ) * K * (bin n M + bin n (M - 1)) * (bin n (M - K) + bin n (M - K - 1)) =
      (n + 1) * ((K - 1) * bin n (M - 1) * bin n (M - K) + K * bin n M * bin n (M - K) +
        K * bin n (M - 1) * bin n (M - K - 1) + (K + 1) * bin n M * bin n (M - K - 1)) := by
    linear_combination (-bin n (M - K) - bin n (M - K - 1)) * R1 +
      (bin n M + bin n (M - 1)) * R2
  field_simp
  linear_combination hD

/-! ### The generating polynomial of the number of parts -/

/-- The generating polynomial `∑_{π ∈ NC(s)} t ^ |π|` of the number of parts of the noncrossing
partitions of `s`. -/
private noncomputable def blockPoly (s : Finset α) : Polynomial ℚ :=
  ∑ P : NoncrossingPartition s, τ ^ #P.1.parts

private theorem blockPoly_empty : blockPoly (∅ : Finset α) = 1 := by
  rw [blockPoly, Fintype.sum_unique, Finpartition.parts_eq_empty_iff.2 rfl]
  simp

/-- The sum over `NC(t)` of `t ^ |π|`, written with the part through `m` separated: it is
`blockPoly t`, except that for `t = ∅` the missing part through `m` contributes the factor `t`. -/
private theorem sum_X_mul_prod_filter (t : Finset α) (m : α) (hm : t.Nonempty → m ∈ t) :
    ∑ P : NoncrossingPartition t, τ * ∏ B ∈ P.1.parts with m ∉ B, τ =
      if #t = 0 then τ else blockPoly t := by
  by_cases ht : #t = 0
  · obtain rfl := card_eq_zero.1 ht
    rw [ite_eq_left ht, Fintype.sum_unique, Finpartition.parts_eq_empty_iff.2 rfl]
    simp
  · rw [ite_eq_right ht, blockPoly]
    refine sum_congr rfl fun P _ => ?_
    have h := P.1.prod_parts_eq_mul_prod_filter_notMem
      (hm (nonempty_of_ne_empty fun h => ht (by simp [h]))) fun _ => τ
    rw [prod_const] at h
    exact h.symm

/-- The recurrence of the generating polynomial by the part containing the first position. -/
private theorem blockPoly_eq_sum (hs : s.Nonempty) :
    blockPoly s = ∑ x ∈ s, (if #{y ∈ s | y < x} = 0 then τ else blockPoly {y ∈ s | y < x}) *
      blockPoly {y ∈ s | x < y} := by
  have h := sum_mul_prod_eq_sum_mul_sum (M := Polynomial ℚ) hs (fun _ => τ) (fun _ => τ)
  have hL := sum_X_mul_prod_filter s (s.min' hs) fun _ => s.min'_mem hs
  rw [ite_eq_right hs.card_pos.ne'] at hL
  beta_reduce at h
  rw [hL] at h
  rw [h]
  refine sum_congr rfl fun x hx => ?_
  congr 1
  · refine sum_X_mul_prod_filter _ _ fun hne => ?_
    obtain ⟨y, hy⟩ := hne
    obtain ⟨hys, hyx⟩ := mem_filter.1 hy
    exact mem_filter.2 ⟨s.min'_mem hs, (s.min'_le y hys).trans_lt hyx⟩
  · simp [blockPoly]

/-- The generating polynomials as a function of the number of positions, by the recurrence of
`blockPoly_eq_sum`. -/
private noncomputable def narayanaPoly : ℕ → Polynomial ℚ
  | 0 => 1
  | n + 1 => ∑ i : Fin (n + 1),
      (if (i : ℕ) = 0 then τ else narayanaPoly i) * narayanaPoly (n - i)
decreasing_by
  all_goals
    have := i.2
    omega

private theorem narayanaPoly_succ (n : ℕ) :
    narayanaPoly (n + 1) =
      ∑ i ∈ range (n + 1), (if i = 0 then τ else narayanaPoly i) * narayanaPoly (n - i) := by
  rw [narayanaPoly]
  exact Fin.sum_univ_eq_sum_range (fun i => (if i = 0 then τ else narayanaPoly i) *
    narayanaPoly (n - i)) (n + 1)

/-- The generating polynomial `∑_{π ∈ NC(s)} t ^ |π|` depends only on the number of positions. -/
private theorem blockPoly_eq_narayanaPoly (s : Finset α) : blockPoly s = narayanaPoly #s := by
  induction hn : #s using Nat.strong_induction_on generalizing s with
  | _ n ih =>
  obtain rfl | hs := s.eq_empty_or_nonempty
  · rw [blockPoly_empty, ← hn, card_empty, narayanaPoly]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (hn ▸ hs.card_pos.ne')
  -- The positions before `x ∈ s`, or after it, are fewer than those of `s`.
  have hlt {x : α} (hx : x ∈ s) {p : α → Prop} [DecidablePred p] (hp : ¬p x) :
      #{y ∈ s | p y} < k + 1 :=
    hn ▸ card_lt_card (filter_ssubset.2 ⟨x, hx, hp⟩)
  have h := sum_card_filter_lt_card_filter_gt s fun i j =>
    (if i = 0 then τ else narayanaPoly i) * narayanaPoly j
  rw [hn, Nat.add_sub_cancel] at h
  rw [blockPoly_eq_sum hs, narayanaPoly_succ]
  refine (sum_congr rfl fun x hx => ?_).trans h
  rw [ih #{y ∈ s | y < x} (hlt hx (lt_irrefl x)) _ rfl,
    ih #{y ∈ s | x < y} (hlt hx (lt_irrefl x)) _ rfl]

/-! ### The generating series and its powers -/

/-- The generating series `A(z) = ∑_{n ≥ 1} q_n(t) z ^ n`. -/
private noncomputable def narayanaSeries : PowerSeries (Polynomial ℚ) :=
  PowerSeries.mk fun n => if n = 0 then 0 else narayanaPoly n

local notation "𝔸" => narayanaSeries

private theorem coeff_narayanaSeries (n : ℕ) :
    PowerSeries.coeff n 𝔸 = if n = 0 then 0 else narayanaPoly n := by
  simp [narayanaSeries]

private theorem constantCoeff_narayanaSeries : PowerSeries.constantCoeff 𝔸 = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_narayanaSeries]
  simp

/-- The functional equation `A = z (t + A) (1 + A)` of the generating series. -/
private theorem narayanaSeries_eq :
    𝔸 = PowerSeries.X * (PowerSeries.C τ + 𝔸) * (1 + 𝔸) := by
  refine PowerSeries.ext fun n => ?_
  cases n with
  | zero => simp [coeff_narayanaSeries]
  | succ n =>
    rw [mul_assoc, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, coeff_narayanaSeries,
      ite_eq_right n.succ_ne_zero, narayanaPoly_succ]
    refine sum_congr rfl fun i hi => ?_
    have hi' := mem_range_succ_iff.1 hi
    congr 1
    · by_cases h : i = 0
      · simp [h, constantCoeff_narayanaSeries]
      · simp [h, PowerSeries.coeff_C, coeff_narayanaSeries]
    · by_cases h : n - i = 0
      · simp [h, constantCoeff_narayanaSeries, narayanaPoly]
      · simp [h, coeff_narayanaSeries, PowerSeries.coeff_one]

private theorem coeff_zero_pow (k : ℕ) :
    PowerSeries.coeff 0 (𝔸 ^ k) = if k = 0 then 1 else 0 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, constantCoeff_narayanaSeries]
  cases k <;> simp

/-- The three-term recurrence for the coefficients of the powers of the generating series. -/
private theorem coeff_succ_pow (k n : ℕ) :
    PowerSeries.coeff (n + 1) (𝔸 ^ (k + 1)) =
      τ * PowerSeries.coeff n (𝔸 ^ k) +
        (PowerSeries.coeff n (𝔸 ^ (k + 1)) + τ * PowerSeries.coeff n (𝔸 ^ (k + 1))) +
          PowerSeries.coeff n (𝔸 ^ (k + 2)) := by
  have h : 𝔸 ^ (k + 1) = PowerSeries.X * (PowerSeries.C τ * 𝔸 ^ k +
      (𝔸 ^ (k + 1) + PowerSeries.C τ * 𝔸 ^ (k + 1)) + 𝔸 ^ (k + 2)) := by
    calc 𝔸 ^ (k + 1) = 𝔸 * 𝔸 ^ k := pow_succ' _ _
      _ = (PowerSeries.X * (PowerSeries.C τ + 𝔸) * (1 + 𝔸)) * 𝔸 ^ k := by
        rw [← narayanaSeries_eq]
      _ = _ := by ring
  conv_lhs => rw [h]
  simp only [PowerSeries.coeff_succ_X_mul, map_add, PowerSeries.coeff_C_mul]

/-- The closed form of the coefficients of the powers of the generating series: for `n ≥ 1`,
`[z ^ n t ^ m] A ^ k = (k / n) C(n, m) C(n, m - k)`. -/
private theorem coeff_coeff_pow {n : ℕ} (hn : 1 ≤ n) (k m : ℕ) :
    (PowerSeries.coeff n (𝔸 ^ k)).coeff m = (k : ℚ) / n * bin n m * bin n ((m : ℤ) - k) := by
  induction n, hn using Nat.le_induction generalizing k m with
  | base =>
    cases k with
    | zero => simp
    | succ k =>
      rw [coeff_succ_pow, coeff_zero_pow, coeff_zero_pow, coeff_zero_pow]
      cases k with
      | zero =>
        rcases m with _ | _ | m
        · simp [bin_of_neg]
        · simp [bin]
        · simp [Polynomial.coeff_X, bin, Nat.choose_eq_zero_of_lt]
      | succ k =>
        have hR : ((k + 1 + 1 : ℕ) : ℚ) / ((1 : ℕ) : ℚ) * bin 1 m *
            bin 1 ((m : ℤ) - ((k + 1 + 1 : ℕ) : ℤ)) = 0 := by
          rcases lt_or_ge m 2 with hm | hm
          · rw [bin_of_neg 1 (by omega : (m : ℤ) - ((k + 1 + 1 : ℕ) : ℤ) < 0)]
            simp
          · rw [bin_natCast, Nat.choose_eq_zero_of_lt (by omega)]
            simp
        refine Eq.trans ?_ hR.symm
        simp
  | succ n hn ih =>
    cases k with
    | zero => simp
    | succ k =>
      rw [coeff_succ_pow, Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add]
      rcases m with _ | m
      · have h0 : ∀ (j i : ℕ), bin j (((0 : ℕ) : ℤ) - ((i + 1 : ℕ) : ℤ)) = 0 := fun j i =>
          bin_of_neg _ (by omega)
        rw [Polynomial.coeff_X_mul_zero, Polynomial.coeff_X_mul_zero, ih (k + 1) 0, ih (k + 2) 0,
          h0, h0, h0]
        simp
      · rw [Polynomial.coeff_X_mul, Polynomial.coeff_X_mul, ih k m, ih (k + 1) m,
          ih (k + 1) (m + 1), ih (k + 2) (m + 1)]
        have key := key_identity n hn (k + 1) ((m : ℤ) + 1)
        push_cast at key ⊢
        have e1 : (m : ℤ) + 1 - 1 = m := by ring
        have e2 : (m : ℤ) + 1 - ((k : ℤ) + 1) = m - k := by ring
        have e3 : (m : ℤ) + 1 - ((k : ℤ) + 1) - 1 = m - ((k : ℤ) + 1) := by ring
        have e4 : (m : ℤ) + 1 - ((k : ℤ) + 2) = m - ((k : ℤ) + 1) := by ring
        rw [e3, e1, e2] at key
        rw [e2, e4]
        linear_combination -key

/-- The coefficient of `t ^ j` in `∑_{π ∈ NC(s)} t ^ |π|` is the number of `π` with `j` parts. -/
private theorem coeff_blockPoly (s : Finset α) (j : ℕ) :
    (blockPoly s).coeff j = (#{P : NoncrossingPartition s | #P.1.parts = j} : ℕ) := by
  rw [blockPoly, Polynomial.finsetSum_coeff, card_filter]
  push_cast
  refine sum_congr rfl fun P _ => ?_
  rw [Polynomial.coeff_X_pow]
  by_cases h : #P.1.parts = j
  · simp [h]
  · simp [h, Ne.symm h]

/-- *Narayana counts.* The number of noncrossing partitions of a finite set `s` of positions in a
linear order with `j + 1` parts, multiplied by `|s|`, is `C(|s|, j + 1) * C(|s|, j)`; that is, the
number is the Narayana number `(1 / |s|) C(|s|, j + 1) C(|s|, j)`. -/
theorem card_mul_card_parts_eq (s : Finset α) (j : ℕ) :
    #s * #{P : NoncrossingPartition s | #P.1.parts = j + 1} =
      (#s).choose (j + 1) * (#s).choose j := by
  obtain h0 | hn := Nat.eq_zero_or_pos #s
  · rw [h0]
    simp
  · have h := coeff_coeff_pow hn 1 (j + 1)
    rw [pow_one, coeff_narayanaSeries, ite_eq_right hn.ne', ← blockPoly_eq_narayanaPoly,
      coeff_blockPoly] at h
    have e : ((j + 1 : ℕ) : ℤ) - ((1 : ℕ) : ℤ) = (j : ℕ) := by push_cast; ring
    rw [e, bin_natCast, bin_natCast] at h
    have hn' : (#s : ℚ) ≠ 0 := by positivity
    have h' : ((#s * #{P : NoncrossingPartition s | #P.1.parts = j + 1} : ℕ) : ℚ) =
        (((#s).choose (j + 1) * (#s).choose j : ℕ) : ℚ) := by
      push_cast
      rw [h]
      field_simp
      simp
    exact_mod_cast h'

/-- The number of noncrossing partitions of a finite set `s` of positions with `j + 1` parts is the
Narayana number `C(|s|, j + 1) C(|s|, j) / |s|`, with natural-number division. -/
theorem card_parts_eq_div (s : Finset α) (j : ℕ) :
    #{P : NoncrossingPartition s | #P.1.parts = j + 1} =
      (#s).choose (j + 1) * (#s).choose j / #s := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · rw [Finset.card_empty, Nat.div_zero]
    refine Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun P _ h => ?_)
    rw [Finpartition.parts_eq_empty_iff.2 rfl] at h
    simp at h
  · rw [← card_mul_card_parts_eq s j, Nat.mul_div_cancel_left _ hs.card_pos]

/-- The number of noncrossing partitions of `Fin n` with `j + 1` parts, multiplied by `n`, is
`C(n, j + 1) * C(n, j)`. -/
theorem card_fin_mul_card_parts_eq (n j : ℕ) :
    n * #{P : NoncrossingPartition (univ : Finset (Fin n)) | #P.1.parts = j + 1} =
      n.choose (j + 1) * n.choose j := by
  simpa using card_mul_card_parts_eq (univ : Finset (Fin n)) j

/-- Only the empty set has a noncrossing partition without parts, and it has exactly one. -/
theorem card_filter_card_parts_eq_zero (s : Finset α) :
    #{P : NoncrossingPartition s | #P.1.parts = 0} = if #s = 0 then 1 else 0 := by
  simp only [card_eq_zero (s := s), card_eq_zero (s := Finpartition.parts _),
    Finpartition.parts_eq_empty_iff, bot_eq_empty]
  split_ifs with hs
  · rw [filter_true_of_mem fun _ _ => hs, card_univ, card_eq_catalan, hs, card_empty, catalan_zero]
  · rw [filter_false_of_mem fun _ _ => hs, card_empty]

/-- The number of noncrossing partitions of a finite set `s` of positions with `j` parts depends
only on the number `|s|` of positions. -/
theorem card_filter_card_parts_eq_of_card_eq {β : Type*} [LinearOrder β] {t : Finset β}
    (h : #s = #t) (j : ℕ) :
    #{P : NoncrossingPartition s | #P.1.parts = j} =
      #{P : NoncrossingPartition t | #P.1.parts = j} := by
  cases j with
  | zero => rw [card_filter_card_parts_eq_zero, card_filter_card_parts_eq_zero, h]
  | succ j => rw [card_parts_eq_div, card_parts_eq_div, h]

/-- A sum over the noncrossing partitions of `s` of a function of their number of parts, grouped
by the number of parts. -/
theorem sum_comp_card_parts_eq_sum_range {M : Type*} [AddCommMonoid M] (s : Finset α)
    (f : ℕ → M) :
    ∑ P : NoncrossingPartition s, f #P.1.parts =
      ∑ j ∈ range (#s + 1), #{P : NoncrossingPartition s | #P.1.parts = j} • f j := by
  rw [← sum_fiberwise_of_maps_to (g := fun P : NoncrossingPartition s => #P.1.parts)
    (t := range (#s + 1)) fun P _ => mem_range.2 (Nat.lt_succ_of_le P.1.card_parts_le_card)]
  exact sum_congr rfl fun j _ => by
    rw [sum_congr rfl fun P hP => by rw [(mem_filter.1 hP).2], sum_const]

/-- Over an empty set `s` of positions, a sum over the noncrossing partitions of `s` of a function
`f` of their number of parts is `f 0`: the only such partition has no parts. -/
theorem sum_comp_card_parts_of_card_eq_zero {M : Type*} [AddCommMonoid M] (hs : #s = 0)
    (f : ℕ → M) : ∑ P : NoncrossingPartition s, f #P.1.parts = f 0 := by
  rw [sum_comp_card_parts_eq_sum_range, hs, zero_add, sum_range_one,
    card_filter_card_parts_eq_zero, ite_eq_left hs, one_smul]

/-- A sum over the noncrossing partitions of a finite set `s` of positions of a function of their
number of parts depends only on the number `|s|` of positions. In particular, such a sum over
`NC(s)` equals the same sum over `NC(Fin |s|)`. -/
theorem sum_comp_card_parts_eq_of_card_eq {β M : Type*} [LinearOrder β] [AddCommMonoid M]
    {t : Finset β} (h : #s = #t) (f : ℕ → M) :
    ∑ P : NoncrossingPartition s, f #P.1.parts = ∑ P : NoncrossingPartition t, f #P.1.parts := by
  rw [sum_comp_card_parts_eq_sum_range, sum_comp_card_parts_eq_sum_range, h]
  exact sum_congr rfl fun j _ => by rw [card_filter_card_parts_eq_of_card_eq h]

/-- Weighting each part `B` of a noncrossing partition of `s` by `r * c ^ #B`, the total weight is
`c ^ #s * ∑_{π ∈ NC(#s)} r ^ |π|`. For `c = 1` this is the Narayana polynomial of `#s`. -/
theorem sum_prod_mul_pow_card {M : Type*} [CommSemiring M] (s : Finset α) (r c : M) :
    ∑ π : NoncrossingPartition s, ∏ B ∈ π.1.parts, r * c ^ #B =
      c ^ #s * ∑ π : NoncrossingPartition (univ : Finset (Fin #s)), r ^ #π.1.parts := by
  simp_rw [prod_mul_distrib, prod_const, prod_pow_eq_pow_sum, Finpartition.sum_card_parts]
  rw [← sum_mul, mul_comm, sum_comp_card_parts_eq_of_card_eq
    (t := (univ : Finset (Fin #s))) (by rw [card_univ, Fintype.card_fin]) fun k => r ^ k]

end TauCeti.NoncrossingPartition
