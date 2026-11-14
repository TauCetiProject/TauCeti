/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.GelfandTsetlin.Shift
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Row sums and weights of Gelfand–Tsetlin patterns

In a Gelfand–Tsetlin pattern `P : TauCeti.GTPattern n`, row `j ≤ n` records the highest weight of
the constituent at level `GL j` along the branching chain `GL 1 ⊂ ⋯ ⊂ GL n`. Summing the entries of
row `j` gives `TauCeti.GTPattern.rowSum P j` (with `rowSum P 0 = 0`), the exponent with which the
central torus of `GL j` acts on the corresponding Gelfand–Tsetlin line, so the diagonal torus of
`GL n` acts by the successive row-sum differences

`wt(P)_r = rowSum P (r + 1) - rowSum P r`

(`TauCeti.GTPattern.weight`). Because `P` may have negative entries, `P.weight : Fin n → ℤ` is an
arbitrary integer weight rather than a nonnegative composition or an antitone sequence: its entries
sum to `∑ i, P.topRow i`, every component lies between the last and first entries of `P.topRow`,
and shifting every informative entry of `P` by `m` adds `m` to every component of `P.weight`. In
the polynomial regime, where `TauCeti.gtPatternEquivSSYT` identifies patterns with bounded
semistandard Young tableaux, `P.weight` agrees with Tau Ceti's `SemistandardYoungTableau.content`.

## Main definitions

* `TauCeti.GTPattern.rowSum`: the sum `∑ k ∈ Finset.range j, P k j` of row `j` of a pattern.
* `TauCeti.GTPattern.weight`: the torus weight `fun r => P.rowSum (r + 1) - P.rowSum r`.
* `TauCeti.GTPattern.weightAddMonoidHom`: `GTPattern.weight` bundled as an additive monoid
  homomorphism `GTPattern n →+ (Fin n → ℤ)`.

## Main results

* `TauCeti.GTPattern.prefixSum_weight`, `TauCeti.GTPattern.sum_weight`,
  `TauCeti.GTPattern.rowSum_le_prefixSum_topRow`, and `TauCeti.GTPattern.dominates_weight_topRow`:
  leading prefix sums of `P.weight` recover `P.rowSum`, total sum equals `∑ i, P.topRow i`, and
  `P.topRow` dominates `P.weight` (`TauCeti.Dominates P.weight P.topRow`).
* `TauCeti.GTPattern.weight_shift`: determinant translation by `m` shifts every entry of `P.weight`
  by `m`.
* `TauCeti.GTPattern.weight_mem_Icc`: every entry of `P.weight` lies between the last and first
  entries of `P.topRow`, so nonnegative patterns have nonnegative weights (`weight_nonneg`).
* `TauCeti.GTPattern.eq_of_topRow_eq_of_weight_eq_two`, `TauCeti.GTPattern.card_topRow_weight_two`,
  and `TauCeti.GTPattern.card_three_adjoint_weight_zero`: low-rank weight-fibre uniqueness and
  explicit counts.
* `SemistandardYoungTableau.weight_toGTPattern`, `TauCeti.GTPattern.natCast_content_toTableau`,
  `TauCeti.GTPattern.content_toTableau`, and `TauCeti.GTPattern.content_toTableau_eq_zero`: under
  the pattern–tableau correspondence, `GTPattern.weight` equals tableau `content`.

## References

* I. M. Gelfand and M. L. Tsetlin, *Finite-dimensional representations of the group of unimodular
  matrices*, Dokl. Akad. Nauk SSSR **71** (1950), 825–828.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), §15.3.
-/

public section

open scoped BigOperators

namespace TauCeti.GTPattern

variable {n : ℕ}

/-! ### Row sums -/

/-- The sum `∑ k ∈ Finset.range j, P k j` of the `j` informative entries in row `j` of a
Gelfand–Tsetlin pattern `P` (zero at `j = 0` and for `n < j`). -/
def rowSum (P : GTPattern n) (j : ℕ) : ℤ :=
  ∑ k ∈ Finset.range j, P k j

theorem rowSum_def (P : GTPattern n) (j : ℕ) :
    P.rowSum j = ∑ k ∈ Finset.range j, P k j :=
  (rfl)

@[simp]
theorem rowSum_zero (P : GTPattern n) : P.rowSum 0 = 0 := by
  simp [rowSum_def]

@[simp]
theorem rowSum_eq_zero_of_lt (P : GTPattern n) {j : ℕ} (hj : n < j) : P.rowSum j = 0 := by
  simp [rowSum_def, P.entry_eq_zero_of_lt hj]

/-- The sum of row `n` is the sum of `P.topRow`. -/
theorem rowSum_top (P : GTPattern n) : P.rowSum n = ∑ i : Fin n, P.topRow i := by
  rw [rowSum_def, ← Fin.sum_univ_eq_sum_range]
  simp [topRow_apply]

/-- For `j ≤ n`, the sum of row `j` is at most the leading partial sum of `P.topRow` of length
`j`. -/
theorem rowSum_le_prefixSum_topRow (P : GTPattern n) {j : ℕ} (hj : j ≤ n) :
    P.rowSum j ≤ TauCeti.prefixSum j P.topRow := by
  rw [rowSum_def, show P.topRow = fun i : Fin n => P i.val n from funext P.topRow_apply,
    TauCeti.prefixSum_eq_sum_range j (fun k => P k n), min_eq_left hj]
  exact Finset.sum_le_sum fun k hk => P.entry_le_entry_of_le (Finset.mem_range.mp hk) hj le_rfl

@[simp]
theorem rowSum_zero_left (j : ℕ) : (0 : GTPattern n).rowSum j = 0 := by
  simp [rowSum_def, zero_apply]

@[simp]
theorem rowSum_add (P Q : GTPattern n) (j : ℕ) :
    (P + Q).rowSum j = P.rowSum j + Q.rowSum j := by
  simp [rowSum_def, add_apply, Finset.sum_add_distrib]

@[simp]
theorem rowSum_nsmul (k : ℕ) (P : GTPattern n) (j : ℕ) :
    (k • P).rowSum j = k • P.rowSum j := by
  rw [rowSum_def, rowSum_def, ← Finset.sum_nsmul]
  simp [nsmul_apply]

@[simp]
theorem rowSum_const (m : ℤ) {j : ℕ} (hj : j ≤ n) :
    (const n m).rowSum j = j * m := by
  rw [rowSum_def, Finset.sum_congr rfl fun k hk =>
    const_apply_of_lt_of_le m (Finset.mem_range.mp hk) hj]
  simp

@[simp]
theorem rowSum_shift (P : GTPattern n) (m : ℤ) {j : ℕ} (hj : j ≤ n) :
    (P.shift m).rowSum j = P.rowSum j + j * m := by
  rw [rowSum_def, Finset.sum_congr rfl fun k hk =>
    P.shift_apply_of_lt_of_le m (Finset.mem_range.mp hk) hj, Finset.sum_add_distrib, ← rowSum_def]
  simp

@[simp]
theorem rowSum_truncate (P : GTPattern (n + 1)) {j : ℕ} (hj : j ≤ n) :
    P.truncate.rowSum j = P.rowSum j := by
  simp [rowSum_def, hj]

@[simp]
theorem rowSum_extend_of_ne (Q : GTPattern n) (l : Fin (n + 1) → ℤ) (h : Interlaces l Q.topRow)
    {j : ℕ} (hj : j ≠ n + 1) : (Q.extend l h).rowSum j = Q.rowSum j := by
  simp [rowSum_def, hj]

@[simp]
theorem rowSum_extend_top (Q : GTPattern n) (l : Fin (n + 1) → ℤ) (h : Interlaces l Q.topRow) :
    (Q.extend l h).rowSum (n + 1) = ∑ i : Fin (n + 1), l i := by
  rw [rowSum_top, topRow_extend]

/-! ### Torus weights of patterns -/

/-- The **weight** of a Gelfand–Tsetlin pattern `P`: its `r`-th entry is the successive row-sum
difference `P.rowSum (r + 1) - P.rowSum r`. -/
def weight (P : GTPattern n) : Fin n → ℤ :=
  fun r => P.rowSum (r.val + 1) - P.rowSum r.val

theorem weight_apply (P : GTPattern n) (r : Fin n) :
    P.weight r = P.rowSum (r.val + 1) - P.rowSum r.val :=
  (rfl)

/-- Unfolded formula for `P.weight` directly in terms of `Finset.range` sums of pattern entries. -/
theorem weight_eq_sub_sum (P : GTPattern n) (r : Fin n) :
    P.weight r =
      (∑ k ∈ Finset.range (r.val + 1), P k (r.val + 1)) - ∑ k ∈ Finset.range r.val, P k r.val :=
  (rfl)

@[simp]
theorem weight_zero : (0 : GTPattern n).weight = 0 := by
  ext r; simp [weight_apply]

@[simp]
theorem weight_add (P Q : GTPattern n) : (P + Q).weight = P.weight + Q.weight := by
  ext r; simp only [weight_apply, Pi.add_apply, rowSum_add]; abel

@[simp]
theorem weight_nsmul (k : ℕ) (P : GTPattern n) : (k • P).weight = k • P.weight := by
  ext r
  simp only [weight_apply, Pi.smul_apply, rowSum_nsmul, nsmul_eq_mul]
  ring

/-- `GTPattern.weight` bundled as an additive monoid homomorphism `GTPattern n →+ (Fin n → ℤ)`. -/
def weightAddMonoidHom : GTPattern n →+ (Fin n → ℤ) where
  toFun := weight
  map_zero' := weight_zero
  map_add' := weight_add

@[simp]
theorem weightAddMonoidHom_apply (P : GTPattern n) : weightAddMonoidHom P = P.weight :=
  (rfl)

@[simp]
theorem weight_const (m : ℤ) : (const n m).weight = fun _ => m := by
  ext r
  rw [weight_apply, rowSum_const m r.isLt, rowSum_const m r.isLt.le]
  push_cast
  ring

/-- Shifting every informative entry of `P` by `m` adds `m` to every entry of `P.weight`. -/
@[simp]
theorem weight_shift (P : GTPattern n) (m : ℤ) :
    (P.shift m).weight = fun r => P.weight r + m := by
  ext r
  rw [weight_apply, rowSum_shift P m r.isLt, rowSum_shift P m r.isLt.le, weight_apply]
  push_cast
  ring

/-- Summing the first `j ≤ n` components of `P.weight` telescopes to `P.rowSum j`. -/
theorem prefixSum_weight (P : GTPattern n) {j : ℕ} (hj : j ≤ n) :
    TauCeti.prefixSum j P.weight = P.rowSum j := by
  unfold weight
  rw [TauCeti.prefixSum_eq_sum_range j (fun k => P.rowSum (k + 1) - P.rowSum k),
    min_eq_left hj, Finset.sum_range_sub, P.rowSum_zero, sub_zero]

/-- The entries of `P.weight` sum to the sum of `P.topRow`. -/
@[simp]
theorem sum_weight (P : GTPattern n) : (∑ r : Fin n, P.weight r) = ∑ i : Fin n, P.topRow i := by
  rw [← TauCeti.prefixSum_of_le le_rfl, P.prefixSum_weight le_rfl, P.rowSum_top]

/-- The highest weight `P.topRow` dominates `P.weight` in the leading-partial-sum order
(`TauCeti.Dominates P.weight P.topRow`: equal total sums and
`∑_{j < k} P.weight j ≤ ∑_{j < k} P.topRow j` for all `k ≤ n`). -/
theorem dominates_weight_topRow (P : GTPattern n) : TauCeti.Dominates P.weight P.topRow :=
  TauCeti.dominates_def.mpr ⟨P.sum_weight.symm, fun k hk => by
    rw [← TauCeti.prefixSum_eq_sum_castLE hk, ← TauCeti.prefixSum_eq_sum_castLE hk,
      P.prefixSum_weight hk]
    exact P.rowSum_le_prefixSum_topRow hk⟩

@[simp]
theorem weight_truncate (P : GTPattern (n + 1)) (r : Fin n) :
    P.truncate.weight r = P.weight r.castSucc := by
  rw [weight_apply, weight_apply, Fin.val_castSucc,
    P.rowSum_truncate (by omega), P.rowSum_truncate (by omega)]

@[simp]
theorem weight_extend_castSucc (Q : GTPattern n) (l : Fin (n + 1) → ℤ) (h : Interlaces l Q.topRow)
    (r : Fin n) : (Q.extend l h).weight r.castSucc = Q.weight r := by
  rw [← weight_truncate, truncate_extend]

@[simp]
theorem weight_extend_last (Q : GTPattern n) (l : Fin (n + 1) → ℤ) (h : Interlaces l Q.topRow) :
    (Q.extend l h).weight (Fin.last n) = (∑ i, l i) - ∑ i, Q.topRow i := by
  rw [weight_apply, Fin.val_last, rowSum_extend_top,
    rowSum_extend_of_ne Q l h (Nat.ne_add_one n), Q.rowSum_top]

/-- Every entry of `P.weight` lies between the last and first entries of `P.topRow`. -/
theorem weight_mem_Icc (P : GTPattern n) (r : Fin n) :
    P.weight r ∈
      Set.Icc (P.topRow ⟨n - 1, by have := r.isLt; omega⟩)
        (P.topRow ⟨0, by have := r.isLt; omega⟩) := by
  constructor
  · have hsum : P.weight r = P r.val (r.val + 1) +
        ∑ k ∈ Finset.range r.val, (P k (r.val + 1) - P k r.val) := by
      rw [weight_eq_sub_sum, Finset.sum_range_succ, Finset.sum_sub_distrib]
      abel
    have hnn : 0 ≤ ∑ k ∈ Finset.range r.val, (P k (r.val + 1) - P k r.val) :=
      Finset.sum_nonneg fun k hk => sub_nonneg.mpr <|
        P.entry_le_entry_succ_row (Finset.mem_range.mp hk) r.isLt
    have hlo := (P.entry_mem_Icc (Nat.lt_succ_self r.val) r.isLt).1
    linarith
  · have hsum : P.weight r = P 0 (r.val + 1) +
        ∑ k ∈ Finset.range r.val, (P (k + 1) (r.val + 1) - P k r.val) := by
      rw [weight_eq_sub_sum, Finset.sum_range_succ', Finset.sum_sub_distrib]
      abel
    have hnp : ∑ k ∈ Finset.range r.val, (P (k + 1) (r.val + 1) - P k r.val) ≤ 0 :=
      Finset.sum_nonpos fun k _ => sub_nonpos.mpr <| P.entry_succ_succ_le_entry r.isLt
    have hhi := (P.entry_mem_Icc (Nat.succ_pos r.val) r.isLt).2
    linarith

/-- Nonnegative (polynomial) patterns have nonnegative weights. -/
theorem weight_nonneg {P : GTPattern n} (hP : 0 ≤ P) (r : Fin n) : 0 ≤ P.weight r :=
  (zero_le_iff_topRow.mp hP ⟨n - 1, by have := r.isLt; omega⟩).trans (P.weight_mem_Icc r).1

/-! ### Low-rank weight fibres -/

/-- Two rank-`2` patterns with the same top row and weight are equal. -/
theorem eq_of_topRow_eq_of_weight_eq_two {P Q : GTPattern 2} (ht : P.topRow = Q.topRow)
    (hw : P.weight = Q.weight) : P = Q := by
  ext i j
  by_cases hij : i < j ∧ j ≤ 2
  · obtain ⟨hlt, hle⟩ := hij
    rcases (by omega : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2)) with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hP1 : P.weight 0 = P 0 1 := by simp [weight_apply, rowSum_def]
      have hQ1 : Q.weight 0 = Q 0 1 := by simp [weight_apply, rowSum_def]
      linarith [congrFun hw 0]
    · simpa [topRow_apply] using congrFun ht 0
    · simpa [topRow_apply] using congrFun ht 1
  · rw [P.entry_eq_zero (by omega), Q.entry_eq_zero (by omega)]

/-- Cardinality of a rank-`2` Gelfand–Tsetlin weight fibre over an integer sequence `l`. -/
theorem card_topRow_weight_two (l w : Fin 2 → ℤ) :
    Nat.card {P : GTPattern 2 // P.topRow = l ∧ P.weight = w} =
      if w 0 + w 1 = l 0 + l 1 ∧ l 1 ≤ w 0 ∧ w 0 ≤ l 0 then 1 else 0 := by
  have : Subsingleton {P : GTPattern 2 // P.topRow = l ∧ P.weight = w} :=
    ⟨fun P Q => Subtype.ext (eq_of_topRow_eq_of_weight_eq_two (P.2.1.trans Q.2.1.symm)
      (P.2.2.trans Q.2.2.symm))⟩
  split_ifs with hcond
  · obtain ⟨hsum, hlo, hhi⟩ := hcond
    let Q₁ : GTPattern 1 := equivOne.symm ![w 0]
    have hQ₁ : Q₁.topRow = ![w 0] :=
      (equivOne_apply Q₁).symm.trans (equivOne.apply_symm_apply ![w 0])
    have hint : Interlaces l Q₁.topRow :=
      interlaces_iff.mpr fun i => by rw [Subsingleton.elim i 0, hQ₁]; exact ⟨hhi, hlo⟩
    let P : GTPattern 2 := Q₁.extend l hint
    have hPtop : P.topRow = l := topRow_extend Q₁ l hint
    have hPw0 : P.weight 0 = w 0 := by
      have h0 : P.weight 0 = Q₁.weight 0 := weight_extend_castSucc Q₁ l hint 0
      have hs := Q₁.sum_weight
      simp only [Fin.sum_univ_one, hQ₁, Matrix.cons_val_zero] at hs
      exact h0.trans hs
    have hPw1 : P.weight 1 = w 1 := by
      have hs := P.sum_weight
      simp only [Fin.sum_univ_two, hPtop, hPw0] at hs
      omega
    have hPw : P.weight = w := by ext r; fin_cases r; exacts [hPw0, hPw1]
    have : Unique {Q : GTPattern 2 // Q.topRow = l ∧ Q.weight = w} :=
      uniqueOfSubsingleton ⟨P, hPtop, hPw⟩
    exact Nat.card_unique
  · refine Nat.card_eq_zero.mpr (Or.inl ⟨fun ⟨P, hPt, hPw⟩ => hcond ?_⟩)
    have hsum : w 0 + w 1 = l 0 + l 1 := by
      have hs := P.sum_weight; simp only [hPw, hPt, Fin.sum_univ_two] at hs; exact hs
    have hmem := P.weight_mem_Icc 0
    rw [hPw, hPt] at hmem
    exact ⟨hsum, hmem.1, hmem.2⟩

/-- Rank-`2` check: the weight-`(1, 1)` Gelfand–Tsetlin fibre over `(2, 0)` has cardinality `1`. -/
theorem card_topRow_weight_two_two_zero_one_one :
    Nat.card {P : GTPattern 2 // P.topRow = ![2, 0] ∧ P.weight = ![1, 1]} = 1 := by
  rw [card_topRow_weight_two]
  decide

private def adjointZeroPattern (b : Bool) : GTPattern 3 where
  entry i j :=
    match i, j with
    | 0, 3 => 1
    | 2, 3 => -1
    | 0, 2 => if b then 1 else 0
    | 1, 2 => if b then -1 else 0
    | _, _ => 0
  zeros' {i j} hout := by
    match i, j with
    | 0, 3 | 2, 3 | 0, 2 | 1, 2 => omega
    | 0, 0 | 0, 1 | 1, 0 | 1, 1 | 1, 3 | 2, 0 | 2, 1 | 2, 2 => rfl
    | i + 3, _ => rfl
    | 0, j + 4 | 1, j + 4 | 2, j + 4 => rfl
  interlacing' {i j} hij hj := by
    have : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) := by omega
    rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cases b <;> decide

@[simp]
private theorem adjointZeroPattern_apply (b : Bool) (i j : ℕ) :
    adjointZeroPattern b i j =
      match i, j with
      | 0, 3 => 1
      | 2, 3 => -1
      | 0, 2 => if b then 1 else 0
      | 1, 2 => if b then -1 else 0
      | _, _ => 0 := by
  rw [← congrFun₂ (entry_eq_coe (P := adjointZeroPattern b)) i j]
  rfl

private theorem adjointZeroPattern_topRow (b : Bool) :
    (adjointZeroPattern b).topRow = ![1, 0, -1] := by
  ext i; fin_cases i <;> simp [topRow_apply]

private theorem adjointZeroPattern_weight (b : Bool) :
    (adjointZeroPattern b).weight = 0 := by
  ext r; fin_cases r <;> cases b <;>
    simp [weight_apply, rowSum_def, Finset.sum_range_succ]

/-- Explicit bijection between the weight-`0` Gelfand–Tsetlin fibre over the rational `SL 3`
adjoint top row `(1, 0, -1)` and `Bool`, corresponding to the two middle rows `(0, 0)` and
`(1, -1)`. -/
private def threeAdjointZeroEquivBool :
    {P : GTPattern 3 // P.topRow = ![1, 0, -1] ∧ P.weight = 0} ≃ Bool where
  toFun P := decide (P.1 0 2 = 1)
  invFun b := ⟨adjointZeroPattern b, adjointZeroPattern_topRow b, adjointZeroPattern_weight b⟩
  left_inv := by
    rintro ⟨P, hTop, hW⟩
    have h03 : P 0 3 = 1 := by simpa [topRow_apply] using congrFun hTop 0
    have h13 : P 1 3 = 0 := by simpa [topRow_apply] using congrFun hTop 1
    have h23 : P 2 3 = -1 := by simpa [topRow_apply] using congrFun hTop 2
    have h01 : P 0 1 = 0 := by simpa [weight_apply, rowSum_def] using congrFun hW 0
    have hrow2 : P 0 2 + P 1 2 = 0 := by
      simpa [weight_apply, rowSum_def, Finset.sum_range_succ, h01] using congrFun hW 1
    have h02_lo : 0 ≤ P 0 2 := by
      simpa [h13] using P.entry_succ_succ_le_entry (i := 0) (j := 2) (by decide)
    have h02_hi : P 0 2 ≤ 1 := by
      simpa [h03] using P.entry_le_entry_succ_row (i := 0) (j := 2) (by decide) (by decide)
    set b := decide (P 0 2 = 1)
    have hb02 : P 0 2 = if b then 1 else 0 := by
      rcases (by omega : P 0 2 = 0 ∨ P 0 2 = 1) with h02 | h02 <;> simp [b, h02]
    have hb12 : P 1 2 = if b then -1 else 0 := by
      rcases (by omega : P 0 2 = 0 ∨ P 0 2 = 1) with h02 | h02 <;> simp [b, h02] <;> omega
    apply Subtype.ext
    ext i j
    dsimp only
    by_cases hij : i < j ∧ j ≤ 3
    · rcases (by omega : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) ∨
          (i = 0 ∧ j = 3) ∨ (i = 1 ∧ j = 3) ∨ (i = 2 ∧ j = 3)) with
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp [h01, hb02, hb12, h03, h13, h23]
    · rw [(adjointZeroPattern b).entry_eq_zero (by omega), P.entry_eq_zero (by omega)]
  right_inv b := by cases b <;> simp

@[simp] private theorem threeAdjointZeroEquivBool_apply
    (P : {P : GTPattern 3 // P.topRow = ![1, 0, -1] ∧ P.weight = 0}) :
    threeAdjointZeroEquivBool P = decide (P.1 0 2 = 1) := (rfl)

@[simp] private theorem threeAdjointZeroEquivBool_symm_apply (b : Bool) (i j : ℕ) :
    (threeAdjointZeroEquivBool.symm b).1 i j =
      match i, j with
      | 0, 3 => 1
      | 2, 3 => -1
      | 0, 2 => if b then 1 else 0
      | 1, 2 => if b then -1 else 0
      | _, _ => 0 :=
  adjointZeroPattern_apply b i j

/-- Rank-`3` check: the weight-`0` Gelfand–Tsetlin fibre over the `SL 3` adjoint weight `(1, 0, -1)`
has cardinality `2` (the `2`-dimensional zero weight space of `𝔰𝔩₃`). -/
theorem card_three_adjoint_weight_zero :
    Nat.card {P : GTPattern 3 // P.topRow = ![1, 0, -1] ∧ P.weight = 0} = 2 := by
  simp [Nat.card_congr threeAdjointZeroEquivBool]

end TauCeti.GTPattern

namespace SemistandardYoungTableau

variable {μ : YoungDiagram}

/-- For `j ≤ n`, row `j` of `T.toGTPattern n` sums to the number of cells of `μ` carrying entries
below `j`, i.e., `∑ k ∈ Finset.range j, (T.content k : ℤ)`. -/
theorem rowSum_toGTPattern (T : SemistandardYoungTableau μ) (n : ℕ) {j : ℕ} (hj : j ≤ n) :
    (T.toGTPattern n).rowSum j = ∑ k ∈ Finset.range j, (T.content k : ℤ) := by
  have hnj : ¬ n < j := Nat.not_lt.mpr hj
  rw [TauCeti.GTPattern.rowSum_def, ← Nat.cast_sum, sum_content_eq_card_filter,
    YoungDiagram.card_filter_cells μ (fun c => T c.1 c.2 < j) (le_max_right j (μ.colLen 0)),
    Nat.cast_sum]
  have hcell (i : ℕ) : (((Finset.range (μ.rowLen i)).filter fun c => T i c < j).card : ℤ) =
      (T.toGTPattern n) i j := by
    rw [toGTPattern_apply, patternEntry_def, ite_eq_right hnj]
  simp_rw [hcell]
  exact Finset.sum_subset (Finset.range_mono (le_max_left j (μ.colLen 0))) fun i _ hi =>
    (T.toGTPattern n).entry_eq_zero_of_le (Nat.not_lt.mp (Finset.mem_range.not.mp hi))

/-- The weight of the Gelfand–Tsetlin pattern read off a semistandard Young tableau `T` agrees on
`Fin n` with `T.content`. -/
@[simp]
theorem weight_toGTPattern (T : SemistandardYoungTableau μ) (n : ℕ) :
    (T.toGTPattern n).weight = fun r => (T.content r.val : ℤ) := by
  ext r
  rw [TauCeti.GTPattern.weight_apply, T.rowSum_toGTPattern n r.isLt,
    T.rowSum_toGTPattern n r.isLt.le, Finset.sum_range_succ, add_sub_cancel_left]

end SemistandardYoungTableau

namespace TauCeti.GTPattern

/-- Under `TauCeti.GTPattern.toTableau`, the content of the semistandard Young tableau attached to
a pattern `P` of shape `μ` equals `P.weight`. -/
@[simp]
theorem natCast_content_toTableau {n : ℕ} (P : GTPattern n) {μ : YoungDiagram}
    (hμ : μ.colLen 0 ≤ n) (hP : ∀ i : Fin n, P.topRow i = (μ.rowLen i : ℤ)) (r : Fin n) :
    ((P.toTableau hμ hP).content r.val : ℤ) = P.weight r := by
  have hinv : (P.toTableau hμ hP).toGTPattern n = P := by
    have h := congrArg Subtype.val ((gtPatternEquivSSYT n μ hμ).symm_apply_apply ⟨P, hP⟩)
    rwa [gtPatternEquivSSYT_symm_apply_coe, gtPatternEquivSSYT_apply_coe] at h
  rw [← congrFun (SemistandardYoungTableau.weight_toGTPattern (P.toTableau hμ hP) n) r, hinv]

/-- Under `TauCeti.GTPattern.toTableau`, the `ℕ`-valued content of the semistandard Young tableau
attached to a pattern `P` of shape `μ` equals `(P.weight r).toNat` on `r : Fin n`. -/
theorem content_toTableau {n : ℕ} (P : GTPattern n) {μ : YoungDiagram}
    (hμ : μ.colLen 0 ≤ n) (hP : ∀ i : Fin n, P.topRow i = (μ.rowLen i : ℤ)) (r : Fin n) :
    (P.toTableau hμ hP).content r.val = (P.weight r).toNat := by
  rw [← P.natCast_content_toTableau hμ hP r, Int.toNat_natCast]

/-- For `n ≤ k`, `P.toTableau hμ hP` uses no letter `k`, so `(P.toTableau hμ hP).content k = 0`. -/
@[simp]
theorem content_toTableau_eq_zero {n : ℕ} (P : GTPattern n) {μ : YoungDiagram}
    (hμ : μ.colLen 0 ≤ n) (hP : ∀ i : Fin n, P.topRow i = (μ.rowLen i : ℤ)) {k : ℕ}
    (hk : n ≤ k) : (P.toTableau hμ hP).content k = 0 := by
  simpa using BoundedSSYT.content_eq_zero (gtPatternEquivSSYT n μ hμ ⟨P, hP⟩) hk

end TauCeti.GTPattern
