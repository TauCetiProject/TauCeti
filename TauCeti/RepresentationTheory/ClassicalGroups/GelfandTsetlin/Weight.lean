/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.BigOperators.Finset.PartialSum
public import TauCeti.RepresentationTheory.ClassicalGroups.GelfandTsetlin.Count
public import TauCeti.RepresentationTheory.ClassicalGroups.GelfandTsetlin.Shift
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

(`TauCeti.GTPattern.rowWeight`, `TauCeti.GTPattern.rowWeight_eq_rowSum_sub`). Because `P` may
have negative entries, `P.rowWeight : Fin n → ℤ` is an arbitrary integer weight rather than a
nonnegative composition or an antitone sequence: its entries sum to `∑ i, P.topRow i`, every
component lies between the last and first entries of `P.topRow`, and shifting every informative
entry of `P` by `m` adds `m` to every component of `P.rowWeight`. In the polynomial regime, where
`TauCeti.gtPatternEquivSSYT` identifies patterns with bounded semistandard Young tableaux,
`P.rowWeight` agrees with Tau Ceti's `SemistandardYoungTableau.content`.

## Main definitions

* `TauCeti.GTPattern.rowSum`: the sum `∑ k ∈ Finset.range j, P k j` of row `j` of a pattern.
* `TauCeti.GTPattern.rowWeightAddMonoidHom`: `GTPattern.rowWeight` bundled as an additive monoid
  homomorphism `GTPattern n →+ (Fin n → ℤ)`.
* `TauCeti.GTPattern.truncateRowWeightSigmaEquiv`: the weight-refined branching equivalence along
  `GL (n + 1) ↓ GL n`.
* `TauCeti.GTPattern.highest`: the highest-weight pattern of a dominant weight, whose rows are
  initial segments of its top row.

## Main results

* `TauCeti.GTPattern.prefixSum_rowWeight`, `TauCeti.GTPattern.rowSum_le_prefixSum_topRow`, and
  `TauCeti.GTPattern.dominates_rowWeight_topRow`: leading prefix sums of `P.rowWeight` recover
  `P.rowSum`, and `P.topRow` dominates `P.rowWeight` (`TauCeti.Dominates P.rowWeight P.topRow`).
* `TauCeti.GTPattern.entry_diag_le_rowWeight`, `TauCeti.GTPattern.rowWeight_le_entry_zero`, and
  `TauCeti.GTPattern.rowWeight_mem_Icc`: every entry of `P.rowWeight` lies between the last and
  first entries of row `r + 1`, hence of `P.topRow`, so nonnegative patterns have nonnegative
  weights (`rowWeight_nonneg`); a dominant row weight is dominated by `P.topWeight`
  (`TauCeti.GTPattern.topWeight_dominates_of_rowWeight_eq`).
* `TauCeti.GTPattern.eq_highest_iff`: a pattern whose weight is its top row is the highest-weight
  pattern.
* `TauCeti.GTPattern.rowWeight_eq_iff_truncate`: the weight of a pattern is determined by the weight
  of its truncation and the degree increment of its top row.
* `TauCeti.GTPattern.card_topRow_rowWeight_succ`, `TauCeti.GTPattern.card_topRow_rowWeight_zero`,
  `TauCeti.GTPattern.card_topRow_rowWeight_one`,
  `TauCeti.GTPattern.eq_of_topRow_eq_of_rowWeight_eq_two`,
  `TauCeti.GTPattern.nonempty_topRow_rowWeight_two_iff`,
  `TauCeti.GTPattern.card_topRow_rowWeight_two`,
  `TauCeti.GTPattern.card_topRow_rowWeight_three`, and
  `TauCeti.GTPattern.card_three_adjoint_rowWeight_zero`: branching weight-fibre recursion, low-rank
  uniqueness, and explicit counts.
* `SemistandardYoungTableau.rowWeight_toGTPattern`, `TauCeti.GTPattern.natCast_content_toTableau`,
  `TauCeti.GTPattern.content_toTableau`, and `TauCeti.GTPattern.content_toTableau_eq_zero`: under
  the pattern–tableau correspondence, `GTPattern.rowWeight` equals tableau `content`.

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
def rowSum (P : GTPattern n) (j : ℕ) : ℤ := ∑ k ∈ Finset.range j, P k j

theorem rowSum_def (P : GTPattern n) (j : ℕ) :
    P.rowSum j = ∑ k ∈ Finset.range j, P k j := (rfl)

@[simp] theorem rowSum_zero (P : GTPattern n) : P.rowSum 0 = 0 := by simp [rowSum_def]
@[simp] theorem rowSum_one (P : GTPattern n) : P.rowSum 1 = P 0 1 := by simp [rowSum_def]

@[simp] theorem rowSum_eq_zero_of_lt (P : GTPattern n) {j : ℕ} (hj : n < j) : P.rowSum j = 0 := by
  simp [rowSum_def, P.entry_eq_zero_of_lt hj]

/-- Summing row `j` past index `j` adds only off-triangle zeros, so any `Finset.range i` with
`j ≤ i` computes `P.rowSum j`. -/
theorem sum_range_entry_eq_rowSum (P : GTPattern n) {i j : ℕ} (hij : j ≤ i) :
    ∑ k ∈ Finset.range i, P k j = P.rowSum j :=
  (Finset.sum_subset (Finset.range_mono hij) fun _ _ hkj =>
    P.entry_eq_zero_of_le (Nat.not_lt.mp (mt Finset.mem_range.mpr hkj))).symm

/-- The sum of row `n` is the sum of `P.topRow`. -/
theorem rowSum_top (P : GTPattern n) : P.rowSum n = ∑ i : Fin n, P.topRow i := by
  rw [rowSum_def, ← Fin.sum_univ_eq_sum_range]; simp [topRow_apply]

/-- Leading partial sums of `P.topRow` agree with `Finset.range` sums of row `n`, since entries
past `n` vanish. -/
theorem prefixSum_topRow (P : GTPattern n) (k : ℕ) :
    TauCeti.prefixSum k P.topRow = ∑ i ∈ Finset.range k, P i n := by
  have htop : P.topRow = fun i : Fin n => P i.val n := funext P.topRow_apply
  rw [htop, TauCeti.prefixSum_eq_sum_range k (fun i => P i n)]
  exact Finset.sum_subset (Finset.range_mono (min_le_left k n)) fun i hi hi' =>
    P.entry_eq_zero_of_le (by simp only [Finset.mem_range, lt_min_iff] at hi hi'; omega)

/-- For `j ≤ n`, the sum of row `j` is at most the leading partial sum of `P.topRow` of length
`j`. -/
theorem rowSum_le_prefixSum_topRow (P : GTPattern n) {j : ℕ} (hj : j ≤ n) :
    P.rowSum j ≤ TauCeti.prefixSum j P.topRow := by
  rw [rowSum_def, P.prefixSum_topRow]
  exact Finset.sum_le_sum fun k hk => P.entry_le_entry_of_le (Finset.mem_range.mp hk) hj le_rfl

@[simp] theorem rowSum_zero_left (j : ℕ) : (0 : GTPattern n).rowSum j = 0 := by
  simp [rowSum_def, zero_apply]

@[simp] theorem rowSum_add (P Q : GTPattern n) (j : ℕ) :
    (P + Q).rowSum j = P.rowSum j + Q.rowSum j := by
  simp [rowSum_def, add_apply, Finset.sum_add_distrib]

@[simp] theorem rowSum_nsmul (k : ℕ) (P : GTPattern n) (j : ℕ) :
    (k • P).rowSum j = k • P.rowSum j := by
  rw [rowSum_def, rowSum_def, ← Finset.sum_nsmul]; simp [nsmul_apply]

@[simp] theorem rowSum_const (m : ℤ) {j : ℕ} (hj : j ≤ n) : (const n m).rowSum j = j * m := by
  rw [rowSum_def, Finset.sum_congr rfl fun k hk =>
    const_apply_of_lt_of_le m (Finset.mem_range.mp hk) hj]; simp

@[simp] theorem rowSum_shift (P : GTPattern n) (m : ℤ) {j : ℕ} (hj : j ≤ n) :
    (P.shift m).rowSum j = P.rowSum j + j * m := by
  rw [shift_eq_add_const, rowSum_add, rowSum_const m hj]

@[simp] theorem rowSum_truncate (P : GTPattern (n + 1)) {j : ℕ} (hj : j ≤ n) :
    P.truncate.rowSum j = P.rowSum j := by simp [rowSum_def, hj]

@[simp] theorem rowSum_extend_of_ne (Q : GTPattern n) (l : Fin (n + 1) → ℤ)
    (h : Interlaces l Q.topRow) {j : ℕ} (hj : j ≠ n + 1) :
    (Q.extend l h).rowSum j = Q.rowSum j := by simp [rowSum_def, hj]

@[simp] theorem rowSum_extend_top (Q : GTPattern n) (l : Fin (n + 1) → ℤ)
    (h : Interlaces l Q.topRow) : (Q.extend l h).rowSum (n + 1) = ∑ i : Fin (n + 1), l i := by
  rw [rowSum_top, topRow_extend]

/-! ### Torus weights of patterns -/

/-- The row weight of `P` is the successive row-sum difference `P.rowSum (r + 1) - P.rowSum r`. -/
theorem rowWeight_eq_rowSum_sub (P : GTPattern n) (r : Fin n) :
    P.rowWeight r = P.rowSum (r.val + 1) - P.rowSum r.val :=
  P.rowWeight_apply r

/-- The `0`-th weight component of a nonempty pattern is its single bottom-row entry `P 0 1`. -/
theorem rowWeight_apply_zero (P : GTPattern (n + 1)) : P.rowWeight 0 = P 0 1 := by
  rw [rowWeight_eq_rowSum_sub, Fin.val_zero, zero_add, rowSum_one, rowSum_zero, sub_zero]

/-- A rank-`1` pattern has a single row, so its torus weight equals its top row. -/
theorem rowWeight_eq_topRow (P : GTPattern 1) : P.rowWeight = P.topRow := by
  ext i; rw [Subsingleton.elim i 0, rowWeight_apply_zero, topRow_apply, Fin.val_zero]

/-- The last weight coordinate of a pattern with `n + 1` rows is the difference between the sums of
its top two rows. -/
theorem rowWeight_last (P : GTPattern (n + 1)) :
    P.rowWeight (Fin.last n) = (∑ i, P.topRow i) - ∑ i, P.truncate.topRow i := by
  rw [rowWeight_eq_rowSum_sub, Fin.val_last, P.rowSum_top, ← P.rowSum_truncate le_rfl,
    P.truncate.rowSum_top]

/-- `GTPattern.rowWeight` bundled as an additive monoid homomorphism
`GTPattern n →+ (Fin n → ℤ)`. -/
def rowWeightAddMonoidHom : GTPattern n →+ (Fin n → ℤ) :=
  { toFun := rowWeight, map_zero' := rowWeight_zero, map_add' := rowWeight_add }

@[simp] theorem rowWeightAddMonoidHom_apply (P : GTPattern n) :
    rowWeightAddMonoidHom P = P.rowWeight :=
  (rfl)

/-- Summing the first `j ≤ n` components of `P.rowWeight` telescopes to `P.rowSum j`. -/
theorem prefixSum_rowWeight (P : GTPattern n) {j : ℕ} (hj : j ≤ n) :
    TauCeti.prefixSum j P.rowWeight = P.rowSum j := by
  rw [show P.rowWeight = fun r : Fin n => P.rowSum (r.val + 1) - P.rowSum r.val from
    funext P.rowWeight_eq_rowSum_sub,
    TauCeti.prefixSum_eq_sum_range j (fun k => P.rowSum (k + 1) - P.rowSum k),
    min_eq_left hj, Finset.sum_range_sub, P.rowSum_zero, sub_zero]

/-- The highest weight `P.topRow` dominates `P.rowWeight` in the leading-partial-sum order
(`TauCeti.Dominates P.rowWeight P.topRow`: equal total sums and
`∑_{j < k} P.rowWeight j ≤ ∑_{j < k} P.topRow j` for all `k ≤ n`). -/
theorem dominates_rowWeight_topRow (P : GTPattern n) : TauCeti.Dominates P.rowWeight P.topRow :=
  TauCeti.dominates_def.mpr ⟨P.sum_rowWeight.symm, fun k hk => by
    rw [← TauCeti.prefixSum_eq_sum_castLE hk, ← TauCeti.prefixSum_eq_sum_castLE hk,
      P.prefixSum_rowWeight hk]
    exact P.rowSum_le_prefixSum_topRow hk⟩

/-- When `P.rowWeight` is a dominant weight `w`, the top weight `P.topWeight` dominates `w`. -/
theorem topWeight_dominates_of_rowWeight_eq (P : GTPattern n) {w : DominantWeight n}
    (hw : P.rowWeight = w.val) : P.topWeight.Dominates w := by
  rw [DominantWeight.dominates_def, topWeight_coe, ← hw]
  exact P.dominates_rowWeight_topRow

/-- Because `P k r ≤ P k (r + 1)` for `k < r < n`, the `r`-th weight coordinate is at least the
last informative entry `P r (r + 1)` of row `r + 1`. -/
theorem entry_diag_le_rowWeight (P : GTPattern n) (r : Fin n) :
    P r.val (r.val + 1) ≤ P.rowWeight r := by
  have hsum : P.rowWeight r = P r.val (r.val + 1) +
      ∑ k ∈ Finset.range r.val, (P k (r.val + 1) - P k r.val) := by
    rw [rowWeight_apply, Finset.sum_range_succ, Finset.sum_sub_distrib]; abel
  have hnn : 0 ≤ ∑ k ∈ Finset.range r.val, (P k (r.val + 1) - P k r.val) :=
    Finset.sum_nonneg fun k hk => sub_nonneg.mpr <|
      P.entry_le_entry_succ_row (Finset.mem_range.mp hk) r.isLt
  linarith

/-- Because `P (k + 1) (r + 1) ≤ P k r` for `r < n`, the `r`-th weight coordinate is at most the
first entry `P 0 (r + 1)` of row `r + 1`. -/
theorem rowWeight_le_entry_zero (P : GTPattern n) (r : Fin n) :
    P.rowWeight r ≤ P 0 (r.val + 1) := by
  have hsum : P.rowWeight r = P 0 (r.val + 1) +
      ∑ k ∈ Finset.range r.val, (P (k + 1) (r.val + 1) - P k r.val) := by
    rw [rowWeight_apply, Finset.sum_range_succ', Finset.sum_sub_distrib]; abel
  have hnp : ∑ k ∈ Finset.range r.val, (P (k + 1) (r.val + 1) - P k r.val) ≤ 0 :=
    Finset.sum_nonpos fun k _ => sub_nonpos.mpr <| P.entry_succ_succ_le_entry r.isLt
  linarith

/-- Every entry of `P.rowWeight` lies between the last and first entries of `P.topRow`. -/
theorem rowWeight_mem_Icc (P : GTPattern n) (r : Fin n) :
    P.rowWeight r ∈
      Set.Icc (P.topRow ⟨n - 1, by have := r.isLt; omega⟩)
        (P.topRow ⟨0, by have := r.isLt; omega⟩) :=
  ⟨(P.entry_mem_Icc (Nat.lt_succ_self r.val) r.isLt).1.trans (P.entry_diag_le_rowWeight r),
    (P.rowWeight_le_entry_zero r).trans (P.entry_mem_Icc (Nat.succ_pos r.val) r.isLt).2⟩

/-- Nonnegative (polynomial) patterns have nonnegative weights. -/
theorem rowWeight_nonneg {P : GTPattern n} (hP : 0 ≤ P) (r : Fin n) : 0 ≤ P.rowWeight r :=
  (zero_le_iff_topRow.mp hP ⟨n - 1, by have := r.isLt; omega⟩).trans (P.rowWeight_mem_Icc r).1

/-! ### The highest-weight pattern -/

/-- The **highest-weight pattern** of a dominant weight `μ`: every row is an initial segment of
`μ`, that is `highest μ i j = μ i` for `i < j ≤ n`. Its top row and its weight are both `μ`, and it
is the only pattern with this property (`TauCeti.GTPattern.eq_highest_iff`). -/
def highest (μ : DominantWeight n) : GTPattern n where
  entry i j := if h : i < j ∧ j ≤ n then μ.val ⟨i, by omega⟩ else 0
  zeros' h := dite_eq_right (by omega)
  interlacing' {i _} hij hj := by
    rw [dite_eq_left ⟨hij, hj.le⟩, dite_eq_left ⟨by omega, hj⟩, dite_eq_left ⟨by omega, hj⟩]
    exact ⟨le_rfl, μ.antitone (Fin.mk_le_mk.mpr (Nat.le_succ i))⟩

theorem highest_apply (μ : DominantWeight n) (i j : ℕ) :
    highest μ i j = if h : i < j ∧ j ≤ n then μ.val ⟨i, by omega⟩ else 0 :=
  (rfl)

@[simp] theorem highest_apply_of_lt_of_le (μ : DominantWeight n) {i j : ℕ} (hij : i < j)
    (hj : j ≤ n) : highest μ i j = μ.val ⟨i, by omega⟩ :=
  dite_eq_left ⟨hij, hj⟩

@[simp] theorem topRow_highest (μ : DominantWeight n) : (highest μ).topRow = μ.val := by
  funext i
  rw [topRow_apply, highest_apply_of_lt_of_le μ i.isLt le_rfl]

/-- Row `j ≤ n` of the highest-weight pattern of `μ` sums to `μ₁ + ⋯ + μⱼ`. -/
@[simp] theorem rowSum_highest (μ : DominantWeight n) {j : ℕ} (hj : j ≤ n) :
    (highest μ).rowSum j = TauCeti.prefixSum j μ.val := by
  rw [← topRow_highest μ, prefixSum_topRow, rowSum_def]
  exact Finset.sum_congr rfl fun k hk => by
    have := Finset.mem_range.mp hk
    rw [highest_apply_of_lt_of_le μ this hj, highest_apply_of_lt_of_le μ (by omega) le_rfl]

@[simp] theorem rowWeight_highest (μ : DominantWeight n) : (highest μ).rowWeight = μ.val := by
  funext r
  rw [rowWeight_eq_rowSum_sub, rowSum_highest μ r.isLt, rowSum_highest μ r.isLt.le,
    TauCeti.prefixSum_succ r.isLt, add_sub_cancel_left]

/-- **A pattern whose weight is its top row is the highest-weight pattern**: `P` is the
highest-weight pattern of `μ` exactly when its top row and its weight are both `μ`. -/
theorem eq_highest_iff {P : GTPattern n} {μ : DominantWeight n} :
    P = highest μ ↔ P.topRow = μ.val ∧ P.rowWeight = μ.val := by
  -- Each row sum is the matching prefix sum of the top row, while each entry is at most the
  -- top-row entry above it, so every row is an initial segment of the top row.
  refine ⟨fun h => h ▸ ⟨topRow_highest μ, rowWeight_highest μ⟩, fun ⟨htop, hw⟩ => ?_⟩
  have hrow {j : ℕ} (hj : j ≤ n) : ∀ k ∈ Finset.range j, P k j = P k n :=
    (Finset.sum_eq_sum_iff_of_le fun k hk =>
      P.entry_le_entry_of_le (Finset.mem_range.mp hk) hj le_rfl).mp (by
        rw [← P.rowSum_def, ← P.prefixSum_rowWeight hj, hw, ← htop, P.prefixSum_topRow])
  ext i j
  by_cases h : i < j ∧ j ≤ n
  · rw [highest_apply_of_lt_of_le μ h.1 h.2, hrow h.2 i (Finset.mem_range.mpr h.1), ← htop,
      topRow_apply]
  · rw [P.entry_eq_zero (by omega), highest_apply, dite_eq_right h]

/-! ### Branching recursion and low-rank weight fibres -/

/-- A pattern `P` with `n + 1` rows has torus weight `w` if and only if its truncation has torus
weight `Fin.init w` and the degree increment between its top two rows equals `w (Fin.last n)`. -/
theorem rowWeight_eq_iff_truncate (P : GTPattern (n + 1)) (w : Fin (n + 1) → ℤ) :
    P.rowWeight = w ↔
      P.truncate.rowWeight = Fin.init w ∧
        (∑ i, P.topRow i) - (∑ i, P.truncate.topRow i) = w (Fin.last n) := by
  rw [funext_iff, Fin.forall_fin_succ', funext_iff, P.rowWeight_last]
  refine and_congr_left fun _ => forall_congr' fun r => ?_
  rw [← P.rowWeight_truncate r, Fin.init_def]

/-- **Weight-refined branching equivalence**: patterns with `n + 1` rows, top row `l`, and torus
weight `w` correspond to interlacing rows `m` paired with `n`-row patterns of top row `m`, torus
weight `Fin.init w`, and degree increment `|l| - |m| = w (Fin.last n)`. -/
def truncateRowWeightSigmaEquiv (l w : Fin (n + 1) → ℤ) :
    {P : GTPattern (n + 1) // P.topRow = l ∧ P.rowWeight = w} ≃
      Σ m : interlacingFinset l,
        {Q : GTPattern n // Q.topRow = m.val ∧ Q.rowWeight = Fin.init w ∧
          (∑ i, l i) - (∑ i, m.val i) = w (Fin.last n)} :=
  let e₁ : {P : GTPattern (n + 1) // P.topRow = l ∧ P.rowWeight = w} ≃
      {P : {P : GTPattern (n + 1) // P.topRow = l} // P.val.rowWeight = w} :=
    (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun P : GTPattern (n + 1) => P.topRow = l) (fun P => P.rowWeight = w)).symm
  let e₂ : {P : {P : GTPattern (n + 1) // P.topRow = l} // P.val.rowWeight = w} ≃
      {x : Σ m : interlacingFinset l, {Q : GTPattern n // Q.topRow = (m : Fin n → ℤ)} //
        x.2.val.rowWeight = Fin.init w ∧ (∑ i, l i) - (∑ i, x.1.val i) = w (Fin.last n)} :=
    Equiv.subtypeEquiv (truncateSigmaEquiv l) fun P => by
      rw [P.val.rowWeight_eq_iff_truncate w, P.property, truncateSigmaEquiv_apply_snd_coe,
        truncateSigmaEquiv_apply_fst_coe]
  let e₃ : {x : Σ m : interlacingFinset l, {Q : GTPattern n // Q.topRow = (m : Fin n → ℤ)} //
        x.2.val.rowWeight = Fin.init w ∧ (∑ i, l i) - (∑ i, x.1.val i) = w (Fin.last n)} ≃
      Σ m : interlacingFinset l,
        {Q : GTPattern n // Q.topRow = m.val ∧ Q.rowWeight = Fin.init w ∧
          (∑ i, l i) - (∑ i, m.val i) = w (Fin.last n)} :=
    { toFun x := ⟨x.val.1, ⟨x.val.2.val, x.val.2.property, x.property.1, x.property.2⟩⟩
      invFun y := ⟨⟨y.1, ⟨y.2.val, y.2.property.1⟩⟩, y.2.property.2.1, y.2.property.2.2⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  e₁.trans (e₂.trans e₃)

@[simp] theorem truncateRowWeightSigmaEquiv_apply_fst_coe (l w : Fin (n + 1) → ℤ)
    (P : {P : GTPattern (n + 1) // P.topRow = l ∧ P.rowWeight = w}) :
    ((truncateRowWeightSigmaEquiv l w P).1 : Fin n → ℤ) = P.val.truncate.topRow := by
  simp [truncateRowWeightSigmaEquiv]

@[simp] theorem truncateRowWeightSigmaEquiv_apply_snd_coe (l w : Fin (n + 1) → ℤ)
    (P : {P : GTPattern (n + 1) // P.topRow = l ∧ P.rowWeight = w}) :
    (truncateRowWeightSigmaEquiv l w P).2.val = P.val.truncate := by
  simp [truncateRowWeightSigmaEquiv, Equiv.coe_subtypeEquiv_eq_map, Subtype.map_def]

@[simp] theorem truncateRowWeightSigmaEquiv_symm_apply_coe (l w : Fin (n + 1) → ℤ)
    (x : Σ m : interlacingFinset l,
      {Q : GTPattern n // Q.topRow = m.val ∧ Q.rowWeight = Fin.init w ∧
        (∑ i, l i) - (∑ i, m.val i) = w (Fin.last n)}) :
    ((truncateRowWeightSigmaEquiv l w).symm x).val =
      x.2.val.extend l (by rw [x.2.property.1]; exact mem_interlacingFinset.mp x.1.property) := by
  simp [truncateRowWeightSigmaEquiv]

/-- **Branching recursion for weight-fibre counts.** A rank-`(n + 1)` Gelfand–Tsetlin pattern of
top row `l` has weight `w` if and only if `∑ r, w r = ∑ i, l i` and its truncation has weight
`Fin.init w`, so weight-fibre cardinalities sum over `TauCeti.interlacingFinset l`. -/
theorem card_topRow_rowWeight_succ (l w : Fin (n + 1) → ℤ) :
    Nat.card {P : GTPattern (n + 1) // P.topRow = l ∧ P.rowWeight = w} =
      if ∑ r, w r = ∑ i, l i then
        ∑ m ∈ interlacingFinset l,
          Nat.card {Q : GTPattern n // Q.topRow = m ∧ Q.rowWeight = Fin.init w}
      else 0 := by
  split_ifs with hsum
  · have e₂ := Equiv.subtypeEquiv (truncateSigmaEquiv l)
      (p := fun P => P.val.rowWeight = w) (q := fun x => x.2.val.rowWeight = Fin.init w) fun P => by
        rw [truncateSigmaEquiv_apply_snd_coe]
        refine ⟨fun hp => funext fun r => by rw [rowWeight_truncate, hp, Fin.init_def],
          fun hq => funext <| Fin.lastCases ?_ fun j => by
            rw [← rowWeight_truncate, hq, Fin.init_def]⟩
        have hPsum := P.val.sum_rowWeight
        rw [P.property, ← hsum, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc] at hPsum
        have hinit : (∑ j : Fin n, P.val.rowWeight j.castSucc) = ∑ j : Fin n, w j.castSucc :=
          Finset.sum_congr rfl fun j _ => by rw [← rowWeight_truncate, hq, Fin.init_def]
        linarith
    have e₃ : {x : Σ m : interlacingFinset l, {Q : GTPattern n // Q.topRow = (m : Fin n → ℤ)} //
          x.2.val.rowWeight = Fin.init w} ≃
        Σ m : interlacingFinset l,
          {Q : GTPattern n // Q.topRow = (m : Fin n → ℤ) ∧ Q.rowWeight = Fin.init w} :=
      { toFun x := ⟨x.val.1, ⟨x.val.2.val, x.val.2.property, x.property⟩⟩, invFun y := ⟨⟨y.1,
          ⟨y.2.val, y.2.property.1⟩⟩, y.2.property.2⟩,
        left_inv _ := rfl, right_inv _ := rfl }
    rw [Nat.card_congr <| (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm.trans (e₂.trans e₃),
      Nat.card_sigma]
    exact Finset.sum_attach (interlacingFinset l) fun m =>
      Nat.card {Q : GTPattern n // Q.topRow = m ∧ Q.rowWeight = Fin.init w}
  · exact Nat.card_eq_zero.mpr (Or.inl ⟨fun ⟨P, hPt, hPw⟩ =>
      hsum (by rw [← hPw, ← hPt, P.sum_rowWeight])⟩)

/-- At rank `0`, the unique empty pattern has empty top row and empty weight. -/
instance uniqueTopRowRowWeightZero (l w : Fin 0 → ℤ) :
    Unique {P : GTPattern 0 // P.topRow = l ∧ P.rowWeight = w} where
  default := ⟨default, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  uniq _ := Subtype.ext (Subsingleton.elim _ _)

/-- Every rank-`0` weight fibre consists of the single empty pattern. -/
theorem card_topRow_rowWeight_zero (l w : Fin 0 → ℤ) :
    Nat.card {P : GTPattern 0 // P.topRow = l ∧ P.rowWeight = w} = 1 :=
  Nat.card_unique

/-- A rank-`1` weight fibre is a single pattern when the weight equals the top row, and empty
otherwise. -/
theorem card_topRow_rowWeight_one (l w : Fin 1 → ℤ) :
    Nat.card {P : GTPattern 1 // P.topRow = l ∧ P.rowWeight = w} =
      if l 0 = w 0 then 1 else 0 := by
  by_cases h : l 0 = w 0
  · have hlw : l = w := funext fun i => by rw [Subsingleton.elim i 0]; exact h
    subst hlw
    rw [ite_eq_left rfl]
    exact (Nat.card_congr (Equiv.subtypeEquivRight fun P => by
      rw [rowWeight_eq_topRow, and_self])).trans (card_topRow_one_eq_one l)
  · rw [ite_eq_right h]
    refine Nat.card_eq_zero.mpr (Or.inl ⟨fun ⟨P, htop, hw⟩ => h ?_⟩)
    have h0 := P.rowWeight_eq_topRow
    rw [hw, htop] at h0
    exact congrFun h0.symm 0

/-- Two rank-`2` patterns with the same top row and weight are equal. -/
theorem eq_of_topRow_eq_of_rowWeight_eq_two {P Q : GTPattern 2} (ht : P.topRow = Q.topRow)
    (hw : P.rowWeight = Q.rowWeight) : P = Q := by
  ext i j; by_cases hij : i < j ∧ j ≤ 2
  · rcases (by omega : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2)) with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · linarith [P.rowWeight_apply_zero, Q.rowWeight_apply_zero, congrFun hw 0]
    · simpa [topRow_apply] using congrFun ht 0
    · simpa [topRow_apply] using congrFun ht 1
  · rw [P.entry_eq_zero (by omega), Q.entry_eq_zero (by omega)]

/-- Every `GL 2` weight space is multiplicity-free: patterns with fixed top row and weight form a
subsingleton. -/
instance subsingleton_topRow_rowWeight_two (l w : Fin 2 → ℤ) :
    Subsingleton {P : GTPattern 2 // P.topRow = l ∧ P.rowWeight = w} :=
  ⟨fun P Q => Subtype.ext
    (eq_of_topRow_eq_of_rowWeight_eq_two (P.property.1.trans Q.property.1.symm)
    (P.property.2.trans Q.property.2.symm))⟩

/-- Cardinality of a rank-`2` Gelfand–Tsetlin weight fibre over an integer sequence `l`. -/
theorem card_topRow_rowWeight_two (l w : Fin 2 → ℤ) :
    Nat.card {P : GTPattern 2 // P.topRow = l ∧ P.rowWeight = w} =
      if w 0 + w 1 = l 0 + l 1 ∧ l 1 ≤ w 0 ∧ w 0 ≤ l 0 then 1 else 0 := by
  split_ifs with hcond
  · obtain ⟨hsum, hlo, hhi⟩ := hcond
    let Q₁ : GTPattern 1 := equivOne.symm ![w 0]
    have hQ₁ : Q₁.topRow = ![w 0] := (equivOne_apply Q₁).symm.trans (equivOne.apply_symm_apply _)
    have hint : Interlaces l Q₁.topRow :=
      interlaces_iff.mpr fun i => by rw [Subsingleton.elim i 0, hQ₁]; exact ⟨hhi, hlo⟩
    let P : GTPattern 2 := Q₁.extend l hint
    have hPtop : P.topRow = l := topRow_extend Q₁ l hint
    have hPw0 : P.rowWeight 0 = w 0 := by
      have h0 : P.rowWeight 0 = Q₁.rowWeight 0 := rowWeight_extend_castSucc Q₁ l hint 0
      rw [h0, Q₁.rowWeight_eq_topRow, hQ₁, Matrix.cons_val_zero]
    have hPw : P.rowWeight = w := by
      have hPw1 : P.rowWeight 1 = w 1 := by
        have hs := P.sum_rowWeight; simp only [Fin.sum_univ_two, hPtop, hPw0] at hs; omega
      ext r; fin_cases r; exacts [hPw0, hPw1]
    have : Unique {Q : GTPattern 2 // Q.topRow = l ∧ Q.rowWeight = w} :=
      uniqueOfSubsingleton ⟨P, hPtop, hPw⟩
    exact Nat.card_unique
  · refine Nat.card_eq_zero.mpr (Or.inl ⟨fun ⟨P, hPt, hPw⟩ => hcond ?_⟩)
    have hs := P.sum_rowWeight; simp only [hPw, hPt, Fin.sum_univ_two] at hs
    have hmem := P.rowWeight_mem_Icc 0; rw [hPw, hPt] at hmem
    exact ⟨hs, hmem.1, hmem.2⟩

/-- A rank-`2` pattern with top row `l` and weight `w` exists if and only if
`w 0 + w 1 = l 0 + l 1` and `l 1 ≤ w 0 ≤ l 0`. -/
theorem nonempty_topRow_rowWeight_two_iff (l w : Fin 2 → ℤ) :
    Nonempty {P : GTPattern 2 // P.topRow = l ∧ P.rowWeight = w} ↔
      w 0 + w 1 = l 0 + l 1 ∧ l 1 ≤ w 0 ∧ w 0 ≤ l 0 := by
  refine (and_iff_left (inferInstance :
    Finite {P : GTPattern 2 // P.topRow = l ∧ P.rowWeight = w})).symm.trans ?_
  rw [← Nat.card_pos_iff, card_topRow_rowWeight_two]
  split_ifs with h <;> simp [h]

/-- Rank-`2` check: the weight-`(1, 1)` Gelfand–Tsetlin fibre over `(2, 0)` has cardinality `1`. -/
theorem card_topRow_rowWeight_two_two_zero_one_one :
    Nat.card {P : GTPattern 2 // P.topRow = ![2, 0] ∧ P.rowWeight = ![1, 1]} = 1 := by
  rw [card_topRow_rowWeight_two]; decide

/-- Explicit `GL 3` weight-fibre cardinality formula obtained by unwinding
`card_topRow_rowWeight_succ` and `card_topRow_rowWeight_two` over the interlacing middle-row entries
`a ∈ [l 1, l 0]` and `b ∈ [l 2, l 1]`. -/
theorem card_topRow_rowWeight_three (l w : Fin 3 → ℤ) :
    Nat.card {P : GTPattern 3 // P.topRow = l ∧ P.rowWeight = w} =
      if w 0 + w 1 + w 2 = l 0 + l 1 + l 2 then
        ∑ a ∈ Finset.Icc (l 1) (l 0), ∑ b ∈ Finset.Icc (l 2) (l 1),
          if w 0 + w 1 = a + b ∧ b ≤ w 0 ∧ w 0 ≤ a then 1 else 0
      else 0 := by
  rw [card_topRow_rowWeight_succ, Fin.sum_univ_three, Fin.sum_univ_three]
  split_ifs with hsum
  · rw [sum_interlacingFinset_three]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [card_topRow_rowWeight_two]; simp [Fin.init_def]
  · rfl

/-- Rank-`3` check: the weight-`0` Gelfand–Tsetlin fibre over the `SL 3` adjoint weight `(1, 0, -1)`
has cardinality `2` (the `2`-dimensional zero weight space of `𝔰𝔩₃`). -/
theorem card_three_adjoint_rowWeight_zero :
    Nat.card {P : GTPattern 3 // P.topRow = ![1, 0, -1] ∧ P.rowWeight = 0} = 2 := by
  rw [card_topRow_rowWeight_three]; decide

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
      (T.toGTPattern n) i j := by rw [toGTPattern_apply, patternEntry_def, ite_eq_right hnj]
  simp_rw [hcell]
  exact Finset.sum_subset (Finset.range_mono (le_max_left j (μ.colLen 0))) fun i _ hi =>
    (T.toGTPattern n).entry_eq_zero_of_le (Nat.not_lt.mp (Finset.mem_range.not.mp hi))

/-- The weight of the Gelfand–Tsetlin pattern read off a semistandard Young tableau `T` agrees on
`Fin n` with `T.content`. -/
@[simp] theorem rowWeight_toGTPattern (T : SemistandardYoungTableau μ) (n : ℕ) :
    (T.toGTPattern n).rowWeight = fun r => (T.content r.val : ℤ) := by
  ext r; rw [TauCeti.GTPattern.rowWeight_eq_rowSum_sub, T.rowSum_toGTPattern n r.isLt,
    T.rowSum_toGTPattern n r.isLt.le, Finset.sum_range_succ, add_sub_cancel_left]

end SemistandardYoungTableau

namespace TauCeti.GTPattern

/-- Under `TauCeti.GTPattern.toTableau`, the content of the semistandard Young tableau attached to
a pattern `P` of shape `μ` equals `P.rowWeight`. -/
@[simp] theorem natCast_content_toTableau {n : ℕ} (P : GTPattern n) {μ : YoungDiagram}
    (hμ : μ.colLen 0 ≤ n) (hP : ∀ i : Fin n, P.topRow i = (μ.rowLen i : ℤ)) (r : Fin n) :
    ((P.toTableau hμ hP).content r.val : ℤ) = P.rowWeight r := by
  have hinv : (P.toTableau hμ hP).toGTPattern n = P := by
    have h := congrArg Subtype.val ((gtPatternEquivSSYT n μ hμ).symm_apply_apply ⟨P, hP⟩)
    rwa [gtPatternEquivSSYT_symm_apply_coe, gtPatternEquivSSYT_apply_coe] at h
  rw [← congrFun (SemistandardYoungTableau.rowWeight_toGTPattern (P.toTableau hμ hP) n) r, hinv]

/-- Under `TauCeti.GTPattern.toTableau`, the `ℕ`-valued content of the semistandard Young tableau
attached to a pattern `P` of shape `μ` equals `(P.rowWeight r).toNat` on `r : Fin n`. -/
theorem content_toTableau {n : ℕ} (P : GTPattern n) {μ : YoungDiagram}
    (hμ : μ.colLen 0 ≤ n) (hP : ∀ i : Fin n, P.topRow i = (μ.rowLen i : ℤ)) (r : Fin n) :
    (P.toTableau hμ hP).content r.val = (P.rowWeight r).toNat := by
  rw [← P.natCast_content_toTableau hμ hP r, Int.toNat_natCast]

/-- For `n ≤ k`, `P.toTableau hμ hP` uses no letter `k`, so `(P.toTableau hμ hP).content k = 0`. -/
@[simp] theorem content_toTableau_eq_zero {n : ℕ} (P : GTPattern n) {μ : YoungDiagram}
    (hμ : μ.colLen 0 ≤ n) (hP : ∀ i : Fin n, P.topRow i = (μ.rowLen i : ℤ)) {k : ℕ}
    (hk : n ≤ k) : (P.toTableau hμ hP).content k = 0 := by
  simpa using BoundedSSYT.content_eq_zero (gtPatternEquivSSYT n μ hμ ⟨P, hP⟩) hk

end TauCeti.GTPattern
