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
# Row sums and torus weights of Gelfand–Tsetlin patterns

Along the chain `GL 1 ⊂ GL 2 ⊂ ⋯ ⊂ GL n`, the `r`-th diagonal factor of the torus of `GL n` is the
quotient of the determinant of `GL (r + 1)` by the determinant of `GL r`. On a Gelfand–Tsetlin
pattern `P : TauCeti.GTPattern n`, the `r`-th coordinate of its torus weight is therefore the
increment `S_{r + 1} - S_r` between consecutive row sums `S_j = ∑_{i < j} P i j`, with `S_0 = 0`.

This file defines `TauCeti.GTPattern.rowSum` and `TauCeti.GTPattern.rowWeight` for arbitrary
signed (rational) Gelfand–Tsetlin patterns and develops their algebraic, order-theoretic, and
tableau properties:

* **Telescoping and additivity:** leading partial sums `TauCeti.prefixSum j P.rowWeight` recover
  `P.rowSum j` (`TauCeti.GTPattern.prefixSum_rowWeight`), so `∑ r, P.rowWeight r = ∑ i, P.topRow i`
  (`TauCeti.GTPattern.sum_rowWeight`), and `rowWeight` is an additive monoid homomorphism
  (`TauCeti.GTPattern.rowWeightAddMonoidHom`) compatible with determinant shifts, truncation, and
  row extension.
* **Two-sided entry bounds and dominance:** the two interlacing inequalities squeeze each weight
  coordinate between the extremal entries of row `r + 1`,
  `P r (r + 1) ≤ P.rowWeight r ≤ P 0 (r + 1)`
  (`TauCeti.GTPattern.entry_diag_le_rowWeight`, `TauCeti.GTPattern.rowWeight_le_entry_zero`), while
  monotonicity along columns implies that `P.topRow` dominates `P.rowWeight` in the leading
  partial-sum order (`TauCeti.GTPattern.dominates_rowWeight_topRow`).
* **Tableau content dictionary:** under `TauCeti.gtPatternEquivSSYT`, the row weight of a polynomial
  pattern coincides with the entry multiplicity `SemistandardYoungTableau.content` of its
  semistandard Young tableau (`SemistandardYoungTableau.rowWeight_toGTPattern`,
  `TauCeti.GTPattern.content_toTableau`).
* **Weight-space branching and low-rank weight fibres:** sorting by the exposed second row refines
  `TauCeti.GTPattern.card_topRow_succ` to a recursion
  `TauCeti.GTPattern.card_topRow_and_rowWeight_succ` for weight multiplicities along
  `GL (n + 1) ↓ GL n`, giving closed forms in ranks `0`, `1`, `2`, and `3`
  (`TauCeti.GTPattern.card_topRow_and_rowWeight_two`,
  `TauCeti.GTPattern.nonempty_topRow_and_rowWeight_two_iff`,
  `TauCeti.GTPattern.card_topRow_and_rowWeight_three`).

## Main definitions

* `TauCeti.GTPattern.rowSum`: the sum `∑ i ∈ Finset.range j, P i j` of row `j` of a pattern.
* `TauCeti.GTPattern.rowWeight`: the torus weight `r ↦ P.rowSum (r.val + 1) - P.rowSum r.val`.
* `TauCeti.GTPattern.rowWeightAddMonoidHom`: `rowWeight` bundled as an `AddMonoidHom`.
* `TauCeti.GTPattern.truncateWeightSigmaEquiv`: weight-refined branching equivalence along
  `GL (n + 1) ↓ GL n`.

## Main results

* `TauCeti.GTPattern.prefixSum_rowWeight`, `TauCeti.GTPattern.sum_rowWeight`.
* `TauCeti.GTPattern.entry_diag_le_rowWeight`, `TauCeti.GTPattern.rowWeight_le_entry_zero`,
  `TauCeti.GTPattern.rowWeight_mem_Icc`.
* `TauCeti.GTPattern.dominates_rowWeight_topRow`,
  `TauCeti.GTPattern.topWeight_dominates_of_rowWeight_eq`.
* `TauCeti.GTPattern.card_topRow_and_rowWeight_succ`,
  `TauCeti.GTPattern.nonempty_topRow_and_rowWeight_two_iff`,
  `TauCeti.GTPattern.card_topRow_and_rowWeight_two`,
  `TauCeti.GTPattern.card_topRow_and_rowWeight_three`.
* `SemistandardYoungTableau.rowWeight_toGTPattern`, `TauCeti.GTPattern.content_toTableau`.

## References

* I. M. Gelfand and M. L. Tsetlin, *Finite-dimensional representations of the group of unimodular
  matrices*, Dokl. Akad. Nauk SSSR **71** (1950), 825–828.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), §15.3.
-/

public section

open Finset

namespace TauCeti

namespace GTPattern

variable {n : ℕ}

/-! ### Row sums and successive row-sum differences -/

/-- The sum `S_j = ∑_{i < j} P i j` of the `j` informative entries in row `j` of a
Gelfand–Tsetlin pattern, with `S_0 = 0` and `S_j = 0` for `n < j`. -/
def rowSum (P : GTPattern n) (j : ℕ) : ℤ :=
  ∑ i ∈ range j, P i j

/-- Defining formula for `TauCeti.GTPattern.rowSum`. -/
theorem rowSum_def (P : GTPattern n) (j : ℕ) :
    P.rowSum j = ∑ i ∈ range j, P i j :=
  (rfl)

@[simp]
theorem rowSum_zero (P : GTPattern n) : P.rowSum 0 = 0 := by
  simp [rowSum_def]

/-- Rows beyond `n` carry only zero entries, so their row sum vanishes. -/
@[simp]
theorem rowSum_eq_zero_of_lt (P : GTPattern n) {j : ℕ} (hj : n < j) : P.rowSum j = 0 := by
  rw [rowSum_def]
  exact sum_eq_zero fun i _ => P.entry_eq_zero_of_lt hj

/-- Summing row `j` past index `j` adds only off-triangle zeros, so any `range i` with `j ≤ i`
computes `P.rowSum j`. -/
theorem sum_range_entry_eq_rowSum (P : GTPattern n) {i j : ℕ} (hij : j ≤ i) :
    ∑ k ∈ range i, P k j = P.rowSum j := by
  rw [rowSum_def]
  exact (sum_subset (range_mono hij) fun k _ hkj =>
    P.entry_eq_zero_of_le (not_lt.mp (mt mem_range.mpr hkj))).symm

/-- The sum of row `n` is the coordinate sum of `P.topRow`. -/
theorem rowSum_top (P : GTPattern n) : P.rowSum n = ∑ i : Fin n, P.topRow i := by
  simp only [rowSum_def, topRow_apply]
  exact (Fin.sum_univ_eq_sum_range (fun i => P i n) n).symm

/-- The **torus weight** (or **row weight**) of a Gelfand–Tsetlin pattern: its `r`-th coordinate is
the row-sum increment `S_{r + 1} - S_r`. -/
def rowWeight (P : GTPattern n) : Fin n → ℤ :=
  fun r => P.rowSum (r.val + 1) - P.rowSum r.val

/-- Defining formula for `TauCeti.GTPattern.rowWeight`. -/
theorem rowWeight_apply (P : GTPattern n) (r : Fin n) :
    P.rowWeight r = P.rowSum (r.val + 1) - P.rowSum r.val :=
  (rfl)

/-- Leading partial sums of `P.rowWeight` telescope to `P.rowSum`. -/
@[simp]
theorem prefixSum_rowWeight (P : GTPattern n) {j : ℕ} (hj : j ≤ n) :
    prefixSum j P.rowWeight = P.rowSum j := by
  induction j with
  | zero => simp
  | succ m ih =>
    have hm : m < n := Nat.lt_of_succ_le hj
    rw [prefixSum_succ hm, ih hm.le, rowWeight_apply]
    abel

/-- The coordinates of `P.rowWeight` sum to the total degree of `P.topRow`. -/
@[simp]
theorem sum_rowWeight (P : GTPattern n) :
    ∑ r : Fin n, P.rowWeight r = ∑ i : Fin n, P.topRow i := by
  rw [← prefixSum_of_le le_rfl P.rowWeight, prefixSum_rowWeight P le_rfl, P.rowSum_top]

/-! ### Additivity, constant patterns, shifts, and truncation -/

@[simp]
theorem rowSum_zero_pattern (j : ℕ) : (0 : GTPattern n).rowSum j = 0 := by
  simp [rowSum_def, zero_apply]

@[simp]
theorem rowSum_add (P Q : GTPattern n) (j : ℕ) :
    (P + Q).rowSum j = P.rowSum j + Q.rowSum j := by
  simp [rowSum_def, add_apply, sum_add_distrib]

@[simp]
theorem rowSum_nsmul (k : ℕ) (P : GTPattern n) (j : ℕ) :
    (k • P).rowSum j = k • P.rowSum j := by
  simp [rowSum_def, nsmul_apply, mul_sum]

@[simp]
theorem rowWeight_zero : (0 : GTPattern n).rowWeight = 0 := by
  ext r
  simp [rowWeight_apply]

@[simp]
theorem rowWeight_add (P Q : GTPattern n) :
    (P + Q).rowWeight = P.rowWeight + Q.rowWeight := by
  ext r
  simp only [rowWeight_apply, Pi.add_apply, rowSum_add]
  abel

@[simp]
theorem rowWeight_nsmul (k : ℕ) (P : GTPattern n) :
    (k • P).rowWeight = k • P.rowWeight := by
  ext r
  simp only [rowWeight_apply, Pi.smul_apply, rowSum_nsmul, nsmul_eq_mul]
  ring

/-- `TauCeti.GTPattern.rowWeight` as an additive monoid homomorphism. -/
def rowWeightAddMonoidHom (n : ℕ) : GTPattern n →+ (Fin n → ℤ) where
  toFun := rowWeight
  map_zero' := rowWeight_zero
  map_add' := rowWeight_add

@[simp]
theorem rowWeightAddMonoidHom_apply (P : GTPattern n) :
    rowWeightAddMonoidHom n P = P.rowWeight :=
  (rfl)

theorem rowSum_const (m : ℤ) {j : ℕ} (hj : j ≤ n) :
    (const n m).rowSum j = (j : ℤ) * m := by
  rw [rowSum_def, sum_congr rfl fun i hi => const_apply_of_lt_of_le m (mem_range.mp hi) hj,
    sum_const, card_range, nsmul_eq_mul]

@[simp]
theorem rowWeight_const (m : ℤ) : (const n m).rowWeight = fun _ => m := by
  ext r
  rw [rowWeight_apply, rowSum_const m (by omega), rowSum_const m r.isLt.le,
    Nat.cast_add, Nat.cast_one]
  ring

theorem rowSum_shift (P : GTPattern n) (m : ℤ) {j : ℕ} (hj : j ≤ n) :
    (P.shift m).rowSum j = P.rowSum j + (j : ℤ) * m := by
  rw [rowSum_def, rowSum_def,
    sum_congr rfl fun i hi => P.shift_apply_of_lt_of_le m (mem_range.mp hi) hj,
    sum_add_distrib, sum_const, card_range, nsmul_eq_mul]

/-- Shifting every informative entry of a pattern by `m` adds `m` to every coordinate of its torus
weight. -/
@[simp]
theorem rowWeight_shift (P : GTPattern n) (m : ℤ) :
    (P.shift m).rowWeight = fun r => P.rowWeight r + m := by
  ext r
  rw [rowWeight_apply, rowWeight_apply, P.rowSum_shift m (by omega),
    P.rowSum_shift m r.isLt.le, Nat.cast_add, Nat.cast_one]
  ring

theorem rowSum_truncate (P : GTPattern (n + 1)) {j : ℕ} (hj : j ≤ n) :
    P.truncate.rowSum j = P.rowSum j := by
  rw [rowSum_def, rowSum_def]
  exact sum_congr rfl fun i _ => by simp [hj]

/-- Deleting the top row restricts `rowWeight` to the first `n` coordinates. -/
@[simp]
theorem rowWeight_truncate (P : GTPattern (n + 1)) (r : Fin n) :
    P.truncate.rowWeight r = P.rowWeight r.castSucc := by
  rw [rowWeight_apply, rowWeight_apply, Fin.val_castSucc,
    P.rowSum_truncate (Nat.succ_le_of_lt r.isLt), P.rowSum_truncate r.isLt.le]

/-- The last weight coordinate of a pattern with `n + 1` rows is the difference between the sums of
its top two rows. -/
theorem rowWeight_last (P : GTPattern (n + 1)) :
    P.rowWeight (Fin.last n) = (∑ i, P.topRow i) - ∑ i, P.truncate.topRow i := by
  rw [rowWeight_apply, Fin.val_last, P.rowSum_top, ← P.rowSum_truncate le_rfl,
    P.truncate.rowSum_top]

@[simp]
theorem rowWeight_extend_castSucc (Q : GTPattern n) (l : Fin (n + 1) → ℤ)
    (h : Interlaces l Q.topRow) (r : Fin n) :
    (Q.extend l h).rowWeight r.castSucc = Q.rowWeight r := by
  rw [← rowWeight_truncate, truncate_extend]

@[simp]
theorem rowWeight_extend_last (Q : GTPattern n) (l : Fin (n + 1) → ℤ)
    (h : Interlaces l Q.topRow) :
    (Q.extend l h).rowWeight (Fin.last n) = (∑ i, l i) - ∑ i, Q.topRow i := by
  rw [rowWeight_last, topRow_extend, truncate_extend]

/-! ### Interlacing bounds and dominance of the top row over `rowWeight` -/

/-- Because `P k r ≤ P k (r + 1)` for `k < r < n`, the `r`-th weight coordinate is at least the
last informative entry `P r (r + 1)` of row `r + 1`. -/
theorem entry_diag_le_rowWeight (P : GTPattern n) (r : Fin n) :
    P r.val (r.val + 1) ≤ P.rowWeight r := by
  rw [rowWeight_apply, rowSum_def, rowSum_def, sum_range_succ, add_sub_right_comm,
    ← sum_sub_distrib]
  have hnn : 0 ≤ ∑ k ∈ range r.val, (P k (r.val + 1) - P k r.val) :=
    sum_nonneg fun k hk => sub_nonneg.mpr (P.entry_le_entry_succ_row (mem_range.mp hk) r.isLt)
  linarith

/-- Because `P (k + 1) (r + 1) ≤ P k r` for `r < n`, the `r`-th weight coordinate is at most the
first entry `P 0 (r + 1)` of row `r + 1`. -/
theorem rowWeight_le_entry_zero (P : GTPattern n) (r : Fin n) :
    P.rowWeight r ≤ P 0 (r.val + 1) := by
  rw [rowWeight_apply, rowSum_def, rowSum_def, sum_range_succ', add_sub_right_comm,
    ← sum_sub_distrib]
  have hnp : ∑ k ∈ range r.val, (P (k + 1) (r.val + 1) - P k r.val) ≤ 0 :=
    sum_nonpos fun k _ => sub_nonpos.mpr (P.entry_succ_succ_le_entry r.isLt)
  linarith

/-- Every weight coordinate of a pattern lies between the last and first entries of its top row. -/
theorem rowWeight_mem_Icc (P : GTPattern n) (r : Fin n) :
    P.rowWeight r ∈ Set.Icc (P.topRow ⟨n - 1, Nat.sub_lt r.pos one_pos⟩) (P.topRow ⟨0, r.pos⟩) :=
  ⟨(P.entry_mem_Icc (Nat.lt_succ_self r.val) (Nat.succ_le_of_lt r.isLt)).1.trans
      (P.entry_diag_le_rowWeight r),
    (P.rowWeight_le_entry_zero r).trans
      (P.entry_mem_Icc (Nat.succ_pos r.val) (Nat.succ_le_of_lt r.isLt)).2⟩

/-- A nonnegative pattern has nonnegative torus weight coordinates. -/
theorem rowWeight_nonneg {P : GTPattern n} (hP : 0 ≤ P) (r : Fin n) : 0 ≤ P.rowWeight r :=
  (zero_le_iff.mp hP r.val (r.val + 1)).trans (P.entry_diag_le_rowWeight r)

/-- **Dominance bound for Gelfand–Tsetlin weights**: for every pattern `P`, `P.rowWeight` and
`P.topRow` have the same total sum and every leading partial sum of `P.rowWeight` is at most the
corresponding leading partial sum of `P.topRow`. -/
theorem dominates_rowWeight_topRow (P : GTPattern n) :
    TauCeti.Dominates P.rowWeight P.topRow := by
  rw [TauCeti.dominates_def]
  refine ⟨P.sum_rowWeight.symm, fun k hk => ?_⟩
  rw [← prefixSum_eq_sum_castLE hk, P.prefixSum_rowWeight hk, rowSum_def]
  have htop : ∑ j : Fin k, P.topRow (Fin.castLE hk j) = ∑ i ∈ range k, P i n := by
    simpa [topRow_apply] using Fin.sum_univ_eq_sum_range (fun i => P i n) k
  rw [htop]
  exact sum_le_sum fun i hi => P.entry_le_entry_of_le (mem_range.mp hi) hk le_rfl

/-- When `P.rowWeight` is dominant, `P.topWeight` dominates it in `DominantWeight.Dominates`. -/
theorem topWeight_dominates_of_rowWeight_eq (P : GTPattern n) {w : DominantWeight n}
    (hw : P.rowWeight = w.1) : P.topWeight.Dominates w := by
  rw [DominantWeight.dominates_def, topWeight_coe, ← hw]
  exact P.dominates_rowWeight_topRow

/-- Finitely many patterns share a prescribed top row together with any further predicate. -/
instance finite_topRow_eq_and (l : Fin n → ℤ) (p : GTPattern n → Prop) :
    Finite {P : GTPattern n // P.topRow = l ∧ p P} :=
  Finite.of_injective
    (fun P : {P : GTPattern n // P.topRow = l ∧ p P} =>
      (⟨P.1, P.2.1⟩ : {P : GTPattern n // P.topRow = l}))
    fun _ _ h => Subtype.ext (Subtype.mk.inj h)

/-! ### Weight-space branching along `GL (n + 1) ↓ GL n` and low-rank weight fibres -/

private theorem rowWeight_eq_iff_truncate {P : GTPattern (n + 1)} {l w : Fin (n + 1) → ℤ}
    (hP : P.topRow = l) :
    P.rowWeight = w ↔
      P.truncate.rowWeight = Fin.init w ∧
        (∑ i, l i) - (∑ i, P.truncate.topRow i) = w (Fin.last n) := by
  rw [funext_iff, Fin.forall_fin_succ', funext_iff, P.rowWeight_last, hP]
  refine and_congr_left fun _ => forall_congr' fun r => ?_
  rw [← P.rowWeight_truncate r, Fin.init_def]

/-- **Weight-space branching equivalence**: patterns with `n + 1` rows, top row `l`, and torus
weight `w` correspond to interlacing rows `m` paired with `n`-row patterns of top row `m`, torus
weight `Fin.init w`, and degree increment `|l| - |m| = wₙ`. -/
def truncateWeightSigmaEquiv (l w : Fin (n + 1) → ℤ) :
    {P : GTPattern (n + 1) // P.topRow = l ∧ P.rowWeight = w} ≃
      Σ m : interlacingFinset l,
        {Q : GTPattern n // Q.topRow = m.1 ∧ Q.rowWeight = Fin.init w ∧
          (∑ i, l i) - (∑ i, m.1 i) = w (Fin.last n)} :=
  let e₁ : {P : GTPattern (n + 1) // P.topRow = l ∧ P.rowWeight = w} ≃
      {P : {P : GTPattern (n + 1) // P.topRow = l} // P.1.rowWeight = w} :=
    { toFun := fun P => ⟨⟨P.1, P.2.1⟩, P.2.2⟩
      invFun := fun P => ⟨P.1.1, P.1.2, P.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e₂ : {P : {P : GTPattern (n + 1) // P.topRow = l} // P.1.rowWeight = w} ≃
      {Q : {Q : GTPattern n // Interlaces l Q.topRow} //
        Q.1.rowWeight = Fin.init w ∧ (∑ i, l i) - (∑ i, Q.1.topRow i) = w (Fin.last n)} :=
    Equiv.subtypeEquiv (truncateEquiv l) fun P => by
      rw [rowWeight_eq_iff_truncate P.2, truncateEquiv_apply_coe]
  let e₃ : {Q : {Q : GTPattern n // Interlaces l Q.topRow} //
        Q.1.rowWeight = Fin.init w ∧ (∑ i, l i) - (∑ i, Q.1.topRow i) = w (Fin.last n)} ≃
      Σ m : interlacingFinset l,
        {Q : GTPattern n // Q.topRow = m.1 ∧ Q.rowWeight = Fin.init w ∧
          (∑ i, l i) - (∑ i, m.1 i) = w (Fin.last n)} :=
    { toFun := fun Q => ⟨⟨Q.1.1.topRow, mem_interlacingFinset.mpr Q.1.2⟩,
        ⟨Q.1.1, rfl, Q.2.1, Q.2.2⟩⟩
      invFun := fun x => ⟨⟨x.2.1, by rw [x.2.2.1]; exact mem_interlacingFinset.mp x.1.2⟩,
        x.2.2.2.1, by rw [x.2.2.1]; exact x.2.2.2.2⟩
      left_inv := fun _ => rfl
      right_inv := by
        rintro ⟨⟨m, hm⟩, ⟨Q, hQ, hw, hd⟩⟩
        have hm' : Q.topRow = m := hQ
        subst hm'
        rfl }
  e₁.trans (e₂.trans e₃)

@[simp]
theorem truncateWeightSigmaEquiv_apply_fst_coe (l w : Fin (n + 1) → ℤ)
    (P : {P : GTPattern (n + 1) // P.topRow = l ∧ P.rowWeight = w}) :
    ((truncateWeightSigmaEquiv l w P).1 : Fin n → ℤ) = P.1.truncate.topRow :=
  congrArg topRow (truncateEquiv_apply_coe l ⟨P.1, P.2.1⟩)

@[simp]
theorem truncateWeightSigmaEquiv_apply_snd_coe (l w : Fin (n + 1) → ℤ)
    (P : {P : GTPattern (n + 1) // P.topRow = l ∧ P.rowWeight = w}) :
    (truncateWeightSigmaEquiv l w P).2.1 = P.1.truncate :=
  truncateEquiv_apply_coe l ⟨P.1, P.2.1⟩

/-- **Branching recursion for weight multiplicities**: the number of patterns with `n + 1` rows, top
row `l`, and weight `w` sums the rank-`n` counts of weight `Fin.init w` over interlacing rows `m`
with `|l| - |m| = wₙ`. -/
theorem card_topRow_and_rowWeight_succ (l w : Fin (n + 1) → ℤ) :
    Nat.card {P : GTPattern (n + 1) // P.topRow = l ∧ P.rowWeight = w} =
      ∑ m ∈ {m ∈ interlacingFinset l | (∑ i, l i) - (∑ i, m i) = w (Fin.last n)},
        Nat.card {Q : GTPattern n // Q.topRow = m ∧ Q.rowWeight = Fin.init w} := by
  rw [Nat.card_congr (truncateWeightSigmaEquiv l w), Nat.card_sigma]
  refine (Finset.sum_attach (interlacingFinset l) fun m =>
    Nat.card {Q : GTPattern n // Q.topRow = m ∧ Q.rowWeight = Fin.init w ∧
      (∑ i, l i) - (∑ i, m i) = w (Fin.last n)}).trans ?_
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases hm : (∑ i, l i) - (∑ i, m i) = w (Fin.last n)
  · rw [ite_eq_left hm]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun Q =>
      and_congr_right fun _ => and_iff_left hm)
  · rw [ite_eq_right hm]
    exact Nat.card_eq_zero.mpr (Or.inl ⟨fun Q => hm Q.2.2.2⟩)

/-- At rank `0`, the unique empty pattern has empty top row and empty weight. -/
instance uniqueTopRowAndRowWeightZero (l w : Fin 0 → ℤ) :
    Unique {P : GTPattern 0 // P.topRow = l ∧ P.rowWeight = w} where
  default := ⟨default, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  uniq _ := Subtype.ext (Subsingleton.elim _ _)

theorem card_topRow_and_rowWeight_zero (l w : Fin 0 → ℤ) :
    Nat.card {P : GTPattern 0 // P.topRow = l ∧ P.rowWeight = w} = 1 :=
  Nat.card_unique

/-- A one-row pattern's torus weight equals its top row. -/
@[simp]
theorem rowWeight_eq_topRow_one (P : GTPattern 1) : P.rowWeight = P.topRow := by
  ext i
  fin_cases i
  simp [rowWeight_apply, rowSum_def, topRow_apply]

theorem card_topRow_and_rowWeight_one (l w : Fin 1 → ℤ) :
    Nat.card {P : GTPattern 1 // P.topRow = l ∧ P.rowWeight = w} =
      if l 0 = w 0 then 1 else 0 := by
  by_cases h : l 0 = w 0
  · have hlw : l = w := funext fun i => by fin_cases i; exact h
    subst hlw
    rw [ite_eq_left rfl]
    let P₀ : {P : GTPattern 1 // P.topRow = l} := default
    refine Nat.card_eq_one_iff_exists.mpr
      ⟨⟨P₀.1, P₀.2, by rw [rowWeight_eq_topRow_one, P₀.2]⟩, fun Q => Subtype.ext ?_⟩
    exact congrArg (fun X : {P : GTPattern 1 // P.topRow = l} => X.1)
      (Subsingleton.elim ⟨Q.1, Q.2.1⟩ P₀)
  · rw [ite_eq_right h]
    refine Nat.card_eq_zero.mpr (Or.inl ⟨fun ⟨P, htop, hw⟩ => h ?_⟩)
    have h0 := P.rowWeight_eq_topRow_one
    rw [hw, htop] at h0
    exact congrFun h0.symm 0

/-- Every `GL 2` weight space is multiplicity-free (`Subsingleton` on patterns with fixed top row
and torus weight). -/
instance subsingleton_topRow_and_rowWeight_two (l w : Fin 2 → ℤ) :
    Subsingleton {P : GTPattern 2 // P.topRow = l ∧ P.rowWeight = w} := by
  refine ⟨fun P Q => Subtype.ext ?_⟩
  have hP : P.1.truncate.topRow 0 = w 0 := by
    rw [← rowWeight_eq_topRow_one, rowWeight_truncate, P.2.2]; rfl
  have hQ : Q.1.truncate.topRow 0 = w 0 := by
    rw [← rowWeight_eq_topRow_one, rowWeight_truncate, Q.2.2]; rfl
  have hPQ : (⟨P.1, P.2.1⟩ : {X : GTPattern 2 // X.topRow = l}) = ⟨Q.1, Q.2.1⟩ := by
    apply (truncateEquiv l).injective
    apply Subtype.ext
    apply equivOne.injective
    ext i
    fin_cases i
    rw [equivOne_apply, equivOne_apply, truncateEquiv_apply_coe, truncateEquiv_apply_coe]
    exact hP.trans hQ.symm
  exact congrArg (fun X : {X : GTPattern 2 // X.topRow = l} => X.1) hPQ

/-- A `GL 2` pattern with top row `l` and weight `w` exists iff `l 1 ≤ w 0 ≤ l 0` and
`w 0 + w 1 = l 0 + l 1`. -/
theorem nonempty_topRow_and_rowWeight_two_iff (l w : Fin 2 → ℤ) :
    Nonempty {P : GTPattern 2 // P.topRow = l ∧ P.rowWeight = w} ↔
      l 1 ≤ w 0 ∧ w 0 ≤ l 0 ∧ w 0 + w 1 = l 0 + l 1 := by
  refine ⟨fun ⟨⟨P, htop, hw⟩⟩ => ?_, fun ⟨hlo, hhi, hsum⟩ => ?_⟩
  · have htr : P.truncate.topRow 0 = w 0 := by
      rw [← rowWeight_eq_topRow_one, rowWeight_truncate, hw]; rfl
    have hint := htop ▸ P.interlaces_topRow_truncate
    have hdeg := P.sum_rowWeight
    rw [hw, htop, Fin.sum_univ_two, Fin.sum_univ_two] at hdeg
    exact ⟨htr ▸ hint.succ_le 0, htr ▸ hint.le_castSucc 0, hdeg⟩
  · let Q : GTPattern 1 := equivOne.symm (fun _ => w 0)
    have hQtop : Q.topRow = fun _ => w 0 :=
      (equivOne_apply Q).symm.trans (equivOne.apply_symm_apply _)
    have hint : Interlaces l Q.topRow := interlaces_iff.mpr fun i => by
      fin_cases i
      rw [hQtop]
      exact ⟨hhi, hlo⟩
    refine ⟨⟨Q.extend l hint, topRow_extend _ _ _,
      (rowWeight_eq_iff_truncate (topRow_extend _ _ _)).mpr ⟨?_, ?_⟩⟩⟩
    · ext i
      fin_cases i
      rw [truncate_extend, rowWeight_eq_topRow_one, hQtop, Fin.init_def]
      rfl
    · rw [truncate_extend, hQtop, Fin.sum_univ_two l, Fin.sum_univ_one]
      change (l 0 + l 1) - w 0 = w 1
      linarith [hsum]

/-- Closed-form count of `GL 2` patterns with top row `l` and torus weight `w`. -/
theorem card_topRow_and_rowWeight_two (l w : Fin 2 → ℤ) :
    Nat.card {P : GTPattern 2 // P.topRow = l ∧ P.rowWeight = w} =
      if l 1 ≤ w 0 ∧ w 0 ≤ l 0 ∧ w 0 + w 1 = l 0 + l 1 then 1 else 0 := by
  by_cases h : l 1 ≤ w 0 ∧ w 0 ≤ l 0 ∧ w 0 + w 1 = l 0 + l 1
  · rw [ite_eq_left h]
    obtain ⟨P⟩ := (nonempty_topRow_and_rowWeight_two_iff l w).mpr h
    exact Nat.card_eq_one_iff_exists.mpr ⟨P, fun Q => Subsingleton.elim Q P⟩
  · rw [ite_eq_right h]
    exact Nat.card_eq_zero.mpr
      (Or.inl ⟨fun P => h ((nonempty_topRow_and_rowWeight_two_iff l w).mp ⟨P⟩)⟩)

/-- Closed-form count of `GL 3` patterns with top row `l` and torus weight `w` as a double sum over
the interlacing middle row `(a, b) ∈ [l₁, l₀] × [l₂, l₁]`. -/
theorem card_topRow_and_rowWeight_three (l w : Fin 3 → ℤ) :
    Nat.card {P : GTPattern 3 // P.topRow = l ∧ P.rowWeight = w} =
      ∑ a ∈ Finset.Icc (l 1) (l 0), ∑ b ∈ Finset.Icc (l 2) (l 1),
        if b ≤ w 0 ∧ w 0 ≤ a ∧ w 0 + w 1 = a + b ∧ (l 0 + l 1 + l 2) - (a + b) = w 2
          then 1 else 0 := by
  rw [card_topRow_and_rowWeight_succ, Finset.sum_filter, ← Finset.sum_product']
  refine Finset.sum_nbij' (fun m => (m 0, m 1)) (fun p => ![p.1, p.2]) ?_ ?_ ?_ ?_ ?_
  · intro m hm
    rw [mem_interlacingFinset] at hm
    exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨hm.succ_le 0, hm.le_castSucc 0⟩,
        Finset.mem_Icc.mpr ⟨hm.succ_le 1, hm.le_castSucc 1⟩⟩
  · intro p hp
    obtain ⟨hp₀, hp₁⟩ := Finset.mem_product.mp hp
    rw [Finset.mem_Icc] at hp₀ hp₁
    refine mem_interlacingFinset.mpr (interlaces_iff.mpr fun i => ?_)
    fin_cases i
    · exact ⟨hp₀.2, hp₀.1⟩
    · exact ⟨hp₁.2, hp₁.1⟩
  · intro m _
    ext i
    fin_cases i <;> rfl
  · intro _ _
    rfl
  · intro m _
    rw [card_topRow_and_rowWeight_two, Fin.sum_univ_three l, Fin.sum_univ_two m]
    change (if (l 0 + l 1 + l 2) - (m 0 + m 1) = w 2 then
        if m 1 ≤ w 0 ∧ w 0 ≤ m 0 ∧ w 0 + w 1 = m 0 + m 1 then 1 else 0 else 0) = _
    by_cases h₁ : (l 0 + l 1 + l 2) - (m 0 + m 1) = w 2 <;>
      by_cases h₂ : m 1 ≤ w 0 ∧ w 0 ≤ m 0 ∧ w 0 + w 1 = m 0 + m 1 <;>
      simp [h₁, h₂]

/-- In `Sym²(ℂ²)`, the zero-SL₂ weight `(1, 1)` occurs with multiplicity `1`. -/
theorem card_topRow_two_zero_and_rowWeight_one_one :
    Nat.card {P : GTPattern 2 // P.topRow = ![2, 0] ∧ P.rowWeight = ![1, 1]} = 1 := by
  rw [card_topRow_and_rowWeight_two]
  decide

/-- **The zero weight space of the `SL 3` adjoint representation `(1, 0, -1)` has dimension `2`**:
its two Gelfand–Tsetlin patterns have middle rows `(1, -1)` and `(0, 0)` with bottom entry `0`. -/
theorem card_topRow_one_zero_neg_one_and_rowWeight_zero :
    Nat.card {P : GTPattern 3 // P.topRow = ![1, 0, -1] ∧ P.rowWeight = 0} = 2 := by
  rw [card_topRow_and_rowWeight_three]
  decide

end GTPattern

end TauCeti

/-! ### Compatibility with semistandard Young tableau content -/

namespace SemistandardYoungTableau

variable {μ : YoungDiagram}

/-- For `j ≤ n`, row `j` of the Gelfand–Tsetlin pattern of a semistandard Young tableau `T` sums to
the number of cells of `μ` carrying entries below `j`, i.e. `∑ k ∈ range j, T.content k`. -/
theorem rowSum_toGTPattern (T : SemistandardYoungTableau μ) {n j : ℕ} (hj : j ≤ n) :
    (T.toGTPattern n).rowSum j = ∑ k ∈ range j, (T.content k : ℤ) := by
  rw [TauCeti.GTPattern.rowSum_def, ← Nat.cast_sum, sum_content_eq_card_filter]
  have hnj : ¬ n < j := not_lt.mpr hj
  have hsum : ∑ i ∈ range j, (T.toGTPattern n) i j =
      ∑ i ∈ range j, (#{c ∈ range (μ.rowLen i) | T i c < j} : ℤ) :=
    sum_congr rfl fun i _ => by simp [patternEntry_def, hnj]
  rw [hsum, ← Nat.cast_sum]
  refine congrArg Nat.cast ?_
  rw [← card_sigma]
  refine card_bij (fun (ic : Σ _ : ℕ, ℕ) _ => (ic.1, ic.2)) ?_ ?_ ?_
  · intro ic hic
    simp only [mem_sigma, mem_range, mem_filter, YoungDiagram.mem_cells] at hic ⊢
    exact ⟨YoungDiagram.mem_iff_lt_rowLen.mpr hic.2.1, hic.2.2⟩
  · rintro ⟨i₁, c₁⟩ _ ⟨i₂, c₂⟩ _ h
    rcases Prod.mk.inj h with ⟨rfl, rfl⟩
    rfl
  · intro p hp
    simp only [mem_filter, YoungDiagram.mem_cells] at hp
    refine ⟨⟨p.1, p.2⟩, ?_, Prod.eta p⟩
    simp only [mem_sigma, mem_range, mem_filter]
    exact ⟨(le_entry T hp.1).trans_lt hp.2, YoungDiagram.mem_iff_lt_rowLen.mp hp.1, hp.2⟩

/-- The `r`-th torus weight coordinate of `T.toGTPattern n` is the entry multiplicity `T.content r`.
-/
@[simp]
theorem rowWeight_toGTPattern (T : SemistandardYoungTableau μ) (n : ℕ) (r : Fin n) :
    (T.toGTPattern n).rowWeight r = (T.content r.val : ℤ) := by
  rw [TauCeti.GTPattern.rowWeight_apply, T.rowSum_toGTPattern (by omega),
    T.rowSum_toGTPattern r.isLt.le, sum_range_succ, add_sub_cancel_left]

end SemistandardYoungTableau

namespace TauCeti.GTPattern

/-- Under `TauCeti.GTPattern.toTableau`, the content at letter `r < n` equals `P.rowWeight r`. -/
@[simp]
theorem content_toTableau {n : ℕ} {μ : YoungDiagram} (P : GTPattern n) (hμ : μ.colLen 0 ≤ n)
    (hP : ∀ i : Fin n, P.topRow i = (μ.rowLen i : ℤ)) (r : Fin n) :
    ((P.toTableau hμ hP).content r.val : ℤ) = P.rowWeight r := by
  have hinv := congrArg Subtype.val ((gtPatternEquivSSYT n μ hμ).symm_apply_apply ⟨P, hP⟩)
  rw [gtPatternEquivSSYT_symm_apply_coe, gtPatternEquivSSYT_apply_coe] at hinv
  rw [← SemistandardYoungTableau.rowWeight_toGTPattern (P.toTableau hμ hP) n r, hinv]

end TauCeti.GTPattern
