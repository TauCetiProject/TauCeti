/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.BigOperators.Finset.PartialSum
public import TauCeti.RepresentationTheory.ClassicalGroups.GelfandTsetlin.Shift
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Row sums and torus weights of Gelfand–Tsetlin patterns

For a Gelfand–Tsetlin pattern `P : TauCeti.GTPattern n`, the `j`-th **row sum**
`P.rowSum j = ∑_{k < j} P k j` records the total degree of the `GL j` constituent at level `j`
along the chain `GL 1 ⊂ ⋯ ⊂ GL n`, with the empty zeroth row having sum `0`. The successive
differences

`P.rowWeight r = P.rowSum (r + 1) - P.rowSum r`

assemble into the **torus weight** `P.rowWeight : Fin n → ℤ` of the pattern. No positivity is
assumed on `P`: signed patterns over rational dominant weights carry signed torus weights, and
determinant shifts translate every coordinate of `P.rowWeight` by the shift parameter.

Three structural properties link `rowWeight` to the rest of the Gelfand–Tsetlin and Young-tableau
API:

1. **Telescoping partial sums and dominance** (`TauCeti.GTPattern.prefixSum_rowWeight`,
   `TauCeti.GTPattern.sum_rowWeight`, `TauCeti.GTPattern.dominates_rowWeight_topRow`): the first
   `j ≤ n` coordinates of `P.rowWeight` sum to `P.rowSum j`, the full sum equals `∑ i, P.topRow i`,
   and upward monotonicity along columns (`P k j ≤ P k n`) gives `P.rowSum j ≤ prefixSum j P.topRow`
   for all `j ≤ n`.
2. **Compatibility with pattern operations** (`TauCeti.GTPattern.rowWeightAddMonoidHom`,
   `TauCeti.GTPattern.rowWeight_shift`, `TauCeti.GTPattern.rowWeight_truncate`,
   `TauCeti.GTPattern.rowWeight_extend_castSucc`, `TauCeti.GTPattern.rowWeight_extend_last`):
   `rowWeight` is an additive monoid homomorphism, shifts uniformly under `GTPattern.shift`, and
   restricts to `Fin.castSucc` under `GTPattern.truncate`.
3. **Agreement with tableau content** (`TauCeti.SemistandardYoungTableau.rowWeight_toGTPattern`,
   `TauCeti.GTPattern.rowWeight_toTableau`): in the polynomial regime where `P.topRow` is the
   row-length sequence of a Young diagram `μ`, `P.rowWeight r` is the number of cells of the
   associated semistandard Young tableau carrying the entry `r`.

## Main definitions

* `TauCeti.GTPattern.rowSum`: the sum `∑_{k < j} P k j` of row `j` of a pattern.
* `TauCeti.GTPattern.rowWeight`: the torus weight `r ↦ P.rowSum (r + 1) - P.rowSum r`.
* `TauCeti.GTPattern.rowWeightAddMonoidHom`: `rowWeight` bundled as an additive monoid homomorphism.

## Main results

* `TauCeti.GTPattern.prefixSum_rowWeight`, `TauCeti.GTPattern.sum_rowWeight`,
  `TauCeti.GTPattern.dominates_rowWeight_topRow`.
* `TauCeti.GTPattern.rowWeight_shift`, `TauCeti.GTPattern.rowWeight_truncate`,
  `TauCeti.GTPattern.finite_topRow_and_rowWeight`.
* `TauCeti.GTPattern.rowWeight_toTableau`.

## References

* I. M. Gelfand and M. L. Tsetlin, *Finite-dimensional representations of the group of unimodular
  matrices*, Dokl. Akad. Nauk SSSR **71** (1950), 825–828.
* A. Molev, *Gelfand–Tsetlin bases for classical Lie algebras*, in *Handbook of Algebra*, Vol. 4
  (2006), 109–170, §2.
-/

public section

open scoped BigOperators

namespace TauCeti

namespace GTPattern

variable {n : ℕ}

/-! ### Row sums -/

/-- The sum `∑_{k < j} P k j` of the informative entries in row `j` of a Gelfand–Tsetlin pattern,
with `rowSum P 0 = 0`. -/
def rowSum (P : GTPattern n) (j : ℕ) : ℤ :=
  ∑ k ∈ Finset.range j, P k j

/-- Defining formula for `TauCeti.GTPattern.rowSum`. -/
theorem rowSum_def (P : GTPattern n) (j : ℕ) :
    P.rowSum j = ∑ k ∈ Finset.range j, P k j := (rfl)

@[simp]
theorem rowSum_zero_row (P : GTPattern n) : P.rowSum 0 = 0 := by
  simp [rowSum]

/-- Rows strictly above `n` carry only zero entries, so their row sum vanishes. -/
@[simp]
theorem rowSum_of_lt (P : GTPattern n) {j : ℕ} (hj : n < j) : P.rowSum j = 0 :=
  Finset.sum_eq_zero fun _ _ => P.entry_eq_zero_of_lt hj

/-- The sum of row `n` is the total sum of `P.topRow`. -/
theorem rowSum_top (P : GTPattern n) : P.rowSum n = ∑ i : Fin n, P.topRow i := by
  rw [rowSum_def, ← Fin.sum_univ_eq_sum_range (fun k => P k n)]
  exact Finset.sum_congr rfl fun i _ => (P.topRow_apply i).symm

@[simp]
theorem rowSum_zero (j : ℕ) : (0 : GTPattern n).rowSum j = 0 := by
  simp [rowSum_def, zero_apply]

@[simp]
theorem rowSum_add (P Q : GTPattern n) (j : ℕ) :
    (P + Q).rowSum j = P.rowSum j + Q.rowSum j := by
  simp [rowSum_def, add_apply, Finset.sum_add_distrib]

@[simp]
theorem rowSum_nsmul (k : ℕ) (P : GTPattern n) (j : ℕ) :
    (k • P).rowSum j = k • P.rowSum j := by
  simp [rowSum_def, nsmul_apply, Finset.mul_sum]

/-- Row `j ≤ n` of the constant pattern `const n m` sums to `j * m`. -/
theorem rowSum_const (m : ℤ) {j : ℕ} (hj : j ≤ n) :
    (const n m).rowSum j = (j : ℤ) * m := by
  rw [rowSum_def, Finset.sum_congr rfl fun k hk =>
    const_apply_of_lt_of_le m (Finset.mem_range.mp hk) hj]
  simp

/-- Shifting every informative entry by `m` adds `j * m` to row `j ≤ n`. -/
theorem rowSum_shift (P : GTPattern n) (m : ℤ) {j : ℕ} (hj : j ≤ n) :
    (P.shift m).rowSum j = P.rowSum j + (j : ℤ) * m := by
  rw [shift_eq_add_const, rowSum_add, rowSum_const m hj]

/-- Truncating the top row preserves all row sums up to level `n`. -/
@[simp]
theorem rowSum_truncate (P : GTPattern (n + 1)) {j : ℕ} (hj : j ≤ n) :
    P.truncate.rowSum j = P.rowSum j := by
  simp [rowSum_def, hj]

/-- Extending by a new top row preserves all earlier row sums. -/
theorem rowSum_extend_of_ne (Q : GTPattern n) (l : Fin (n + 1) → ℤ)
    (h : Interlaces l Q.topRow) {j : ℕ} (hj : j ≠ n + 1) :
    (Q.extend l h).rowSum j = Q.rowSum j := by
  simp [rowSum_def, hj]

/-- Extending by `l` gives top row sum `∑ i, l i`. -/
@[simp]
theorem rowSum_extend_top (Q : GTPattern n) (l : Fin (n + 1) → ℤ)
    (h : Interlaces l Q.topRow) :
    (Q.extend l h).rowSum (n + 1) = ∑ i : Fin (n + 1), l i := by
  rw [rowSum_top, topRow_extend]

/-! ### Torus weight (successive row-sum differences) -/

/-- The **torus weight** of a Gelfand–Tsetlin pattern: coordinate `r` is the row-sum difference
`P.rowSum (r + 1) - P.rowSum r`. -/
def rowWeight (P : GTPattern n) : Fin n → ℤ :=
  fun r => P.rowSum (r.val + 1) - P.rowSum r.val

theorem rowWeight_apply (P : GTPattern n) (r : Fin n) :
    P.rowWeight r = P.rowSum (r.val + 1) - P.rowSum r.val := (rfl)

/-- Expanded difference-of-sums formula for `TauCeti.GTPattern.rowWeight`. -/
theorem rowWeight_eq_sum_sub_sum (P : GTPattern n) (r : Fin n) :
    P.rowWeight r =
      (∑ k ∈ Finset.range (r.val + 1), P k (r.val + 1)) - ∑ k ∈ Finset.range r.val, P k r.val :=
  (rfl)

/-- **Telescoping prefix sums**: the first `j ≤ n` coordinates of `P.rowWeight` sum to `P.rowSum j`.
This fails past `n`: for `n < j`, `prefixSum j P.rowWeight = P.rowSum n` whereas `P.rowSum j = 0`.
-/
@[simp]
theorem prefixSum_rowWeight (P : GTPattern n) {j : ℕ} (hj : j ≤ n) :
    prefixSum j P.rowWeight = P.rowSum j := by
  induction j with
  | zero => simp
  | succ k ih =>
    rw [prefixSum_succ (Nat.lt_of_succ_le hj), ih (Nat.le_of_succ_le hj), rowWeight_apply]
    abel

/-- The coordinates of `P.rowWeight` sum to the total weight `∑ i, P.topRow i`. -/
@[simp]
theorem sum_rowWeight (P : GTPattern n) :
    (∑ r : Fin n, P.rowWeight r) = ∑ i : Fin n, P.topRow i := by
  rw [← prefixSum_of_le le_rfl P.rowWeight, prefixSum_rowWeight P le_rfl, rowSum_top]

@[simp]
theorem rowWeight_zero : (0 : GTPattern n).rowWeight = 0 := by
  ext r; simp [rowWeight_apply]

@[simp]
theorem rowWeight_add (P Q : GTPattern n) : (P + Q).rowWeight = P.rowWeight + Q.rowWeight := by
  ext r; simp only [rowWeight_apply, Pi.add_apply, rowSum_add]; abel

@[simp]
theorem rowWeight_nsmul (k : ℕ) (P : GTPattern n) : (k • P).rowWeight = k • P.rowWeight := by
  ext r; simp only [rowWeight_apply, Pi.smul_apply, rowSum_nsmul, nsmul_eq_mul]; ring

/-- `TauCeti.GTPattern.rowWeight` bundled as an additive monoid homomorphism. -/
def rowWeightAddMonoidHom : GTPattern n →+ (Fin n → ℤ) where
  toFun := rowWeight
  map_zero' := rowWeight_zero
  map_add' := rowWeight_add

@[simp]
theorem rowWeightAddMonoidHom_apply (P : GTPattern n) :
    rowWeightAddMonoidHom P = P.rowWeight := (rfl)

@[simp]
theorem rowWeight_const (m : ℤ) : (const n m).rowWeight = fun _ => m := by
  ext r
  rw [rowWeight_apply, rowSum_const m r.isLt, rowSum_const m r.isLt.le]
  push_cast
  ring

/-- Shifting every informative entry of `P` by `m` adds `m` to each coordinate of `P.rowWeight`. -/
@[simp]
theorem rowWeight_shift (P : GTPattern n) (m : ℤ) :
    (P.shift m).rowWeight = fun r => P.rowWeight r + m := by
  rw [shift_eq_add_const, rowWeight_add, rowWeight_const]
  rfl

/-- Truncating the top row restricts `rowWeight` along `Fin.castSucc`. -/
@[simp]
theorem rowWeight_truncate (P : GTPattern (n + 1)) (r : Fin n) :
    P.truncate.rowWeight r = P.rowWeight r.castSucc := by
  rw [rowWeight_apply, rowSum_truncate P r.isLt, rowSum_truncate P r.isLt.le,
    rowWeight_apply, Fin.val_castSucc]

/-- Extending a pattern preserves the first `n` coordinates of `rowWeight`. -/
@[simp]
theorem rowWeight_extend_castSucc (Q : GTPattern n) (l : Fin (n + 1) → ℤ)
    (h : Interlaces l Q.topRow) (r : Fin n) :
    (Q.extend l h).rowWeight r.castSucc = Q.rowWeight r := by
  rw [← rowWeight_truncate, truncate_extend]

/-- The last coordinate of `(Q.extend l h).rowWeight` is the total-sum increment
`(∑ i, l i) - (∑ i, Q.topRow i)`. -/
theorem rowWeight_extend_last (Q : GTPattern n) (l : Fin (n + 1) → ℤ)
    (h : Interlaces l Q.topRow) :
    (Q.extend l h).rowWeight (Fin.last n) = (∑ i, l i) - ∑ i, Q.topRow i := by
  rw [rowWeight_apply, Fin.val_last, rowSum_extend_top,
    rowSum_extend_of_ne Q l h (Nat.ne_of_lt (Nat.lt_succ_self n)), rowSum_top]

/-- For a one-row pattern, `rowWeight` agrees with `topRow`. -/
@[simp]
theorem rowWeight_one (P : GTPattern 1) : P.rowWeight = P.topRow := by
  ext i
  obtain rfl : i = 0 := Subsingleton.elim i 0
  simp [rowWeight_apply, rowSum_def, topRow_apply]

/-! ### Dominance by the top row and finiteness of weight fibres -/

/-- Each row sum at level `j ≤ n` is bounded above by the sum of the first `j` entries of `topRow`.
-/
theorem rowSum_le_prefixSum_topRow (P : GTPattern n) {j : ℕ} (hj : j ≤ n) :
    P.rowSum j ≤ prefixSum j P.topRow := by
  have htop : P.topRow = fun i : Fin n => P i n := funext P.topRow_apply
  rw [rowSum_def, htop, prefixSum_eq_sum_range j (fun k => P k n), min_eq_left hj]
  exact Finset.sum_le_sum fun k hk => P.entry_le_entry_of_le (Finset.mem_range.mp hk) hj le_rfl

/-- **Dominance of pattern weights**: for every (possibly signed) Gelfand–Tsetlin pattern `P`,
`P.rowWeight` and `P.topRow` have the same total sum and every leading partial sum of `P.rowWeight`
is at most the corresponding leading partial sum of `P.topRow`. -/
theorem dominates_rowWeight_topRow (P : GTPattern n) : Dominates P.rowWeight P.topRow := by
  rw [dominates_def]
  refine ⟨P.sum_rowWeight.symm, fun k hk => ?_⟩
  rw [← prefixSum_eq_sum_castLE hk, ← prefixSum_eq_sum_castLE hk, P.prefixSum_rowWeight hk]
  exact P.rowSum_le_prefixSum_topRow hk

/-- **Finiteness of Gelfand–Tsetlin weight fibres**: only finitely many patterns have a prescribed
top row and torus weight. -/
instance finite_topRow_and_rowWeight (l w : Fin n → ℤ) :
    Finite {P : GTPattern n // P.topRow = l ∧ P.rowWeight = w} :=
  Finite.of_injective
    (fun P : {P : GTPattern n // P.topRow = l ∧ P.rowWeight = w} =>
      (⟨P.1, P.2.1⟩ : {P : GTPattern n // P.topRow = l}))
    fun _ _ h => Subtype.ext (congrArg (·.1) h)

end GTPattern

end TauCeti

/-! ### Agreement with semistandard Young tableau content -/

namespace SemistandardYoungTableau

variable {μ : YoungDiagram}

/-- For `j ≤ n`, row `j` of `T.toGTPattern n` sums to the number of cells of `T` carrying entries
strictly below `j`. -/
theorem rowSum_toGTPattern (T : SemistandardYoungTableau μ) {n j : ℕ} (hj : j ≤ n) :
    (T.toGTPattern n).rowSum j = ∑ r ∈ Finset.range j, (T.content r : ℤ) := by
  rw [TauCeti.GTPattern.rowSum_def, ← Nat.cast_sum, sum_content_eq_card_filter]
  have hnj : ¬ n < j := not_lt.mpr hj
  simp only [toGTPattern_apply, patternEntry_def, hnj, ↓reduceIte, ← Nat.cast_sum]
  congr 1
  rw [← Finset.card_sigma]
  refine Finset.card_bij (fun p _ => (p.1, p.2)) ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter] at hp
    exact Finset.mem_filter.mpr
      ⟨(YoungDiagram.mem_cells _).mpr (YoungDiagram.mem_iff_lt_rowLen.mpr hp.2.1), hp.2.2⟩
  · rintro ⟨i₁, c₁⟩ _ ⟨i₂, c₂⟩ _ h
    exact Sigma.ext (Prod.mk.inj h).1 (heq_of_eq (Prod.mk.inj h).2)
  · intro c hc
    obtain ⟨hmem, hlt⟩ := Finset.mem_filter.mp hc
    have hmem' : c ∈ μ := (YoungDiagram.mem_cells c).mp hmem
    refine ⟨⟨c.1, c.2⟩, Finset.mem_sigma.mpr ⟨Finset.mem_range.mpr
      ((le_entry T hmem').trans_lt hlt), Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (YoungDiagram.mem_iff_lt_rowLen.mp hmem'), hlt⟩⟩, Prod.eta c⟩

/-- The torus weight of `T.toGTPattern n` counts the cells of `T` carrying each entry `r < n`. -/
@[simp]
theorem rowWeight_toGTPattern (T : SemistandardYoungTableau μ) (n : ℕ) (r : Fin n) :
    (T.toGTPattern n).rowWeight r = (T.content r.val : ℤ) := by
  rw [TauCeti.GTPattern.rowWeight_apply, T.rowSum_toGTPattern r.isLt,
    T.rowSum_toGTPattern r.isLt.le, Finset.sum_range_succ, add_sub_cancel_left]

end SemistandardYoungTableau

namespace TauCeti.GTPattern

/-- **Torus weight equals tableau content**: when `P.topRow` is the row-length sequence of a Young
diagram `μ` with at most `n` rows, `P.rowWeight r` is the multiplicity of `r` in `P.toTableau`. -/
@[simp]
theorem rowWeight_toTableau {n : ℕ} {μ : YoungDiagram} (P : GTPattern n) (hμ : μ.colLen 0 ≤ n)
    (hP : ∀ i : Fin n, P.topRow i = (μ.rowLen i : ℤ)) (r : Fin n) :
    ((P.toTableau hμ hP).content r.val : ℤ) = P.rowWeight r := by
  have hTP : SemistandardYoungTableau.toGTPattern (P.toTableau hμ hP) n = P := by
    have h := congrArg (·.1) ((gtPatternEquivSSYT n μ hμ).symm_apply_apply ⟨P, hP⟩)
    simpa only [gtPatternEquivSSYT_symm_apply_coe, gtPatternEquivSSYT_apply_coe] using h
  rw [← SemistandardYoungTableau.rowWeight_toGTPattern (P.toTableau hμ hP) n r, hTP]

end TauCeti.GTPattern
