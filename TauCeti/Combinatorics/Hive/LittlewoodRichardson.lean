/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hive.GelfandTsetlin
public import TauCeti.Combinatorics.Young.LittlewoodRichardson.Basic
import Mathlib.Tactic.FinCases

/-!
# Hives and Littlewood–Richardson tableaux

For Young diagrams `λ, μ, γ` with at most `n` rows, the normalized integer hives of size `n` with
clockwise product boundary `(λ, μ, γ*)` correspond bijectively to the Littlewood–Richardson
tableaux of shape `γ / λ` and content `μ` (`TauCeti.Hive.fixedIntegerHiveEquivLRTableau`). So
the hive count of `(λ, μ, γ*)` is the Littlewood–Richardson coefficient `c^γ_{λ μ}`
(`TauCeti.Hive.hiveCount_productBoundary_eq_natCard_lrTableau`).

The bijection factors through the hive's Gelfand–Tsetlin pattern of
`TauCeti.Hive.fixedIntegerHiveEquivGTPattern`. A Littlewood–Richardson tableau `T` determines
the pattern `T.toGTPattern n` whose entry `(k, j)` is the number of letters `k` in the first `j`
rows of `T`. Under this dictionary, with `a r k` the number of letters `k` in row `r`:

* the first rhombus family (`P k j ≤ P k (j + 1)`) is the nonnegativity of `a r k`;
* the second rhombus family (`P (k + 1) (j + 1) ≤ P k j`) is the ballot condition, in the row-count
  form `TauCeti.SkewSemistandardYoungTableau.isLatticeWord_readingWord_iff`;
* the remaining family `TauCeti.Hive.IsGTCompletable` is column strictness, in the row-count form
  `TauCeti.SkewSemistandardYoungTableau.rowLen_add_sum_range_rowCount_succ_le`;
* the top row of the pattern is the content `μ`, and its weight is `γ - λ` because the entries of
  row `r` of a Littlewood–Richardson tableau are at most `r` (`TauCeti.LRTableau.entry_le`).

Conversely a pattern is turned into row counts by the differences `P k (r + 1) - P k r`, and a
skew tableau is recovered from its row counts by sorting each row
(`TauCeti.SkewSemistandardYoungTableau.ofRowCount`). In the product chart the hive value at
`(i, j)` is `λ₀ + ⋯ + λⱼ₋₁` plus the number of letters below `i` in the first `j` rows
(`TauCeti.Hive.fixedIntegerHiveEquivLRTableau_symm_apply_ofChart`), and the number of letters
`k` in row `r` is the corresponding mixed difference of the hive
(`TauCeti.Hive.natCast_rowCount_fixedIntegerHiveEquivLRTableau`).

## Main definitions

* `TauCeti.LRTableau.toGTPattern`: the Gelfand–Tsetlin pattern of row-count partial sums of a
  Littlewood–Richardson tableau.
* `TauCeti.Hive.lrTableauEquivGTPattern`: Littlewood–Richardson tableaux of shape `γ / λ` and
  content `μ` correspond to hive-completable patterns with top row `μ` and weight `γ - λ`.
* `TauCeti.Hive.fixedIntegerHiveEquivLRTableau`,
  `TauCeti.Hive.fixedIntegerHiveEquivLRTableauOfShift`,
  `TauCeti.Hive.fixedIntegerHiveDetShiftEquivLRTableau`: the hive–tableau bijection for
  Young diagrams, polynomial-shifted dominant weights, and canonical determinant shifts.

## Main results

* `TauCeti.Hive.hiveCount_productBoundary_eq_natCard_lrTableau`: the hive count of `(λ, μ, γ*)`
  is the Littlewood–Richardson coefficient `c^γ_{λ μ}`.
* `TauCeti.Hive.hiveCount_productBoundary_eq_natCard_lrTableau_shape`,
  `TauCeti.Hive.hiveCount_productBoundary_eq_natCard_lrTableau_shift`,
  `TauCeti.Hive.hiveCount_productBoundary_of_isPolynomial`,
  `TauCeti.Hive.hiveCount_productBoundary`: the same for polynomial dominant weights of `GL n`, for
  determinant-shifted weights, and unconditionally for arbitrary signed dominant weights.
* `TauCeti.Hive.hiveCount_productBoundary_zero_left`,
  `TauCeti.Hive.hiveCount_productBoundary_zero_right`,
  `TauCeti.Hive.hiveCount_two_std_dual_triv`, `TauCeti.Hive.hiveCount_three_checks`: unit-weight
  fibre counts and concrete signed rank-`2` and rank-`3` hive counts.

## References

* A. Knutson and T. Tao, *The honeycomb model of $\mathrm{GL}_n(\mathbb{C})$ tensor products I:
  proof of the saturation conjecture*, J. Amer. Math. Soc. **12** (1999), 1055–1090, Appendix 2.
* A. S. Buch, *The saturation conjecture (after A. Knutson and T. Tao)*, Enseign. Math. **46**
  (2000), 43–60, Theorem 3.18.
-/

public section

open Finset

namespace TauCeti

/-! ### The Gelfand–Tsetlin pattern of a Littlewood–Richardson tableau -/

namespace LRTableau

variable {lam γ μ : YoungDiagram}

/-- The **Gelfand–Tsetlin pattern of a Littlewood–Richardson tableau** `T`: its entry `(k, j)`
is the number of letters `k` in the first `j ≤ n` rows of `T`. The ballot condition is the
interlacing inequality `P (k + 1) (j + 1) ≤ P k j`, and since row `r` of `T` holds only letters
`k ≤ r`, the entries with `j ≤ k` vanish. -/
def toGTPattern (n : ℕ) (T : LRTableau lam γ μ) : GTPattern n where
  entry k j := if j ≤ n then ∑ r ∈ range j, (T.val.rowCount r k : ℤ) else 0
  zeros' {k j} h := by
    split_ifs with hj
    · refine sum_eq_zero fun r hr => ?_
      rw [T.rowCount_eq_zero_of_lt (by grind), Nat.cast_zero]
    · rfl
  interlacing' {k j} _ hj := by
    have hlat := (T.val.isLatticeWord_readingWord_iff.mp T.property.2) k j
    rw [ite_eq_left hj.le, ite_eq_left (Nat.succ_le_of_lt hj), ite_eq_left (Nat.succ_le_of_lt hj)]
    exact ⟨sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (Nat.le_succ j))
      fun _ _ _ => Nat.cast_nonneg _, by exact_mod_cast hlat⟩

theorem toGTPattern_apply (n : ℕ) (T : LRTableau lam γ μ) (k j : ℕ) :
    T.toGTPattern n k j = if j ≤ n then ∑ r ∈ range j, (T.val.rowCount r k : ℤ) else 0 :=
  (rfl)

@[simp]
theorem toGTPattern_apply_of_le {n : ℕ} (T : LRTableau lam γ μ) (k : ℕ) {j : ℕ} (hj : j ≤ n) :
    T.toGTPattern n k j = ∑ r ∈ range j, (T.val.rowCount r k : ℤ) := by
  rw [toGTPattern_apply, ite_eq_left hj]

/-- Consecutive rows of `T.toGTPattern n` differ by the row counts of `T`. -/
theorem toGTPattern_succ_sub {n : ℕ} (T : LRTableau lam γ μ) (k : ℕ) {r : ℕ} (hr : r < n) :
    T.toGTPattern n k (r + 1) - T.toGTPattern n k r = T.val.rowCount r k := by
  rw [toGTPattern_apply_of_le _ _ hr, toGTPattern_apply_of_le _ _ hr.le, sum_range_succ,
    add_sub_cancel_left]

/-- The top row of `T.toGTPattern n` is the content `μ` of `T`. -/
theorem topRow_toGTPattern {n : ℕ} (hγ : γ.colLen 0 ≤ n) (T : LRTableau lam γ μ) :
    (T.toGTPattern n).topRow = (weightOfShape n μ).val := by
  ext k
  rw [GTPattern.topRow_apply, toGTPattern_apply_of_le _ _ le_rfl, weightOfShape_apply,
    ← Nat.cast_sum, T.val.sum_range_rowCount_eq_content _ hγ, T.property.1]

/-- The rows of `T.toGTPattern n` sum to the sizes of the first rows of the skew shape. -/
theorem rowSum_toGTPattern {n : ℕ} (T : LRTableau lam γ μ) {j : ℕ} (hj : j ≤ n) :
    (T.toGTPattern n).rowSum j = ∑ r ∈ range j, ((γ.rowLen r : ℤ) - lam.rowLen r) := by
  rw [GTPattern.rowSum_def, sum_congr rfl fun k _ => T.toGTPattern_apply_of_le k hj, sum_comm]
  refine sum_congr rfl fun r hr => ?_
  rw [← Nat.cast_sum, T.sum_range_rowCount_of_lt (mem_range.mp hr),
    Nat.cast_sub (YoungDiagram.rowLen_le_of_le T.val.le r)]

/-- The weight of `T.toGTPattern n` is `γ - λ`. -/
@[simp]
theorem rowWeight_toGTPattern {n : ℕ} (T : LRTableau lam γ μ) :
    (T.toGTPattern n).rowWeight = (weightOfShape n γ).val - (weightOfShape n lam).val := by
  ext r
  rw [GTPattern.rowWeight_eq_rowSum_sub, T.rowSum_toGTPattern r.isLt,
    T.rowSum_toGTPattern r.isLt.le, sum_range_succ, add_sub_cancel_left, Pi.sub_apply,
    weightOfShape_apply, weightOfShape_apply]

/-- Column strictness of `T` is the remaining rhombus family of the hive chart completion. -/
@[simp]
theorem isGTCompletable_toGTPattern {n : ℕ} (T : LRTableau lam γ μ) :
    Hive.IsGTCompletable (weightOfShape n lam) (T.toGTPattern n) := by
  rw [Hive.isGTCompletable_iff_sum_sub_le]
  intro i j _ hj
  have hcol := T.val.rowLen_add_sum_range_rowCount_succ_le j i
  simp only [T.toGTPattern_succ_sub _ (by omega : j + 1 < n),
    T.toGTPattern_succ_sub _ (by omega : j < n), weightOfShape_apply]
  push_cast [← Nat.cast_sum]
  omega

end LRTableau

namespace Hive

/-! ### Row counts from a Gelfand–Tsetlin pattern -/

section RowCount

variable {n : ℕ} {lam γ μ : YoungDiagram}

/-- The number of letters `k` in row `r` read off a pattern `P`: the difference
`P k (r + 1) - P k r`, truncated at `0`. For the patterns of interest it is nonnegative in rows
`r < n` and zero in rows `r ≥ n`. -/
private def gtRowCount (P : GTPattern n) (r k : ℕ) : ℕ := (P k (r + 1) - P k r).toNat

private theorem natCast_gtRowCount {P : GTPattern n} (hP : ∀ i : Fin n, 0 ≤ P.topRow i)
    {r : ℕ} (hr : r < n) (k : ℕ) : (gtRowCount P r k : ℤ) = P k (r + 1) - P k r := by
  refine Int.toNat_of_nonneg (sub_nonneg.mpr ?_)
  rcases lt_trichotomy k r with hkr | rfl | hkr
  · exact P.entry_le_entry_succ_row hkr hr
  · rw [P.entry_eq_zero_of_le le_rfl]; exact P.entry_nonneg hP _ _
  · rw [P.entry_eq_zero_of_le hkr.le, P.entry_eq_zero_of_le hkr]

private theorem gtRowCount_eq_zero_of_le {P : GTPattern n} (hP : ∀ i : Fin n, 0 ≤ P.topRow i)
    {r : ℕ} (hr : n ≤ r) (k : ℕ) : gtRowCount P r k = 0 := by
  rw [gtRowCount, P.entry_eq_zero_of_lt (Nat.lt_succ_of_le hr), zero_sub, Int.toNat_eq_zero,
    neg_nonpos]
  exact P.entry_nonneg hP _ _

private theorem gtRowCount_eq_zero_of_lt (P : GTPattern n) {r k : ℕ} (hrk : r < k) :
    gtRowCount P r k = 0 := by
  rw [gtRowCount, P.entry_eq_zero_of_le hrk, P.entry_eq_zero_of_le hrk.le, sub_zero,
    Int.toNat_zero]

/-- The row counts of `P` telescope along a column: the letters `k` in the first `x` rows. -/
private theorem sum_range_natCast_gtRowCount {P : GTPattern n}
    (hP : ∀ i : Fin n, 0 ≤ P.topRow i) {x : ℕ} (hx : x ≤ n) (k : ℕ) :
    ∑ r ∈ range x, (gtRowCount P r k : ℤ) = P k x := by
  rw [sum_congr rfl fun r hr => natCast_gtRowCount hP ((mem_range.mp hr).trans_le hx) k,
    sum_range_sub (fun r => P k r), P.entry_eq_zero_of_le (Nat.zero_le k), sub_zero]

/-- The row counts of a pattern with weight `γ - λ` fill row `r` of the skew shape `γ / λ`. -/
private theorem sum_range_natCast_gtRowCount_of_lt {P : GTPattern n}
    (hP : ∀ i : Fin n, 0 ≤ P.topRow i)
    (hW : P.rowWeight = (weightOfShape n γ).val - (weightOfShape n lam).val)
    {r x : ℕ} (hr : r < n) (hrx : r < x) :
    ∑ k ∈ range x, (gtRowCount P r k : ℤ) = γ.rowLen r - lam.rowLen r := by
  have hw := congrFun hW ⟨r, hr⟩
  rw [GTPattern.rowWeight_eq_rowSum_sub, Pi.sub_apply, weightOfShape_apply,
    weightOfShape_apply] at hw
  rw [sum_congr rfl fun k _ => natCast_gtRowCount hP hr k, sum_sub_distrib,
    P.sum_range_entry_eq_rowSum hrx, P.sum_range_entry_eq_rowSum hrx.le]
  exact hw

end RowCount

/-! ### Littlewood–Richardson tableaux from Gelfand–Tsetlin patterns -/

section OfGTPattern

variable {n : ℕ} {lam γ μ : YoungDiagram}

/-- The hypotheses on a pattern `P` under which its row counts are those of a
Littlewood–Richardson tableau of shape `γ / λ` and content `μ`. -/
private structure IsLRPattern (n : ℕ) (lam γ μ : YoungDiagram) (P : GTPattern n) : Prop where
  hlam : lam.colLen 0 ≤ n
  hγ : γ.colLen 0 ≤ n
  hμ : μ.colLen 0 ≤ n
  top : P.topRow = (weightOfShape n μ).val
  weight : P.rowWeight =
    (weightOfShape n γ).val - (weightOfShape n lam).val
  completable : IsGTCompletable (weightOfShape n lam) P

namespace IsLRPattern

variable {P : GTPattern n}

private theorem topRow_nonneg (h : IsLRPattern n lam γ μ P) (i : Fin n) : 0 ≤ P.topRow i := by
  rw [h.top, weightOfShape_apply]; exact Nat.cast_nonneg _

/-- The row counts of `P` fill the rows of `γ / λ`, so `λ ≤ γ`. -/
private theorem sum_range_gtRowCount (h : IsLRPattern n lam γ μ P) (r : ℕ) :
    ∑ k ∈ range n, gtRowCount P r k = γ.rowLen r - lam.rowLen r := by
  rcases lt_or_ge r n with hr | hr
  · have hs := sum_range_natCast_gtRowCount_of_lt h.topRow_nonneg h.weight hr hr
    push_cast [← Nat.cast_sum] at hs
    omega
  · rw [sum_eq_zero fun k _ => gtRowCount_eq_zero_of_le h.topRow_nonneg hr k,
      YoungDiagram.rowLen_eq_zero_of_colLen_le (h.hγ.trans hr), Nat.zero_sub]

private theorem le (h : IsLRPattern n lam γ μ P) : lam ≤ γ := by
  refine YoungDiagram.le_of_forall_rowLen_le fun r => ?_
  rcases lt_or_ge r n with hr | hr
  · have hs := sum_range_natCast_gtRowCount_of_lt h.topRow_nonneg h.weight hr hr
    have : (0 : ℤ) ≤ ∑ k ∈ range n, (gtRowCount P r k : ℤ) := sum_nonneg fun _ _ => by positivity
    omega
  · rw [YoungDiagram.rowLen_eq_zero_of_colLen_le (h.hlam.trans hr)]; exact Nat.zero_le _

/-- Column strictness of the filling with the row counts of `P`: this is `IsGTCompletable` in
rows `i + 1 < n` and letters `x ≤ i`; for larger letters both rows are full, and rows `i + 1 ≥ n`
are empty. -/
private theorem col (h : IsLRPattern n lam γ μ P) (i x : ℕ) :
    lam.rowLen (i + 1) + ∑ l ∈ range (x + 1), gtRowCount P (i + 1) l ≤
      lam.rowLen i + ∑ l ∈ range x, gtRowCount P i l := by
  have hanti := lam.rowLen_anti i (i + 1) (Nat.le_succ i)
  rcases le_or_gt n (i + 1) with hi | hi
  · rw [sum_eq_zero fun l _ => gtRowCount_eq_zero_of_le h.topRow_nonneg hi l]
    omega
  rcases le_or_gt x i with hxi | hxi
  · have hc := (isGTCompletable_iff_sum_sub_le _ P).mp h.completable x i hxi hi
    rw [weightOfShape_apply, weightOfShape_apply] at hc
    rw [← sum_congr rfl fun l _ => natCast_gtRowCount h.topRow_nonneg hi l,
      ← sum_congr rfl fun l _ => natCast_gtRowCount h.topRow_nonneg (Nat.lt_of_succ_lt hi) l] at hc
    push_cast [← Nat.cast_sum] at hc
    omega
  · have h₁ := sum_range_natCast_gtRowCount_of_lt h.topRow_nonneg h.weight hi
      (by omega : i + 1 < x + 1)
    have h₂ := sum_range_natCast_gtRowCount_of_lt h.topRow_nonneg h.weight
      (Nat.lt_of_succ_lt hi) hxi
    have hγ := γ.rowLen_anti i (i + 1) (Nat.le_succ i)
    push_cast [← Nat.cast_sum] at h₁ h₂
    omega

/-- The skew tableau of shape `γ / λ` whose rows hold the row counts of `P`. -/
private def tableau (h : IsLRPattern n lam γ μ P) : SkewSemistandardYoungTableau lam γ :=
  .ofRowCount h.le n (gtRowCount P) h.sum_range_gtRowCount h.col

private theorem rowCount_tableau (h : IsLRPattern n lam γ μ P) (r k : ℕ) :
    h.tableau.rowCount r k = gtRowCount P r k := by
  refine SkewSemistandardYoungTableau.rowCount_ofRowCount _ _ _ (fun i l hl => ?_) r k
  rcases le_or_gt n i with hi | hi
  · exact gtRowCount_eq_zero_of_le h.topRow_nonneg hi l
  · exact gtRowCount_eq_zero_of_lt P (hi.trans_le hl)

/-- The letters `k` in the first `x ≤ n` rows of `h.tableau` number `P k x`. -/
private theorem sum_range_natCast_rowCount_tableau (h : IsLRPattern n lam γ μ P) {x : ℕ}
    (hx : x ≤ n) (k : ℕ) : ∑ r ∈ range x, (h.tableau.rowCount r k : ℤ) = P k x := by
  simp only [rowCount_tableau, sum_range_natCast_gtRowCount h.topRow_nonneg hx]

private theorem content_tableau (h : IsLRPattern n lam γ μ P) :
    ⇑h.tableau.content = μ.rowLen := by
  ext k
  have hs := h.sum_range_natCast_rowCount_tableau le_rfl k
  rw [← Nat.cast_sum, h.tableau.sum_range_rowCount_eq_content _ h.hγ] at hs
  rcases lt_or_ge k n with hk | hk
  · have ht := congrFun h.top ⟨k, hk⟩
    rw [GTPattern.topRow_apply, weightOfShape_apply] at ht
    exact_mod_cast hs.trans ht
  · rw [P.entry_eq_zero_of_le hk, Nat.cast_eq_zero] at hs
    rw [hs, YoungDiagram.rowLen_eq_zero_of_colLen_le (h.hμ.trans hk)]

/-- The ballot condition on `h.tableau` is the second interlacing inequality of `P`. -/
private theorem isLatticeWord_tableau (h : IsLRPattern n lam γ μ P) :
    h.tableau.readingWord.IsLatticeWord := by
  refine h.tableau.isLatticeWord_readingWord_iff.mpr fun k x => ?_
  suffices hz : ∑ r ∈ range (x + 1), (h.tableau.rowCount r (k + 1) : ℤ) ≤
      ∑ r ∈ range x, (h.tableau.rowCount r k : ℤ) by exact_mod_cast hz
  rcases lt_or_ge x n with hx | hx
  · rw [h.sum_range_natCast_rowCount_tableau hx, h.sum_range_natCast_rowCount_tableau hx.le]
    exact P.entry_succ_succ_le_entry hx
  · -- Past row `n` the rows are empty, and the inequality is between top-row entries.
    have hz : ∀ y, n ≤ y → ∀ l, ∑ r ∈ range y, (h.tableau.rowCount r l : ℤ) = P l n := by
      intro y hy l
      rw [← h.sum_range_natCast_rowCount_tableau le_rfl l, eq_comm]
      refine sum_subset (range_subset_range.mpr hy) fun r _ hr' => ?_
      rw [rowCount_tableau, gtRowCount_eq_zero_of_le h.topRow_nonneg
        (not_lt.mp (mem_range.not.mp hr')), Nat.cast_zero]
    rw [hz _ (hx.trans (Nat.le_succ x)), hz _ hx]
    rcases lt_or_ge (k + 1) n with hk | hk
    · exact P.entry_succ_le_entry hk
    · rw [P.entry_eq_zero_of_le hk]; exact P.entry_nonneg h.topRow_nonneg _ _

/-- The Littlewood–Richardson tableau whose row counts are read off `P`. -/
private def lrTableau (h : IsLRPattern n lam γ μ P) : LRTableau lam γ μ :=
  ⟨h.tableau, h.content_tableau, h.isLatticeWord_tableau⟩

end IsLRPattern

end OfGTPattern

/-! ### The equivalences -/

section Equiv

variable {n : ℕ} {lam γ μ : YoungDiagram}

/-- **Littlewood–Richardson tableaux as hive-completable patterns**: for Young diagrams `λ, μ, γ`
with at most `n` rows, the Littlewood–Richardson tableaux of shape `γ / λ` and content `μ`
correspond to the Gelfand–Tsetlin patterns with top row `μ`, weight `γ - λ` and
`IsGTCompletable λ`, by counting the letters `k` in the first `j` rows. -/
def lrTableauEquivGTPattern (hlam : lam.colLen 0 ≤ n) (hγ : γ.colLen 0 ≤ n)
    (hμ : μ.colLen 0 ≤ n) :
    LRTableau lam γ μ ≃
      {P : GTPattern n // P.topRow = (weightOfShape n μ).val ∧
        P.rowWeight =
          (weightOfShape n γ).val - (weightOfShape n lam).val ∧
        IsGTCompletable (weightOfShape n lam) P} where
  toFun T := ⟨T.toGTPattern n, T.topRow_toGTPattern hγ, T.rowWeight_toGTPattern,
    T.isGTCompletable_toGTPattern⟩
  invFun P := IsLRPattern.lrTableau ⟨hlam, hγ, hμ, P.property.1, P.property.2.1, P.property.2.2⟩
  left_inv T := by
    refine Subtype.ext (SkewSemistandardYoungTableau.eq_of_rowCount_eq fun r k => ?_)
    refine (IsLRPattern.rowCount_tableau ⟨hlam, hγ, hμ, T.topRow_toGTPattern hγ,
      T.rowWeight_toGTPattern, T.isGTCompletable_toGTPattern⟩ r k).trans ?_
    rcases lt_or_ge r n with hr | hr
    · rw [gtRowCount, T.toGTPattern_succ_sub k hr, Int.toNat_natCast]
    · rw [gtRowCount_eq_zero_of_le (fun i => (T.topRow_toGTPattern hγ).symm ▸ Nat.cast_nonneg _)
        hr, T.val.rowCount_eq_zero_of_colLen_le (hγ.trans hr)]
  right_inv P := by
    refine Subtype.ext (GTPattern.ext fun k j => ?_)
    rcases le_or_gt j n with hj | hj
    · exact (LRTableau.toGTPattern_apply_of_le _ k hj).trans
        (IsLRPattern.sum_range_natCast_rowCount_tableau ⟨hlam, hγ, hμ, P.property.1, P.property.2.1,
            P.property.2.2⟩
          hj k)
    · rw [LRTableau.toGTPattern_apply, ite_eq_right hj.not_ge, P.val.entry_eq_zero_of_lt hj]

@[simp]
theorem lrTableauEquivGTPattern_apply_coe (hlam : lam.colLen 0 ≤ n) (hγ : γ.colLen 0 ≤ n)
    (hμ : μ.colLen 0 ≤ n) (T : LRTableau lam γ μ) :
    (lrTableauEquivGTPattern hlam hγ hμ T).val = T.toGTPattern n :=
  (rfl)

/-- The tableau of a pattern `P` has `P k (r + 1) - P k r` letters `k` in each row `r < n`. -/
theorem natCast_rowCount_lrTableauEquivGTPattern_symm (hlam : lam.colLen 0 ≤ n)
    (hγ : γ.colLen 0 ≤ n) (hμ : μ.colLen 0 ≤ n)
    (P : {P : GTPattern n // P.topRow = (weightOfShape n μ).val ∧
        P.rowWeight =
          (weightOfShape n γ).val - (weightOfShape n lam).val ∧
        IsGTCompletable (weightOfShape n lam) P})
    {r : ℕ} (hr : r < n) (k : ℕ) :
    (((lrTableauEquivGTPattern hlam hγ hμ).symm P).val.rowCount r k : ℤ) =
      P.val k (r + 1) - P.val k r := by
  have h : IsLRPattern n lam γ μ P.val := ⟨hlam, hγ, hμ, P.property.1, P.property.2.1,
      P.property.2.2⟩
  exact (congrArg Nat.cast (h.rowCount_tableau r k)).trans (natCast_gtRowCount h.topRow_nonneg hr k)

/-- **The hive–Littlewood–Richardson bijection**: for Young diagrams `λ, μ, γ` with at most `n`
rows, the normalized integer hives with clockwise boundary `(λ, μ, γ*)` correspond to the
Littlewood–Richardson tableaux of shape `γ / λ` and content `μ`. The hive value at `(i, j)` of the
product chart is `λ₀ + ⋯ + λⱼ₋₁` plus the number of letters below `i` in the first `j` rows of the
tableau. -/
def fixedIntegerHiveEquivLRTableau (hlam : lam.colLen 0 ≤ n) (hγ : γ.colLen 0 ≤ n)
    (hμ : μ.colLen 0 ≤ n) :
    FixedIntegerHive (productBoundary (weightOfShape n lam)
      (weightOfShape n μ) (weightOfShape n γ)) ≃
      LRTableau lam γ μ :=
  (fixedIntegerHiveEquivGTPattern _ _ _).trans (lrTableauEquivGTPattern hlam hγ hμ).symm

/-- The hive of a Littlewood–Richardson tableau `T` takes the value `λ₀ + ⋯ + λⱼ₋₁` plus the
number of letters below `i` in the first `j` rows of `T` at the point `(i, j)` of the product
chart. -/
@[simp]
theorem fixedIntegerHiveEquivLRTableau_symm_apply_ofChart (hlam : lam.colLen 0 ≤ n)
    (hγ : γ.colLen 0 ≤ n) (hμ : μ.colLen 0 ≤ n) (T : LRTableau lam γ μ) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ n) :
    ((fixedIntegerHiveEquivLRTableau hlam hγ hμ).symm T).val (Vertex.ofChart n i j hij hj) =
      prefixSum j (weightOfShape n lam).val +
        ∑ k ∈ range i, ∑ r ∈ range j, (T.val.rowCount r k : ℤ) := by
  simp only [fixedIntegerHiveEquivLRTableau, Equiv.symm_trans_apply, Equiv.symm_symm,
    fixedIntegerHiveEquivGTPattern_symm_apply_coe, lrTableauEquivGTPattern_apply_coe,
    ofGTPattern_ofChart, gtCompletion_def, LRTableau.toGTPattern_apply_of_le _ _ hj]

/-- The tableau of a hive `h` has `P k (r + 1) - P k r` letters `k` in each row `r < n`, where
`P = h.toGTPattern` is the difference pattern `P k j = h(k + 1, j) - h(k, j)` (`k < j`) of the
product chart. For `k < r` this is the mixed difference
`h(k + 1, r + 1) - h(k, r + 1) - h(k + 1, r) + h(k, r)`, and for `k = r` it is
`h(r + 1, r + 1) - h(r, r + 1)`. -/
theorem natCast_rowCount_fixedIntegerHiveEquivLRTableau (hlam : lam.colLen 0 ≤ n)
    (hγ : γ.colLen 0 ≤ n) (hμ : μ.colLen 0 ≤ n)
    (h : FixedIntegerHive (productBoundary (weightOfShape n lam)
      (weightOfShape n μ) (weightOfShape n γ)))
    {r : ℕ} (hr : r < n) (k : ℕ) :
    ((fixedIntegerHiveEquivLRTableau hlam hγ hμ h).val.rowCount r k : ℤ) =
      h.val.toGTPattern k (r + 1) - h.val.toGTPattern k r := by
  rw [fixedIntegerHiveEquivLRTableau, Equiv.trans_apply,
    natCast_rowCount_lrTableauEquivGTPattern_symm hlam hγ hμ _ hr k,
    fixedIntegerHiveEquivGTPattern_apply_coe]

/-- **Hive counts are Littlewood–Richardson coefficients**: for Young diagrams `λ, μ, γ` with at
most `n` rows, the number of integer hives with boundary `(λ, μ, γ*)` is `c^γ_{λ μ}`. -/
theorem hiveCount_productBoundary_eq_natCard_lrTableau (hlam : lam.colLen 0 ≤ n)
    (hγ : γ.colLen 0 ≤ n) (hμ : μ.colLen 0 ≤ n) :
    hiveCount (productBoundary (weightOfShape n lam)
      (weightOfShape n μ) (weightOfShape n γ)) =
      Nat.card (LRTableau lam γ μ) := by
  rw [← natCard_fixedIntegerHive]
  exact Nat.card_congr (fixedIntegerHiveEquivLRTableau hlam hγ hμ)

/-- **Hive counts of polynomial weights are Littlewood–Richardson coefficients**: for polynomial
dominant weights `λ, μ, γ` of `GL n`, the number of integer hives with boundary `(λ, μ, γ*)` is
the Littlewood–Richardson coefficient of their Young diagrams. -/
theorem hiveCount_productBoundary_eq_natCard_lrTableau_shape {lam μ γ : DominantWeight n}
    (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial) (hγ : γ.IsPolynomial) :
    hiveCount (productBoundary lam μ γ) = Nat.card (LRTableau lam.shape γ.shape μ.shape) := by
  conv_lhs => rw [← weightOfShape_shape hlam, ← weightOfShape_shape hμ,
    ← weightOfShape_shape hγ]
  exact hiveCount_productBoundary_eq_natCard_lrTableau (DominantWeight.colLen_zero_shape_le lam)
    (DominantWeight.colLen_zero_shape_le γ) (DominantWeight.colLen_zero_shape_le μ)

/-- **Hive counts of signed weights are Littlewood–Richardson coefficients**: if determinant
shifts by `a` of `λ`, by `b` of `μ` and by `a + b` of `γ` make all three dominant weights of
`GL n` polynomial, the number of integer hives with boundary `(λ, μ, γ*)` is the
Littlewood–Richardson coefficient of the Young diagrams of the shifted weights. In particular this
coefficient does not depend on the choice of such shifts. -/
theorem hiveCount_productBoundary_eq_natCard_lrTableau_shift {lam μ γ : DominantWeight n}
    {a b : ℤ} (hlam : (lam.shift a).IsPolynomial) (hμ : (μ.shift b).IsPolynomial)
    (hγ : (γ.shift (a + b)).IsPolynomial) :
    hiveCount (productBoundary lam μ γ) =
      Nat.card (LRTableau (lam.shift a).shape (γ.shift (a + b)).shape (μ.shift b).shape) := by
  rw [← hiveCount_productBoundary_shift lam μ γ a b]
  exact hiveCount_productBoundary_eq_natCard_lrTableau_shape hlam hμ hγ

end Equiv

/-! ### Signed dominant weights, unit-weight fibres, and concrete checks -/

section Signed

variable {n : ℕ}

open scoped Classical in
/-- For polynomial input weights `lam, μ` and any dominant weight `γ`, `hiveCount` equals the
Littlewood–Richardson coefficient when `γ` is polynomial and `0` otherwise. -/
theorem hiveCount_productBoundary_of_isPolynomial {lam μ : DominantWeight n}
    (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial) (γ : DominantWeight n) :
    hiveCount (productBoundary lam μ γ) =
      if γ.IsPolynomial then Nat.card (LRTableau lam.shape γ.shape μ.shape) else 0 := by
  split_ifs with hγ
  · exact hiveCount_productBoundary_eq_natCard_lrTableau_shape hlam hμ hγ
  · exact hiveCount_eq_zero_iff.mpr ⟨fun ⟨_, hb⟩ => hγ (isPolynomial_of_productBoundary hb hlam hμ)⟩

/-- Object equivalence between `FixedIntegerHive (productBoundary lam μ γ)` and
Littlewood–Richardson tableaux for arbitrary signed dominant weights shifted into the polynomial
cone by `(a, b)`. -/
def fixedIntegerHiveEquivLRTableauOfShift {lam μ γ : DominantWeight n} {a b : ℤ}
    (hla : (lam.shift a).IsPolynomial) (hmb : (μ.shift b).IsPolynomial)
    (hgc : (γ.shift (a + b)).IsPolynomial) :
    FixedIntegerHive (productBoundary lam μ γ) ≃
      LRTableau (lam.shift a).shape (γ.shift (a + b)).shape (μ.shift b).shape :=
  (fixedIntegerHiveShiftEquiv lam μ γ a b).trans <| by
    have h := fixedIntegerHiveEquivLRTableau (DominantWeight.colLen_zero_shape_le (lam.shift a))
      (DominantWeight.colLen_zero_shape_le (γ.shift (a + b)))
      (DominantWeight.colLen_zero_shape_le (μ.shift b))
    rwa [weightOfShape_shape hla, weightOfShape_shape hmb, weightOfShape_shape hgc] at h

/-- Canonical determinant-shifted equivalence between `FixedIntegerHive (productBoundary lam μ γ)`
and Littlewood–Richardson tableaux of shapes `lam.detShiftShape` and `μ.detShiftShape`, whenever
`lam.detShift + μ.detShift ≤ γ.detShift`. -/
def fixedIntegerHiveDetShiftEquivLRTableau {lam μ γ : DominantWeight n}
    (hdet : lam.detShift + μ.detShift ≤ γ.detShift) :
    FixedIntegerHive (productBoundary lam μ γ) ≃
      LRTableau lam.detShiftShape
        (γ.shift (-(lam.detShift + μ.detShift))).shape μ.detShiftShape := by
  have hneg : -lam.detShift + -μ.detShift = -(lam.detShift + μ.detShift) := by omega
  have hgc : (γ.shift (-lam.detShift + -μ.detShift)).IsPolynomial := by
    rw [hneg, DominantWeight.isPolynomial_iff_zero_le_detShift]
    match n, lam, μ, γ, hdet with
    | 0, _, _, _, _ => simp
    | _ + 1, _, _, _, hdet => rw [DominantWeight.detShift_shift]; omega
  have hsh (w : DominantWeight n) : (w.shift (-w.detShift)).shape = w.detShiftShape := by
    rw [← w.weightOfShape_detShiftShape, shape_weightOfShape w.colLen_zero_detShiftShape_le]
  rw [← hsh lam, ← hsh μ, ← hneg]
  exact fixedIntegerHiveEquivLRTableauOfShift lam.isPolynomial_shift_neg_detShift
    μ.isPolynomial_shift_neg_detShift hgc

open scoped Classical in
/-- **Shift independence of Littlewood–Richardson hive counts**: for any shifts `a, b : ℤ` making
`lam.shift a` and `μ.shift b` polynomial, the shifted tableau count equals
`hiveCount (productBoundary lam μ γ)` and hence does not depend on `(a, b)`. -/
theorem hiveCount_productBoundary_eq_ite_shift {lam μ : DominantWeight n} (γ : DominantWeight n)
    {a b : ℤ} (hla : (lam.shift a).IsPolynomial) (hmb : (μ.shift b).IsPolynomial) :
    hiveCount (productBoundary lam μ γ) =
      if (γ.shift (a + b)).IsPolynomial then
        Nat.card (LRTableau (lam.shift a).shape (γ.shift (a + b)).shape (μ.shift b).shape)
      else 0 := by
  rw [← hiveCount_productBoundary_shift lam μ γ a b,
    hiveCount_productBoundary_of_isPolynomial hla hmb]

open scoped Classical in
/-- **Littlewood–Richardson formula for `hiveCount` on arbitrary signed dominant weights** via the
canonical determinant-twist decomposition. -/
theorem hiveCount_productBoundary (lam μ γ : DominantWeight n) :
    hiveCount (productBoundary lam μ γ) =
      if lam.detShift + μ.detShift ≤ γ.detShift then
        Nat.card (LRTableau lam.detShiftShape
          (γ.shift (-(lam.detShift + μ.detShift))).shape μ.detShiftShape)
      else 0 := by
  split_ifs with hdet
  · rw [← natCard_fixedIntegerHive]
    exact Nat.card_congr (fixedIntegerHiveDetShiftEquivLRTableau hdet)
  · exact hiveCount_eq_zero_iff.mpr ⟨fun ⟨_, hb⟩ => hdet (detShift_le_of_productBoundary hb)⟩

open scoped Classical in
/-- With trivial first input weight `0`, `productBoundary 0 μ γ` has one integer hive when `γ = μ`
and none otherwise. -/
theorem hiveCount_productBoundary_zero_left (μ γ : DominantWeight n) :
    hiveCount (productBoundary 0 μ γ) = if γ = μ then 1 else 0 := by
  rw [← hiveCount_productBoundary_shift 0 μ γ 0 (-μ.detShift), zero_add,
    DominantWeight.shift_zero,
    hiveCount_productBoundary_of_isPolynomial DominantWeight.isPolynomial_zero
      μ.isPolynomial_shift_neg_detShift,
    DominantWeight.shape_zero, natCard_lrTableau_bot_left]
  rcases eq_or_ne γ μ with rfl | h
  · simp [γ.isPolynomial_shift_neg_detShift]
  · simp only [h, ↓reduceIte]
    split_ifs with hp hm
    · exfalso
      apply h
      have heq : γ.shift (-μ.detShift) = μ.shift (-μ.detShift) := by
        rw [← weightOfShape_shape hp, ← weightOfShape_shape μ.isPolynomial_shift_neg_detShift, hm]
      simpa using congrArg (fun w : DominantWeight n => w.shift μ.detShift) heq
    · rfl
    · rfl

open scoped Classical in
/-- With trivial second input weight `0`, `productBoundary lam 0 γ` has one integer hive when
`γ = lam` and none otherwise. -/
theorem hiveCount_productBoundary_zero_right (lam γ : DominantWeight n) :
    hiveCount (productBoundary lam 0 γ) = if γ = lam then 1 else 0 := by
  rw [← hiveCount_productBoundary_dual, DominantWeight.dual_zero,
    hiveCount_productBoundary_zero_left]
  exact if_congr DominantWeight.dual_injective.eq_iff rfl rfl

/-- Signed rank-`2` check: `λ = (1, 0), μ = (0, -1), γ = (0, 0)` has `hiveCount = 1`
(the trivial invariant in `V ⊗ V*`), whereas truncating negative entries to `0` would give
`((1, 0), (0, 0), (0, 0))` with `hiveCount = 0`. -/
theorem hiveCount_two_std_dual_triv :
    hiveCount (productBoundary ⟨![1, 0], by decide⟩ ⟨![0, -1], by decide⟩ ⟨![0, 0], by decide⟩) = 1
      ∧ hiveCount
        (productBoundary ⟨![1, 0], by decide⟩ ⟨![0, 0], by decide⟩ ⟨![0, 0], by decide⟩) = 0 := by
  let lam : DominantWeight 2 := ⟨![1, 0], by decide⟩
  let μ : DominantWeight 2 := ⟨![0, -1], by decide⟩
  let γ : DominantWeight 2 := ⟨![0, 0], by decide⟩
  constructor
  · have hsh : productBoundary (lam.shift 0) (μ.shift 1) (γ.shift (0 + 1)) =
        productBoundary ⟨![1, 0], by decide⟩ ⟨![1, 0], by decide⟩ ⟨![1, 1], by decide⟩ := by
      ext s i
      fin_cases s <;> fin_cases i <;>
        simp [productBoundary_zero, productBoundary_one, productBoundary_two, lam, μ, γ]
    rw [← hiveCount_productBoundary_shift lam μ γ 0 1, hsh]
    exact hiveCount_two_std_std_det
  · refine hiveCount_eq_zero_iff.mpr ⟨fun ⟨_, hb⟩ => ?_⟩
    have hsum := sum_eq_of_productBoundary hb
    simp [Fin.sum_univ_two] at hsum

private theorem isRhombusConcave_of_chartThree (c : ℕ → ℕ → ℤ)
    (hH : c 0 0 + c 1 2 ≤ c 0 1 + c 1 1 ∧ c 0 1 + c 1 3 ≤ c 0 2 + c 1 2 ∧
      c 1 1 + c 2 3 ≤ c 1 2 + c 2 2)
    (hC : c 1 1 + c 0 2 ≤ c 0 1 + c 1 2 ∧ c 1 2 + c 0 3 ≤ c 0 2 + c 1 3 ∧
      c 2 2 + c 1 3 ≤ c 1 2 + c 2 3)
    (hV : c 0 1 + c 2 2 ≤ c 1 1 + c 1 2 ∧ c 0 2 + c 2 3 ≤ c 1 2 + c 1 3 ∧
      c 1 2 + c 3 3 ≤ c 2 2 + c 2 3) :
    IsRhombusConcave (fun p : Vertex 3 => c p.z (3 - p.x)) := by
  rw [isRhombusConcave_iff_ofChart]
  have hv (i j : ℕ) (hij : i ≤ j) (hjn : j ≤ 3) :
      (let p := Vertex.ofChart 3 i j hij hjn; c p.z (3 - p.x)) = c i j := by
    simp only [Vertex.ofChart_z, Vertex.ofChart_x, Nat.sub_sub_self hjn]
  refine ⟨fun i j hij hjn => ?_, fun i j hij hjn => ?_, fun i j hij hjn => ?_⟩
  · simp only [hv]
    rcases (by omega : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2)) with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp only [hC]
  · simp only [hv]
    rcases (by omega : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2)) with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp only [hV]
  · simp only [hv]
    rcases (by omega : (i = 0 ∧ j = 0) ∨ (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 1)) with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp only [hH]

/-- A rank-`3` hive with fixed boundary `B` is uniquely determined by its value at the single
interior vertex `(1, 1, 1)`. -/
private theorem fixedIntegerHive_three_ext {B : Fin 3 → Fin 3 → ℤ}
    (k₁ k₂ : FixedIntegerHive B)
    (hmid : k₁.val ⟨1, 1, 1, rfl⟩ = k₂.val ⟨1, 1, 1, rfl⟩) : k₁ = k₂ := by
  refine Subtype.ext <| ext fun p => ?_
  have := p.sum_eq
  by_cases hz : p.z = 0
  · rw [show p = Vertex.edgePoint 3 0 ⟨p.y, by omega⟩ by ext <;> simp [hz]; omega,
      k₁.val.apply_edgePoint_zero, k₂.val.apply_edgePoint_zero, k₁.property, k₂.property]
  · by_cases hx : p.x = 0
    · rw [show p = Vertex.edgePoint 3 1 ⟨p.z, by omega⟩ by ext <;> simp [hx]; omega,
        k₁.val.apply_edgePoint_one, k₂.val.apply_edgePoint_one, k₁.property, k₂.property]
    · by_cases hy : p.y = 0
      · rw [show p = Vertex.edgePoint 3 2 ⟨p.x, by omega⟩ by ext <;> simp [hy]; omega,
          k₁.val.apply_edgePoint_two, k₂.val.apply_edgePoint_two, k₁.property, k₂.property]
      · rw [show p = ⟨1, 1, 1, rfl⟩ by ext <;> simp <;> omega, hmid]

/-- Rhombus bounds on the interior value `k.val (1, 1, 1)` of any rank-`3` product-boundary hive. -/
private theorem apply_center_bounds_three {lam μ γ : DominantWeight 3}
    (k : FixedIntegerHive (productBoundary lam μ γ)) :
    lam.val 0 + lam.val 2 + μ.val 0 ≤ k.val ⟨1, 1, 1, rfl⟩ ∧
      k.val ⟨1, 1, 1, rfl⟩ ≤ lam.val 0 + lam.val 1 + μ.val 0 := by
  have hch12 : Vertex.ofChart 3 1 2 (by decide) (by decide) = ⟨1, 1, 1, rfl⟩ := by ext <;> simp
  have hsumlt (w : DominantWeight 3) (j : ℕ) :
      (∑ r : Fin 3 with r.val < j, w.val r) =
        (if 0 < j then w.val 0 else 0) + (if 1 < j then w.val 1 else 0) +
          (if 2 < j then w.val 2 else 0) := by
    simp [Finset.sum_filter, Fin.sum_univ_three, add_assoc]
  have hrH := k.val.le_of_isRhombus
    (isRhombus_ofChart_diag_x (n := 3) (i := 0) (j := 1) (by decide) (by decide))
  have hrC := k.val.le_of_isRhombus
    (isRhombus_ofChart_diag_y (n := 3) (i := 0) (j := 2) (by decide) (by decide))
  simp only [apply_ofChart_zero_left_of_productBoundary k.property,
    apply_ofChart_right_of_productBoundary k.property, TauCeti.prefixSum_def,
    Fin.sum_univ_three, hsumlt, hch12] at hrH hrC
  simp only [Nat.lt_add_one, Nat.zero_lt_two, Nat.one_lt_ofNat, lt_self_iff_false,
    Nat.not_ofNat_lt_one, ↓reduceIte] at hrH hrC
  omega

/-- Rank-`3` check `c^{(2, 0, 0)}_{(1, 0, 0), (1, 0, 0)} = 1` and the classic multiplicity-two
example `c^{(3, 2, 1)}_{(2, 1, 0), (2, 1, 0)} = 2`, whose unique interior vertex `(1, 1, 1)` takes
the two values `4` and `5`. -/
theorem hiveCount_three_checks :
    hiveCount
      (productBoundary ⟨![1, 0, 0], by decide⟩ ⟨![1, 0, 0], by decide⟩ ⟨![2, 0, 0], by decide⟩) = 1
    ∧ hiveCount
      (productBoundary ⟨![2, 1, 0], by decide⟩ ⟨![2, 1, 0], by decide⟩ ⟨![3, 2, 1], by decide⟩) = 2
    := by
  let B₁ := productBoundary (⟨![1, 0, 0], by decide⟩ : DominantWeight 3)
    ⟨![1, 0, 0], by decide⟩ ⟨![2, 0, 0], by decide⟩
  let B₂ := productBoundary (⟨![2, 1, 0], by decide⟩ : DominantWeight 3)
    ⟨![2, 1, 0], by decide⟩ ⟨![3, 2, 1], by decide⟩
  let c₁ (i j : ℕ) : ℤ := if j = 0 then 0 else if i = 0 then 1 else 2
  let c₂ (m : ℤ) (i j : ℕ) : ℤ :=
    if i = 0 then (if j = 0 then 0 else if j = 1 then 2 else 3)
    else if i = 1 then (if j = 1 then 3 else if j = 2 then m else 5)
    else if j = 2 then 5 else 6
  let h₁ : FixedIntegerHive B₁ :=
    ⟨⟨fun p => c₁ p.z (3 - p.x), by simp [c₁],
        fun hr => (isRhombusConcave_def _).mp
          (isRhombusConcave_of_chartThree c₁ (by decide) (by decide) (by decide)) hr⟩,
      by ext s k; fin_cases s <;> fin_cases k <;>
        simp [B₁, c₁, boundary_apply, productBoundary_zero, productBoundary_one,
          productBoundary_two]⟩
  let mk₂ (m : ℤ) (hm : m = 4 ∨ m = 5) : FixedIntegerHive B₂ :=
    ⟨⟨fun p => c₂ m p.z (3 - p.x), by simp [c₂],
        fun hr => (isRhombusConcave_def _).mp (isRhombusConcave_of_chartThree (c₂ m)
          (by rcases hm with rfl | rfl <;> decide)
          (by rcases hm with rfl | rfl <;> decide)
          (by rcases hm with rfl | rfl <;> decide)) hr⟩,
      by ext s k; fin_cases s <;> fin_cases k <;>
        simp [B₂, c₂, boundary_apply, productBoundary_zero, productBoundary_one,
          productBoundary_two]⟩
  let h₂₄ := mk₂ 4 (Or.inl rfl)
  let h₂₅ := mk₂ 5 (Or.inr rfl)
  constructor
  · rw [← card_fixedIntegerHive]
    refine Fintype.card_eq_one_iff.mpr ⟨h₁, fun k => fixedIntegerHive_three_ext k h₁ ?_⟩
    have hb := apply_center_bounds_three k
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at hb
    have hc₁ : h₁.val ⟨1, 1, 1, rfl⟩ = 2 := rfl
    omega
  · have huniv : (Finset.univ : Finset (FixedIntegerHive B₂)) = {h₂₄, h₂₅} := by
      ext k
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
      have hb := apply_center_bounds_three k
      simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons] at hb
      rcases (by omega : k.val ⟨1, 1, 1, rfl⟩ = 4 ∨ k.val ⟨1, 1, 1, rfl⟩ = 5) with h4 | h5
      · exact Or.inl (fixedIntegerHive_three_ext k h₂₄ h4)
      · exact Or.inr (fixedIntegerHive_three_ext k h₂₅ h5)
    have hne : h₂₄ ≠ h₂₅ := fun h => by
      have hm : (4 : ℤ) = 5 := congrArg (fun k : FixedIntegerHive B₂ => k.val ⟨1, 1, 1, rfl⟩) h
      omega
    rw [← card_fixedIntegerHive, ← Finset.card_univ, huniv, Finset.card_pair hne]

end Signed

end Hive

end TauCeti
