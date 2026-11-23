/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hive.GelfandTsetlin
public import TauCeti.Combinatorics.Young.LittlewoodRichardson.Basic

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
* `TauCeti.Hive.fixedIntegerHiveEquivLRTableau`: the hive–tableau bijection.

## Main results

* `TauCeti.Hive.hiveCount_productBoundary_eq_natCard_lrTableau`: the hive count of `(λ, μ, γ*)`
  is the Littlewood–Richardson coefficient `c^γ_{λ μ}`.
* `TauCeti.Hive.hiveCount_productBoundary_eq_natCard_lrTableau_shape`,
  `TauCeti.Hive.hiveCount_productBoundary_eq_natCard_lrTableau_shift`: the same for polynomial
  dominant weights of `GL n`, and for arbitrary dominant weights after determinant shifts making
  them polynomial.

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
      YoungDiagram.rowLen_eq_zero_iff.mpr (h.hγ.trans hr), Nat.zero_sub]

private theorem le (h : IsLRPattern n lam γ μ P) : lam ≤ γ := by
  refine YoungDiagram.le_of_forall_rowLen_le fun r => ?_
  rcases lt_or_ge r n with hr | hr
  · have hs := sum_range_natCast_gtRowCount_of_lt h.topRow_nonneg h.weight hr hr
    have : (0 : ℤ) ≤ ∑ k ∈ range n, (gtRowCount P r k : ℤ) := sum_nonneg fun _ _ => by positivity
    omega
  · rw [YoungDiagram.rowLen_eq_zero_iff.mpr (h.hlam.trans hr)]; exact Nat.zero_le _

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
    rw [hs, YoungDiagram.rowLen_eq_zero_iff.mpr (h.hμ.trans hk)]

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

end Hive

end TauCeti
