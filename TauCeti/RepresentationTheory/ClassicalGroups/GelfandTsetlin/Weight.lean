/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.GelfandTsetlin.Shift
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Abel
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
semistandard Young tableaux, `P.weight` agrees with `SemistandardYoungTableau.content`.

## Main definitions

* `TauCeti.GTPattern.rowSum`: the sum `∑ k ∈ Finset.range j, P k j` of row `j` of a pattern.
* `TauCeti.GTPattern.weight`: the torus weight `fun r => P.rowSum (r + 1) - P.rowSum r`.
* `TauCeti.GTPattern.weightAddMonoidHom`: `GTPattern.weight` bundled as an additive monoid
  homomorphism `GTPattern n →+ (Fin n → ℤ)`.

## Main results

* `TauCeti.GTPattern.sum_weight_lt` and `TauCeti.GTPattern.sum_weight`: leading partial sums of
  `P.weight` recover `P.rowSum`, and the total sum equals `∑ i, P.topRow i`.
* `TauCeti.GTPattern.weight_shift`: determinant translation by `m` shifts every entry of `P.weight`
  by `m`.
* `TauCeti.GTPattern.weight_mem_Icc`: every entry of `P.weight` lies between the last and first
  entries of `P.topRow`, so nonnegative patterns have nonnegative weights (`weight_nonneg`).
* `SemistandardYoungTableau.weight_toGTPattern` and `TauCeti.GTPattern.natCast_content_toTableau`:
  under the pattern–tableau correspondence, `GTPattern.weight` equals tableau `content`.

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
theorem rowSum_of_lt (P : GTPattern n) {j : ℕ} (hj : n < j) : P.rowSum j = 0 := by
  simp [rowSum_def, P.entry_eq_zero_of_lt hj]

/-- The sum of row `n` is the sum of `P.topRow`. -/
theorem rowSum_top (P : GTPattern n) : P.rowSum n = ∑ i : Fin n, P.topRow i := by
  rw [rowSum_def, ← Fin.sum_univ_eq_sum_range]
  simp [topRow_apply]

@[simp]
theorem zero_rowSum (j : ℕ) : (0 : GTPattern n).rowSum j = 0 := by
  simp [rowSum_def, zero_apply]

@[simp]
theorem add_rowSum (P Q : GTPattern n) (j : ℕ) :
    (P + Q).rowSum j = P.rowSum j + Q.rowSum j := by
  simp [rowSum_def, add_apply, Finset.sum_add_distrib]

@[simp]
theorem nsmul_rowSum (k : ℕ) (P : GTPattern n) (j : ℕ) :
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
  ext r; simp only [weight_apply, Pi.add_apply, add_rowSum]; abel

@[simp]
theorem weight_nsmul (k : ℕ) (P : GTPattern n) : (k • P).weight = k • P.weight := by
  ext r
  simp only [weight_apply, Pi.smul_apply, nsmul_rowSum, nsmul_eq_mul]
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
theorem sum_weight_lt (P : GTPattern n) {j : ℕ} (hj : j ≤ n) :
    (∑ r : Fin n with r.val < j, P.weight r) = P.rowSum j := by
  have hmap : ({r : Fin n | r.val < j} : Finset (Fin n)) = Finset.univ.map (Fin.castLEEmb hj) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Fin.castLEEmb_apply]
    exact ⟨fun hr => ⟨⟨r.val, hr⟩, Fin.ext rfl⟩, fun ⟨s, hs⟩ => hs ▸ s.isLt⟩
  rw [hmap, Finset.sum_map]
  have hfin : (∑ s : Fin j, P.weight (Fin.castLEEmb hj s)) =
      ∑ k ∈ Finset.range j, (P.rowSum (k + 1) - P.rowSum k) := by
    rw [← Fin.sum_univ_eq_sum_range]
    rfl
  rw [hfin, Finset.sum_range_sub, P.rowSum_zero, sub_zero]

/-- The entries of `P.weight` sum to the sum of `P.topRow`. -/
@[simp]
theorem sum_weight (P : GTPattern n) : (∑ r : Fin n, P.weight r) = ∑ i : Fin n, P.topRow i := by
  have hall : ({r : Fin n | r.val < n} : Finset (Fin n)) = Finset.univ := by
    ext r; simp
  simpa [hall, P.rowSum_top] using P.sum_weight_lt le_rfl

@[simp]
theorem weight_truncate (P : GTPattern (n + 1)) (r : Fin n) :
    P.truncate.weight r = P.weight r.castSucc := by
  rw [weight_apply, weight_apply, Fin.val_castSucc,
    P.rowSum_truncate (by omega), P.rowSum_truncate (by omega)]

@[simp]
theorem weight_extend_castSucc (Q : GTPattern n) (l : Fin (n + 1) → ℤ) (h : Interlaces l Q.topRow)
    (r : Fin n) : (Q.extend l h).weight r.castSucc = Q.weight r := by
  rw [← weight_truncate, truncate_extend]

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

/-- Any refinement of a fixed-top-row pattern subtype is finite. -/
instance finite_topRow_eq_and (l : Fin n → ℤ) (p : GTPattern n → Prop) :
    Finite {P : GTPattern n // P.topRow = l ∧ p P} :=
  Finite.of_injective (fun P => (⟨P.1, P.2.1⟩ : {P : GTPattern n // P.topRow = l}))
    fun _ _ h => Subtype.ext (by simpa using h)

end TauCeti.GTPattern

namespace SemistandardYoungTableau

variable {μ : YoungDiagram}

/-- For `j ≤ n`, row `j` of `T.toGTPattern n` sums to the number of cells of `μ` carrying entries
below `j`, i.e., `∑ k ∈ Finset.range j, (T.content k : ℤ)`. -/
theorem rowSum_toGTPattern (T : SemistandardYoungTableau μ) (n : ℕ) {j : ℕ} (hj : j ≤ n) :
    (T.toGTPattern n).rowSum j = ∑ k ∈ Finset.range j, (T.content k : ℤ) := by
  have hnj : ¬ n < j := Nat.not_lt.mpr hj
  rw [TauCeti.GTPattern.rowSum_def, ← Nat.cast_sum, sum_content_eq_card_filter]
  have hpart : ({c ∈ μ.cells | T c.1 c.2 < j}).card =
      ∑ i ∈ Finset.range j,
        (({c ∈ μ.cells | T c.1 c.2 < j}).filter fun c => c.1 = i).card := by
    refine Finset.card_eq_sum_card_fiberwise fun c hc => ?_
    have hc' := T.filter_entry_lt_subset_filter_fst_lt j (Finset.mem_coe.mp hc)
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hc').2
  rw [hpart, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [toGTPattern_apply, patternEntry_def, ite_eq_right hnj, Nat.cast_inj]
  refine Finset.card_bij (fun col _ => (i, col)) (fun col hcol => ?_)
    (fun _ _ _ _ h => Prod.mk.inj h |>.2) (fun c hc => ?_)
  · obtain ⟨hcr, hlt⟩ := Finset.mem_filter.mp hcol
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨(YoungDiagram.mem_cells (i, col)).mpr
          (YoungDiagram.mem_iff_lt_rowLen.mpr (Finset.mem_range.mp hcr)),
        hlt⟩, rfl⟩
  · obtain ⟨hmem, rfl⟩ := Finset.mem_filter.mp hc
    obtain ⟨hcell, hlt⟩ := Finset.mem_filter.mp hmem
    exact ⟨c.2, Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr
          (YoungDiagram.mem_iff_lt_rowLen.mp ((YoungDiagram.mem_cells c).mp hcell)),
        hlt⟩, Prod.eta c⟩

/-- The weight of the Gelfand–Tsetlin pattern read off a semistandard Young tableau `T` agrees on
`Fin n` with `T.content`. -/
@[simp]
theorem weight_toGTPattern (T : SemistandardYoungTableau μ) (n : ℕ) (r : Fin n) :
    (T.toGTPattern n).weight r = (T.content r.val : ℤ) := by
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
  rw [← SemistandardYoungTableau.weight_toGTPattern (P.toTableau hμ hP) n r, hinv]

end TauCeti.GTPattern
