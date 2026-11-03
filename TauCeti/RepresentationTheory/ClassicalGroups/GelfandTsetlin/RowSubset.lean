/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Fin.Basic
public import TauCeti.RepresentationTheory.ClassicalGroups.GelfandTsetlin.AddMonoid
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.GroupTheory.Finiteness

/-!
# Row-subset patterns generate the polynomial Gelfand-Tsetlin patterns

The **row-subset pattern** `TauCeti.GTPattern.rowSubset I` of a set `I` of rows of an `n × n`
matrix has row `j` equal to `(1, …, 1, 0, …, 0)`, with as many ones as there are elements of `I`
below `j`.  Under the correspondence `λ_{c,j} = ∑_{r < j} e(r, c)` between exponents `e` of the
matrix entries `z_{r,c}` and patterns, it is the exponent `∏_c z_{i_c, c}` of the main diagonal of
the minor on the rows `I = {i_0 < ⋯ < i_{d-1}}` and the first `d` columns.  The main result is that
these `2 ^ n` patterns generate the polynomial patterns as an additive monoid: every nonnegative
pattern is the sum of its threshold patterns `[λ_{c,j} ≥ k]`, `k ≥ 1`, and a pattern with entries
in `{0, 1}` is a row-subset pattern.  In particular the monoid of polynomial patterns is finitely
generated, and the pattern of all rows is the constant pattern `1`, whose addition is the
determinant shift `TauCeti.GTPattern.shift 1`.

## Main definitions

* `TauCeti.GTPattern.rowSubset I`: the row-subset pattern of `I : Finset (Fin n)`.

## Main results

* `TauCeti.GTPattern.rowSubset_univ`: the pattern of all rows is the constant pattern `1`.
* `TauCeti.GTPattern.rowSubset_injective`: distinct row subsets give distinct patterns.
* `TauCeti.GTPattern.mem_range_rowSubset`: the row-subset patterns are exactly the patterns with
  entries in `{0, 1}`.
* `TauCeti.GTPattern.closure_range_rowSubset`: the row-subset patterns generate the nonnegative
  patterns, and `TauCeti.GTPattern.fg_nonneg`: that monoid is finitely generated.

## References

* E. Miller and B. Sturmfels, *Combinatorial Commutative Algebra*, GTM 227, Springer, 2005,
  Chapter 14 (Gelfand-Tsetlin patterns as the initial semigroup of the flag-minor algebra).
* M. Kogan and E. Miller, *Toric degeneration of Schubert varieties and Gelfand-Tsetlin
  polytopes*, Adv. Math. **193** (2005), 1-17.
-/

public section

open Finset

namespace TauCeti

namespace GTPattern

variable {n : ℕ}

/-! ### Row-subset patterns -/

/-- The **row-subset pattern** of a set `I` of rows: its row `j` consists of
`#{r ∈ I | r < j}` ones followed by zeros.  For `I = {i_0 < ⋯ < i_{d-1}}` its entry `λ_{c,j}` is
`1` exactly when `c < d` and `i_c < j`; this is the pattern `∑_{r < j} e(r, c)` of the diagonal
exponent `e` of `∏_{c < d} z_{i_c, c}`. -/
def rowSubset (I : Finset (Fin n)) : GTPattern n where
  entry c j := if j ≤ n ∧ c < #{r ∈ I | r.val < j} then 1 else 0
  zeros' := by
    intro c j h
    have := card_filter_val_lt_le I j
    rw [ite_eq_right_iff]
    omega
  interlacing' := by
    intro c j hcj hj
    have h := card_filter_castSucc_lt_succ I ⟨j, hj⟩
    simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at h
    split_ifs at h <;> constructor <;> split_ifs <;> omega

theorem rowSubset_apply (I : Finset (Fin n)) (c j : ℕ) :
    rowSubset I c j = if j ≤ n ∧ c < #{r ∈ I | r.val < j} then 1 else 0 :=
  (rfl)

/-- The top row of the pattern of `I` consists of `#I` ones followed by zeros. -/
@[simp]
theorem topRow_rowSubset (I : Finset (Fin n)) :
    (rowSubset I).topRow = fun i : Fin n => if (i : ℕ) < #I then (1 : ℤ) else 0 := by
  funext i
  rw [topRow_apply, rowSubset_apply, filter_true_of_mem fun r _ => r.2]
  simp

theorem zero_le_rowSubset (I : Finset (Fin n)) : 0 ≤ rowSubset I :=
  zero_le_iff.2 fun c j => by rw [rowSubset_apply]; split_ifs <;> simp

@[simp]
theorem rowSubset_empty : rowSubset (∅ : Finset (Fin n)) = 0 := by
  ext c j
  simp [rowSubset_apply, zero_apply]

/-- **The pattern of all rows is the constant pattern `1`**, the pattern of the determinant;
adding it is the determinant shift `TauCeti.GTPattern.shift 1`. -/
@[simp]
theorem rowSubset_univ : rowSubset (univ : Finset (Fin n)) = const n 1 := by
  ext c j
  rw [rowSubset_apply, const_apply, Fin.card_filter_val_lt]
  by_cases h : j ≤ n
  · simp only [h, true_and, and_true, min_eq_right h]
  · simp [h]

/-- In the pattern of `I`, row `j ≤ n` has exactly `#{r ∈ I | r < j}` nonzero entries. -/
private theorem card_filter_rowSubset_ne_zero (I : Finset (Fin n)) {j : ℕ} (hj : j ≤ n) :
    #{c ∈ range j | rowSubset I c j ≠ 0} = #{r ∈ I | r.val < j} := by
  have hk := card_filter_val_lt_le I j
  have : {c ∈ range j | rowSubset I c j ≠ 0} = range #{r ∈ I | r.val < j} := by
    ext c
    simp only [mem_filter, mem_range, rowSubset_apply, hj, true_and, ne_eq, ite_eq_right_iff,
      one_ne_zero, imp_false, not_not]
    omega
  rw [this, card_range]

/-- **Distinct row subsets give distinct patterns**, so the row-subset patterns are `2 ^ n`
distinct patterns. -/
theorem rowSubset_injective : Function.Injective (rowSubset (n := n)) := by
  intro I J h
  have hcount : ∀ j, j ≤ n → #{r ∈ I | r.val < j} = #{r ∈ J | r.val < j} := fun j hj => by
    rw [← card_filter_rowSubset_ne_zero I hj, ← card_filter_rowSubset_ne_zero J hj, h]
  -- A row `r` belongs to `I` exactly when the count increases from row `r` to row `r + 1`.
  ext r
  have hI := card_filter_castSucc_lt_succ I r
  have hJ := card_filter_castSucc_lt_succ J r
  simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at hI hJ
  rw [hcount _ r.2, hcount _ r.2.le] at hI
  split_ifs at hI hJ <;> simp_all

/-! ### The row-subset patterns generate the nonnegative patterns -/

/-- In a pattern with entries in `{0, 1}`, row `j` is `(1, …, 1, 0, …, 0)`: an informative entry
is `1` exactly when it lies before the number of ones of its row. -/
private theorem eq_one_iff_lt_card {Q : GTPattern n} (hQ : ∀ i j, Q i j = 0 ∨ Q i j = 1)
    {c j : ℕ} (hc : c < j) (hj : j ≤ n) : Q c j = 1 ↔ c < #{c ∈ range j | Q c j = 1} := by
  have hcard : #{c ∈ range j | Q c j = 1} = #{i : Fin j | Q i j = 1} := by
    rw [← card_map Fin.valEmbedding, map_filter' _ Fin.valEmbedding, Fin.map_valEmbedding_univ,
      ← Nat.Iio_eq_range]
    exact congrArg card <| filter_congr fun b hb =>
      ⟨fun h => ⟨⟨b, mem_Iio.1 hb⟩, h, rfl⟩, fun ⟨_, ha, hab⟩ => hab ▸ ha⟩
  rw [hcard]
  -- The entries equal to `1` form an initial segment of the row, since the row decreases.
  refine (Fin.lt_card_filter_univ_iff_apply_of_imp (j := ⟨c, hc⟩) (fun i : Fin j => Q i j = 1)
    fun c' c hcc' h1 => ?_).symm
  have := Q.entry_anti hj hcc' c'.2
  rcases hQ c j with h | h <;> omega

/-- A pattern with entries in `{0, 1}` is a row-subset pattern.  The rows of `I` are those at
which the number of ones increases. -/
private theorem exists_eq_rowSubset {Q : GTPattern n} (hQ : ∀ i j, Q i j = 0 ∨ Q i j = 1) :
    ∃ I : Finset (Fin n), Q = rowSubset I := by
  -- `k j` is the number of ones in row `j`, and row `j` is `(1, …, 1, 0, …, 0)`.
  obtain ⟨k, hk⟩ : ∃ k : ℕ → ℕ, ∀ j, k j = #{c ∈ range j | Q c j = 1} := ⟨_, fun _ => rfl⟩
  have hrow : ∀ {c j}, c < j → j ≤ n → (Q c j = 1 ↔ c < k j) := fun hc hj => by
    rw [hk]
    exact eq_one_iff_lt_card hQ hc hj
  have hk_le : ∀ j, k j ≤ j := fun j => by
    rw [hk]
    exact (card_filter_le _ _).trans (card_range j).le
  -- Consecutive counts differ by `0` or `1`, by the two interlacing inequalities.
  have hk_mono : ∀ j, j < n → k j ≤ k (j + 1) := fun j hj => by
    have := hk_le j
    rcases Nat.eq_zero_or_pos (k j) with h0 | hpos
    · omega
    have h1 : Q (k j - 1) j = 1 := (hrow (by omega) hj.le).2 (by omega)
    have h2 := Q.entry_le_entry_succ_row (i := k j - 1) (by omega) hj
    have h3 : Q (k j - 1) (j + 1) = 1 := by rcases hQ (k j - 1) (j + 1) with h | h <;> omega
    have := (hrow (j := j + 1) (by omega) (by omega)).1 h3
    omega
  have hk_succ : ∀ j, j < n → k (j + 1) ≤ k j + 1 := fun j hj => by
    have := hk_le (j + 1)
    by_cases hlt : k (j + 1) ≤ 1
    · omega
    have h1 : Q (k (j + 1) - 2 + 1) (j + 1) = 1 :=
      (hrow (j := j + 1) (by omega) (by omega)).2 (by omega)
    have h2 := Q.entry_succ_succ_le_entry (i := k (j + 1) - 2) hj
    have h3 : Q (k (j + 1) - 2) j = 1 := by rcases hQ (k (j + 1) - 2) j with h | h <;> omega
    have := (hrow (by omega) hj.le).1 h3
    omega
  -- The rows of `I` are those at which the count increases, so `k j` of them lie below `j`.
  obtain ⟨I, hI⟩ : ∃ I : Finset (Fin n), ∀ r, r ∈ I ↔ k (r.val + 1) = k r.val + 1 :=
    ⟨univ.filter fun r : Fin n => k (r.val + 1) = k r.val + 1, fun r => by simp⟩
  have hcount : ∀ j, j ≤ n → #{r ∈ I | r.val < j} = k j := by
    intro j hj
    induction j with
    | zero => simp [hk]
    | succ j ih =>
      have h := card_filter_castSucc_lt_succ I ⟨j, by omega⟩
      simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at h
      rw [h, ih (by omega)]
      have := hk_mono j (by omega)
      have := hk_succ j (by omega)
      split_ifs with h <;> simp only [hI] at h <;> omega
  refine ⟨I, ?_⟩
  ext c j
  rw [rowSubset_apply]
  by_cases hj : j ≤ n
  · rw [hcount j hj]
    by_cases hcj : c < j
    · split_ifs with h'
      · exact (hrow hcj hj).2 h'.2
      · rcases hQ c j with h | h
        · exact h
        · exact absurd ⟨hj, (hrow hcj hj).1 h⟩ h'
    · rw [Q.entry_eq_zero (Or.inr (by omega)), ite_eq_right (by have := hk_le j; omega)]
  · rw [Q.entry_eq_zero (Or.inl (by omega)), ite_eq_right (by omega)]

/-- **The row-subset patterns are exactly the patterns with entries in `{0, 1}`.** -/
theorem mem_range_rowSubset {Q : GTPattern n} :
    Q ∈ Set.range rowSubset ↔ ∀ i j, Q i j = 0 ∨ Q i j = 1 := by
  refine ⟨?_, fun hQ => ?_⟩
  · rintro ⟨I, rfl⟩ i j
    rw [rowSubset_apply]
    split_ifs <;> simp
  · obtain ⟨I, hI⟩ := exists_eq_rowSubset hQ
    exact ⟨I, hI.symm⟩

/-- The threshold pattern `[λ_{i,j} ≥ k]` of a pattern, on its informative cells. -/
private def threshold (P : GTPattern n) (k : ℤ) : GTPattern n where
  entry i j := if i < j ∧ j ≤ n ∧ k ≤ P i j then 1 else 0
  zeros' := by
    intro i j h
    rw [ite_eq_right_iff]
    omega
  interlacing' := by
    intro i j hij hj
    have h1 := P.entry_le_entry_succ_row hij hj
    have h2 := P.entry_succ_succ_le_entry (i := i) hj
    constructor <;> split_ifs <;> omega

private theorem threshold_apply (P : GTPattern n) (k : ℤ) (i j : ℕ) :
    threshold P k i j = if i < j ∧ j ≤ n ∧ k ≤ P i j then 1 else 0 :=
  (rfl)

/-- A nonnegative pattern is the sum of its threshold patterns `[λ_{i,j} ≥ k]`, `1 ≤ k ≤ N`, for
any bound `N` on its entries. -/
private theorem sum_threshold {P : GTPattern n} (hP : 0 ≤ P) {N : ℤ} (hN : ∀ i j, P i j ≤ N) :
    ∑ k ∈ Icc 1 N, threshold P k = P := by
  ext i j
  rw [coe_sum, Finset.sum_apply, Finset.sum_apply]
  simp only [threshold_apply]
  by_cases h : i < j ∧ j ≤ n
  · simp only [h, true_and]
    rw [sum_boole, filter_congr (p := fun k => k ≤ P i j) (q := fun k => k ∈ Icc 1 (P i j))
      (fun k hk => by simp only [mem_Icc] at hk ⊢; have := hN i j; omega),
      filter_mem_eq_inter, inter_eq_right.2 (Icc_subset_Icc le_rfl (hN i j)), Int.card_Icc]
    have := zero_le_iff.1 hP i j
    simp only [add_sub_cancel_right, Int.toNat_of_nonneg this]
  · rw [P.entry_eq_zero (by omega)]
    exact sum_eq_zero fun k _ => ite_eq_right fun h' => h ⟨h'.1, h'.2.1⟩

/-- **The row-subset patterns generate the nonnegative patterns.**  The additive monoid of
polynomial Gelfand-Tsetlin patterns is generated by the `2 ^ n` patterns
`TauCeti.GTPattern.rowSubset I`, `I ⊆ {0, …, n - 1}`. -/
theorem closure_range_rowSubset :
    AddSubmonoid.closure (Set.range (rowSubset (n := n))) = AddSubmonoid.nonneg (GTPattern n) := by
  apply le_antisymm
  · rw [AddSubmonoid.closure_le]
    rintro _ ⟨I, rfl⟩
    exact zero_le_rowSubset I
  · intro P (hP : 0 ≤ P)
    have hN : ∀ i j, P i j ≤ ∑ i' ∈ range (n + 1), ∑ j' ∈ range (n + 1), |P i' j'| :=
      fun i j => (le_abs_self _).trans (abs_le_sum_abs P i j)
    rw [← sum_threshold hP hN]
    refine AddSubmonoid.sum_mem _ fun k _ => AddSubmonoid.subset_closure ?_
    refine mem_range_rowSubset.2 fun i j => ?_
    rw [threshold_apply]
    split_ifs <;> simp

/-- **The monoid of polynomial Gelfand-Tsetlin patterns is finitely generated.** -/
theorem fg_nonneg : (AddSubmonoid.nonneg (GTPattern n)).FG :=
  AddSubmonoid.fg_iff _ |>.2 ⟨_, closure_range_rowSubset, Set.finite_range _⟩

end GTPattern

end TauCeti
