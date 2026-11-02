/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Fin.Basic
public import TauCeti.RepresentationTheory.ClassicalGroups.GelfandTsetlin.Shift
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Pi
public import Mathlib.GroupTheory.Finiteness

/-!
# The additive monoid of Gelfand-Tsetlin patterns

The interlacing inequalities defining a Gelfand-Tsetlin pattern are homogeneous linear
inequalities between entries, so patterns can be added entrywise: `TauCeti.GTPattern n` is an
ordered cancellative commutative monoid for the pointwise addition and order of its entries.  It is
not a group, since negating a pattern reverses its inequalities.  The determinant translation
`TauCeti.GTPattern.shift` is addition of the constant pattern `TauCeti.GTPattern.const`, and the
polynomial patterns, those with nonnegative entries, form Mathlib's submonoid
`AddSubmonoid.nonneg (GTPattern n)`.

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

* `TauCeti.GTPattern.instAddCancelCommMonoid`, `TauCeti.GTPattern.instPartialOrder` and
  `TauCeti.GTPattern.instIsOrderedCancelAddMonoid`: the entrywise additive and order structures.
* `TauCeti.GTPattern.const n m`: the pattern all of whose informative entries equal `m`.
* `TauCeti.GTPattern.rowSubset I`: the row-subset pattern of `I : Finset (Fin n)`.

## Main results

* `TauCeti.GTPattern.shift_eq_add_const`: the determinant shift by `m` adds `const n m`.
* `TauCeti.GTPattern.zero_le_iff_isPolynomial`: a pattern is nonnegative exactly when its top
  weight is polynomial.
* `TauCeti.GTPattern.exists_zero_le_shift`: every pattern becomes nonnegative after a determinant
  shift by a natural number.
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

/-! ### The entrywise additive monoid -/

instance : Zero (GTPattern n) where
  zero := ⟨0, fun _ => rfl, fun _ _ => ⟨le_rfl, le_rfl⟩⟩

instance : Add (GTPattern n) where
  add P Q :=
    ⟨⇑P + ⇑Q, fun h => by simp [P.entry_eq_zero h, Q.entry_eq_zero h], fun hij hj =>
      ⟨add_le_add (P.entry_le_entry_succ_row hij hj) (Q.entry_le_entry_succ_row hij hj),
        add_le_add (P.entry_succ_succ_le_entry hj) (Q.entry_succ_succ_le_entry hj)⟩⟩

instance : SMul ℕ (GTPattern n) where
  smul k P :=
    ⟨k • ⇑P, fun h => by simp [P.entry_eq_zero h], fun hij hj => by
      simp only [Pi.smul_apply]
      exact ⟨by gcongr; exact P.entry_le_entry_succ_row hij hj,
        by gcongr; exact P.entry_succ_succ_le_entry hj⟩⟩

@[simp, norm_cast]
theorem coe_zero : ⇑(0 : GTPattern n) = 0 :=
  (rfl)

@[simp, norm_cast]
theorem coe_add (P Q : GTPattern n) : ⇑(P + Q) = ⇑P + ⇑Q :=
  (rfl)

@[simp, norm_cast]
theorem coe_nsmul (k : ℕ) (P : GTPattern n) : ⇑(k • P) = k • ⇑P :=
  (rfl)

theorem zero_apply (i j : ℕ) : (0 : GTPattern n) i j = 0 :=
  (rfl)

theorem add_apply (P Q : GTPattern n) (i j : ℕ) : (P + Q) i j = P i j + Q i j :=
  (rfl)

theorem nsmul_apply (k : ℕ) (P : GTPattern n) (i j : ℕ) : (k • P) i j = k • P i j :=
  (rfl)

/-- Gelfand-Tsetlin patterns form a cancellative commutative monoid under entrywise addition. -/
instance instAddCancelCommMonoid : AddCancelCommMonoid (GTPattern n) :=
  DFunLike.coe_injective.addCancelCommMonoid _ coe_zero coe_add fun _ _ => coe_nsmul _ _

/-- The array of entries of a pattern, as an additive monoid homomorphism. -/
def coeFnAddMonoidHom : GTPattern n →+ ℕ → ℕ → ℤ where
  toFun := (⇑)
  map_zero' := coe_zero
  map_add' := coe_add

@[simp]
theorem coeFnAddMonoidHom_apply (P : GTPattern n) : coeFnAddMonoidHom P = ⇑P :=
  (rfl)

@[simp, norm_cast]
theorem coe_sum {ι : Type*} (s : Finset ι) (P : ι → GTPattern n) :
    ⇑(∑ i ∈ s, P i) = ∑ i ∈ s, ⇑(P i) :=
  map_sum coeFnAddMonoidHom P s

@[simp]
theorem topRow_zero : (0 : GTPattern n).topRow = 0 := by
  funext i
  rw [topRow_apply, zero_apply, Pi.zero_apply]

@[simp]
theorem topRow_add (P Q : GTPattern n) : (P + Q).topRow = P.topRow + Q.topRow := by
  funext i
  rw [topRow_apply, add_apply, Pi.add_apply, topRow_apply, topRow_apply]

@[simp]
theorem topRow_nsmul (k : ℕ) (P : GTPattern n) : (k • P).topRow = k • P.topRow := by
  funext i
  rw [topRow_apply, nsmul_apply, Pi.smul_apply, topRow_apply]

/-! ### The entrywise order -/

/-- Gelfand-Tsetlin patterns are ordered entrywise. -/
instance instPartialOrder : PartialOrder (GTPattern n) :=
  PartialOrder.lift (⇑) DFunLike.coe_injective

@[simp, norm_cast]
theorem coe_le_coe {P Q : GTPattern n} : ⇑P ≤ ⇑Q ↔ P ≤ Q :=
  Iff.rfl

theorem le_def {P Q : GTPattern n} : P ≤ Q ↔ ∀ i j, P i j ≤ Q i j :=
  Iff.rfl

/-- The entrywise order is compatible with entrywise addition. -/
instance instIsOrderedCancelAddMonoid : IsOrderedCancelAddMonoid (GTPattern n) :=
  Function.Injective.isOrderedCancelAddMonoid _ coe_add coe_le_coe

theorem zero_le_iff {P : GTPattern n} : 0 ≤ P ↔ ∀ i j, 0 ≤ P i j :=
  le_def

/-- A pattern is nonnegative exactly when its top row is: every entry dominates an entry of the
top row. -/
theorem zero_le_iff_topRow {P : GTPattern n} : 0 ≤ P ↔ ∀ i, 0 ≤ P.topRow i :=
  ⟨fun h i => by rw [topRow_apply]; exact zero_le_iff.1 h _ _,
    fun h => zero_le_iff.2 (P.entry_nonneg h)⟩

/-- The nonnegative patterns are those whose top weight is polynomial. -/
theorem zero_le_iff_isPolynomial {P : GTPattern n} : 0 ≤ P ↔ P.topWeight.IsPolynomial := by
  rw [DominantWeight.isPolynomial_iff_zero_le_detShift, zero_le_iff_topRow]
  refine ⟨fun h => ?_, fun h i => ?_⟩
  · cases n with
    | zero => exact (DominantWeight.detShift_eq_zero_of_isEmpty _).ge
    | succ n => rw [DominantWeight.detShift_succ, topWeight_coe]; exact h _
  · simpa using h.trans (P.topWeight.detShift_le i)

/-! ### Constant patterns and determinant shifts -/

/-- The constant pattern: every informative entry equals `m`.  Adding it to a pattern is the
determinant shift by `m` (`TauCeti.GTPattern.shift_eq_add_const`). -/
def const (n : ℕ) (m : ℤ) : GTPattern n :=
  (0 : GTPattern n).shift m

theorem const_apply (m : ℤ) (i j : ℕ) : const n m i j = if i < j ∧ j ≤ n then m else 0 := by
  rw [const, shift_apply, zero_apply, zero_add]

@[simp]
theorem const_apply_of_lt_of_le (m : ℤ) {i j : ℕ} (hij : i < j) (hj : j ≤ n) :
    const n m i j = m := by
  rw [const_apply, ite_eq_left_iff.2 fun h => absurd ⟨hij, hj⟩ h]

@[simp]
theorem topRow_const (m : ℤ) : (const n m).topRow = fun _ => m := by
  funext i
  rw [topRow_apply]
  exact const_apply_of_lt_of_le m i.2 le_rfl

@[simp]
theorem const_zero : const n 0 = 0 :=
  shift_zero 0

theorem const_add (m m' : ℤ) : const n (m + m') = const n m + const n m' := by
  ext i j
  rw [add_apply, const_apply, const_apply, const_apply]
  split_ifs <;> simp

/-- **The determinant shift is addition of a constant pattern.** -/
theorem shift_eq_add_const (P : GTPattern n) (m : ℤ) : P.shift m = P + const n m := by
  ext i j
  rw [add_apply, shift_apply, const_apply]
  split_ifs with h
  · rfl
  · rw [P.entry_eq_zero (by omega), add_zero]

/-- Every entry of a pattern is bounded in absolute value by the sum of the absolute values of
the entries `λ_{i,j}` with `i, j ≤ n`, which contain all the informative ones. -/
private theorem abs_le_sum_abs (P : GTPattern n) (i j : ℕ) :
    |P i j| ≤ ∑ i' ∈ range (n + 1), ∑ j' ∈ range (n + 1), |P i' j'| := by
  have hnn : ∀ i', 0 ≤ ∑ j' ∈ range (n + 1), |P i' j'| := fun _ =>
    sum_nonneg fun _ _ => abs_nonneg _
  by_cases h : i < j ∧ j ≤ n
  · calc |P i j| ≤ ∑ j' ∈ range (n + 1), |P i j'| :=
          single_le_sum (f := fun j' => |P i j'|) (fun _ _ => abs_nonneg _)
            (mem_range.2 (by omega))
      _ ≤ _ := single_le_sum (f := fun i' => ∑ j' ∈ range (n + 1), |P i' j'|)
            (fun i' _ => hnn i') (mem_range.2 (by omega))
  · rw [P.entry_eq_zero (by omega), abs_zero]
    exact sum_nonneg fun i' _ => hnn i'

/-- **Every pattern is a polynomial pattern up to a determinant shift**: some shift by a natural
number makes all of its entries nonnegative. -/
theorem exists_zero_le_shift (P : GTPattern n) : ∃ m : ℕ, 0 ≤ P.shift m := by
  refine ⟨(∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1), |P i j|).toNat,
    zero_le_iff.2 fun i j => ?_⟩
  rw [shift_apply]
  split_ifs
  · have := abs_le_sum_abs P i j
    have := neg_abs_le (P i j)
    have := Int.self_le_toNat (∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1), |P i j|)
    omega
  · exact le_rfl

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
    have h := card_filter_val_lt_add_one I hj
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
  have hI := card_filter_val_lt_add_one I r.2
  have hJ := card_filter_val_lt_add_one J r.2
  rw [hcount _ r.2, hcount _ r.2.le, Fin.eta] at hI
  rw [Fin.eta] at hJ
  split_ifs at hI hJ <;> simp_all

/-! ### The row-subset patterns generate the nonnegative patterns -/

/-- In a pattern with entries in `{0, 1}`, row `j` is `(1, …, 1, 0, …, 0)`: an informative entry
is `1` exactly when it lies before the number of ones of its row. -/
private theorem eq_one_iff_lt_card {Q : GTPattern n} (hQ : ∀ i j, Q i j = 0 ∨ Q i j = 1)
    {c j : ℕ} (hc : c < j) (hj : j ≤ n) : Q c j = 1 ↔ c < #{c ∈ range j | Q c j = 1} := by
  -- The entries equal to `1` form an initial segment of the row, since the row decreases.
  have hdown : ∀ {c c'}, c ≤ c' → c' < j → Q c' j = 1 → Q c j = 1 := fun {c c'} hcc' hc' h1 => by
    have := Q.entry_anti hj hcc' hc'
    rcases hQ c j with h | h <;> omega
  constructor
  · intro h
    have : range (c + 1) ⊆ {c ∈ range j | Q c j = 1} := fun x hx => by
      rw [mem_range] at hx
      exact mem_filter.2 ⟨mem_range.2 (by omega), hdown (by omega) hc h⟩
    simpa using card_le_card this
  · intro h
    by_contra hc1
    have : {c ∈ range j | Q c j = 1} ⊆ range c := fun x hx => by
      rw [mem_filter, mem_range] at hx
      rw [mem_range]
      by_contra hxc
      exact hc1 (hdown (by omega) hx.1 hx.2)
    have := card_le_card this
    rw [card_range] at this
    omega

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
      rw [card_filter_val_lt_add_one I (by omega : j < n), ih (by omega)]
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
