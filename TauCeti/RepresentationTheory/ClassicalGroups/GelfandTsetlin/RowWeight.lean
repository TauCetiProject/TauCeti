/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.BigOperators.Finset.PartialSum
public import TauCeti.RepresentationTheory.ClassicalGroups.GelfandTsetlin.Shift
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Row sums and torus weights of Gelfand–Tsetlin patterns

Along the chain `GL 0 ⊂ GL 1 ⊂ ⋯ ⊂ GL n`, the `j`-th row `(P 0 j, …, P (j - 1) j)` of a signed
Gelfand–Tsetlin pattern `P : GTPattern n` records the highest weight on `GL j`, so the `j`-th
determinant character acts with exponent `P.rowSum j = ∑_{k < j} P k j`. Consequently, the `r`-th
coordinate of the diagonal torus of `GL n` acts on the Gelfand–Tsetlin line `gtLine λ P` with
weight `P.rowWeight r = P.rowSum (r + 1) - P.rowSum r`, the empty row `j = 0` having sum zero.

Both `GTPattern.rowSum` and `GTPattern.rowWeight` respect the entrywise additive monoid structure on
`GTPattern n`, commute as expected with `GTPattern.const` and `GTPattern.shift`, and telescope via
`TauCeti.prefixSum`: `prefixSum j P.rowWeight = P.rowSum j` for `j ≤ n`, so the coordinates of
`P.rowWeight` sum to `∑ r, P.topRow r`.

## Main definitions

* `TauCeti.GTPattern.rowSum`: the `j`-th row sum `∑_{k < j} P k j` of `P : GTPattern n`.
* `TauCeti.GTPattern.rowWeight`: the torus weight `r ↦ P.rowSum (r + 1) - P.rowSum r` in
  `Fin n → ℤ`.
* `TauCeti.GTPattern.rowWeightAddMonoidHom`: `GTPattern.rowWeight` as an additive monoid
  homomorphism `GTPattern n →+ (Fin n → ℤ)`.

## Main results

* `TauCeti.GTPattern.prefixSum_rowWeight`: `prefixSum j P.rowWeight = P.rowSum j` for `j ≤ n`.
* `TauCeti.GTPattern.sum_rowWeight`: the coordinates of `P.rowWeight` sum to `∑ r, P.topRow r`.
* `TauCeti.GTPattern.rowWeight_shift`: shifting a pattern by `m` adds `m` to each coordinate of its
  row weight.
* `TauCeti.GTPattern.card_topRow_rowWeight_three_one_zero_neg_one_zero`: the zero-weight fibre over
  the `GL 3` adjoint highest weight `(1, 0, -1)` has cardinality `2` and contains a pattern with a
  negative interior entry.

## References

* I. M. Gelfand and M. L. Tsetlin, *Finite-dimensional representations of the group of unimodular
  matrices*, Doklady Akad. Nauk SSSR **71** (1950), 825–828.
* A. Molev, *Yangians and Classical Lie Algebras* (2007), §2.2.
-/

public section

open scoped BigOperators

namespace TauCeti.GTPattern

variable {n : ℕ}

/-- The sum `∑_{k < j} P k j` of the `j`-th row of a Gelfand–Tsetlin pattern `P : GTPattern n`,
with `P.rowSum 0 = 0`. -/
def rowSum (P : GTPattern n) (j : ℕ) : ℤ :=
  ∑ k ∈ Finset.range j, P k j

theorem rowSum_def (P : GTPattern n) (j : ℕ) :
    P.rowSum j = ∑ k ∈ Finset.range j, P k j := (rfl)

@[simp] theorem rowSum_zero_right (P : GTPattern n) : P.rowSum 0 = 0 := by
  simp [rowSum_def]

@[simp] theorem rowSum_zero_left (j : ℕ) : (0 : GTPattern n).rowSum j = 0 := by
  simp [rowSum_def]

@[simp] theorem rowSum_add (P Q : GTPattern n) (j : ℕ) :
    (P + Q).rowSum j = P.rowSum j + Q.rowSum j := by
  simp [rowSum_def, Finset.sum_add_distrib]

@[simp] theorem rowSum_nsmul (k : ℕ) (P : GTPattern n) (j : ℕ) :
    (k • P).rowSum j = k • P.rowSum j := by
  simp [rowSum_def, Finset.mul_sum]

theorem rowSum_of_gt (P : GTPattern n) {j : ℕ} (hj : n < j) : P.rowSum j = 0 := by
  simp [rowSum_def, P.entry_eq_zero_of_lt hj]

theorem rowSum_last (P : GTPattern n) :
    P.rowSum n = ∑ r : Fin n, P.topRow r := by
  rw [rowSum_def, ← Fin.sum_univ_eq_sum_range (fun k => P k n) n]
  simp_rw [topRow_apply]

theorem rowSum_shift_of_le (P : GTPattern n) (m : ℤ) {j : ℕ} (hjn : j ≤ n) :
    (P.shift m).rowSum j = P.rowSum j + j * m := by
  rw [rowSum_def, rowSum_def]
  have hcongr : ∑ k ∈ Finset.range j, P.shift m k j = ∑ k ∈ Finset.range j, (P k j + m) :=
    Finset.sum_congr rfl fun k hk => P.shift_apply_of_lt_of_le m (Finset.mem_range.mp hk) hjn
  rw [hcongr, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem rowSum_truncate (P : GTPattern (n + 1)) {j : ℕ} (hjn : j ≤ n) :
    P.truncate.rowSum j = P.rowSum j := by
  rw [rowSum_def, rowSum_def]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [truncate_apply, ite_eq_left hjn]

/-- The diagonal-torus weight of `P : GTPattern n` as successive row-sum differences
`r ↦ P.rowSum (r + 1) - P.rowSum r`, the empty row `j = 0` having sum zero. -/
def rowWeight (P : GTPattern n) : Fin n → ℤ := fun r =>
  P.rowSum (r.val + 1) - P.rowSum r.val

@[simp] theorem rowWeight_apply (P : GTPattern n) (r : Fin n) :
    P.rowWeight r = P.rowSum (r.val + 1) - P.rowSum r.val := (rfl)

theorem rowWeight_eq_sum_sub_sum (P : GTPattern n) (r : Fin n) :
    P.rowWeight r =
      (∑ k ∈ Finset.range (r.val + 1), P k (r.val + 1)) - ∑ k ∈ Finset.range r.val, P k r.val :=
  (rfl)

@[simp] theorem rowWeight_zero : (0 : GTPattern n).rowWeight = 0 := by
  ext r; simp

@[simp] theorem rowWeight_add (P Q : GTPattern n) :
    (P + Q).rowWeight = P.rowWeight + Q.rowWeight := by
  ext r
  simp only [Pi.add_apply, rowWeight_apply, rowSum_add]
  omega

@[simp] theorem rowWeight_nsmul (k : ℕ) (P : GTPattern n) :
    (k • P).rowWeight = k • P.rowWeight := by
  ext r
  simp only [Pi.smul_apply, rowWeight_apply, rowSum_nsmul, nsmul_eq_mul]
  ring

/-- `GTPattern.rowWeight` as an additive monoid homomorphism `GTPattern n →+ (Fin n → ℤ)`. -/
def rowWeightAddMonoidHom (n : ℕ) : GTPattern n →+ (Fin n → ℤ) where
  toFun := rowWeight
  map_zero' := rowWeight_zero
  map_add' := rowWeight_add

@[simp] theorem rowWeightAddMonoidHom_apply (P : GTPattern n) :
    rowWeightAddMonoidHom n P = P.rowWeight := (rfl)

/-- Determinant-shifting every informative entry of `P` by `m` adds `m` to every coordinate of
`P.rowWeight`. -/
@[simp] theorem rowWeight_shift (P : GTPattern n) (m : ℤ) :
    (P.shift m).rowWeight = fun r => P.rowWeight r + m := by
  ext r
  rw [rowWeight_apply, rowWeight_apply, P.rowSum_shift_of_le m r.isLt,
    P.rowSum_shift_of_le m (Nat.le_of_lt r.isLt)]
  push_cast
  ring

@[simp] theorem rowWeight_const (m : ℤ) : (const n m).rowWeight = fun _ => m := by
  have hc : const n m = (0 : GTPattern n).shift m := by
    rw [shift_eq_add_const, zero_add]
  rw [hc, rowWeight_shift]
  simp

/-- The prefix sum of the first `j` coordinates of `P.rowWeight` (`j ≤ n`) telescopes to
`P.rowSum j`. -/
@[simp] theorem prefixSum_rowWeight (P : GTPattern n) {j : ℕ} (hjn : j ≤ n) :
    prefixSum j P.rowWeight = P.rowSum j := by
  induction j with
  | zero => simp
  | succ m ih =>
    rw [prefixSum_succ (by omega) P.rowWeight, ih (by omega), rowWeight_apply]
    dsimp only
    omega

/-- The coordinates of `P.rowWeight` sum to the sum of the top row of `P`. -/
theorem sum_rowWeight (P : GTPattern n) :
    (∑ r : Fin n, P.rowWeight r) = ∑ r : Fin n, P.topRow r := by
  rw [← prefixSum_of_le le_rfl P.rowWeight, P.prefixSum_rowWeight le_rfl, P.rowSum_last]

/-! ### Zero-weight fibre of the `GL 3` adjoint highest weight `(1, 0, -1)` -/

section AdjointThree

private def mkTwo (a b₀ b₁ : ℤ) (hlo : b₁ ≤ a) (hhi : a ≤ b₀) : GTPattern 2 :=
  ((default : GTPattern 0).extend ![a] (interlaces_iff.mpr fun i => i.elim0)).extend ![b₀, b₁]
    (interlaces_iff.mpr fun i => by fin_cases i; simp [hlo, hhi])

private def adjointZeroOne : GTPattern 3 :=
  (mkTwo 0 0 0 le_rfl le_rfl).extend ![1, 0, -1]
    (interlaces_iff.mpr fun i => by fin_cases i <;> simp [mkTwo])

private def adjointZeroTwo : GTPattern 3 :=
  (mkTwo 0 1 (-1) (by decide) (by decide)).extend ![1, 0, -1]
    (interlaces_iff.mpr fun i => by fin_cases i <;> simp [mkTwo])

/-- The zero-weight fibre over `(1, 0, -1)` contains a pattern with a negative interior entry. -/
theorem exists_neg_entry_three_one_zero_neg_one_zero :
    ∃ P : GTPattern 3, P.topRow = ![1, 0, -1] ∧ P.rowWeight = 0 ∧ P 1 2 < 0 := by
  refine ⟨adjointZeroTwo, by simp [adjointZeroTwo], ?_, by simp [adjointZeroTwo, mkTwo]⟩
  ext r; fin_cases r <;> simp [adjointZeroTwo, mkTwo, rowSum_def, Finset.sum_range_succ]

/-- In `GL 3`, the zero-weight Gelfand–Tsetlin fibre over the adjoint highest weight `(1, 0, -1)`
has cardinality `2` (matching the dimension of the Cartan subalgebra of `𝔰𝔩 3`). -/
theorem card_topRow_rowWeight_three_one_zero_neg_one_zero :
    Nat.card {P : GTPattern 3 // P.topRow = ![1, 0, -1] ∧ P.rowWeight = 0} = 2 := by
  have h1 : adjointZeroOne.topRow = ![1, 0, -1] ∧ adjointZeroOne.rowWeight = 0 := by
    refine ⟨by simp [adjointZeroOne], ?_⟩
    ext r; fin_cases r <;> simp [adjointZeroOne, mkTwo, rowSum_def, Finset.sum_range_succ]
  have h2 : adjointZeroTwo.topRow = ![1, 0, -1] ∧ adjointZeroTwo.rowWeight = 0 := by
    refine ⟨by simp [adjointZeroTwo], ?_⟩
    ext r; fin_cases r <;> simp [adjointZeroTwo, mkTwo, rowSum_def, Finset.sum_range_succ]
  have hext : ∀ Q P : GTPattern 3,
      (∀ i j, (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) ∨
        (i = 0 ∧ j = 3) ∨ (i = 1 ∧ j = 3) ∨ (i = 2 ∧ j = 3) → Q i j = P i j) → Q = P := by
    intro Q P hQP
    ext i j
    by_cases hlt : i < j ∧ j ≤ 3
    · exact hQP i j (by omega)
    · rw [Q.entry_eq_zero (by omega), P.entry_eq_zero (by omega)]
  let e : Bool ≃ {P : GTPattern 3 // P.topRow = ![1, 0, -1] ∧ P.rowWeight = 0} :=
    { toFun := fun b => if b then ⟨adjointZeroOne, h1⟩ else ⟨adjointZeroTwo, h2⟩
      invFun := fun P => decide (P.1 0 2 = 0)
      left_inv := fun b => by cases b <;> simp [adjointZeroOne, adjointZeroTwo, mkTwo]
      right_inv := by
        rintro ⟨P, hTop, hW⟩
        have hP03 : P 0 3 = 1 := by simpa using congrFun hTop 0
        have hP13 : P 1 3 = 0 := by simpa using congrFun hTop 1
        have hP23 : P 2 3 = -1 := by simpa using congrFun hTop 2
        have hW0 : P 0 1 = 0 := by simpa [rowSum_def] using congrFun hW 0
        have hW1 : P 0 2 + P 1 2 = 0 := by
          have hw := congrFun hW 1
          simpa [rowSum_def, Finset.sum_range_succ, hW0] using hw
        have h12 : P 1 2 = -P 0 2 := by omega
        have hi02_hi : P 0 2 ≤ 1 := hP03 ▸ P.entry_le_entry_succ_row (by decide) (by decide)
        have hi02_lo : 0 ≤ P 0 2 := hP13 ▸ P.entry_succ_succ_le_entry (i := 0) (j := 2) (by decide)
        rcases (by omega : P 0 2 = 0 ∨ P 0 2 = 1) with h02 | h02
        · simp only [h02, decide_true, ite_true, Subtype.mk.injEq]
          refine hext _ _ fun i j hij => ?_
          rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
              ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
            simp [adjointZeroOne, mkTwo, hW0, h12, h02, hP03, hP13, hP23]
        · have hne0 : ¬ P 0 2 = 0 := by omega
          simp only [hne0, decide_false, Bool.false_eq_true, ite_false, Subtype.mk.injEq]
          refine hext _ _ fun i j hij => ?_
          rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
              ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
            simp [adjointZeroTwo, mkTwo, hW0, h12, h02, hP03, hP13, hP23] }
  rw [Nat.card_congr e.symm, Nat.card_eq_fintype_card, Fintype.card_bool]

end AdjointThree

end TauCeti.GTPattern
