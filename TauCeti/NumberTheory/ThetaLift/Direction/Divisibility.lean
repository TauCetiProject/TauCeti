/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.LocalPrimeSum
public import TauCeti.NumberTheory.ThetaLift.Direction.Congruences
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Predicted divisibility of theta jets

At each place, the box count is the number of height-one columns plus the number of boxes in
all other columns. The predicted divisibility credits the reciprocal prime sum for each box,
and subtracts the cost of the congruences between directions at a place and its partners. At the
ramified prime the deduction includes the exponent zero, although the box credit does not.

The formula is `New.predictedDivisibility` in `New/Derivatives/Divisibility/Count.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean/tree/72fead1/grh) at revision `72fead1`.
-/

public noncomputable section

open Finset

namespace TauCeti

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The number of boxes at one place. `none` indexes the height-one columns; the remaining
column multiplicities are indexed by `some i`, with heights given by `height`. -/
def directionBoxCount (height : κ → ℕ) (a : Option κ → ℕ) : ℕ :=
  a none + ∑ i, a (some i) * height i

/-- Count the boxes by multiplying the number of columns at each height by that height. -/
theorem directionBoxCount_def (height : κ → ℕ) (a : Option κ → ℕ) :
    directionBoxCount height a = a none + ∑ i, a (some i) * height i := (rfl)

/-- The deduction at one place, in units of the valuation of the target modulus. The congruence
cost counts powers of a `q`th root of that modulus, so divide it by `q`. -/
def directionDeduction (height : κ → ℕ) (a b : Option κ → ℕ) (q : ℕ)
    (markL markR : Bool) : ℝ :=
  (directionDeductionCost height a b q markL markR : ℝ) / q

/-- The formula for the deduction in terms of the integer congruence cost. -/
theorem directionDeduction_def (height : κ → ℕ) (a b : Option κ → ℕ) (q : ℕ)
    (markL markR : Bool) :
    directionDeduction height a b q markL markR =
      (directionDeductionCost height a b q markL markR : ℝ) / q := (rfl)

/-- The deduction is nonnegative, including at the exponent-zero term `q = 1`. -/
@[simp] theorem directionDeduction_nonneg (height : κ → ℕ) (a b : Option κ → ℕ) (q : ℕ)
    (markL markR : Bool) : 0 ≤ directionDeduction height a b q markL markR := by
  rw [directionDeduction_def]
  positivity

/-- The credit for all boxes minus the unmarked deduction separates into two positive parts
and the linear cost for ordinary columns. The quotient is the source scaling factor. -/
theorem div_directionBoxCount_sub_directionDeduction (height : κ → ℕ) (a b : Option κ → ℕ)
    (q : ℕ) :
    (directionBoxCount height a : ℝ) / q - directionDeduction height a b q false false =
      max ((a none : ℝ) / q - ((∑ i, b (some i) : ℕ) + b none : ℝ)) 0 +
        max (((∑ i, a (some i) * height i : ℕ) : ℝ) / q -
          (∑ i, b (some i) * height i : ℕ)) 0 - (∑ i, a (some i) : ℕ) / (q : ℝ) := by
  by_cases hq : q = 0
  · simp only [hq, directionDeduction_def, Nat.cast_zero, div_zero, sub_zero, zero_sub]
    rw [max_eq_right (neg_nonpos.mpr (by positivity)),
      max_eq_right (neg_nonpos.mpr (by positivity)), add_zero]
  have hq' : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  have hmax (x y : ℝ) : max (x - y) 0 = x - min x y := by
    simpa only [sub_self, min_comm] using max_sub_sub_left x y x
  simp only [directionBoxCount_def, directionDeduction_def, directionDeductionCost_def,
    Bool.false_eq_true, ite_false, Nat.cast_add, Nat.cast_min, Nat.cast_mul, add_div,
    ← min_div_div_right (Nat.cast_nonneg q), mul_div_cancel_left₀ _ hq', hmax]
  ring

open OneSidedBound

/-- Credit the number of boxes at the reciprocal prime sum and subtract the deductions over
prime powers. The partner indexed by `q` is the one at the power `q = p ^ e`; therefore at the
ramified exponent zero use `partner 1`. -/
def predictedDivisibility (d : ℕ) [Fact d.Prime] (p : ℕ) (height : κ → ℕ)
    (a : ι → Option κ → ℕ) (partner : ℕ → ι → ι) : ℝ :=
  (∑ i, (directionBoxCount height (a i) : ℝ)) * localPrimeSum d p (fun q ↦ (q : ℝ)⁻¹) -
    localPrimeSum d p (fun q ↦ ∑ i, directionDeduction height (a i) (a (partner q i)) q
      false false) -
    (if p = d then (∑ i, directionDeduction height (a i) (a (partner 1 i)) 1 false false) / 2
      else 0)

/-- The predicted divisibility is the full box credit less the positive-exponent deductions
and the separate ramified exponent-zero deduction. -/
theorem predictedDivisibility_def (d : ℕ) [Fact d.Prime] (p : ℕ) (height : κ → ℕ)
    (a : ι → Option κ → ℕ) (partner : ℕ → ι → ι) :
    predictedDivisibility d p height a partner =
      (∑ i, (directionBoxCount height (a i) : ℝ)) * localPrimeSum d p (fun q ↦ (q : ℝ)⁻¹) -
        localPrimeSum d p (fun q ↦ ∑ i, directionDeduction height (a i) (a (partner q i)) q
          false false) -
        (if p = d then (∑ i, directionDeduction height (a i) (a (partner 1 i)) 1 false false) / 2
          else 0) := (rfl)

/-- Erasing the distinguished columns at marked places changes the predicted divisibility
only by the lost box credit and the replacement of unmarked deductions by marked ones. -/
theorem predictedDivisibility_erase_add (d : ℕ) [Fact d.Prime] (p : ℕ) (height : κ → ℕ)
    (a : ι → Option κ → ℕ) (partner : ℕ → ι → ι) (mark : ι → Bool) :
    let erased (i : ι) (j : Option κ) := j.elim (if mark i then 0 else a i none) (a i ∘ some)
    let γ := localPrimeSum d p (fun q ↦ (q : ℝ)⁻¹)
    predictedDivisibility d p height erased partner +
      (∑ i, (if mark i then (a i none : ℝ) else 0)) * γ =
      (∑ i, (directionBoxCount height (a i) : ℝ)) * γ -
        localPrimeSum d p (fun q ↦ ∑ i, directionDeduction height (a i) (a (partner q i)) q
          (mark i) (mark (partner q i))) -
        (if p = d then
          (∑ i, directionDeduction height (a i) (a (partner 1 i)) 1
            (mark i) (mark (partner 1 i))) / 2
          else 0) := by
  intro erased γ
  have hc (q : ℕ) (i : ι) :
      directionDeduction height (erased i) (erased (partner q i)) q false false =
        directionDeduction height (a i) (a (partner q i)) q (mark i) (mark (partner q i)) := by
    simp only [directionDeduction_def]
    exact congrArg (fun k : ℕ ↦ (k : ℝ) / q)
      (directionDeductionCost_eq_unmarked height (a i) (a (partner q i)) q
        (mark i) (mark (partner q i))).symm
  have hb : (∑ i, (directionBoxCount height (erased i) : ℝ)) +
      (∑ i, (if mark i then (a i none : ℝ) else 0)) =
        ∑ i, (directionBoxCount height (a i) : ℝ) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun i _ ↦ ?_
    cases hm : mark i <;> simp [directionBoxCount_def, erased, hm]
    ring
  simp only [predictedDivisibility_def, hc]
  rw [← hb, add_mul]
  ring

/-- Paying for all ordinary columns, all their boxes and all distinguished columns bounds
the deduction independently of the partner. -/
theorem directionDeduction_le (height : κ → ℕ) (a b : Option κ → ℕ) (q : ℕ)
    (markL markR : Bool) : directionDeduction height a b q markL markR ≤
      (((directionBoxCount height a + ∑ i, a (some i) : ℕ) : ℝ) / q) := by
  rw [directionDeduction_def, directionBoxCount_def, directionDeductionCost_def]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg q)
  norm_cast
  have h : (if markL then 0 else a none) ≤ a none := by split <;> simp
  linarith [Nat.min_le_left (if markL then 0 else a none)
    (q * ((∑ i, b (some i)) + if markR then 0 else b none)),
    Nat.min_le_left (∑ i, a (some i) * height i) (q * (∑ i, b (some i) * height i))]

/-- The summed deduction converges absolutely in the exponent, even if the partner varies
arbitrarily with the prime power. -/
theorem summable_sum_directionDeduction {p : ℕ} (hp : 1 < p) (height : κ → ℕ)
    (a : ι → Option κ → ℕ) (partner : ℕ → ι → ι) (mark : ι → Bool) :
    Summable (fun e : ℕ ↦ ∑ i, directionDeduction height (a i) (a (partner (p ^ e) i))
      (p ^ e) (mark i) (mark (partner (p ^ e) i))) := by
  have hp' : 1 < (p : ℝ) := by exact_mod_cast hp
  have hs := summable_geometric_of_lt_one (by positivity : 0 ≤ (p : ℝ)⁻¹)
    (inv_lt_one_of_one_lt₀ hp')
  refine summable_sum fun i _ ↦ (hs.mul_left
    (((directionBoxCount height (a i) + ∑ j, a i (some j) : ℕ) : ℝ))).of_norm_bounded fun e ↦ ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (directionDeduction_nonneg ..), inv_pow,
    ← Nat.cast_pow, ← div_eq_mul_inv]
  exact directionDeduction_le ..

/-- Truncating the exponents used for the congruences can only increase the lower bound
on the jet valuation. At the ramified prime the finite set may include zero. -/
theorem predictedDivisibility_le_sub_sum_directionDeduction (d : ℕ) [Fact d.Prime] (p : ℕ)
    (height : κ → ℕ) (a : ι → Option κ → ℕ) (partner : ℕ → ι → ι) (s : Finset ℕ)
    (hs : ∀ e ∈ s, p = d ∨ legendreSym d p = -1 ∧ Odd e) :
    predictedDivisibility d p height a partner ≤
      (∑ i, (directionBoxCount height (a i) : ℝ)) * localPrimeSum d p (fun q ↦ (q : ℝ)⁻¹) -
        (if p = d then (1 / 2 : ℝ) else 1) *
          ∑ e ∈ s, ∑ i, directionDeduction height (a i) (a (partner (p ^ e) i)) (p ^ e)
            false false := by
  let C (e : ℕ) := ∑ i, directionDeduction height (a i) (a (partner (p ^ e) i)) (p ^ e)
    false false
  let A (e : ℕ) := p = d ∨ legendreSym d p = -1 ∧ Odd e
  let F (e : ℕ) := if A e then C e else 0
  have hC (e : ℕ) : 0 ≤ C e := sum_nonneg fun _ _ ↦ directionDeduction_nonneg ..
  have hF : Summable F := by
    by_cases hp : 1 < p
    · have hS : Summable C := summable_sum_directionDeduction hp height a partner (fun _ ↦ false)
      exact hS.of_norm_bounded fun e ↦ by
        by_cases he : A e <;> simp [F, he, abs_of_nonneg (hC e), hC e, Real.norm_eq_abs]
    have hd := (Fact.out : d.Prime).two_le
    obtain rfl | rfl : p = 0 ∨ p = 1 := by omega
    · have hnd : 0 ≠ d := by omega
      simp [F, A, hnd, legendreSym]
    · have hnd : 1 ≠ d := by omega
      simp [F, A, hnd]
  have hpartial : ∑ e ∈ s, C e ≤ ∑' e, F e := by
    calc
      ∑ e ∈ s, C e = ∑ e ∈ s, F e := sum_congr rfl fun e he ↦ (ite_eq_left (hs e he)).symm
      _ ≤ _ := hF.sum_le_tsum s fun e _ ↦ by by_cases he : A e <;> simp [F, he, hC e]
  have heq : (fun e ↦ if e = 0 then 0 else F e) =
      fun e ↦ if 0 < e ∧ A e then C e else 0 := by
    funext e
    by_cases he : e = 0 <;> simp [F, he, Nat.pos_of_ne_zero]
  have hsum := (hF.tsum_eq_add_tsum_ite 0).trans
    (congrArg (fun v : ℕ → ℝ ↦ F 0 + ∑' e, v e) heq)
  let w := if p = d then (1 / 2 : ℝ) else 1
  have hw : 0 ≤ w := by dsimp only [w]; split <;> norm_num
  have h := mul_le_mul_of_nonneg_left (hpartial.trans_eq hsum) hw
  have hzero : w * F 0 = if p = d then C 0 / 2 else 0 := by
    by_cases hpd : p = d <;> simp [w, F, A, hpd, mul_comm, div_eq_mul_inv]
  rw [mul_add, hzero] at h
  rw [predictedDivisibility_def, localPrimeSum_def d p (fun q ↦
    ∑ i, directionDeduction height (a i) (a (partner q i)) q false false)]
  simpa only [w, C, A, pow_zero, sub_sub, add_comm] using sub_le_sub_left h
    ((∑ i, (directionBoxCount height (a i) : ℝ)) * localPrimeSum d p (fun q ↦ (q : ℝ)⁻¹))

end TauCeti
