/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Statistics.Samples.EmpiricalMean

/-!
# Classification risk, empirical risk and the ERM inequality

This file fixes the vocabulary of binary classification. Classifiers are maps `h : X → Bool`,
data are pairs in `X × Bool`, and real scores are read against a Boolean label through
`labelSign`, which sends `true` to `1` and `false` to `-1`.

* The misclassification probability `classificationError P h = P(h(X) ≠ Y)` of a classifier under
  a law `P` on `X × Bool` is a real number; it is computed with `Measure.real`, so it is an outer
  probability when `h` is not measurable. For a probability measure it lies in `[0, 1]`, it
  vanishes exactly when `P` is concentrated on the graph of `h`, and for a measurable `h` the
  errors of `h` and of the opposite classifier add up to `1`.
* The empirical error `empiricalError h z` is the fraction of points of a sample
  `z : Fin n → X × Bool` that `h` misclassifies: the empirical mean of the `0`–`1` loss. It lies
  in `[0, 1]` and vanishes exactly when `h` is consistent with the sample. For a measurable `h`
  it is an unbiased estimator of the misclassification probability under an i.i.d. sample of
  size `n ≠ 0`.
* The ERM inequality: an approximate minimizer of an empirical criterion that is uniformly within
  `D` of the true criterion is within `2 D + ε` of every competitor. With the risk as criterion
  and the uniform deviation over a class as `D`, this is the excess-risk bound of empirical risk
  minimization.

## Main definitions

* `TauCeti.labelSign b`: the sign `±1` of a Boolean label.
* `TauCeti.classificationError P h`: the misclassification probability of `h` under `P`.
* `TauCeti.empiricalError h z`: the fraction of the sample `z` that `h` misclassifies.

## Main results

* `TauCeti.labelSign_mul_self`, `TauCeti.labelSign_not`, `TauCeti.sum_labelSign`: the label
  sign squares to `1`, flips under negation of the label, and averages to `0`.
* `TauCeti.classificationError_eq_integral`: the misclassification probability of a measurable
  classifier as the expected `0`–`1` loss.
* `TauCeti.classificationError_eq_zero_iff`,
  `TauCeti.classificationError_add_classificationError_not`.
* `TauCeti.empiricalError_eq_empiricalMean`, `TauCeti.empiricalError_eq_zero_iff`,
  `TauCeti.integral_empiricalError`.
* `TauCeti.le_add_two_mul_add_of_isApproxMin`: the ERM inequality.

The ERM inequality is Devroye–Györfi–Lugosi, Lemma 8.2.

## References

* L. Devroye, L. Györfi, G. Lugosi, *A Probabilistic Theory of Pattern Recognition*, Springer,
  1996.
-/

public section

noncomputable section

open MeasureTheory Finset

namespace TauCeti

/-! ### The sign of a Boolean label -/

/-- The sign `±1` of a Boolean label: `true ↦ 1` and `false ↦ -1`. -/
def labelSign (b : Bool) : ℝ := if b then 1 else -1

/-- The defining formula of `labelSign`. -/
theorem labelSign_def (b : Bool) : labelSign b = if b then 1 else -1 :=
  (rfl)

/-- The label `true` has sign `1`. -/
@[simp]
theorem labelSign_true : labelSign true = 1 :=
  (rfl)

/-- The label `false` has sign `-1`. -/
@[simp]
theorem labelSign_false : labelSign false = -1 :=
  (rfl)

/-- Negating a label negates its sign. -/
@[simp]
theorem labelSign_not (b : Bool) : labelSign (!b) = -labelSign b := by
  cases b <;> simp

/-- The sign of a label squares to `1`. -/
@[simp]
theorem labelSign_mul_self (b : Bool) : labelSign b * labelSign b = 1 := by
  cases b <;> simp

/-- The sign of a label has absolute value `1`. -/
@[simp]
theorem abs_labelSign (b : Bool) : |labelSign b| = 1 := by
  cases b <;> simp

/-- The sign of a label is never `0`; in particular `labelSign` is not the `0`–`1` coding of
labels. -/
@[simp]
theorem labelSign_ne_zero (b : Bool) : labelSign b ≠ 0 := by
  cases b <;> simp

/-- Distinct labels have distinct signs. -/
theorem labelSign_injective : Function.Injective labelSign := by
  intro a b
  cases a <;> cases b <;> norm_num

/-- The two label signs sum to `0`: a uniform random label has mean sign `0`. -/
theorem sum_labelSign : ∑ b : Bool, labelSign b = 0 := by
  simp

/-! ### Misclassification probability -/

section ClassificationError

variable {X : Type*} [MeasurableSpace X]

/-- The misclassification probability `P(h(X) ≠ Y)` of a classifier `h : X → Bool` under a law
`P` on `X × Bool`. It is an outer probability when `h` is not measurable. -/
def classificationError (P : Measure (X × Bool)) (h : X → Bool) : ℝ :=
  P.real {z | h z.1 ≠ z.2}

/-- The defining formula of `classificationError`. -/
theorem classificationError_def (P : Measure (X × Bool)) (h : X → Bool) :
    classificationError P h = P.real {z | h z.1 ≠ z.2} :=
  (rfl)

/-- The misclassification probability is nonnegative. -/
theorem classificationError_nonneg (P : Measure (X × Bool)) (h : X → Bool) :
    0 ≤ classificationError P h :=
  measureReal_nonneg

/-- Under a probability measure (or the zero measure) the misclassification probability is at
most `1`. -/
theorem classificationError_le_one (P : Measure (X × Bool)) [IsZeroOrProbabilityMeasure P]
    (h : X → Bool) : classificationError P h ≤ 1 :=
  measureReal_le_one

/-- Under a finite measure a classifier has misclassification probability `0` exactly when the
law is concentrated on its graph. -/
@[simp]
theorem classificationError_eq_zero_iff (P : Measure (X × Bool)) [IsFiniteMeasure P]
    (h : X → Bool) : classificationError P h = 0 ↔ ∀ᵐ z ∂P, h z.1 = z.2 := by
  rw [classificationError_def, measureReal_eq_zero_iff, measure_eq_zero_iff_ae_notMem]
  simp

/-- The misclassification probability of a measurable classifier is the expected `0`–`1`
loss. -/
theorem classificationError_eq_integral (P : Measure (X × Bool)) {h : X → Bool}
    (hh : Measurable h) :
    classificationError P h = ∫ z, (if h z.1 = z.2 then 0 else 1) ∂P := by
  have hs : MeasurableSet {z : X × Bool | h z.1 ≠ z.2} :=
    (measurableSet_eq_fun (hh.comp measurable_fst) measurable_snd).compl
  rw [classificationError_def, ← integral_indicator_one hs]
  congr 1 with z
  by_cases hz : h z.1 = z.2 <;> simp [hz]

/-- Under a probability measure, a measurable classifier and the opposite classifier have
misclassification probabilities adding up to `1`: exactly one of the two errs at each pair. -/
theorem classificationError_add_classificationError_not (P : Measure (X × Bool))
    [IsProbabilityMeasure P] {h : X → Bool} (hh : Measurable h) :
    classificationError P h + classificationError P (fun x ↦ !h x) = 1 := by
  have hs : MeasurableSet {z : X × Bool | h z.1 ≠ z.2} :=
    (measurableSet_eq_fun (hh.comp measurable_fst) measurable_snd).compl
  have hc : {z : X × Bool | (!h z.1) ≠ z.2} = {z : X × Bool | h z.1 ≠ z.2}ᶜ := by
    ext z
    cases h z.1 <;> cases z.2 <;> simp
  rw [classificationError_def, classificationError_def, hc,
    measureReal_add_measureReal_compl hs, probReal_univ]

end ClassificationError

/-! ### Empirical error -/

section EmpiricalError

variable {X : Type*} {n : ℕ}

/-- The empirical error of a classifier `h : X → Bool` on a sample `z : Fin n → X × Bool`: the
fraction of sample points that `h` misclassifies (`0` for the empty sample). -/
def empiricalError (h : X → Bool) (z : Fin n → X × Bool) : ℝ :=
  ((univ.filter fun i ↦ h (z i).1 ≠ (z i).2).card : ℝ) / n

/-- The defining formula of `empiricalError`. -/
theorem empiricalError_def (h : X → Bool) (z : Fin n → X × Bool) :
    empiricalError h z = ((univ.filter fun i ↦ h (z i).1 ≠ (z i).2).card : ℝ) / n :=
  (rfl)

/-- The empirical error is the empirical mean of the `0`–`1` loss. -/
theorem empiricalError_eq_empiricalMean (h : X → Bool) (z : Fin n → X × Bool) :
    empiricalError h z = empiricalMean (fun w ↦ if h w.1 = w.2 then 0 else 1) z := by
  rw [empiricalError_def, empiricalMean_def, ← sum_boole]
  congr 1
  refine sum_congr rfl fun i _ ↦ ?_
  by_cases hi : h (z i).1 = (z i).2 <;> simp [hi]

/-- The empirical error is nonnegative. -/
theorem empiricalError_nonneg (h : X → Bool) (z : Fin n → X × Bool) : 0 ≤ empiricalError h z :=
  div_nonneg (Nat.cast_nonneg _) n.cast_nonneg

/-- The empirical error is at most `1`. -/
theorem empiricalError_le_one (h : X → Bool) (z : Fin n → X × Bool) : empiricalError h z ≤ 1 := by
  refine div_le_one_of_le₀ ?_ n.cast_nonneg
  exact_mod_cast (card_filter_le _ _).trans_eq (by simp)

/-- The empirical error vanishes exactly when the classifier is consistent with the sample. -/
@[simp]
theorem empiricalError_eq_zero_iff (h : X → Bool) (z : Fin n → X × Bool) :
    empiricalError h z = 0 ↔ ∀ i, h (z i).1 = (z i).2 := by
  rcases n with _ | n
  · simp [empiricalError_def]
  · simp [empiricalError_def, filter_eq_empty_iff, Nat.cast_add_one_ne_zero]

/-- On a nonempty sample, the empirical errors of a classifier and of the opposite classifier add
up to `1`. -/
theorem empiricalError_add_empiricalError_not [NeZero n] (h : X → Bool) (z : Fin n → X × Bool) :
    empiricalError h z + empiricalError (fun x ↦ !h x) z = 1 := by
  rw [empiricalError_eq_empiricalMean, empiricalError_eq_empiricalMean, ← empiricalMean_add]
  convert empiricalMean_const 1 z with w
  cases h w.1 <;> cases w.2 <;> simp

/-- The empirical error is unbiased: under an i.i.d. sample of size `n ≠ 0` from a probability
measure `P` (or from the zero measure), the mean empirical error of a measurable classifier is
its misclassification probability. -/
theorem integral_empiricalError [MeasurableSpace X] [NeZero n] (P : Measure (X × Bool))
    [IsZeroOrProbabilityMeasure P] {h : X → Bool} (hh : Measurable h) :
    ∫ z, empiricalError h z ∂(Measure.pi fun _ : Fin n ↦ P) = classificationError P h := by
  have hm : Measurable fun w : X × Bool ↦ if h w.1 = w.2 then (0 : ℝ) else 1 :=
    Measurable.ite (measurableSet_eq_fun (hh.comp measurable_fst) measurable_snd)
      measurable_const measurable_const
  have hint : Integrable (fun w : X × Bool ↦ if h w.1 = w.2 then (0 : ℝ) else 1) P :=
    Integrable.of_bound hm.aestronglyMeasurable 1 (ae_of_all _ fun w ↦ by split_ifs <;> simp)
  simp only [empiricalError_eq_empiricalMean]
  rw [integral_empiricalMean P hint, classificationError_eq_integral P hh]

end EmpiricalError

/-! ### The ERM inequality -/

/-- **The ERM inequality** (Devroye–Györfi–Lugosi, Lemma 8.2): if `t₀` minimizes the empirical
criterion `Rn` up to `ε` and `Rn` is uniformly within `D` of the criterion `R`, then `t₀` is
within `2 * D + ε` of every competitor for `R`. -/
theorem le_add_two_mul_add_of_isApproxMin {T : Type*} (R Rn : T → ℝ) (t₀ : T) (D ε : ℝ)
    (hmin : ∀ t, Rn t₀ ≤ Rn t + ε) (hdev : ∀ t, |Rn t - R t| ≤ D) (t : T) :
    R t₀ ≤ R t + 2 * D + ε := by
  have h₀ := abs_le.mp (hdev t₀)
  have h₁ := abs_le.mp (hdev t)
  linarith [hmin t]

end TauCeti
