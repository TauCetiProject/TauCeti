/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.InformationTheory.Hamming
public import TauCeti.Statistics.Samples.EmpiricalMean

/-!
# Classification risk, empirical risk and the ERM inequality

This file fixes the vocabulary of binary classification. Classifiers are maps `h : X → Bool`,
data are pairs in `X × Bool`, and real scores are read against a Boolean label through
`labelSign`, which sends `true` to `1` and `false` to `-1`.

* The error mass `classificationError P h = P.real {z | h z.1 ≠ z.2}` of a classifier under a
  measure `P` on `X × Bool` is a real number, computed with `Measure.real`: an infinite error mass
  becomes `0`, and for a non-measurable `h` it is an outer measure. When `P` is a probability law
  it is the misclassification probability `P(h(X) ≠ Y)`. Under a probability measure (or the zero
  measure) it lies in `[0, 1]`; under a finite measure it vanishes exactly when `h z.1 = z.2` for
  `P`-almost every `z`; and under a probability measure the errors of a measurable `h` and of the
  opposite classifier add up to `1`. For a measurable `h` it is the integral of the `0`–`1` loss.
* The empirical error `empiricalError h z` is the fraction of points of a sample
  `z : Fin n → X × Bool` that `h` misclassifies: the Hamming distance between the predicted and
  the observed labels divided by `n`, and the empirical mean of the `0`–`1` loss. It lies in
  `[0, 1]` and vanishes exactly when `h` is consistent with the sample. For a measurable `h` it is
  a measurable function of the sample, integrable under `Measure.pi fun _ ↦ P` for a finite
  measure `P`, and an unbiased estimator of the misclassification probability under an i.i.d.
  sample of size `n ≠ 0` from a probability law.
* The ERM inequality: if an approximate minimizer of an empirical criterion is uniformly within
  `D` of the true criterion, then its true criterion is at most that of every competitor plus
  `2 * D + ε`. With the risk as criterion and the uniform deviation over a class as `D`, this is
  the excess-risk bound of empirical risk minimization.

## Main definitions

* `TauCeti.labelSign b`: the sign `±1` of a Boolean label.
* `TauCeti.classificationError P h`: the real error mass `P.real {z | h z.1 ≠ z.2}` of `h`; the
  misclassification probability when `P` is a probability law.
* `TauCeti.empiricalError h z`: the fraction of the sample `z` that `h` misclassifies.

## Main results

* `TauCeti.labelSign_mul_self`, `TauCeti.labelSign_not`, `TauCeti.sum_labelSign`: the label
  sign squares to `1`, flips under negation of the label, and averages to `0`.
* `TauCeti.classificationError_eq_integral`: the error mass of a measurable classifier as the
  integral of the `0`–`1` loss.
* `TauCeti.classificationError_eq_zero_iff`,
  `TauCeti.classificationError_add_classificationError_not`.
* `TauCeti.empiricalError_eq_empiricalMean`, `TauCeti.empiricalError_eq_zero_iff`,
  `TauCeti.measurable_empiricalError`, `TauCeti.integrable_empiricalError`,
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

/-! ### Error mass and misclassification probability -/

section ClassificationError

variable {X : Type*} [MeasurableSpace X]

/-- The error mass `P.real {z | h z.1 ≠ z.2}` of a classifier `h : X → Bool` under a measure `P`
on `X × Bool`; for a probability law `P` it is the misclassification probability `P(h(X) ≠ Y)`.
An infinite error mass becomes `0`, and the error mass is an outer measure when `h` is not
measurable. -/
def classificationError (P : Measure (X × Bool)) (h : X → Bool) : ℝ :=
  P.real {z | h z.1 ≠ z.2}

/-- The defining formula of `classificationError`. -/
theorem classificationError_def (P : Measure (X × Bool)) (h : X → Bool) :
    classificationError P h = P.real {z | h z.1 ≠ z.2} :=
  (rfl)

/-- The error mass is nonnegative. -/
theorem classificationError_nonneg (P : Measure (X × Bool)) (h : X → Bool) :
    0 ≤ classificationError P h :=
  measureReal_nonneg

/-- Under the zero measure every classifier has error mass `0`. -/
@[simp]
theorem classificationError_zero (h : X → Bool) :
    classificationError (0 : Measure (X × Bool)) h = 0 :=
  measureReal_zero_apply _

/-- Under a probability measure (or the zero measure) the error mass is at most `1`. -/
theorem classificationError_le_one (P : Measure (X × Bool)) [IsZeroOrProbabilityMeasure P]
    (h : X → Bool) : classificationError P h ≤ 1 :=
  measureReal_le_one

/-- Under a finite measure a classifier has error mass `0` exactly when it agrees with the label
almost everywhere: `h z.1 = z.2` for `P`-almost every `z`. -/
@[simp]
theorem classificationError_eq_zero_iff (P : Measure (X × Bool)) [IsFiniteMeasure P]
    (h : X → Bool) : classificationError P h = 0 ↔ ∀ᵐ z ∂P, h z.1 = z.2 := by
  rw [classificationError_def, measureReal_eq_zero_iff, measure_eq_zero_iff_ae_notMem]
  simp

/-- The error mass of a measurable classifier is the integral of the `0`–`1` loss. -/
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
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, ne_eq, Bool.not_eq_iff]
  rw [classificationError_def, classificationError_def, hc,
    measureReal_add_measureReal_compl hs, probReal_univ]

end ClassificationError

/-! ### Empirical error -/

section EmpiricalError

variable {X : Type*} {n : ℕ}

/-- The empirical error of a classifier `h : X → Bool` on a sample `z : Fin n → X × Bool`: the
fraction of sample points that `h` misclassifies, that is the Hamming distance between the
predicted and the observed labels divided by `n` (`0` for the empty sample). -/
def empiricalError (h : X → Bool) (z : Fin n → X × Bool) : ℝ :=
  (hammingDist (fun i ↦ h (z i).1) (fun i ↦ (z i).2) : ℝ) / n

/-- The defining formula of `empiricalError` as a count of misclassified sample points. -/
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

/-- The empirical error on the empty sample is `0`. -/
@[simp]
theorem empiricalError_fin_zero (h : X → Bool) (z : Fin 0 → X × Bool) : empiricalError h z = 0 := by
  simp [empiricalError_def]

/-- The empirical error is nonnegative. -/
theorem empiricalError_nonneg (h : X → Bool) (z : Fin n → X × Bool) : 0 ≤ empiricalError h z :=
  div_nonneg (Nat.cast_nonneg _) n.cast_nonneg

/-- The empirical error is at most `1`. -/
theorem empiricalError_le_one (h : X → Bool) (z : Fin n → X × Bool) : empiricalError h z ≤ 1 := by
  refine div_le_one_of_le₀ ?_ n.cast_nonneg
  exact_mod_cast hammingDist_le_card_fintype.trans_eq (Fintype.card_fin n)

/-- The empirical error vanishes exactly when the classifier is consistent with the sample. -/
@[simp]
theorem empiricalError_eq_zero_iff (h : X → Bool) (z : Fin n → X × Bool) :
    empiricalError h z = 0 ↔ ∀ i, h (z i).1 = (z i).2 := by
  rcases eq_zero_or_neZero n with rfl | hn
  · simp
  · rw [empiricalError, div_eq_zero_iff, Nat.cast_eq_zero, Nat.cast_eq_zero, hammingDist_eq_zero,
      funext_iff, or_iff_left (NeZero.ne n)]

/-- On a nonempty sample, the empirical errors of a classifier and of the opposite classifier add
up to `1`. -/
theorem empiricalError_add_empiricalError_not [NeZero n] (h : X → Bool) (z : Fin n → X × Bool) :
    empiricalError h z + empiricalError (fun x ↦ !h x) z = 1 := by
  have hc : (univ.filter fun i ↦ (!h (z i).1) ≠ (z i).2) =
      univ.filter fun i ↦ ¬h (z i).1 ≠ (z i).2 :=
    filter_congr fun i _ ↦ not_congr Bool.not_eq_iff
  rw [empiricalError_def, empiricalError_def, hc, ← add_div, ← Nat.cast_add,
    card_filter_add_card_filter_not, card_univ, Fintype.card_fin,
    div_self (Nat.cast_ne_zero.mpr (NeZero.ne n) : (n : ℝ) ≠ 0)]

variable [MeasurableSpace X]

/-- The `0`–`1` loss of a measurable classifier is measurable. -/
private theorem measurable_zeroOneLoss {h : X → Bool} (hh : Measurable h) :
    Measurable fun w : X × Bool ↦ if h w.1 = w.2 then (0 : ℝ) else 1 :=
  Measurable.ite (measurableSet_eq_fun (hh.comp measurable_fst) measurable_snd)
    measurable_const measurable_const

/-- The `0`–`1` loss of a measurable classifier is integrable under a finite measure. -/
private theorem integrable_zeroOneLoss (P : Measure (X × Bool)) [IsFiniteMeasure P]
    {h : X → Bool} (hh : Measurable h) :
    Integrable (fun w : X × Bool ↦ if h w.1 = w.2 then (0 : ℝ) else 1) P :=
  Integrable.of_bound (measurable_zeroOneLoss hh).aestronglyMeasurable 1
    (ae_of_all _ fun w ↦ by split_ifs <;> simp)

/-- The empirical error of a measurable classifier is a measurable function of the sample. -/
@[fun_prop]
theorem measurable_empiricalError {h : X → Bool} (hh : Measurable h) :
    Measurable fun z : Fin n → X × Bool ↦ empiricalError h z := by
  simp only [empiricalError_eq_empiricalMean]
  exact measurable_empiricalMean (measurable_zeroOneLoss hh)

/-- For a finite measure `P` and a measurable classifier, the empirical error is integrable under
the product measure `Measure.pi fun _ ↦ P`. -/
theorem integrable_empiricalError (P : Measure (X × Bool)) [IsFiniteMeasure P] {h : X → Bool}
    (hh : Measurable h) :
    Integrable (fun z : Fin n → X × Bool ↦ empiricalError h z) (Measure.pi fun _ ↦ P) := by
  simp only [empiricalError_eq_empiricalMean]
  exact integrable_empiricalMean P (integrable_zeroOneLoss P hh)

/-- The empirical error is unbiased: under an i.i.d. sample of size `n ≠ 0` from a probability
measure `P`, the mean empirical error of a measurable classifier is its misclassification
probability. The same integral identity holds, with both sides `0`, when `P` is the zero
measure. -/
theorem integral_empiricalError [NeZero n] (P : Measure (X × Bool))
    [IsZeroOrProbabilityMeasure P] {h : X → Bool} (hh : Measurable h) :
    ∫ z, empiricalError h z ∂(Measure.pi fun _ : Fin n ↦ P) = classificationError P h := by
  simp only [empiricalError_eq_empiricalMean]
  rw [integral_empiricalMean P (integrable_zeroOneLoss P hh), classificationError_eq_integral P hh]

end EmpiricalError

/-! ### The ERM inequality -/

/-- **The ERM inequality** (Devroye–Györfi–Lugosi, Lemma 8.2): if `t₀` minimizes the empirical
criterion `Rn` up to `ε` and `Rn` is uniformly within `D` of the criterion `R`, then the
criterion of `t₀` is at most that of every competitor plus `2 * D + ε`:
`R t₀ ≤ R t + 2 * D + ε`. -/
theorem le_add_two_mul_add_of_isApproxMin {T : Type*} (R Rn : T → ℝ) (t₀ : T) (D ε : ℝ)
    (hmin : ∀ t, Rn t₀ ≤ Rn t + ε) (hdev : ∀ t, |Rn t - R t| ≤ D) (t : T) :
    R t₀ ≤ R t + 2 * D + ε := by
  have h₀ := abs_le.mp (hdev t₀)
  have h₁ := abs_le.mp (hdev t)
  linarith [hmin t]

end TauCeti
