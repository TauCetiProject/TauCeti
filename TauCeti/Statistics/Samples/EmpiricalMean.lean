/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.BigOperators.Expect
public import TauCeti.Probability.Process.EmpiricalMeasure
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Empirical means of functions over a sample

For a real function `g : Z → ℝ` and a sample `z : Fin n → Z`, the empirical mean
`empiricalMean g z = (∑ i, g (z i)) / n` is the average of `g` over the sample points. It is the
finite average `𝔼 i, g (z i)` and, for strongly measurable `g`, the integral of `g` against the
empirical measure of `z`. For
the empty sample (`n = 0`) it is `0`, the junk value of division by zero, not the average of an
empty family, so statements about a constant or about expectations assume `n ≠ 0`.

The empirical mean is linear in the function, monotone in the values at the sample points, and
symmetric in the sample; replacing one sample point changes it by the change of `g` divided by
`n`, which is the bounded-differences input of McDiarmid's inequality. Under an i.i.d. sample of
size `n` from a finite measure `P` the empirical mean of a `P`-integrable function is integrable,
and for a probability measure and `n ≠ 0` it is unbiased: its mean is `∫ g ∂P`.

## Main definitions

* `TauCeti.empiricalMean g z`: the average `n⁻¹ ∑ i, g (z i)` of `g` over the sample `z`.

## Main results

* `TauCeti.empiricalMean_eq_expect`: the empirical mean as the finite average `𝔼 i, g (z i)`.
* `TauCeti.empiricalMean_eq_integral`: the empirical mean of a strongly measurable function as
  an integral against `TauCeti.Probability.empiricalFiniteMeasure z`.
* `TauCeti.empiricalMean_const`, `TauCeti.empiricalMean_add`, `TauCeti.empiricalMean_sub`,
  `TauCeti.empiricalMean_neg`, `TauCeti.empiricalMean_const_mul`: constants and linearity.
* `TauCeti.empiricalMean_mono`, `TauCeti.empiricalMean_nonneg`,
  `TauCeti.empiricalMean_le_of_forall_le`, `TauCeti.le_empiricalMean_of_forall_le`: order.
* `TauCeti.empiricalMean_comp_perm`: invariance under permutations of the sample.
* `TauCeti.empiricalMean_update_sub`: the effect of replacing one sample point.
* `TauCeti.integrable_empiricalMean`, `TauCeti.integral_empiricalMean`: integrability under
  `Measure.pi fun _ ↦ P` for a finite measure `P`, and unbiasedness for a probability measure.
-/

public section

noncomputable section

open MeasureTheory Finset
open scoped BigOperators

namespace TauCeti

variable {Z : Type*} {n : ℕ}

/-- The empirical mean `n⁻¹ ∑ i, g (z i)` of a real function `g` over a sample `z : Fin n → Z`.
For the empty sample (`n = 0`) it is `0`. -/
def empiricalMean (g : Z → ℝ) (z : Fin n → Z) : ℝ :=
  (∑ i, g (z i)) / n

/-- The defining formula of `empiricalMean`. -/
theorem empiricalMean_def (g : Z → ℝ) (z : Fin n → Z) :
    empiricalMean g z = (∑ i, g (z i)) / n :=
  (rfl)

/-- The empirical mean is the finite average of the values of `g` at the sample points. -/
theorem empiricalMean_eq_expect (g : Z → ℝ) (z : Fin n → Z) :
    empiricalMean g z = 𝔼 i, g (z i) := by
  rw [empiricalMean_def, Fintype.expect_eq_sum_div_card, Fintype.card_fin]

/-- The empirical mean over the empty sample is `0`. -/
@[simp]
theorem empiricalMean_fin_zero (g : Z → ℝ) (z : Fin 0 → Z) : empiricalMean g z = 0 := by
  simp [empiricalMean_def]

/-- The empirical mean of a constant over a nonempty sample is that constant. -/
@[simp]
theorem empiricalMean_const [NeZero n] (c : ℝ) (z : Fin n → Z) :
    empiricalMean (fun _ ↦ c) z = c := by
  rw [empiricalMean_eq_expect, Finset.expect_const univ_nonempty]

/-- The empirical mean is additive in the function. -/
theorem empiricalMean_add (f g : Z → ℝ) (z : Fin n → Z) :
    empiricalMean (fun w ↦ f w + g w) z = empiricalMean f z + empiricalMean g z := by
  simp only [empiricalMean_def, sum_add_distrib, add_div]

/-- The empirical mean commutes with subtraction of functions. -/
theorem empiricalMean_sub (f g : Z → ℝ) (z : Fin n → Z) :
    empiricalMean (fun w ↦ f w - g w) z = empiricalMean f z - empiricalMean g z := by
  simp only [empiricalMean_def, sum_sub_distrib, sub_div]

/-- The empirical mean commutes with negation of the function. -/
theorem empiricalMean_neg (g : Z → ℝ) (z : Fin n → Z) :
    empiricalMean (fun w ↦ -g w) z = -empiricalMean g z := by
  simp only [empiricalMean_def, sum_neg_distrib, neg_div]

/-- The empirical mean commutes with multiplication of the function by a constant. -/
theorem empiricalMean_const_mul (c : ℝ) (g : Z → ℝ) (z : Fin n → Z) :
    empiricalMean (fun w ↦ c * g w) z = c * empiricalMean g z := by
  simp only [empiricalMean_def, ← mul_sum, mul_div_assoc]

/-- The empirical mean is monotone in the values of the function at the sample points. -/
theorem empiricalMean_mono {f g : Z → ℝ} {z : Fin n → Z} (h : ∀ i, f (z i) ≤ g (z i)) :
    empiricalMean f z ≤ empiricalMean g z :=
  div_le_div_of_nonneg_right (sum_le_sum fun i _ ↦ h i) n.cast_nonneg

/-- The empirical mean of a function that is nonnegative at the sample points is nonnegative. -/
theorem empiricalMean_nonneg {g : Z → ℝ} {z : Fin n → Z} (h : ∀ i, 0 ≤ g (z i)) :
    0 ≤ empiricalMean g z :=
  div_nonneg (sum_nonneg fun i _ ↦ h i) n.cast_nonneg

/-- On a nonempty sample, an upper bound for `g` at the sample points bounds its empirical
mean. -/
theorem empiricalMean_le_of_forall_le [NeZero n] {g : Z → ℝ} {z : Fin n → Z} {c : ℝ}
    (h : ∀ i, g (z i) ≤ c) : empiricalMean g z ≤ c :=
  (empiricalMean_mono (f := g) (g := fun _ ↦ c) h).trans_eq (empiricalMean_const c z)

/-- On a nonempty sample, a lower bound for `g` at the sample points bounds its empirical
mean. -/
theorem le_empiricalMean_of_forall_le [NeZero n] {g : Z → ℝ} {z : Fin n → Z} {c : ℝ}
    (h : ∀ i, c ≤ g (z i)) : c ≤ empiricalMean g z :=
  (empiricalMean_const c z).symm.trans_le (empiricalMean_mono (f := fun _ ↦ c) h)

/-- The empirical mean is a symmetric function of the sample. -/
theorem empiricalMean_comp_perm (g : Z → ℝ) (z : Fin n → Z) (σ : Equiv.Perm (Fin n)) :
    empiricalMean g (z ∘ σ) = empiricalMean g z := by
  simp only [empiricalMean_def, Function.comp_apply, Equiv.sum_comp σ fun i ↦ g (z i)]

/-- Replacing the `i`-th sample point by `w` changes the empirical mean by
`(g w - g (z i)) / n`. -/
theorem empiricalMean_update_sub (g : Z → ℝ) (z : Fin n → Z) (i : Fin n) (w : Z) :
    empiricalMean g (Function.update z i w) - empiricalMean g z = (g w - g (z i)) / n := by
  rw [empiricalMean_def, empiricalMean_def, ← sub_div, ← sum_sub_distrib,
    Fintype.sum_eq_single i fun j hj ↦ by simp [Function.update_of_ne hj]]
  simp

variable [MeasurableSpace Z]

/-- The empirical mean of a strongly measurable function is its integral against the empirical
measure of the sample. -/
theorem empiricalMean_eq_integral {g : Z → ℝ} (hg : StronglyMeasurable g) (z : Fin n → Z) :
    empiricalMean g z = ∫ w, g w ∂(Probability.empiricalFiniteMeasure z : Measure Z) := by
  rw [Probability.integral_empiricalFiniteMeasure hg, Fintype.card_fin, smul_eq_mul,
    empiricalMean_def, inv_mul_eq_div]

/-- Under an i.i.d. sample from a finite measure `P`, the empirical mean of a `P`-integrable
function is integrable. -/
theorem integrable_empiricalMean (P : Measure Z) [IsFiniteMeasure P] {g : Z → ℝ}
    (hg : Integrable g P) :
    Integrable (fun z : Fin n → Z ↦ empiricalMean g z) (Measure.pi fun _ ↦ P) := by
  simp only [empiricalMean_def]
  exact (integrable_finsetSum _ fun i _ ↦ integrable_comp_eval hg).div_const _

/-- The empirical mean is unbiased: under an i.i.d. sample of size `n ≠ 0` from a probability
measure `P` (or from the zero measure), the mean of the empirical mean of a `P`-integrable
function `g` is `∫ g ∂P`. -/
theorem integral_empiricalMean [NeZero n] (P : Measure Z) [IsZeroOrProbabilityMeasure P]
    {g : Z → ℝ} (hg : Integrable g P) :
    ∫ z, empiricalMean g z ∂(Measure.pi fun _ : Fin n ↦ P) = ∫ w, g w ∂P := by
  rcases eq_zero_or_isProbabilityMeasure P with rfl | hP
  · have h0 : Measure.pi (fun _ : Fin n ↦ (0 : Measure Z)) = 0 := by
      rw [← Measure.measure_univ_eq_zero, ← Set.pi_univ, Measure.pi_pi]
      simp [NeZero.ne n]
    simp [h0]
  have heq (i : Fin n) : ∫ z, g (z i) ∂(Measure.pi fun _ : Fin n ↦ P) = ∫ w, g w ∂P :=
    integral_comp_eval hg.aestronglyMeasurable
  simp only [empiricalMean_def]
  rw [integral_div, integral_finsetSum _ fun i _ ↦ integrable_comp_eval hg]
  simp only [heq, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [NeZero.ne n]

end TauCeti
