/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul
public import Mathlib.Probability.Moments.Variance

/-!
# Moment-generating functions of sums of coordinates under a product measure

A statistic of the form `x ↦ ∑ j, f j (x j)` under a finite product measure `Measure.pi μ` has
exponential `∏ j, exp (t * f j (x j))`, so Fubini's theorem turns its moment-generating function
into the product of the coordinate ones. For a product of *probability* measures each factor is
positive exactly on its exponential-integrability domain, so the domain of the sum is then the
intersection of the domains of the coordinates. That step genuinely needs the coordinates to be
probability measures: under the zero measure, for instance, the moment-generating function
vanishes everywhere while the integrability domain is all of `ℝ`.

These are the facts that turn a quadratic statistic of a Gaussian vector, written in
eigen-coordinates, into a product of one-dimensional moment-generating functions.

The second moment of a sum of coordinates is simpler still: the variances add
(`ProbabilityTheory.variance_sum_pi`). For the average of `n` independent copies of one square
integrable statistic this gives variance `Var[f] / n`, and Chebyshev's inequality turns that into
the **weak law of large numbers** with an explicit rate: the average deviates from the mean by at
least `t` with probability at most `Var[f] / (n t²)`.

## Main results

* `TauCeti.mgf_sum_pi` — the moment-generating function of a sum of coordinate
  statistics factors over the coordinates, for every argument;
* `TauCeti.integrableExpSet_sum_pi` — for a product of probability measures, its
  exponential-integrability domain is the intersection of the coordinate domains;
* `TauCeti.meas_ge_le_variance_div_card_mul_sq_pi` — the weak law of large numbers in Chebyshev's
  form, for the average of independent copies of a square-integrable statistic.
-/

public section

open MeasureTheory ProbabilityTheory

namespace TauCeti

variable {ι : Type*} [Fintype ι] {E : ι → Type*} [∀ i, MeasurableSpace (E i)]
  {μ : ∀ i, Measure (E i)}

/-- Under a product measure the exponential of a sum of coordinate statistics factors over the
coordinates, so Fubini's theorem turns its integral into a product of one-dimensional
moment-generating functions. No integrability hypothesis is needed: off the common domain both
sides are zero. -/
theorem mgf_sum_pi [∀ i, SigmaFinite (μ i)] (f : ∀ i, E i → ℝ) (t : ℝ) :
    mgf (fun x ↦ ∑ j, f j (x j)) (Measure.pi μ) t = ∏ j, mgf (f j) (μ j) t := by
  simp only [mgf, Finset.mul_sum, Real.exp_sum]
  exact integral_fintype_prod_eq_prod fun j (u : E j) ↦ Real.exp (t * f j u)

/-- Under a product of probability measures, a sum of coordinate statistics has finite
exponential moments of order `t` exactly when every coordinate does. -/
theorem integrableExpSet_sum_pi [∀ i, IsProbabilityMeasure (μ i)] (f : ∀ i, E i → ℝ) :
    integrableExpSet (fun x ↦ ∑ j, f j (x j)) (Measure.pi μ) =
      ⋂ j, integrableExpSet (f j) (μ j) := by
  ext t
  rw [Set.mem_iInter]
  have hpi : t ∈ integrableExpSet (fun x ↦ ∑ j, f j (x j)) (Measure.pi μ) ↔
      0 < ∏ j, mgf (f j) (μ j) t := by
    rw [← mgf_sum_pi]
    exact mgf_pos_iff.symm
  have hj (j : ι) : t ∈ integrableExpSet (f j) (μ j) ↔ 0 < mgf (f j) (μ j) t := mgf_pos_iff.symm
  simp only [hpi, hj]
  refine ⟨fun h j ↦ mgf_nonneg.lt_of_ne' fun hj ↦ ?_, fun h ↦ Finset.prod_pos fun j _ ↦ h j⟩
  exact absurd (Finset.prod_eq_zero (Finset.mem_univ j) hj) h.ne'

section WeakLaw

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]

/-- **The weak law of large numbers, in Chebyshev's form.** Under the product of `|ι|` copies of a
probability measure `ν`, the average of a square-integrable statistic `f` over the coordinates
deviates from its mean `∫ f dν` by at least `t` with probability at most `Var[f] / (|ι| t²)`.

The average has variance `Var[f] / |ι|` because the coordinates are independent
(`ProbabilityTheory.variance_sum_pi`), so this is Chebyshev's inequality
`ProbabilityTheory.meas_ge_le_variance_div_sq` for it. -/
theorem meas_ge_le_variance_div_card_mul_sq_pi [Nonempty ι] {f : Ω → ℝ} (hf : MemLp f 2 ν)
    {t : ℝ} (ht : 0 < t) :
    (Measure.pi fun _ : ι => ν) {x | t ≤ |(∑ j, f (x j)) / Fintype.card ι - ∫ a, f a ∂ν|} ≤
      ENNReal.ofReal (Var[f; ν] / (Fintype.card ι * t ^ 2)) := by
  have hN : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  have hX : ∀ _ : ι, MemLp (fun a => f a * (Fintype.card ι : ℝ)⁻¹) 2 ν :=
    fun _ => hf.mul_const _
  have hsum : (fun x : ι → Ω => (∑ j, f (x j)) / Fintype.card ι) =
      ∑ j : ι, fun x : ι → Ω => f (x j) * (Fintype.card ι : ℝ)⁻¹ := by
    ext x
    simp only [Finset.sum_apply, div_eq_mul_inv, Finset.sum_mul]
  have hmemLp : MemLp (fun x : ι → Ω => (∑ j, f (x j)) / Fintype.card ι) 2
      (Measure.pi fun _ : ι => ν) := by
    rw [hsum]
    exact memLp_finsetSum' _ fun j _ =>
      (hX j).comp_measurePreserving (measurePreserving_eval (fun _ : ι => ν) j)
  have hvar : Var[fun x : ι → Ω => (∑ j, f (x j)) / Fintype.card ι; Measure.pi fun _ : ι => ν] =
      Var[f; ν] / Fintype.card ι := by
    rw [hsum, variance_sum_pi hX, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      variance_mul_const]
    field_simp
  have hmean : ∫ x, (∑ j, f (x j)) / Fintype.card ι ∂(Measure.pi fun _ : ι => ν) =
      ∫ a, f a ∂ν := by
    rw [integral_div, integral_finsetSum _ fun j _ =>
      integrable_comp_eval (hf.integrable one_le_two)]
    rw [Finset.sum_congr rfl fun j _ =>
      integral_comp_eval (μ := fun _ : ι => ν) (i := j) hf.aestronglyMeasurable,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  have h := meas_ge_le_variance_div_sq hmemLp ht
  rwa [hvar, hmean, div_div] at h

end WeakLaw

end TauCeti
