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
public import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Moments and moment-generating functions of sums under a product measure

The multinomial expansion and finite-product integration express every natural moment of a sum
of coordinate statistics in terms of their individual moments. The finite index set
`Finset.piAntidiag Finset.univ n` consists exactly of the exponent vectors with total degree `n`.

A statistic of the form `x ↦ ∑ j, f j (x j)` under a finite product measure `Measure.pi μ` has
exponential `∏ j, exp (t * f j (x j))`, so Fubini's theorem turns its moment-generating function
into the product of the coordinate ones. For a product of *probability* measures each factor is
positive exactly on its exponential-integrability domain, so the domain of the sum is then the
intersection of the domains of the coordinates. That step genuinely needs the coordinates to be
probability measures: under the zero measure, for instance, the moment-generating function
vanishes everywhere while the integrability domain is all of `ℝ`.

These are the facts that turn a quadratic statistic of a Gaussian vector, written in
eigen-coordinates, into a product of one-dimensional moment-generating functions.

The variance of a sum of coordinates is simpler still: the coordinates are independent, so their
variances add (`ProbabilityTheory.variance_sum_pi`). For the average of `n` independent copies of
one square integrable statistic this gives variance `Var[f] / n`, and Chebyshev's inequality turns
that into the **weak law of large numbers** with an explicit rate: the average deviates from the
mean by at least `t` with probability at most `Var[f] / (n t²)`.

## Main results

* `TauCeti.integral_pow_sum_pi` — the multinomial formula for natural moments of coordinate sums;
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

/-- The natural moment of a sum of coordinate statistics under a finite product measure is the
multinomial sum of products of their moments. Integrability of the coordinate powers through
order `n` suffices; the measures need not be probability measures. -/
theorem integral_pow_sum_pi [DecidableEq ι] {𝕜 : Type*} [RCLike 𝕜]
    (f : ∀ i, E i → 𝕜) (n : ℕ)
    (hf : ∀ i m, m ≤ n → Integrable (fun x ↦ f i x ^ m) (μ i)) :
    ∫ x, (∑ i, f i (x i)) ^ n ∂Measure.pi μ =
      ∑ k ∈ Finset.piAntidiag Finset.univ n,
        (Nat.multinomial Finset.univ k : 𝕜) * ∏ i, ∫ x, f i x ^ k i ∂μ i := by
  classical
  -- The zeroth powers ensure finiteness of the component measures, so Fubini applies.
  have (i : ι) : IsFiniteMeasure (μ i) :=
    (integrable_const_iff_isFiniteMeasure (one_ne_zero : (1 : 𝕜) ≠ 0)).mp
      (by simpa using hf i 0 (Nat.zero_le n))
  have hterm (k : ι → ℕ) (hk : k ∈ Finset.piAntidiag Finset.univ n) :
      Integrable (fun x ↦ (Nat.multinomial Finset.univ k : 𝕜) * ∏ i, f i (x i) ^ k i)
        (Measure.pi μ) := by
    apply Integrable.const_mul
    apply Integrable.fintype_prod_dep (f := fun i x ↦ f i x ^ k i)
    intro i
    apply hf i (k i)
    rw [← (Finset.mem_piAntidiag.mp hk).1]
    exact Finset.single_le_sum (fun j _ ↦ Nat.zero_le (k j)) (Finset.mem_univ i)
  simp_rw [Finset.sum_pow_eq_sum_piAntidiag]
  rw [integral_finsetSum _ hterm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [integral_const_mul, integral_fintype_prod_eq_prod (fun i x ↦ f i x ^ k i)]

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
deviates from its mean `∫ f dν` by at least `t` with probability at most `Var[f] / (|ι| t²)`. -/
theorem meas_ge_le_variance_div_card_mul_sq_pi [Nonempty ι] {f : Ω → ℝ} (hf : MemLp f 2 ν)
    {t : ℝ} (ht : 0 < t) :
    (Measure.pi fun _ : ι => ν) {x | t ≤ |(∑ j, f (x j)) / Fintype.card ι - ∫ a, f a ∂ν|} ≤
      ENNReal.ofReal (Var[f; ν] / (Fintype.card ι * t ^ 2)) := by
  -- The average has variance `Var[f] / |ι|` because the coordinates are independent
  -- (`variance_sum_pi`), so this is Chebyshev's inequality `meas_ge_le_variance_div_sq` for it.
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
