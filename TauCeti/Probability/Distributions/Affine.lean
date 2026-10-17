/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.CDF
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul
public import Mathlib.Probability.Moments.Variance
import TauCeti.MeasureTheory.Measure.Measurability

/-!
# Affine images of real laws

For a measure `μ` on `ℝ` and real numbers `a`, `b`, the law of `a + b X` for `X` with law `μ` is
the pushforward `μ.map (fun x => a + b * x)`. This file computes the elementary observables of
that pushforward in terms of those of `μ`: the cumulative distribution function, integrability
and moments, and the exponential transforms. Once a location-scale identity between two families
is known as an equality of measures, these formulas transfer each observable along it.

The cdf at a positive slope is the cdf of `μ` at the pulled-back point. At a negative slope the
map reverses order, so it is one minus the mass `μ` gives to the open half-line below the
pulled-back point: this left limit of the cdf cannot be replaced by the cdf itself when `μ` has
an atom there. At slope zero the pushforward of a probability measure is the Dirac mass at `a`,
which is Mathlib's `MeasureTheory.Measure.map_const`.

The variance, moment-generating function and characteristic function computations follow
Mathlib's `ProbabilityTheory.variance_id_map`, `ProbabilityTheory.variance_const_add` and
`ProbabilityTheory.variance_const_mul`, `ProbabilityTheory.mgf_const_add` and
`ProbabilityTheory.mgf_const_mul`, and `MeasureTheory.charFun_apply_real`, which they reduce to.

## Main results

* `TauCeti.Probability.map_affine_map_affine` — affine pushforwards compose;
* `TauCeti.Probability.measurable_map_affine` — affine pushforward is jointly measurable in the
  probability law, intercept, and slope;
* `TauCeti.Probability.cdf_map_affine_of_pos`, `TauCeti.Probability.cdf_map_affine_of_neg` — the
  cdf at a positive and at a negative slope;
* `TauCeti.Probability.memLp_id_map_affine_iff` — a nonconstant affine image has exactly the
  absolute moments of the original law;
* `TauCeti.Probability.integral_id_map_affine`, `TauCeti.Probability.variance_id_map_affine` —
  the mean `a + b E[X]` and the variance `b ^ 2 Var[X]`;
* `TauCeti.Probability.moment_id_map_affine`, `TauCeti.Probability.centralMoment_id_map_affine` —
  raw moments by the binomial expansion, and central moments scaled by `b ^ n`;
* `TauCeti.Probability.mgf_id_map_affine`, `TauCeti.Probability.integrableExpSet_id_map_affine`,
  `TauCeti.Probability.cgf_id_map_affine` — the moment-generating function `exp (a t) M(b t)`,
  its domain `{t | b t ∈ D}`, and the cumulant-generating function `a t + K(b t)` on it;
* `TauCeti.Probability.charFun_map_affine` — the characteristic function `exp (i a t) φ(b t)`.
-/

public section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace TauCeti.Probability

variable {μ : Measure ℝ} {a b : ℝ}

/-- The affine map `x ↦ a + b * x` is measurable. -/
private theorem measurable_affine (a b : ℝ) : Measurable fun x : ℝ => a + b * x := by fun_prop

/-- **Composition of affine pushforwards.** Applying `y ↦ c + d * y` after `x ↦ a + b * x` is the
single affine map with intercept `c + d * a` and slope `d * b`. -/
theorem map_affine_map_affine (a b c d : ℝ) :
    (μ.map fun x => a + b * x).map (fun y => c + d * y) =
      μ.map fun x => c + d * a + d * b * x := by
  rw [Measure.map_map (measurable_affine c d) (measurable_affine a b)]
  congr 1
  ext x
  simp only [Function.comp_apply]
  ring

/-- Affine pushforward is jointly measurable in the probability law, intercept, and slope. -/
@[fun_prop]
theorem measurable_map_affine :
    Measurable fun p : ProbabilityMeasure ℝ × ℝ × ℝ =>
      (p.1 : Measure ℝ).map fun x => p.2.1 + p.2.2 * x := by
  exact measurable_subtype_coe.comp
    (TauCeti.MeasureTheory.measurable_probabilityMeasure_map_of_measurable_uncurry
      (f := fun p : ℝ × ℝ => fun x => p.1 + p.2 * x) (by fun_prop))

/-! ### Cumulative distribution functions -/

/-- At a positive slope, the cdf of the affine image is the cdf of `μ` at the pulled-back point
`(x - a) / b`. -/
theorem cdf_map_affine_of_pos [IsProbabilityMeasure μ] (hb : 0 < b) (x : ℝ) :
    cdf (μ.map fun y => a + b * y) x = cdf μ ((x - a) / b) := by
  have hpre : (fun y => a + b * y) ⁻¹' Iic x = Iic ((x - a) / b) := by
    ext y
    simp only [mem_preimage, mem_Iic, le_div_iff₀ hb]
    constructor <;> intro h <;> linarith
  rw [cdf_eq_real, cdf_eq_real, map_measureReal_apply (measurable_affine a b) measurableSet_Iic,
    hpre]

/-- At a negative slope, the cdf of the affine image is one minus the mass `μ` gives to the open
half-line below the pulled-back point `(x - a) / b`, that is, one minus the left limit of the cdf
of `μ` there. -/
theorem cdf_map_affine_of_neg [IsProbabilityMeasure μ] (hb : b < 0) (x : ℝ) :
    cdf (μ.map fun y => a + b * y) x = 1 - μ.real (Iio ((x - a) / b)) := by
  have hpre : (fun y => a + b * y) ⁻¹' Iic x = (Iio ((x - a) / b))ᶜ := by
    ext y
    simp only [mem_preimage, mem_Iic, mem_compl_iff, mem_Iio, not_lt, div_le_iff_of_neg hb]
    constructor <;> intro h <;> linarith
  rw [cdf_eq_real, map_measureReal_apply (measurable_affine a b) measurableSet_Iic, hpre,
    measureReal_compl measurableSet_Iio, probReal_univ]

/-! ### Integrability and moments -/

/-- **Absolute moments of an affine image.** For a nonzero slope, the affine image of a finite
measure has a finite `p`-th absolute moment exactly when the original measure does. -/
theorem memLp_id_map_affine_iff [IsFiniteMeasure μ] (hb : b ≠ 0) {p : ℝ≥0∞} :
    MemLp id p (μ.map fun x => a + b * x) ↔ MemLp id p μ := by
  rw [memLp_map_measure_iff aestronglyMeasurable_id (measurable_affine a b).aemeasurable]
  refine ⟨fun h => ?_, fun h => (memLp_const a).add (h.const_mul b)⟩
  have h' := ((memLp_const (-a)).add h).const_mul b⁻¹
  refine h'.ae_eq (ae_of_all _ fun x => ?_)
  simp only [Pi.add_apply, Function.comp_apply, id_eq]
  field_simp
  ring

/-- **Mean of an affine image.** If `μ` is a probability measure with integrable identity, then
the mean of `a + b X` is `a + b E[X]`. -/
theorem integral_id_map_affine [IsProbabilityMeasure μ] (h : Integrable id μ) :
    ∫ x, x ∂(μ.map fun x => a + b * x) = a + b * ∫ x, x ∂μ := by
  have hb : Integrable (fun x => b * x) μ := h.const_mul b
  rw [integral_map (f := fun x => x) (measurable_affine a b).aemeasurable (by fun_prop),
    integral_add (integrable_const a) hb, integral_const, integral_const_mul]
  simp

/-- **Variance of an affine image.** The variance of `a + b X` is `b ^ 2 Var[X]`. No moment
hypothesis is needed: both sides vanish when `X` is not square-integrable and `b ≠ 0`. -/
theorem variance_id_map_affine [IsProbabilityMeasure μ] :
    Var[id; μ.map fun x => a + b * x] = b ^ 2 * Var[id; μ] := by
  rw [variance_id_map (measurable_affine a b).aemeasurable,
    variance_const_add (by fun_prop) a, variance_const_mul]
  rw [Function.id_def]

/-- **Raw moments of an affine image.** If `μ` is a finite measure with finite `n`-th
absolute moment, then the `n`-th moment of `a + b X` is the binomial expansion
`∑ k ≤ n, (n choose k) a ^ (n - k) b ^ k E[X ^ k]`. -/
theorem moment_id_map_affine [IsFiniteMeasure μ] {n : ℕ}
    (h : Integrable (fun x => |x| ^ n) μ) :
    moment id n (μ.map fun x => a + b * x) =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * a ^ (n - k) * b ^ k * moment id k μ := by
  have hk : ∀ k ∈ Finset.range (n + 1), Integrable (fun x : ℝ =>
      (n.choose k : ℝ) * a ^ (n - k) * b ^ k * x ^ k) μ := by
    intro k hk
    have habs : Integrable (fun x : ℝ => ‖x‖ ^ k) μ :=
      integrable_norm_pow_of_le (f := fun x : ℝ => x) (by fun_prop) (Nat.lt_succ_iff.mp
        (Finset.mem_range.mp hk)) (by simpa only [Real.norm_eq_abs] using h)
    refine Integrable.const_mul ?_ _
    exact habs.mono' (by fun_prop) (ae_of_all _ fun x => by simp [norm_pow])
  simp only [moment_def, Pi.pow_apply, id_eq]
  rw [integral_map (f := fun x => x ^ n) (measurable_affine a b).aemeasurable (by fun_prop)]
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ hk]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [add_comm a, add_pow]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **Central moments of an affine image.** If `μ` is a probability measure with integrable
identity, then the `n`-th central moment of `a + b X` is `b ^ n` times that of `X`. -/
theorem centralMoment_id_map_affine [IsProbabilityMeasure μ] (h : Integrable id μ) (n : ℕ) :
    centralMoment id n (μ.map fun x => a + b * x) = b ^ n * centralMoment id n μ := by
  simp only [centralMoment, Pi.pow_apply, Pi.sub_apply, id_eq]
  rw [integral_id_map_affine h, integral_map (f := fun y : ℝ => (y - (a + b * ∫ x : ℝ, x ∂μ)) ^ n)
    (measurable_affine a b).aemeasurable (by fun_prop), ← integral_const_mul (b ^ n)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  dsimp only
  rw [← mul_pow]
  ring

/-! ### Exponential transforms -/

/-- **Moment-generating function of an affine image.** `M_{a + bX}(t) = exp (a t) M_X(b t)`. -/
theorem mgf_id_map_affine (t : ℝ) :
    mgf id (μ.map fun x => a + b * x) t = exp (a * t) * mgf id μ (b * t) := by
  rw [mgf_map (measurable_affine a b).aemeasurable (by fun_prop), Function.id_comp,
    mgf_const_add, mgf_const_mul, mul_comm t a]
  rw [Function.id_def]

/-- **Exponential-integrability domain of an affine image.** `a + b X` has a finite exponential
moment at `t` exactly when `X` has one at `b t`. -/
theorem integrableExpSet_id_map_affine :
    integrableExpSet id (μ.map fun x => a + b * x) =
      (fun t => b * t) ⁻¹' integrableExpSet id μ := by
  ext t
  simp only [integrableExpSet, mem_preimage, mem_ofPred_eq, id_eq]
  rw [integrable_map_measure (by fun_prop) (measurable_affine a b).aemeasurable]
  have hfun : ((fun x : ℝ => exp (t * x)) ∘ fun x => a + b * x) =
      fun x => exp (a * t) * exp (b * t * x) := by
    ext x
    simp only [Function.comp_apply, ← exp_add]
    ring_nf
  rw [hfun, integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (exp_pos _).ne')]

/-- **Cumulant-generating function of an affine image.** On the exponential-integrability domain,
`K_{a + bX}(t) = a t + K_X(b t)`. -/
theorem cgf_id_map_affine [NeZero μ] {t : ℝ} (ht : b * t ∈ integrableExpSet id μ) :
    cgf id (μ.map fun x => a + b * x) t = a * t + cgf id μ (b * t) := by
  rw [cgf, cgf, mgf_id_map_affine, log_mul (exp_pos _).ne' (mgf_pos' (NeZero.ne μ) ht).ne',
    log_exp]

/-- **Characteristic function of an affine image.** `φ_{a + bX}(t) = exp (i a t) φ_X(b t)`. -/
theorem charFun_map_affine (t : ℝ) :
    charFun (μ.map fun x => a + b * x) t =
      Complex.exp (a * t * Complex.I) * charFun μ (b * t) := by
  rw [charFun_apply_real, charFun_apply_real,
    integral_map (measurable_affine a b).aemeasurable (by fun_prop), ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  dsimp only
  rw [← Complex.exp_add]
  push_cast
  ring_nf

end TauCeti.Probability
