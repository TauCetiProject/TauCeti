/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude, Codex, The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Probability.ConditionalProbability
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import TauCeti.Probability.Density
import TauCeti.Probability.Distributions.Gamma.CharFun
-- Non-public: the finite-extrema CDF formulas are used only inside proofs.
import TauCeti.Probability.Distributions.Relations
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# Elementary theory of the exponential distribution

This file completes the elementary moment, transform, and tail API for Mathlib's exponential
measure, parametrized by its rate. For a positive rate `r`, it evaluates all moments, identifies
the exact exponential-moment domain, computes the moment- and cumulant-generating functions and the
characteristic function, and deduces the mean and variance. It also establishes the memoryless
property and computes the law of the minimum of independent exponentials.

**Moments come from one formula.** `integral_pow_expMeasure` computes every moment,
`∫ x ^ n ∂(expMeasure r) = n ! / r ^ n`, and the mean and second moment are its `n = 1` and `n = 2`
specializations.

**The exponential law is the shape-one Gamma law.** Mathlib defines `expMeasure r` as
`gammaMeasure 1 r`, so the moments, the exponential-integrability domain, and the transforms are
the `a = 1` cases of the Gamma results in `TauCeti.Probability.Distributions.Gamma.Basic` and
`TauCeti.Probability.Distributions.Gamma.CharFun`, rewritten into their exponential closed forms.

## Main results

* `integrable_expMeasure_iff`, `integral_expMeasure_eq`,
  `integrable_expMeasure_iff_integrableOn_Ioi`, `integral_expMeasure_eq_integral_Ioi` —
  integrability and integration against the exponential law, transferred to the real density;
* `integrable_pow_expMeasure` — every moment is integrable, for `0 < r`;
* `integral_pow_expMeasure` — the `n`-th moment, `n ! / r ^ n`, for `0 < r`;
* `integrable_rpow_expMeasure_iff`, `integral_rpow_expMeasure` — the exact real-power moment
  threshold `-1 < q` and formula `Gamma (1 + q) / r ^ q`, for `0 < r`;
* `integral_id_expMeasure`, `integral_sq_expMeasure` — the mean and the second moment;
* `variance_id_expMeasure` — the variance `(r ^ 2)⁻¹`;
* `memLp_id_expMeasure` — the identity is square-integrable, for `0 < r`;
* `memLp_log_expMeasure`, `integrable_log_expMeasure`, `integral_log_expMeasure` — finite moments,
  integrability, and the mean of the logarithm under a positive-rate exponential law;
* `integrable_exp_mul_expMeasure_iff` — exact exponential integrability threshold `t < r`;
* `integrableExpSet_id_expMeasure` — exact domain `(-∞, r)`;
* `mgf_id_expMeasure` — moment-generating function `r / (r - t)`;
* `cgf_id_expMeasure` — cumulant-generating function `log (r / (r - t))`;
* `charFun_expMeasure` — characteristic function `(r : ℂ) / (r - I * t)`;
* `measureReal_Ioi_expMeasure`, `measure_Ioi_expMeasure` — tail probabilities;
* `expMeasure_map_const_mul` — positive scaling divides the rate;
* `memoryless_expMeasure` — the conditional tail is unchanged by elapsed time;
* `map_sub_cond_expMeasure` — conditional on exceeding a nonnegative threshold, the excess
  has the original exponential law;
* `map_min_expMeasure` — the minimum map sends a product of exponential laws to the exponential
  law whose rate is the sum of the rates;
* `hasLaw_min_expMeasure_of_indepFun` — minimum of independent exponentials;
* `hasLaw_min_iid_expMeasure` — minimum of `d` i.i.d. exponentials of rate `r` is exponential of
  rate `d * r`.
* `nnrealExpMeasure` — the exponential measure transported to `ℝ≥0`.

## References

* [mathlib4#35504](https://github.com/leanprover-community/mathlib4/pull/35504) by Joakim
  Björnander (Apache 2.0): the names and theorem shapes of the mgf, moment and memorylessness
  results below, and the proof of memorylessness, are adapted from it.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal NNReal Topology

namespace TauCeti.Probability

variable {a r s t : ℝ} {n : ℕ}

/-- `expMeasure r` is the Lebesgue measure weighted by its exponential density. -/
theorem expMeasure_eq_withDensity (r : ℝ) :
    expMeasure r = volume.withDensity (exponentialPDF r) := rfl

/-- Every singleton has zero exponential measure, for every rate. -/
instance nullSingletonClass_expMeasure (r : ℝ) : NullSingletonClass (expMeasure r) := by
  rw [expMeasure_eq_withDensity]
  infer_instance

/-- `expMeasure r` is its exponential density against Lebesgue measure restricted to the
positive half-line. -/
theorem expMeasure_eq_withDensity_restrict_Ioi (r : ℝ) :
    expMeasure r = (volume.restrict (Ioi (0 : ℝ))).withDensity (exponentialPDF r) := by
  -- Mathlib defines the exponential measure and density as the shape-one Gamma versions.
  change gammaMeasure 1 r = (volume.restrict (Ioi (0 : ℝ))).withDensity (gammaPDF 1 r)
  exact gammaMeasure_eq_withDensity_restrict_Ioi 1 r

/-- The measure `expMeasure r` is concentrated on the positive reals, for every `r`. For `0 < r`
this says an exponential random variable is almost surely positive; for `r ≤ 0` the measure is
zero and the statement holds trivially. -/
theorem ae_pos_expMeasure (r : ℝ) : ∀ᵐ x ∂expMeasure r, 0 < x := by
  rw [expMeasure]
  exact ae_pos_gammaMeasure 1 r

/-- Scaling an exponential variable by a positive constant divides its rate by that constant. -/
@[simp]
theorem expMeasure_map_const_mul (hr : 0 < r) {c : ℝ} (hc : 0 < c) :
    (expMeasure r).map (c * ·) = expMeasure (r / c) := by
  simpa only [expMeasure] using gammaMeasure_map_const_mul one_pos hr hc

/-- `expMeasure r` presented by its real-valued density, the form in which the shared density
bridge of `TauCeti/Probability/Density.lean` applies. -/
private lemma expMeasure_eq_withDensity_ofReal (r : ℝ) :
    expMeasure r = volume.withDensity fun x => ENNReal.ofReal (exponentialPDFReal r x) :=
  (rfl)

section Transfer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Integrability transfer.** A function is integrable against an exponential law with positive
rate exactly when its density-weighted version is Lebesgue integrable. -/
theorem integrable_expMeasure_iff (hr : 0 < r) {g : ℝ → E} :
    Integrable g (expMeasure r) ↔ Integrable fun x => exponentialPDFReal r x • g x := by
  rw [expMeasure_eq_withDensity_ofReal]
  exact Probability.integrable_withDensity_ofReal_iff
    (measurable_exponentialPDFReal r).aemeasurable (ae_of_all _ (exponentialPDFReal_nonneg hr))

/-- **Integral transfer.** An integral against an exponential law with positive rate is the
density-weighted Lebesgue integral. -/
theorem integral_expMeasure_eq (hr : 0 < r) (g : ℝ → E) :
    ∫ x, g x ∂expMeasure r = ∫ x, exponentialPDFReal r x • g x := by
  rw [expMeasure_eq_withDensity_ofReal]
  exact Probability.integral_withDensity_ofReal
    (measurable_exponentialPDFReal r).aemeasurable (ae_of_all _ (exponentialPDFReal_nonneg hr)) g

/-- Integrability against an exponential law is integrability of the weighted integrand over
`(0, ∞)`. -/
theorem integrable_expMeasure_iff_integrableOn_Ioi (hr : 0 < r) (g : ℝ → E) :
    Integrable g (expMeasure r) ↔
      IntegrableOn (fun x => (r * exp (-(r * x))) • g x) (Ioi 0) := by
  rw [expMeasure, integrable_gammaMeasure_iff_integrableOn_Ioi one_pos hr]
  simp only [Real.rpow_one, Gamma_one, div_one, sub_self, rpow_zero, mul_one]

/-- An integral against an exponential law is the set integral of the weighted integrand over
`(0, ∞)`. -/
theorem integral_expMeasure_eq_integral_Ioi (hr : 0 < r) (g : ℝ → E) :
    ∫ x, g x ∂expMeasure r = ∫ x in Ioi 0, (r * exp (-(r * x))) • g x := by
  rw [expMeasure, integral_gammaMeasure_eq_integral_Ioi one_pos hr]
  simp only [Real.rpow_one, Gamma_one, div_one, sub_self, rpow_zero, mul_one]

end Transfer

/-- A real power is integrable under a positive-rate exponential law exactly when its exponent
is greater than `-1`. -/
@[simp]
theorem integrable_rpow_expMeasure_iff (hr : 0 < r) (q : ℝ) :
    Integrable (fun x : ℝ ↦ x ^ q) (expMeasure r) ↔ -1 < q := by
  rw [expMeasure, integrable_rpow_gammaMeasure_iff one_pos hr]

/-- The real-power moment of a positive-rate exponential law, on its exact integrability
domain. -/
theorem integral_rpow_expMeasure (hr : 0 < r) {q : ℝ} (hq : -1 < q) :
    ∫ x : ℝ, x ^ q ∂expMeasure r = Real.Gamma (1 + q) / r ^ q := by
  rw [expMeasure, integral_rpow_gammaMeasure one_pos hr hq, Real.Gamma_one, div_one,
    Real.rpow_neg hr.le, inv_mul_eq_div]

/-- **Every moment of the exponential law is integrable.** This is not implied by the moment
formula below: Lean's integral is defined for non-integrable functions too, so an integral equality
alone says nothing about finiteness. -/
@[simp]
theorem integrable_pow_expMeasure (hr : 0 < r) (n : ℕ) :
    Integrable (fun x => x ^ n) (expMeasure r) := by
  rw [expMeasure]
  exact integrable_pow_gammaMeasure one_pos hr n

/-- **The moments of the exponential law.** `∫ x ^ n ∂(expMeasure r) = n ! / r ^ n`, for every `n`.

No nondegeneracy hypothesis on `n` is needed: at `n = 0` both sides are `1`. The mean and the
second moment below are the `n = 1` and `n = 2` cases. -/
@[simp]
theorem integral_pow_expMeasure (hr : 0 < r) (n : ℕ) :
    ∫ x, x ^ n ∂(expMeasure r) = (Nat.factorial n : ℝ) / r ^ n := by
  rw [expMeasure, integral_pow_gammaMeasure one_pos hr, add_comm,
    Real.Gamma_nat_eq_factorial, Real.Gamma_one, one_mul]

/-- **The mean of the exponential law** with rate `r` is `r⁻¹`. -/
@[simp]
theorem integral_id_expMeasure (hr : 0 < r) : ∫ x, x ∂(expMeasure r) = r⁻¹ := by
  simpa using integral_pow_expMeasure hr 1

/-- The second moment of the exponential law with rate `r` is `2 / r ^ 2`. -/
theorem integral_sq_expMeasure (hr : 0 < r) : ∫ x, x ^ 2 ∂(expMeasure r) = 2 / r ^ 2 := by
  simpa using integral_pow_expMeasure hr 2

/-- **The variance of the exponential law** with rate `r` is `(r ^ 2)⁻¹`. -/
@[simp]
theorem variance_id_expMeasure (hr : 0 < r) : Var[id; expMeasure r] = (r ^ 2)⁻¹ := by
  rw [expMeasure, variance_id_gammaMeasure one_pos hr, one_div]

/-- The identity function belongs to `L²` of an exponential law with positive rate. -/
theorem memLp_id_expMeasure (hr : 0 < r) : MemLp id 2 (expMeasure r) := by
  rw [expMeasure]
  exact memLp_id_gammaMeasure one_pos hr

/-- The logarithm belongs to every finite `Lᵖ` space under a positive-rate exponential law. -/
theorem memLp_log_expMeasure (hr : 0 < r) (p : ℝ≥0) : MemLp log p (expMeasure r) := by
  apply memLp_of_mem_interior_integrableExpSet
  apply interior_mono (s := Ioi (-1))
  · intro t ht
    rw [integrableExpSet, expMeasure]
    refine ((integrable_rpow_gammaMeasure_iff one_pos hr t).2 ht).congr ?_
    filter_upwards [ae_pos_gammaMeasure 1 r] with x hx
    rw [Real.rpow_def_of_pos hx]
    congr 1
    ring
  · simp

/-- The logarithm is integrable under every positive-rate exponential law. -/
@[simp]
theorem integrable_log_expMeasure (hr : 0 < r) : Integrable log (expMeasure r) :=
  memLp_one_iff_integrable.mp (memLp_log_expMeasure hr 1)

/-- The mean of the logarithm under an exponential law of positive rate `r` is
`-γ - log r`. -/
@[simp]
theorem integral_log_expMeasure (hr : 0 < r) :
    ∫ e : ℝ, log e ∂expMeasure r = -Real.eulerMascheroniConstant - log r := by
  rw [integral_expMeasure_eq_integral_Ioi hr]
  simp only [smul_eq_mul]
  have hscale := integral_comp_mul_left_Ioi'
    (fun y : ℝ => exp (-y) * log (y / r)) 0 hr
  simp only [mul_zero, mul_div_cancel_left₀ _ hr.ne', smul_eq_mul] at hscale
  have hlog : IntegrableOn (fun x : ℝ => log x * exp (-x)) (Ioi 0) := by
    simpa only [one_mul, mul_one, neg_mul, smul_eq_mul, mul_comm] using
      (integrable_expMeasure_iff_integrableOn_Ioi one_pos log).mp
        (integrable_log_expMeasure one_pos)
  calc
    (∫ x in Ioi 0, r * exp (-(r * x)) * log x) =
        r * ∫ x in Ioi 0, exp (-(r * x)) * log x := by
      rw [← integral_const_mul]
      congr 1
      funext x
      ring
    _ = ∫ x in Ioi 0, exp (-x) * log (x / r) := hscale
    (∫ x in Ioi 0, exp (-x) * log (x / r)) =
        ∫ x in Ioi 0, log x * exp (-x) - log r * exp (-x) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp only
      rw [log_div (ne_of_gt hx) hr.ne']
      ring
    _ = -Real.eulerMascheroniConstant - log r := by
      rw [integral_sub hlog ((integrableOn_exp_neg_Ioi 0).const_mul _),
        integral_const_mul, integral_exp_neg_Ioi_zero]
      linarith [Real.eulerMascheroniConstant_eq_neg_integral_log]

/-- **The exact exponential-integrability threshold.** The integrand `exp (t * x)` is integrable
against an exponential law with positive rate `r` exactly when `t < r`. -/
@[simp]
lemma integrable_exp_mul_expMeasure_iff (hr : 0 < r) :
    Integrable (fun x => exp (t * x)) (expMeasure r) ↔ t < r := by
  rw [expMeasure]
  exact ⟨fun h => not_le.mp fun hrt => not_integrable_exp_mul_id_gammaMeasure one_pos hr hrt h,
    integrable_exp_mul_id_gammaMeasure one_pos hr⟩

/-- **The exact exponential-integrability domain** of an exponential law with positive rate is
`(-∞, r)`. -/
@[simp]
theorem integrableExpSet_id_expMeasure (hr : 0 < r) :
    integrableExpSet id (expMeasure r) = Set.Iio r := by
  rw [expMeasure, integrableExpSet_id_gammaMeasure one_pos hr]

/-- **The moment-generating function of an exponential law** with positive rate, on its finiteness
domain `t < r`. -/
@[simp]
theorem mgf_id_expMeasure (hr : 0 < r) (ht : t < r) :
    mgf id (expMeasure r) t = r / (r - t) := by
  rw [expMeasure, mgf_id_gammaMeasure one_pos hr ht, Real.rpow_neg_one,
    one_sub_div hr.ne', inv_div]

/-- The cumulant-generating function of an exponential law with positive rate. -/
@[simp]
theorem cgf_id_expMeasure (hr : 0 < r) (ht : t < r) :
    cgf id (expMeasure r) t = log (r / (r - t)) := by
  rw [cgf, mgf_id_expMeasure hr ht]

/-- The characteristic function of an exponential law with positive rate. -/
@[simp]
theorem charFun_expMeasure (hr : 0 < r) (t : ℝ) :
    charFun (expMeasure r) t = (r : ℂ) / (r - Complex.I * t) := by
  rw [expMeasure, charFun_gammaMeasure one_pos hr, Complex.ofReal_one,
    Complex.cpow_neg_one, one_sub_div (Complex.ofReal_ne_zero.mpr hr.ne'), inv_div]

/-- The real-valued tail probability of a positive-rate exponential law. -/
@[simp]
lemma measureReal_Ioi_expMeasure (hr : 0 < r) (x : ℝ) :
    (expMeasure r).real (Ioi x) = if 0 ≤ x then exp (-(r * x)) else 1 := by
  have _ : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  rw [← compl_Iic, measureReal_compl measurableSet_Iic, probReal_univ, ← cdf_eq_real,
    cdf_expMeasure_eq hr x]
  by_cases hx : 0 ≤ x
  · rw [ite_eq_left hx, ite_eq_left hx]
    ring
  · rw [ite_eq_right hx, ite_eq_right hx]
    ring

/-- The tail probability of a positive-rate exponential law. -/
@[simp]
lemma measure_Ioi_expMeasure (hr : 0 < r) (x : ℝ) :
    (expMeasure r) (Ioi x) = ENNReal.ofReal (if 0 ≤ x then exp (-(r * x)) else 1) := by
  have _ : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  rw [← measureReal_Ioi_expMeasure hr x, measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- An exponential law of positive rate has positive survival at every finite point. -/
theorem cdf_expMeasure_lt_one (hr : 0 < r) (x : ℝ) : cdf (expMeasure r) x < 1 := by
  rw [cdf_expMeasure_eq hr]
  split_ifs <;> linarith [Real.exp_pos (-(r * x))]

/-- The memoryless property of a positive-rate exponential law, stated with conditional
probability: after surviving for time `s`, the chance of surviving a further time `t` is the
original tail probability at `t`. -/
theorem memoryless_expMeasure (hr : 0 < r) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    cond (expMeasure r) (Ioi s) (Ioi (s + t)) = (expMeasure r) (Ioi t) := by
  have hst : Ioi s ∩ Ioi (s + t) = Ioi (s + t) := by
    rw [Set.inter_eq_right]
    intro x hx
    exact lt_of_le_of_lt (le_add_of_nonneg_right ht) hx
  rw [cond_apply measurableSet_Ioi, hst, measure_Ioi_expMeasure hr s,
    measure_Ioi_expMeasure hr (s + t), measure_Ioi_expMeasure hr t,
    ite_eq_left hs, ite_eq_left (add_nonneg hs ht), ite_eq_left ht]
  have hexponent : -(-(r * s)) + -(r * (s + t)) = -(r * t) := by ring
  rw [← ENNReal.ofReal_inv_of_pos (exp_pos _), ← ENNReal.ofReal_mul (by positivity),
    ← Real.exp_neg, ← Real.exp_add, hexponent]

/-- The excess above a nonnegative threshold, conditional on exceeding that threshold, has
the original exponential law. This is the measure-level form of memorylessness. -/
theorem map_sub_cond_expMeasure (hr : 0 < r) (hs : 0 ≤ s) :
    (cond (expMeasure r) (Ioi s)).map (fun x => x - s) = expMeasure r := by
  let _ := isProbabilityMeasure_expMeasure hr
  have htail : expMeasure r (Ioi s) ≠ 0 := by
    rw [measure_Ioi_expMeasure hr, ite_eq_left hs]
    exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  let _ := cond_isProbabilityMeasure htail
  apply Measure.eq_of_cdf
  ext x
  have hpre : (fun y : ℝ => y - s) ⁻¹' Iic x = Iic (s + x) := by
    ext y
    simp only [mem_preimage, mem_Iic]
    constructor <;> intro h <;> linarith
  rw [cdf_eq_real, map_measureReal_apply (by fun_prop) measurableSet_Iic, hpre]
  by_cases hx : 0 ≤ x
  · have hmemory : (cond (expMeasure r) (Ioi s)).real (Ioi (s + x)) =
        (expMeasure r).real (Ioi x) :=
      congrArg ENNReal.toReal (memoryless_expMeasure hr hs hx)
    rw [← compl_Ioi, measureReal_compl measurableSet_Ioi, probReal_univ, hmemory,
      cdf_eq_real, ← compl_Ioi, measureReal_compl measurableSet_Ioi, probReal_univ]
  · have hinter : Ioi s ∩ Iic (s + x) = ∅ := by
      ext y
      simp only [mem_inter_iff, mem_Ioi, mem_Iic, mem_empty_iff_false, iff_false]
      rintro ⟨hy, hy'⟩
      linarith
    rw [measureReal_def, cond_apply measurableSet_Ioi, hinter]
    simp [cdf_expMeasure_eq hr, hx]

/-- **The minimum of independent exponential laws is exponential.** Mapping the product of
positive-rate exponential laws under the pointwise minimum gives the exponential law whose rate
is the sum of the input rates. -/
theorem map_min_expMeasure (hr : 0 < r) (hs : 0 < s) :
    ((expMeasure r).prod (expMeasure s)).map (fun z => min z.1 z.2) =
      expMeasure (r + s) := by
  have _ : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  have _ : IsProbabilityMeasure (expMeasure s) := isProbabilityMeasure_expMeasure hs
  have _ : IsProbabilityMeasure (expMeasure (r + s)) :=
    isProbabilityMeasure_expMeasure (add_pos hr hs)
  apply Measure.eq_of_cdf
  ext x
  rw [cdf_eq_real, map_measureReal_apply_of_aemeasurable (by fun_prop) measurableSet_Iic,
    cdf_expMeasure_eq (add_pos hr hs) x]
  have hpreimage : (fun z : ℝ × ℝ => min z.1 z.2) ⁻¹' Iic x =
      (Ioi x ×ˢ Ioi x)ᶜ := by
    ext z
    simp only [mem_preimage, mem_Iic, mem_compl_iff, mem_prod, mem_Ioi, not_and_or, not_lt,
      min_le_iff]
  rw [hpreimage]
  rw [measureReal_compl (measurableSet_Ioi.prod measurableSet_Ioi), probReal_univ,
    measureReal_prod_prod,
    measureReal_Ioi_expMeasure hr x, measureReal_Ioi_expMeasure hs x]
  by_cases hx : 0 ≤ x
  · have hexp : -(r * x) + -(s * x) = -((r + s) * x) := by ring
    rw [ite_eq_left hx, ite_eq_left hx, ite_eq_left hx, ← exp_add, hexp]
  · rw [ite_eq_right hx, ite_eq_right hx, ite_eq_right hx]
    norm_num

/-- The minimum of two independent random variables with exponential laws has an exponential law
whose rate is the sum of their rates. -/
theorem hasLaw_min_expMeasure_of_indepFun {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X Y : Ω → ℝ} (hr : 0 < r) (hs : 0 < s)
    (hXY : IndepFun X Y P) (hX : HasLaw X (expMeasure r) P)
    (hY : HasLaw Y (expMeasure s) P) :
    HasLaw (fun ω => min (X ω) (Y ω)) (expMeasure (r + s)) P := by
  have _ : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  have _ : IsFiniteMeasure P := hX.isFiniteMeasure
  have hpair : HasLaw (fun ω => (X ω, Y ω))
      ((expMeasure r).prod (expMeasure s)) P := hXY.hasLaw_prod hX hY
  have hmin := (hasLaw_map ((measurable_fst.min measurable_snd).aemeasurable)).comp hpair
  rw [map_min_expMeasure hr hs] at hmin
  exact hmin.congr (ae_of_all _ fun _ => rfl)

/-- The minimum of `d` independent exponential variables of a common positive rate `r` is
exponential of rate `d * r`. This is the `d`-fold form of
`TauCeti.Probability.hasLaw_min_expMeasure_of_indepFun`, which allows two different rates. -/
theorem hasLaw_min_iid_expMeasure {Ω ι : Type*} {mΩ : MeasurableSpace Ω} [Fintype ι] [Nonempty ι]
    {P : Measure Ω} {X : ι → Ω → ℝ} (hr : 0 < r) (hindep : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) (expMeasure r) P) :
    HasLaw (fun ω => Finset.univ.inf' Finset.univ_nonempty fun i => X i ω)
      (expMeasure ((Fintype.card ι : ℝ) * r)) P := by
  have hd : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos_iff.2 ‹Nonempty ι›
  have _ : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  have _ : IsProbabilityMeasure (expMeasure ((Fintype.card ι : ℝ) * r)) :=
    isProbabilityMeasure_expMeasure (mul_pos hd hr)
  have hmin : AEMeasurable (fun ω => Finset.univ.inf' Finset.univ_nonempty fun i => X i ω) P := by
    simp_rw [Finset.inf'_univ_eq_ciInf]
    exact AEMeasurable.iInf fun i => (hlaw i).aemeasurable
  have _ : IsProbabilityMeasure P := (hlaw (Classical.arbitrary ι)).isProbabilityMeasure
  refine ⟨hmin, ?_⟩
  refine Measure.eq_of_cdf _ _ ?_
  ext x
  rw [cdf_min_iid hindep hlaw x, cdf_expMeasure_eq hr x,
    cdf_expMeasure_eq (mul_pos hd hr) x]
  by_cases hx : 0 ≤ x
  · rw [ite_eq_left hx, ite_eq_left hx, sub_sub_cancel, ← Real.exp_nat_mul]
    congr 2
    ring
  · rw [ite_eq_right hx, ite_eq_right hx, sub_zero, one_pow, sub_self]

/-- The exponential measure of rate `r` on `ℝ≥0`, obtained by transporting the usual exponential
law on `ℝ` along `Real.toNNReal`.

For `r > 0` this transport loses no information because the exponential law is supported on the
nonnegative half-line. -/
noncomputable def nnrealExpMeasure (r : ℝ) : Measure ℝ≥0 :=
  (expMeasure r).map Real.toNNReal

/-- The exponential measure on `ℝ≥0` is the pushforward of Mathlib's exponential measure along
`Real.toNNReal`. -/
theorem nnrealExpMeasure_def (r : ℝ) :
    nnrealExpMeasure r = (expMeasure r).map Real.toNNReal := (rfl)

/-- At unit rate, `nnrealExpMeasure` is the measure with density `e⁻ˣ` on the nonnegative real
half-line, transported to `ℝ≥0`.  The displayed `if` makes the zero density on negative reals
explicit before the transport. -/
theorem nnrealExpMeasure_one_eq_map_withDensity :
    nnrealExpMeasure 1 =
      (volume.withDensity fun x : ℝ =>
        ENNReal.ofReal (if 0 ≤ x then Real.exp (-x) else 0)).map Real.toNNReal := by
  rw [nnrealExpMeasure_def, Probability.expMeasure_eq_withDensity]
  apply congrArg (Measure.map Real.toNNReal)
  apply congrArg volume.withDensity
  funext x
  rw [exponentialPDF_eq]
  by_cases hx : 0 ≤ x <;> simp [hx]

/-- The positive-rate exponential measure on `ℝ≥0` is a probability measure. -/
theorem isProbabilityMeasure_nnrealExpMeasure {r : ℝ} (hr : 0 < r) :
    IsProbabilityMeasure (nnrealExpMeasure r) := by
  let _ := isProbabilityMeasure_expMeasure hr
  rw [nnrealExpMeasure_def]
  infer_instance

end TauCeti.Probability
