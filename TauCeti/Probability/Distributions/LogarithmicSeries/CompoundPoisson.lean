/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.CompoundPoisson.RandomSum
public import TauCeti.Probability.Distributions.LogarithmicSeries.Basic
public import TauCeti.Probability.Distributions.NegativeBinomial.Basic
import TauCeti.Probability.Distributions.CompoundPoisson.Transforms
import TauCeti.Probability.Distributions.LogarithmicSeries.Transforms
import TauCeti.Probability.Distributions.NegativeBinomial.Transforms
import TauCeti.Probability.Moments.Determinacy
import TauCeti.Analysis.SpecialFunctions.Log.MulExpLtOne

/-!
# Negative-binomial laws as compound Poisson sums

For `r ≥ 0` and `0 < q < 1`, a Poisson number of logarithmic-series jumps with parameter `q`
and intensity `-r * log (1 - q)` has negative-binomial law with shape `r` and success
probability `1 - q`. The measure identity is accompanied by a random-variable version.
Shape zero includes the empty sum and gives Dirac mass at zero.

The identification uses the existing compound Poisson and logarithmic-series mgfs and
moment-generating-function uniqueness near zero.

See N. L. Johnson, A. W. Kemp, and S. Kotz, *Univariate Discrete Distributions*, 3rd ed.,
Wiley, 2005, Chapter 7, for the logarithmic-series compounding identity.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped Topology

namespace TauCeti.Probability

private theorem mgf_logarithmicSeries_compoundPoisson {r q : ℝ} (hr : 0 ≤ r)
    (hq0 : 0 < q) (hq1 : q < 1) {t : ℝ} (ht : t < -log q) :
    mgf (Nat.castAddMonoidHom ℝ)
        (compoundPoissonMeasure (Real.toNNReal (-(r * log (1 - q))))
          (logarithmicSeriesMeasure q)) t =
      ((1 - q) / (1 - q * exp t)) ^ r := by
  have hlog : log (1 - q) < 0 := log_neg (by linarith) (by linarith)
  have hrate : 0 ≤ -(r * log (1 - q)) :=
    neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hr hlog.le)
  have hprob := isProbabilityMeasure_logarithmicSeriesMeasure hq0 hq1
  have hjump : Integrable (fun k : ℕ => exp (t * (k : ℝ)))
      (logarithmicSeriesMeasure q) := by
    simpa only [Function.comp_def] using
      (MeasurableEmbedding.natCast (α := ℝ)).integrable_map_iff.mp
        ((integrable_exp_mul_id_map_cast_logarithmicSeriesMeasure_iff hq0 hq1 t).2 ht)
  have hcompound := integrable_exp_mul_compoundPoissonMeasure
    (Real.toNNReal (-(r * log (1 - q)))) (f := Nat.castAddMonoidHom ℝ) (by fun_prop) hjump
  rw [mgf_compoundPoissonMeasure _ (by fun_prop) hcompound,
    Real.coe_toNNReal _ hrate]
  have hmgf : mgf (Nat.castAddMonoidHom ℝ) (logarithmicSeriesMeasure q) t =
      log (1 - q * exp t) / log (1 - q) := by
    rw [Nat.coe_castAddMonoidHom, ← mgf_id_map (μ := logarithmicSeriesMeasure q)
      (X := (Nat.cast : ℕ → ℝ)) Measurable.of_discrete.aemeasurable]
    exact mgf_id_map_cast_logarithmicSeriesMeasure hq0 hq1 ht
  have hden : 0 < 1 - q * exp t := sub_pos.mpr ((mul_exp_lt_one_iff hq0).2 ht)
  rw [hmgf, rpow_def_of_pos (div_pos (by linarith) hden),
    log_div (by linarith) hden.ne']
  congr 1
  field_simp [ne_of_lt hlog]
  ring

/-- Logarithmic-series jumps compounded at intensity `-r * log (1 - q)` give a
negative-binomial law of shape `r` and success probability `1 - q`, including `r = 0`. -/
@[simp]
theorem compoundPoissonMeasure_logarithmicSeriesMeasure {r q : ℝ} (hr : 0 ≤ r)
    (hq0 : 0 < q) (hq1 : q < 1) :
    compoundPoissonMeasure (Real.toNNReal (-(r * log (1 - q)))) (logarithmicSeriesMeasure q) =
      negativeBinomialMeasure r (1 - q) := by
  rcases hr.eq_or_lt with rfl | hr
  · simp [negativeBinomialMeasure_zero (by linarith : 0 < 1 - q) (by linarith)]
  have hprob := isProbabilityMeasure_logarithmicSeriesMeasure hq0 hq1
  have hnb := isProbabilityMeasure_negativeBinomialMeasure hr.le
    (by linarith : 0 < 1 - q) (by linarith)
  apply (MeasurableEmbedding.natCast (α := ℝ)).map_injective
  symm
  apply TauCeti.Measure.ext_of_mgf
  · rw [integrableExpSet_id_map_cast_negativeBinomialMeasure hr
      (by linarith : 0 < 1 - q) (by linarith)]
    have hopen : IsOpen {t : ℝ | (1 - (1 - q)) * exp t < 1} :=
      isOpen_lt (by fun_prop) continuous_const
    rw [hopen.interior_eq]
    simpa using hq1
  · filter_upwards [gt_mem_nhds (neg_pos.mpr (log_neg hq0 hq1))] with t ht
    have hcp := mgf_logarithmicSeries_compoundPoisson hr.le hq0 hq1 ht
    rw [Nat.coe_castAddMonoidHom, ← mgf_id_map Measurable.of_discrete.aemeasurable] at hcp
    rw [hcp, mgf_id_map_cast_negativeBinomialMeasure hr.le (by linarith : 0 < 1 - q)
      (by linarith) (by simpa using (mul_exp_lt_one_iff hq0).2 ht)]
    simp

end TauCeti.Probability

namespace ProbabilityTheory

/-- A Poisson count independent of an iid logarithmic-series sequence selects a prefix sum
with negative-binomial law. The zero-shape case gives the empty sum almost surely. -/
theorem iIndepFun.hasLaw_sum_range_negativeBinomialMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : ℕ → Ω → ℕ} {N : Ω → ℕ} {r q : ℝ} (hindep : iIndepFun X P)
    (hr : 0 ≤ r) (hq0 : 0 < q) (hq1 : q < 1)
    (hX : ∀ i, HasLaw (X i) (TauCeti.Probability.logarithmicSeriesMeasure q) P)
    (hN : HasLaw N (poissonMeasure (Real.toNNReal (-(r * log (1 - q))))) P)
    (hNX : IndepFun N (fun ω i => X i ω) P) :
    HasLaw (fun ω => ∑ i ∈ Finset.range (N ω), X i ω)
      (TauCeti.Probability.negativeBinomialMeasure r (1 - q)) P := by
  rw [← TauCeti.Probability.compoundPoissonMeasure_logarithmicSeriesMeasure hr hq0 hq1]
  exact hindep.hasLaw_sum_range_compoundPoissonMeasure hX hN hNX

end ProbabilityTheory
