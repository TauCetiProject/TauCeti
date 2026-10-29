/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.NoncentralBeta.Moments
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import TauCeti.Probability.Moments.WeakConvergence
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Weak continuity of noncentral Beta laws

Noncentral Beta laws depend jointly weakly continuously on their nonnegative first shape,
positive second shape and nonnegative noncentrality. This includes the atom at zero when
the first shape vanishes, and the Dirac law when the first shape and noncentrality both
vanish. The topology is the weak topology on `ProbabilityMeasure ℝ`.

Every natural moment is continuous in these parameters. The Poisson moment series from
`hasSum_integral_pow_noncentralBetaMeasure` is locally uniformly convergent: its Beta
product factors lie in `[0, 1]`, and a bound on the noncentrality gives a summable
exponential-series majorant. The method of moments
`ProbabilityMeasure.tendsto_of_tendsto_integral_pow` then applies because the laws are
concentrated on the compact interval `[0, 1]`.
-/

public section

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped NNReal

namespace TauCeti.Probability

/-- Every natural moment of the noncentral Beta law is jointly continuous on the full
probability parameter domain, including first shape zero and noncentrality zero. -/
theorem continuous_integral_pow_noncentralBetaMeasure (n : ℕ) :
    Continuous (fun p : ℝ≥0 × Ioi (0 : ℝ) × ℝ≥0 ↦
      ∫ x, x ^ n ∂noncentralBetaMeasure p.1 p.2.1 p.2.2) := by
  let f (j : ℕ) (p : ℝ≥0 × Ioi (0 : ℝ) × ℝ≥0) : ℝ :=
    (Real.exp (-(p.2.2 : ℝ) / 2) * ((p.2.2 : ℝ) / 2) ^ j / j.factorial) *
      ∏ i ∈ Finset.range n,
        ((p.1 : ℝ) + j + i) / ((p.1 : ℝ) + j + (p.2.1 : ℝ) + i)
  have hf (j : ℕ) : Continuous (f j) := by
    apply Continuous.mul (by fun_prop)
    apply continuous_finsetProd
    intro i _
    exact (by fun_prop : Continuous (fun p : ℝ≥0 × Ioi (0 : ℝ) × ℝ≥0 ↦
      (p.1 : ℝ) + j + i)).div (by fun_prop) (fun p ↦ by
        have hb : 0 < (p.2.1 : ℝ) := p.2.1.2
        positivity)
  have heq (p : ℝ≥0 × Ioi (0 : ℝ) × ℝ≥0) :
      (∫ x, x ^ n ∂noncentralBetaMeasure p.1 p.2.1 p.2.2) = ∑' j, f j p :=
    integral_pow_noncentralBetaMeasure p.1.coe_nonneg p.2.1.2 n
  simp_rw [heq]
  refine continuous_iff_continuousAt.2 fun p ↦ ?_
  -- Bound noncentrality locally to obtain one summable majorant for the whole series.
  let R : ℝ := (p.2.2 : ℝ) + 1
  have hcont : ContinuousOn (fun q ↦ ∑' j, f j q)
      {q : ℝ≥0 × Ioi (0 : ℝ) × ℝ≥0 | (q.2.2 : ℝ) < R} := by
    refine continuousOn_tsum (fun j ↦ (hf j).continuousOn)
      (Real.summable_pow_div_factorial (R / 2)) ?_
    intro j q hq
    have hb : 0 < (q.2.1 : ℝ) := q.2.1.2
    have hq' : (q.2.2 : ℝ) < R := hq
    -- The Beta product stays in the unit interval even at first shape zero.
    have hratio₀ (i : ℕ) :
        0 ≤ ((q.1 : ℝ) + j + i) / ((q.1 : ℝ) + j + (q.2.1 : ℝ) + i) := by
      positivity
    have hratio₁ (i : ℕ) :
        ((q.1 : ℝ) + j + i) / ((q.1 : ℝ) + j + (q.2.1 : ℝ) + i) ≤ 1 := by
      apply (div_le_one (by positivity)).2
      linarith
    have hprod₀ : 0 ≤ ∏ i ∈ Finset.range n,
        ((q.1 : ℝ) + j + i) / ((q.1 : ℝ) + j + (q.2.1 : ℝ) + i) :=
      Finset.prod_nonneg fun i _ ↦ hratio₀ i
    have hprod₁ : (∏ i ∈ Finset.range n,
        ((q.1 : ℝ) + j + i) / ((q.1 : ℝ) + j + (q.2.1 : ℝ) + i)) ≤ 1 :=
      Finset.prod_le_one₀ (fun i _ ↦ hratio₀ i) (fun i _ ↦ hratio₁ i)
    have hexp : Real.exp (-(q.2.2 : ℝ) / 2) ≤ 1 :=
      Real.exp_le_one_iff.2 (div_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr q.2.2.coe_nonneg) (by norm_num))
    have hpow : ((q.2.2 : ℝ) / 2) ^ j ≤ (R / 2) ^ j :=
      pow_le_pow_left₀ (by positivity)
        (div_le_div_of_nonneg_right hq'.le (by norm_num)) j
    dsimp only [f]
    rw [Real.norm_of_nonneg (by positivity)]
    calc
      _ ≤ Real.exp (-(q.2.2 : ℝ) / 2) * ((q.2.2 : ℝ) / 2) ^ j / j.factorial :=
        mul_le_of_le_one_right (by positivity) hprod₁
      _ ≤ (R / 2) ^ j / j.factorial := by
        gcongr
        exact (mul_le_of_le_one_left (by positivity) hexp).trans hpow
  exact hcont.continuousAt ((isOpen_lt (by fun_prop) continuous_const).mem_nhds
    (by dsimp [R]; linarith))

/-- Noncentral Beta laws depend jointly weakly continuously on nonnegative first shape,
positive second shape and nonnegative noncentrality, including their atomic boundaries. -/
theorem continuous_noncentralBetaMeasure :
    Continuous (Y := ProbabilityMeasure ℝ) (fun p : ℝ≥0 × Ioi (0 : ℝ) × ℝ≥0 ↦
      (⟨noncentralBetaMeasure p.1 p.2.1 p.2.2,
        isProbabilityMeasure_noncentralBetaMeasure p.1.coe_nonneg p.2.1.2 p.2.2⟩ :
          ProbabilityMeasure ℝ)) := by
  refine continuous_iff_continuousAt.2 fun p ↦ ?_
  apply ProbabilityMeasure.tendsto_of_tendsto_integral_pow (K := Icc (0 : ℝ) 1) isCompact_Icc
  · exact ae_iff.1 (ae_mem_Icc_noncentralBetaMeasure p.1 p.2.1 p.2.2)
  · intro n
    exact .of_forall fun q ↦ integrable_pow_noncentralBetaMeasure q.1 q.2.1 q.2.2 n
  · intro n
    exact (continuous_integral_pow_noncentralBetaMeasure n).tendsto p

end TauCeti.Probability

namespace Continuous

variable {T : Type*} [TopologicalSpace T]

/-- Continuous valid shapes and noncentrality give a weakly continuous noncentral Beta law
on an arbitrary topological parameter space. -/
@[fun_prop]
theorem noncentralBetaMeasure {a b : T → ℝ} {l : T → ℝ≥0}
    (ha : Continuous a) (hb : Continuous b) (hl : Continuous l)
    (ha₀ : ∀ t, 0 ≤ a t) (hb₀ : ∀ t, 0 < b t) :
    Continuous (Y := ProbabilityMeasure ℝ) (fun t ↦
      (⟨TauCeti.Probability.noncentralBetaMeasure (a t) (b t) (l t),
        TauCeti.Probability.isProbabilityMeasure_noncentralBetaMeasure (ha₀ t) (hb₀ t) (l t)⟩ :
          ProbabilityMeasure ℝ)) := by
  exact TauCeti.Probability.continuous_noncentralBetaMeasure.comp
    ((ha.subtype_mk ha₀).prodMk ((hb.subtype_mk hb₀).prodMk hl))

end Continuous
