/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic
public import TauCeti.Probability.Quantile

/-!
# The monotone quantile coupling of two real laws

Two probability laws on `ℝ` are simultaneously represented by their quantile functions: each is
the law of its own quantile function under the uniform law on the open unit interval. Reading the
two quantile functions off the *same* uniform variable produces the **monotone coupling**

`μ.quantileCoupling ν = (volume.restrict (Ioo 0 1)).map fun t ↦ (μ.quantile t, ν.quantile t)`,

the classical monotone rearrangement of the two laws: both coordinates are nondecreasing
functions of one and the same variable, by `MeasureTheory.Measure.monotoneOn_quantile`. It is a
genuine transport plan of `μ` and `ν`, and its transport objective for the ground distance of `ℝ`
is the `L^p (0,1)` distance of the two quantile functions. Every `p`-Wasserstein distance of two
real laws is therefore at most that explicit one-dimensional integral.

The reverse inequality — that the monotone coupling is optimal, so that the bound below is an
identity — is a separate result about the rearrangement inequality for the costs `|x - y| ^ p` and
is not proved here.

## Main definitions

* `MeasureTheory.Measure.quantileCoupling` — the monotone coupling of two real laws.

## Main statements

* `MeasureTheory.Measure.isCoupling_quantileCoupling` — the monotone coupling is a transport plan;
* `TauCeti.eLpNorm_edist_quantileCoupling` — its transport objective is the `L^p (0,1)` distance
  of the two quantile functions;
* `TauCeti.wassersteinEDist_le_eLpNorm_quantile_sub` — the resulting upper bound on the
  Wasserstein distance of two real laws.

## References

* C. Villani, *Topics in Optimal Transportation*, GSM 58, AMS 2003, §2.2, where the monotone
  rearrangement of two real laws is built from the quantile functions.
* F. Santambrogio, *Optimal Transport for Applied Mathematicians*, Birkhäuser 2015, §2.2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace MeasureTheory.Measure

/-- The **monotone coupling** of two laws on `ℝ`: the joint law of the two quantile functions
read off a single uniform variable on the open unit interval. Both coordinates are nondecreasing
in that variable, which is what makes the plan the monotone rearrangement of the two laws. -/
def quantileCoupling (μ ν : Measure ℝ) : Measure (ℝ × ℝ) :=
  (volume.restrict (Ioo (0 : ℝ) 1)).map fun t ↦ (μ.quantile t, ν.quantile t)

/-- The monotone coupling is the pushforward of the uniform law along the pair of quantile
functions. The definition's body is not exposed, so this is the lemma downstream modules should
rewrite with. -/
theorem quantileCoupling_def (μ ν : Measure ℝ) :
    quantileCoupling μ ν
      = (volume.restrict (Ioo (0 : ℝ) 1)).map fun t ↦ (μ.quantile t, ν.quantile t) := (rfl)

/-- The monotone coupling is a transport plan of the two laws: inverse transform sampling
identifies each of its marginals. -/
theorem isCoupling_quantileCoupling (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : TauCeti.IsCoupling (quantileCoupling μ ν) μ ν where
  fst_eq := by
    rw [Measure.fst, quantileCoupling_def, Measure.map_map measurable_fst (by fun_prop)]
    exact μ.map_quantile_volume_Ioo
  snd_eq := by
    rw [Measure.snd, quantileCoupling_def, Measure.map_map measurable_snd (by fun_prop)]
    exact ν.map_quantile_volume_Ioo

/-- The monotone coupling of any two laws on `ℝ` is a probability measure, being a pushforward of
the uniform law on the open unit interval. -/
instance isProbabilityMeasure_quantileCoupling (μ ν : Measure ℝ) :
    IsProbabilityMeasure (quantileCoupling μ ν) := by
  have : IsProbabilityMeasure (volume.restrict (Ioo (0 : ℝ) 1)) := ⟨by simp⟩
  rw [quantileCoupling_def]
  infer_instance

end MeasureTheory.Measure

namespace TauCeti

/-- The transport objective of the monotone coupling is the `L^p (0,1)` distance of the two
quantile functions. -/
theorem eLpNorm_edist_quantileCoupling (p : ℝ≥0∞) (μ ν : Measure ℝ) :
    eLpNorm (fun z : ℝ × ℝ ↦ edist z.1 z.2) p (μ.quantileCoupling ν)
      = eLpNorm (fun t ↦ μ.quantile t - ν.quantile t) p (volume.restrict (Ioo (0 : ℝ) 1)) := by
  rw [Measure.quantileCoupling_def,
    eLpNorm_map_measure measurable_edist.aestronglyMeasurable (by fun_prop)]
  exact eLpNorm_congr_enorm_ae
    (.of_forall fun t ↦ by simp [Function.comp_apply, edist_eq_enorm_sub])

/-- The `p`-Wasserstein distance of two real laws is at most the `L^p (0,1)` distance of their
quantile functions, the transport objective of the monotone coupling. -/
theorem wassersteinEDist_le_eLpNorm_quantile_sub (p : ℝ≥0∞) (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    wassersteinEDist p μ ν
      ≤ eLpNorm (fun t ↦ μ.quantile t - ν.quantile t) p (volume.restrict (Ioo (0 : ℝ) 1)) :=
  (wassersteinEDist_le (μ.isCoupling_quantileCoupling ν) p).trans_eq
    (eLpNorm_edist_quantileCoupling p μ ν)

end TauCeti
