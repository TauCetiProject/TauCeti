/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.FrechetMean.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Space
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Borel

/-!
# Fréchet barycenters of finitely supported laws on the Wasserstein space

Let `μ j` be finitely many points of the Wasserstein space `P_p(X)` and `w j` nonnegative weights.
The `p`-Fréchet power functional of the finitely supported law `∑ j, w j • δ_{μ j}` on `P_p(X)` is
the weighted `p`-Wasserstein cost `z ↦ ∑ j, w j * W_p(z, μ j) ^ p`, which is finite on `P_p(X)`.
So over a Polish space and for `1 ≤ p < ∞`, where `P_p(X)` is a Borel space, the Fréchet
barycenters of `∑ j, w j • δ_{μ j}` are exactly the minimizers of that cost over `P_p(X)`.

## Main statements

* `TauCeti.WassersteinSpace.isFrechetBarycenter_sum_smul_dirac_iff_isMinOn` — on a Polish space,
  the Fréchet barycenters of `∑ j, w j • δ_{μ j}` on `P_p(X)` are the minimizers over `P_p(X)` of
  the weighted `p`-Wasserstein cost.
* `TauCeti.WassersteinSpace.isMinOn_sum_mul_wassersteinEDist_rpow_of_isFrechetBarycenter` — on a
  Polish space, a barycenter in `P_p(X)` of `∑ j, w j • δ_{μ j}` minimizes the weighted cost over
  all laws.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace TauCeti

variable {J X : Type*} [Fintype J] [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [CompleteSpace X] {w : J → ℝ≥0} {p : ℝ≥0∞}

/-- **Fréchet barycenters of a finitely supported law on `P_p(X)`.** On a Polish metric space and
for `1 ≤ p < ∞`, a point `ν` of the Wasserstein space `P_p(X)` is a `p`-Fréchet barycenter of
`∑ j, w j • δ_{μ j}` exactly when it minimizes the weighted `p`-Wasserstein cost
`z ↦ ∑ j, w j * W_p(z, μ j) ^ p` over `P_p(X)`. That cost is finite on `P_p(X)`, so the finiteness
condition in the definition of a barycenter holds automatically. -/
theorem WassersteinSpace.isFrechetBarycenter_sum_smul_dirac_iff_isMinOn [Fact (1 ≤ p)]
    (hp_top : p ≠ ∞) (μ : J → WassersteinSpace p X) (ν : WassersteinSpace p X) :
    IsFrechetBarycenter p (∑ j, w j • Measure.dirac (μ j)) ν ↔
      IsMinOn (fun z : WassersteinSpace p X ↦ ∑ j, (w j : ℝ≥0∞) *
          wassersteinEDist p ((z : ProbabilityMeasure X) : Measure X)
            ((μ j : ProbabilityMeasure X) : Measure X) ^ p.toReal) univ ν := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have := WassersteinSpace.borelSpace (X := X) (p := p) hp_top
  set P := ∑ j, w j • Measure.dirac (μ j)
  have hm (z : WassersteinSpace p X) : AEMeasurable (fun y ↦ edist z y) P :=
    (continuous_const.edist continuous_id).measurable.aemeasurable
  have hF (z : WassersteinSpace p X) : frechetPower p P z =
      ∑ j, (w j : ℝ≥0∞) * wassersteinEDist p ((z : ProbabilityMeasure X) : Measure X)
        ((μ j : ProbabilityMeasure X) : Measure X) ^ p.toReal := by
    simp only [P, frechetPower_sum_smul_dirac, WassersteinSpace.edist_def, ENNReal.smul_def,
      smul_eq_mul]
  have hR : frechetRadius p P ν ≠ ∞ := by
    intro h
    have := frechetRadius_rpow_eq_frechetPower hp0 hp_top (hm ν)
    rw [h, ENNReal.top_rpow_of_pos (ENNReal.toReal_pos hp0 hp_top), hF] at this
    exact WassersteinSpace.sum_mul_wassersteinEDist_rpow_ne_top μ ν this.symm
  rw [isFrechetBarycenter_iff_forall_frechetPower_le hp0 hp_top (hm ν) hm, and_iff_right hR,
    isMinOn_univ_iff]
  simp only [hF]

/-- **A barycenter in `P_p(X)` minimizes over all probability laws.** On a Polish metric space and
for `1 ≤ p < ∞`, a `p`-Fréchet barycenter `ν` in `P_p(X)` of the finitely supported law
`∑ j, w j • δ_{μ j}`, with weights summing to `1`, minimizes the weighted `p`-Wasserstein cost
`ν' ↦ ∑ j, w j * W_p(ν', μ j) ^ p` over all probability laws `ν'` on `X`, not only over `P_p(X)`.
-/
theorem WassersteinSpace.isMinOn_sum_mul_wassersteinEDist_rpow_of_isFrechetBarycenter
    [Fact (1 ≤ p)] (hp_top : p ≠ ∞) (hw : ∑ j, w j = 1) {μ : J → WassersteinSpace p X}
    {ν : WassersteinSpace p X} (hν : IsFrechetBarycenter p (∑ j, w j • Measure.dirac (μ j)) ν) :
    IsMinOn (fun ν' ↦ ∑ j, (w j : ℝ≥0∞) *
        wassersteinEDist p ν' ((μ j : ProbabilityMeasure X) : Measure X) ^ p.toReal)
      {ν' | IsProbabilityMeasure ν'} ((ν : ProbabilityMeasure X) : Measure X) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have hmin := (WassersteinSpace.isFrechetBarycenter_sum_smul_dirac_iff_isMinOn hp_top μ ν).1 hν
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hw.trans_ne one_ne_zero)
  refine isMinOn_iff.2 fun ν' (hν' : IsProbabilityMeasure ν') ↦ ?_
  by_cases htop : ∑ j, (w j : ℝ≥0∞) *
      wassersteinEDist p ν' ((μ j : ProbabilityMeasure X) : Measure X) ^ p.toReal = ∞
  · exact htop ▸ le_top
  -- A law of finite barycentric cost has finite `p`-th moment, so it is a point of `P_p(X)`.
  have hmom := hasFiniteMoment_of_sum_mul_wassersteinEDist_rpow_ne_top measurable_edist
    (Finset.mem_univ j₀) (ENNReal.coe_ne_zero.2 hj₀) (μ j₀).hasFiniteMoment
    (ENNReal.toReal_pos hp0 hp_top) htop
  have hcoe : ((WassersteinSpace.mk ⟨ν', hν'⟩ hmom : ProbabilityMeasure X) : Measure X) = ν' :=
    congrArg ProbabilityMeasure.toMeasure (WassersteinSpace.coe_mk _ _)
  have hz := isMinOn_iff.1 hmin (WassersteinSpace.mk ⟨ν', hν'⟩ hmom) (mem_univ _)
  rwa [hcoe] at hz

end TauCeti
