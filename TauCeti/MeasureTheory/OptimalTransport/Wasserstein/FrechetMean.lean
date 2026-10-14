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

end TauCeti
