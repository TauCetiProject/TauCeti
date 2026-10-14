/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.FrechetMean.CATZero
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Quantile.Isometry
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Borel
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.PopulationBarycenter

/-!
# Uniqueness of quadratic barycenters on the line

The quantile isometry makes the quadratic Wasserstein space `P₂(ℝ)` a CAT(0) space
(`TauCeti.WassersteinSpace.instIsCATZeroSpace`), and the CAT(0) inequality makes quadratic Fréchet
barycenters unique. With the Le Gouic--Loubes existence theorem, every law on `P₂(ℝ)` with finite
second moment has exactly one quadratic Wasserstein barycenter. Unlike the barycenter theory on
`ℝⁿ` (`TauCeti.WassersteinSpace.subsingleton_frechetBarycenters_two`), this needs no absolute
continuity of any of the averaged laws.

## Main statements

* `TauCeti.WassersteinSpace.existsUnique_isFrechetBarycenter_real` — a law on `P₂(ℝ)` with finite
  second moment has exactly one quadratic Wasserstein barycenter.

## References

* T. Le Gouic and J.-M. Loubes, *Existence and consistency of Wasserstein barycenters*,
  Probab. Theory Related Fields 168 (2017), 901--917, for existence of population barycenters.
* K.-T. Sturm, *Probability measures on metric spaces of nonpositive curvature*, in *Heat
  Kernels and Analysis on Manifolds, Graphs, and Metric Spaces*, Contemp. Math. 338 (2003),
  357--390, for barycenters in CAT(0) spaces.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

namespace WassersteinSpace

/-- **Population Wasserstein barycenters on the line exist and are unique.** A probability law
`P` on `P₂(ℝ)` with finite second moment has exactly one quadratic Fréchet barycenter, a
minimizer of `ν ↦ ∫ W₂(ν, μ)² dP(μ)`. Existence is the Le Gouic--Loubes theorem
`TauCeti.WassersteinSpace.exists_isFrechetBarycenter`; uniqueness holds because `P₂(ℝ)` is
CAT(0). No absolute continuity is assumed. -/
theorem existsUnique_isFrechetBarycenter_real (P : Measure (WassersteinSpace 2 ℝ))
    [IsProbabilityMeasure P] (hP : HasFiniteMoment 2 P) :
    ∃! ν : WassersteinSpace 2 ℝ, IsFrechetBarycenter 2 P ν := by
  have := borelSpace (X := ℝ) (p := 2) ENNReal.ofNat_ne_top
  obtain ⟨ν, hν⟩ := exists_isFrechetBarycenter ENNReal.ofNat_ne_top P hP
  exact ⟨ν, hν, fun ν' hν' ↦ dist_eq_zero.1 (hν'.dist_eq_zero hν)⟩

end WassersteinSpace

end TauCeti
