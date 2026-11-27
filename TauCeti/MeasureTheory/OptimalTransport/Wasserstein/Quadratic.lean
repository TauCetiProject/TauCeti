/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Cost.Quadratic.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic

/-!
# Quadratic Wasserstein bridge to the half-squared-norm cost

On a seminormed additive group, the `2`-Wasserstein distance squared `W₂(μ, ν) ^ 2` equals twice
the optimal quadratic transport cost `TauCeti.transportCost` for `‖x - y‖ ^ 2 / 2`. Separating this
bridge from `TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic` keeps quadratic pairing-cost
theory out of general Wasserstein imports.

## Main statements

* `TauCeti.wassersteinEDist_two_sq_eq_two_mul_transportCost` — `W₂(μ, ν) ^ 2` equals twice the
  transport cost of `‖x - y‖ ^ 2 / 2`.
* `TauCeti.wassersteinEDist_ne_top_iff_transportCost_norm_sub_sq_div_two_ne_top` — finiteness of
  `W₂` distance is equivalent to finiteness of the quadratic transport cost for `‖x - y‖ ^ 2 / 2`.
* `TauCeti.transportCost_norm_sub_sq_div_two_ne_top_of_wassersteinEDist_ne_top` — finite `W₂`
  distance implies finite quadratic transport cost for `‖x - y‖ ^ 2 / 2` without topology or
  second-countability hypotheses.
* `TauCeti.isCyclicallyMonotone_support_of_eLpNorm_eq` — a coupling realizing finite quadratic
  Wasserstein distance has cyclically monotone support for the cost `‖x - y‖ ^ 2 / 2`.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

section NormedFiniteCost

variable {E : Type*} [SeminormedAddCommGroup E] [MeasurableSpace E] {μ ν : Measure E}

/-- Finite quadratic Wasserstein distance implies finite quadratic transport cost for
`‖x - y‖ ^ 2 / 2`. -/
theorem transportCost_norm_sub_sq_div_two_ne_top_of_wassersteinEDist_ne_top
    (hfin : wassersteinEDist 2 μ ν ≠ ∞) :
    transportCost (fun z : E × E ↦ ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) μ ν ≠ ∞ := by
  obtain ⟨π, hπ, hπlt⟩ := wassersteinEDist_lt_iff.1 hfin.lt_top
  have hae : AEStronglyMeasurable (fun z : E × E ↦ edist z.1 z.2) π :=
    aestronglyMeasurable_of_eLpNorm_ne_top hπlt.ne
  have hsq : ∫⁻ z : E × E, ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2) ∂π ≤
      eLpNorm (fun z : E × E ↦ edist z.1 z.2) 2 π ^ 2 := by
    rw [eLpNorm_two_sq_eq_lintegral hae]
    refine lintegral_mono fun z ↦ ?_
    rw [eNorm_eq_self, ← ENNReal.rpow_two, edist_rpow_two_eq_two_mul_ofReal_norm_sub_sq_div_two]
    exact le_mul_of_one_le_left zero_le one_le_two
  exact ((transportCost_le_lintegral hπ _).trans hsq |>.trans_lt
    (ENNReal.pow_lt_top hπlt)).ne

end NormedFiniteCost

section NormedOptimal

variable {E : Type*} [SeminormedAddCommGroup E] [MeasurableSpace E] [OpensMeasurableSpace E]
  [SecondCountableTopology E] {μ ν : Measure E}

/-- For the quadratic Wasserstein exponent `p = 2` on a seminormed additive group,
`W₂(μ, ν) ^ 2` equals twice the quadratic transport cost `‖x - y‖ ^ 2 / 2`. -/
theorem wassersteinEDist_two_sq_eq_two_mul_transportCost (μ ν : Measure E) :
    wassersteinEDist 2 μ ν ^ 2 =
      2 * transportCost (fun z : E × E ↦ ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) μ ν := by
  have h := wassersteinEDist_rpow_eq_transportCost (p := 2) (μ := μ) (ν := ν)
    measurable_edist two_ne_zero ENNReal.ofNat_ne_top
  rw [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat] at h
  rw [h, ← transportCost_const_mul two_ne_zero ENNReal.ofNat_ne_top]
  congr 1
  funext z
  exact edist_rpow_two_eq_two_mul_ofReal_norm_sub_sq_div_two z

/-- On a second countable seminormed additive group with open sets measurable, the `2`-Wasserstein
distance is finite if and only if the quadratic transport cost for `‖x - y‖ ^ 2 / 2` is finite. -/
theorem wassersteinEDist_ne_top_iff_transportCost_norm_sub_sq_div_two_ne_top (μ ν : Measure E) :
    wassersteinEDist 2 μ ν ≠ ∞ ↔
      transportCost (fun z : E × E ↦ ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) μ ν ≠ ∞ := by
  refine ⟨transportCost_norm_sub_sq_div_two_ne_top_of_wassersteinEDist_ne_top, fun hfin ↦ ?_⟩
  rw [← (ENNReal.pow_ne_top_iff (n := 2)).trans (or_iff_left two_ne_zero),
    wassersteinEDist_two_sq_eq_two_mul_transportCost]
  exact ENNReal.mul_ne_top ENNReal.ofNat_ne_top hfin

/-- **Optimal quadratic Wasserstein plans have cyclically monotone support.** If `π` is a coupling
of a finite measure `μ` and a measure `ν` at finite quadratic Wasserstein distance whose quadratic
cost realizes `W₂(μ, ν)`, then its support is cyclically monotone for `‖x - y‖ ^ 2 / 2`. -/
theorem isCyclicallyMonotone_support_of_eLpNorm_eq [IsFiniteMeasure μ] {π : Measure (E × E)}
    (hfin : wassersteinEDist 2 μ ν ≠ ∞) (hπ : IsCoupling π μ ν)
    (hW : eLpNorm (fun z : E × E ↦ edist z.1 z.2) 2 π = wassersteinEDist 2 μ ν) :
    IsCyclicallyMonotone (fun z : E × E ↦ ‖z.1 - z.2‖ ^ 2 / 2) π.support := by
  have hopt : IsOptimalCoupling (fun z : E × E ↦ ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) π μ ν :=
    isOptimalCoupling_norm_sub_sq_div_two_of_edist_rpow_two (by
      simpa only [ENNReal.toReal_ofNat] using
        (isOptimalCoupling_edist_rpow_iff measurable_edist two_ne_zero ENNReal.ofNat_ne_top).2
          ⟨hπ, hW⟩)
  exact (isCyclicallyMonotone_ofReal_iff fun _ ↦ by positivity).1
    (hopt.isCyclicallyMonotone_support continuous_ofReal_norm_sub_sq_div_two
      (transportCost_norm_sub_sq_div_two_ne_top_of_wassersteinEDist_ne_top hfin))

end NormedOptimal

end TauCeti
