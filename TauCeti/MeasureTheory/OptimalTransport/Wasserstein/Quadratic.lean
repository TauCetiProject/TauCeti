/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Cost.Quadratic
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
* `TauCeti.transportCost_norm_sub_sq_div_two_ne_top_of_wassersteinEDist_ne_top` — finite `W₂`
  distance implies finite quadratic transport cost for `‖x - y‖ ^ 2 / 2`.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

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

/-- Finite quadratic Wasserstein distance implies finite quadratic transport cost for
`‖x - y‖ ^ 2 / 2`. -/
theorem transportCost_norm_sub_sq_div_two_ne_top_of_wassersteinEDist_ne_top
    (hfin : wassersteinEDist 2 μ ν ≠ ∞) :
    transportCost (fun z : E × E ↦ ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) μ ν ≠ ∞ := by
  intro htop
  have hsq := wassersteinEDist_two_sq_eq_two_mul_transportCost μ ν
  rw [htop, ENNReal.mul_top two_ne_zero] at hsq
  exact ENNReal.pow_ne_top hfin hsq

end NormedOptimal

end TauCeti
