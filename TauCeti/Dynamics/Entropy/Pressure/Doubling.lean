/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Entropy.Doubling
public import TauCeti.Dynamics.Entropy.Pressure
import TauCeti.Analysis.Asymptotics.ExpGrowth

/-!
# Pressure of constant potentials for the doubling map

For the doubling map `x ↦ 2 • x` of `UnitAddCircle` and a constant potential `c`, the topological
pressure is `log 2 + c` (`TauCeti.topologicalPressure_two_nsmul_unitAddCircle_const`): the pressure
of a constant potential is the entropy plus the constant (`TauCeti.topologicalPressure_const`),
and the entropy of the doubling map is `log 2` (`TauCeti.coverEntropy_two_nsmul_unitAddCircle`).

The weights `exp (birkhoffSum T φ n x)` matter: weighting each point of a dynamical net by
`exp c` instead of `exp (n * c)` only multiplies the net counts by a constant, which does not
change their growth rate, so it would give `log 2`
(`TauCeti.iSup_expGrowthSup_exp_mul_netMaxcard_two_nsmul_unitAddCircle`).

## Main results

* `TauCeti.topologicalPressure_two_nsmul_unitAddCircle_const`: `P(doubling, c) = log 2 + c`.
* `TauCeti.iSup_expGrowthSup_exp_mul_netMaxcard_two_nsmul_unitAddCircle`: weighting the points
  of a net by `exp c` gives `log 2`.
-/

public section

namespace TauCeti

open Dynamics Set Filter ExpGrowth
open scoped Uniformity ENNReal

/-- **Check.** For the doubling map of the circle and a constant potential `c`, the topological
pressure is `log 2 + c`. -/
theorem topologicalPressure_two_nsmul_unitAddCircle_const (c : ℝ) :
    topologicalPressure (fun z : UnitAddCircle ↦ 2 • z) (fun _ ↦ c) = ENNReal.log 2 + c := by
  rw [topologicalPressure_const, coverEntropy_two_nsmul_unitAddCircle]

/-- **Check.** Weighting every point of a dynamical net of the doubling map by `exp c`, rather
than by `exp (birkhoffSum T (fun _ ↦ c) n x) = exp (n * c)`, gives growth rate `log 2` for every
`c`: a constant factor does not change exponential growth. -/
theorem iSup_expGrowthSup_exp_mul_netMaxcard_two_nsmul_unitAddCircle (c : ℝ) :
    ⨆ U ∈ 𝓤 UnitAddCircle, expGrowthSup (fun n ↦ ENNReal.ofReal (Real.exp c) *
      (netMaxcard (fun z : UnitAddCircle ↦ 2 • z) univ U n : ℝ≥0∞)) = ENNReal.log 2 := by
  have h0 : ENNReal.ofReal (Real.exp c) ≠ 0 := by simpa using Real.exp_pos c
  rw [← coverEntropy_two_nsmul_unitAddCircle, coverEntropy_eq_iSup_netEntropyEntourage]
  simp only [expGrowthSup_const_mul h0 ENNReal.ofReal_ne_top, netEntropyEntourage]

end TauCeti
