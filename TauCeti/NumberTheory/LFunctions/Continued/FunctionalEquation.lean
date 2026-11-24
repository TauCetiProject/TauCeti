/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Continued.Basic

/-!
# The functional equation of the continued function

A functional equation `Λ(s) = ε Λ^∨(1 - s)` for a completed function passes to the continued
function against the dual record:

`γ(s) L(s) = ε N^(1/2 - s) γ^∨(1 - s) L^∨(1 - s)`.

It holds as an equality of punctured germs at every point, with no hypothesis beyond the
functional equation. For a record with a meromorphic continuation (`HasMeromorphicContinuation`)
it also holds pointwise wherever both gamma factors are regular and the record has no pole at `s`.
The pole at `1 - conj s` is then excluded by the symmetry of the polar divisor. At a pole of the
record the pointwise statement compares retained representatives and can fail.

The statements follow Christian Merten's earlier construction in Tau Ceti PR #41996,
transported to the canonical `AnalyticLFunctionData.continuedL`.

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory* (2004), §5.1.
-/

public section

open Complex ComplexConjugate Filter Topology

namespace TauCeti.LFunctions.AnalyticLFunctionData

variable {d : AnalyticLFunctionData}

private theorem gammaFactor_mul_continuedL_eq_of_completed {z : ℂ}
    (hfz : d.completed z = d.rootNumber * d.dual.completed (1 - z))
    (hc : d.completed z = ((d.conductor : ℕ) : ℂ) ^ (z / 2) * d.gammaFactor z * d.continuedL z)
    (hc' : d.dual.completed (1 - z) = ((d.conductor : ℕ) : ℂ) ^ ((1 - z) / 2) *
      d.dual.gammaFactor (1 - z) * d.dual.continuedL (1 - z)) :
    d.gammaFactor z * d.continuedL z =
      d.rootNumber * ((d.conductor : ℕ) : ℂ) ^ (1 / 2 - z) *
        d.dual.gammaFactor (1 - z) * d.dual.continuedL (1 - z) := by
  refine mul_left_cancel₀ (d.conductor_cpow_ne_zero (z / 2)) ?_
  have hexp : (1 - z) / 2 = z / 2 + (1 / 2 - z) := by ring
  rw [hexp, cpow_add _ _ (Nat.cast_ne_zero.mpr d.conductor.ne_zero)] at hc'
  linear_combination -hc + hfz + d.rootNumber * hc'

/-- **The functional equation of the continued function, as germs.** The functions
`γ(z) L(z)` and `ε N^(1/2 - z) γ^∨(1 - z) L^∨(1 - z)` agree on a punctured neighbourhood of every
point, poles included. Without a meromorphic completion both continued functions vanish. -/
theorem HasFunctionalEquation.gammaFactor_mul_continuedL_eventuallyEq
    (hfe : d.HasFunctionalEquation) (s : ℂ) :
    (fun z ↦ d.gammaFactor z * d.continuedL z) =ᶠ[𝓝[≠] s]
      fun z ↦ d.rootNumber * ((d.conductor : ℕ) : ℂ) ^ (1 / 2 - z) *
        d.dual.gammaFactor (1 - z) * d.dual.continuedL (1 - z) := by
  by_cases hm : Meromorphic d.completed
  swap
  · have hm' : ¬ Meromorphic d.dual.completed := fun h ↦ hm <| by
      simpa [dual_completed, Function.comp_def] using h.conj_conj
    simp [continuedL_of_not_meromorphic hm, continuedL_of_not_meromorphic hm']
  have hm' : Meromorphic d.dual.completed := by
    rw [dual_completed]
    exact hm.conj_conj
  have ht : Tendsto (fun z : ℂ ↦ 1 - z) (𝓝[≠] s) (𝓝[≠] (1 - s)) :=
    (continuous_const.sub continuous_id).continuousWithinAt.tendsto_nhdsWithin fun _ hz ↦
      sub_right_injective.ne hz
  filter_upwards [hfe.eventuallyEq s, completed_eventuallyEq_mul_continuedL hm s,
    ht.eventually (completed_eventuallyEq_mul_continuedL hm' (1 - s))] with z hfz hc hc'
  rw [dual_conductor] at hc'
  exact gammaFactor_mul_continuedL_eq_of_completed hfz hc hc'

/-- **The pointwise functional equation of the continued function.** For a record with a
meromorphic continuation, it holds at `s` when the record has no pole there and both gamma factors
are regular. The record then has no pole at `1 - conj s` either. -/
theorem HasFunctionalEquation.gammaFactor_mul_continuedL_eq
    (hfe : d.HasFunctionalEquation) (hm : d.HasMeromorphicContinuation) {s : ℂ}
    (hp : d.polarOrder s = 0) (hγ : d.gammaFactor s ≠ 0)
    (hγ' : d.dual.gammaFactor (1 - s) ≠ 0) :
    d.gammaFactor s * d.continuedL s =
      d.rootNumber * ((d.conductor : ℕ) : ℂ) ^ (1 / 2 - s) *
        d.dual.gammaFactor (1 - s) * d.dual.continuedL (1 - s) := by
  have hc' := hm.dual.completed_eq_mul_continuedL hγ'
  rw [dual_conductor] at hc'
  exact gammaFactor_mul_continuedL_eq_of_completed
    (hfe.completed_eq s hp ((hfe.polarOrder_one_sub_conj s).trans hp))
    (hm.completed_eq_mul_continuedL hγ) hc'

end TauCeti.LFunctions.AnalyticLFunctionData
