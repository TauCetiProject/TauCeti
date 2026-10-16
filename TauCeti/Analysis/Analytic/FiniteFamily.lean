/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.ChangeOrigin
public import TauCeti.Topology.Order.FiniteFamily

/-!
# Distinct ordered analytic branches

For a finite family of real analytic germs, suppose every pair coinciding at the central
parameter agrees as germs. Selecting one label for each distinct central value produces
analytic functions on a common open neighborhood, strictly ordered at every parameter there,
with exactly the same range as the original family. Thus repeated root labels can be removed
without losing analyticity or any roots. The selection is fixed throughout the neighborhood;
it is not a pointwise sorting operation. Zero branches and empty families are allowed.

The collision hypothesis is essential: the germs `x ↦ x` and `x ↦ -x` coincide at zero but
their distinct-value count changes there. For polynomial root branches, persistence of
collisions must be established before applying the ordering theorem.

## References

S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
construction*, Journal of Symbolic Computation 92 (2019), 52–69, Section 4.
-/

public section

open Filter Set Topology

namespace TauCeti

/-- Remove repeated labels from a finite real analytic family with persistent central
collisions. On one open neighborhood the selected original functions are analytic, strictly
increasing in their index, and enumerate exactly the original range. The embedding selects
labels once and for all, so further identities of the original branches remain available. -/
theorem exists_analyticOnNhd_strictMono_range_eq {E ι : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Finite ι] {f : ι → E → ℝ} {x₀ : E}
    (hf : ∀ i, AnalyticAt ℝ (f i) x₀)
    (heq : ∀ i j, f i x₀ = f j x₀ → f i =ᶠ[𝓝 x₀] f j) :
    ∃ k : ℕ, ∃ e : Fin k ↪ ι, ∃ U : Set E, IsOpen U ∧ x₀ ∈ U ∧
      (∀ i, AnalyticOnNhd ℝ (f (e i)) U) ∧
      ∀ x ∈ U, StrictMono (fun i ↦ f (e i) x) ∧
        range (fun i ↦ f (e i) x) = range (fun i ↦ f i x) := by
  obtain ⟨k, e, horder⟩ := exists_eventually_strictMono_range_eq
    (fun i ↦ (hf i).continuousAt) heq
  have hanalytic : ∀ᶠ x in 𝓝 x₀, ∀ i, AnalyticAt ℝ (f (e i)) x :=
    eventually_all.2 fun i ↦ (hf (e i)).eventually_analyticAt
  obtain ⟨U, hU, hopen, hx₀⟩ := eventually_nhds_iff.1 (horder.and hanalytic)
  exact ⟨k, e, U, hopen, hx₀, fun i x hx ↦ (hU x hx).2 i,
    fun x hx ↦ (hU x hx).1⟩

end TauCeti
