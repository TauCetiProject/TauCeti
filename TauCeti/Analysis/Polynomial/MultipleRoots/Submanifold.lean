/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.MultipleRoots.Basic
public import TauCeti.Analysis.Analytic.Submanifold.Basic

/-!
# Analytic roots on analytic submanifolds

Continuous root functions of polynomial families with intrinsically analytic coefficients and
locally constant positive multiplicity are intrinsically analytic on an analytic submanifold.
Degree bounds are needed only on the submanifold, locally at each point; the ambient fibers can
behave differently. Apply the constant-multiplicity root theorem in the free coordinates of a chart.

This is the regularity step turning continuous delineations into analytic delineations.

## References

S. McCallum, *An improved projection operation for cylindrical algebraic decomposition*,
Springer (1998), 242–268 (analytic delineability).
-/

public section

open Filter Polynomial Set Topology

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜] [CompleteSpace 𝕜]
  {n d : ℕ} {S : Set (Fin n → 𝕜)} {F : (Fin n → 𝕜) → 𝕜[X]}
  {r : (Fin n → 𝕜) → 𝕜}

/-- A continuous root function on an analytic submanifold is intrinsically analytic if the
coefficients are intrinsically analytic and its positive multiplicity is locally constant. Only
local bounds on the degrees of fibers over the submanifold are required. -/
theorem IsAnalyticSubmanifold.analyticOnSubmanifold_of_rootMultiplicity_eq
    (hS : IsAnalyticSubmanifold d S)
    (hF : ∀ i, AnalyticOnSubmanifold d (fun x ↦ (F x).coeff i) S)
    (hdeg : ∀ x ∈ S, ∃ b : ℕ, ∀ᶠ y in 𝓝[S] x, (F y).natDegree ≤ b)
    (hr : ContinuousOn r S)
    (hmult : ∀ x ∈ S, ∃ m : ℕ, 0 < m ∧
      ∀ᶠ y in 𝓝[S] x, (F y).rootMultiplicity (r y) = m) :
    AnalyticOnSubmanifold d r S := by
  rw [hS.analyticOnSubmanifold_iff]
  intro x hx e he hxe
  let a := firstCoords 𝕜 n d (e x)
  let φ := fun u ↦ e.symm (firstCoords 𝕜 d n u)
  have hφ : AnalyticAt 𝕜 φ a := he.analyticAt_symm_firstCoords hxe hx
  have hφx : φ a = x := he.symm_firstCoords_firstCoords_apply hxe hx
  have hmem : ∀ᶠ u in 𝓝 a, φ u ∈ S :=
    (he.eventually_symm_firstCoords_mem hxe hx).mono fun _ hu ↦ hu.2
  have ht : Tendsto φ (𝓝 a) (𝓝[S] x) := by
    rw [← hφx]
    exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within φ hφ.continuousAt hmem
  have hrc : ContinuousAt (r ∘ φ) a := by
    simpa only [ContinuousAt, Function.comp_apply, hφx] using (hr x hx).tendsto.comp ht
  obtain ⟨b, hb⟩ := hdeg x hx
  obtain ⟨m, hm, hmult⟩ := hmult x hx
  exact Polynomial.analyticAt_of_eventually_rootMultiplicity_eq
    (fun i _ ↦ (hF i).analyticAt_chart hx he hxe) (ht.eventually hb)
    hrc hm (ht.eventually hmult)

end TauCeti
