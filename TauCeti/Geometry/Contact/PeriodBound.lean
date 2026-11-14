/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Flat
public import TauCeti.Geometry.Contact.Flow
import TauCeti.Dynamics.Flow.PeriodBound

/-!
# A positive lower bound for Reeb periods

On a compact boundaryless contact manifold, all positive periods of Reeb trajectories have a
common positive lower bound. The bound applies to multiply covered trajectories as well as simple
ones, and does not require nondegeneracy. It follows from the compact-flow period bound because
the Reeb field is smooth, complete and nowhere zero.

Trajectories are expressed using the existing `IsMIntegralCurve` predicate; no new orbit carrier is
needed. The result supplies the lower-period input to finiteness arguments for Reeb orbits of
bounded action.

## References

* F. Bourgeois, Y. Eliashberg, H. Hofer, K. Wysocki, E. Zehnder,
  *Compactness results in Symplectic Field Theory*, Section 2.3 (periodic Reeb orbits).
-/

public section

open Set
open scoped ContDiff Manifold

namespace TauCeti.SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M] [CompactSpace M]
  {α : SmoothForm I M ℝ 1}

/-- On a compact boundaryless contact manifold, positive periods of Reeb integral curves are
uniformly bounded away from zero, including the periods of all their covers. -/
theorem IsContactForm.exists_pos_period_le (hα : α.IsContactForm) :
    ∃ ε > 0, ∀ γ : ℝ → M, IsMIntegralCurve γ α.reebVectorField →
      ∀ T > 0, Function.Periodic γ T → ε ≤ T := by
  let hc := hα.isCompleteVectorField_reebVectorField
  obtain ⟨ε, hε, hbound⟩ := (hα.reebFlow hc).exists_pos_period_le_of_isCompact isCompact_univ
    fun x _ ↦ hα.exists_reebFlow_ne_self hc x
  refine ⟨ε, hε, fun γ hγ T hT hperiod ↦ hbound (γ 0) (mem_univ _) T hT ?_⟩
  rw [hα.reebFlow_def hc,
    globalFlow_eq_of_isMIntegralCurve (hα.contMDiff_reebVectorField.of_le (by simp)) hc hγ T]
  simpa only [zero_add] using hperiod 0

end TauCeti.SmoothForm
