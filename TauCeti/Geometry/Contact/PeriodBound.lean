/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Flat
public import TauCeti.Geometry.Manifold.IntegralCurve.GlobalFlow
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
  have hv : ContMDiff I I.tangent 1 (fun x ↦
      (⟨x, α.reebVectorField x⟩ : TangentBundle I M)) :=
    hα.contMDiff_reebVectorField.of_le (by simp)
  let hc := isCompleteVectorField_of_compactSpace hv
  let ϕ := globalFlow α.reebVectorField hv hc
  have hmove (x : M) : ∃ t, ϕ t x ≠ x := by
    by_contra h
    have hfix : ∀ t, ϕ t x = x := by simpa only [not_exists, not_not] using h
    exact hα.reebVectorField_ne_zero x ((globalFlow_eq_self_iff hv hc x).mp hfix)
  obtain ⟨ε, hε, hbound⟩ := ϕ.exists_pos_period_le_of_isCompact isCompact_univ
    (fun x _ ↦ hmove x)
  refine ⟨ε, hε, fun γ hγ T hT hperiod ↦ hbound (γ 0) (mem_univ _) T hT ?_⟩
  rw [globalFlow_eq_of_isMIntegralCurve hv hc hγ T]
  simpa only [zero_add] using hperiod 0

end TauCeti.SmoothForm
