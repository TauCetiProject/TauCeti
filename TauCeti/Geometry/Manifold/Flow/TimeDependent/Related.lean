/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.TimeDependent

/-!
# Symmetries of time-dependent vector fields commute with their flows

Let `X` be a time-dependent vector field on a manifold `M` whose suspension is complete, so that
its time-dependent flow `TauCeti.timeDependentFlowOf X s t` is defined everywhere. If a
differentiable map `g : M → M` carries the field to itself, `dg (X u x) = X u (g x)` at all times
and points, then the image under `g` of a solution of the equation is again a solution, and by
uniqueness of solutions `g` commutes with every time map of the flow
(`TauCeti.apply_timeDependentFlowOf_of_mfderiv_eq`).

This is the time-dependent counterpart of the naturality of autonomous flows in
`TauCeti.Geometry.Manifold.Flow.Related`. It makes flows of invariant time-dependent fields
equivariant: for a group acting by such maps, as for the Moser fields built from invariant forms
in equivariant Moser arguments, every time map of the flow commutes with the action.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 9,
  Proposition 9.6 (naturality of integral curves).
-/

public section

open scoped Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I 1 M] [BoundarylessManifold I M] {X : ℝ → (x : M) → TangentSpace I x}

/-- **Symmetries of a time-dependent field commute with its flow.** If the suspension is complete
and the differential of a differentiable map `g` carries `X u x` to `X u (g x)` at all times and
points, then `g` commutes with every time map of the flow. -/
theorem apply_timeDependentFlowOf_of_mfderiv_eq
    (hcomplete : IsCompleteVectorField (timeDependentSuspensionField X))
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    {g : M → M} (hg : MDifferentiable I I g) (hgX : ∀ u x, mfderiv I I g x (X u x) = X u (g x))
    (s t : ℝ) (x : M) :
    g (timeDependentFlowOf X s t x) = timeDependentFlowOf X s t (g x) := by
  -- The image under `g` of the flow curve through `x` solves the equation through `g x`.
  have h := timeDependentFlowOf_eq_of_forall_hasMFDerivAt hX
    (γ := fun u ↦ g (timeDependentFlowOf X s u x)) (fun u ↦ by
      have hc := (hg _).hasMFDerivAt.comp u
        (hasMFDerivAt_timeDependentFlowOf hX
          ((timeDependentFlowDomain_eq_univ hcomplete).symm ▸ Set.mem_univ ((s, u), x)))
      have hd : (mfderiv I I g (timeDependentFlowOf X s u x)).comp
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X u (timeDependentFlowOf X s u x))) =
          (1 : ℝ →L[ℝ] ℝ).smulRight (X u (g (timeDependentFlowOf X s u x))) := by
        ext
        simp [hgX]
      exact hd ▸ hc) s t
  rw [timeDependentFlowOf_self] at h
  exact h.symm

end TauCeti
