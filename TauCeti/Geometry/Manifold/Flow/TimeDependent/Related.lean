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
its time-dependent flow `TauCeti.timeDependentFlowOf X s t` is defined everywhere, and let `Y` be a
time-dependent field on a manifold `M'`. If a differentiable map `f : M → M'` relates the fields,
`df (X u x) = Y u (f x)` at all times and points, then the image under `f` of a solution for `X`
is a solution for `Y`, and by uniqueness of solutions `f` intertwines every time map of the two
flows (`TauCeti.apply_timeDependentFlowOf_of_mfderiv_eq`).

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
  {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M'] [T2Space M']
  [IsManifold I' 1 M'] [BoundarylessManifold I' M'] {Y : ℝ → (y : M') → TangentSpace I' y}

/-- **Related time-dependent fields have intertwined flows.** If the suspension of `X` is complete
and the differential of a differentiable map `f` carries `X u x` to `Y u (f x)` at all times and
points, then `f` carries every time map of the flow of `X` to the corresponding time map of the
flow of `Y`. -/
theorem apply_timeDependentFlowOf_of_mfderiv_eq
    (hcomplete : IsCompleteVectorField (timeDependentSuspensionField X))
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    (hY : ContMDiff (𝓘(ℝ, ℝ).prod I') I'.tangent 1
      (fun p : ℝ × M' ↦ (⟨p.2, Y p.1 p.2⟩ : TangentBundle I' M')))
    {f : M → M'} (hf : MDifferentiable I I' f) (hXY : ∀ u x, mfderiv I I' f x (X u x) = Y u (f x))
    (s t : ℝ) (x : M) :
    f (timeDependentFlowOf X s t x) = timeDependentFlowOf Y s t (f x) := by
  -- The image under `f` of the flow curve of `X` through `x` solves the equation of `Y` through
  -- `f x`.
  have h := timeDependentFlowOf_eq_of_forall_hasMFDerivAt hY
    (γ := fun u ↦ f (timeDependentFlowOf X s u x)) (fun u ↦ by
      have hc := (hf _).hasMFDerivAt.comp u
        (hasMFDerivAt_timeDependentFlowOf hX
          ((timeDependentFlowDomain_eq_univ hcomplete).symm ▸ Set.mem_univ ((s, u), x)))
      have hd : (mfderiv I I' f (timeDependentFlowOf X s u x)).comp
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X u (timeDependentFlowOf X s u x))) =
          (1 : ℝ →L[ℝ] ℝ).smulRight (Y u (f (timeDependentFlowOf X s u x))) := by
        ext
        simp [hXY]
      exact hd ▸ hc) s t
  rw [timeDependentFlowOf_self] at h
  exact h.symm

end TauCeti
