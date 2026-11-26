/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.TimeDependent
public import TauCeti.Geometry.Manifold.Orientation.Family

/-!
# Time-dependent flows preserve orientations

Let `X` be a jointly `C¹` time-dependent vector field on a finite-dimensional boundaryless manifold
`M` whose suspension is complete, so that its time-dependent flow `φ_{s, t}` is defined everywhere.
Every time map `φ_{s, t}` preserves every orientation of `M`
(`TauCeti.isOrientationPreservingAt_timeDependentFlowOf`): the maps `φ_{s, u}`, for `u` running
over the real line, form a jointly `C¹` family of diffeomorphisms which is the identity at `u = s`,
and the orientation behaviour of such a family does not change along the connected parameter line
(`TauCeti.Manifold.Orientation.isOrientationPreservingAt_of_family_eq_id`).

This is the time-dependent counterpart of
`TauCeti.IsAdaptedPseudoGradient.isOrientationPreservingAt_flow` for the flow of an autonomous
pseudo-gradient. It applies to the transition diffeomorphisms of continuation fields, which are
time maps of time-dependent flows.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapters 9 (time-dependent flows) and 15 (orientations).
-/

public section

open scoped Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [IsManifold I 1 M] [BoundarylessManifold I M]
  {X : ℝ → (x : M) → TangentSpace I x} {ι : Type*} [Fintype ι]

/-- **Time-dependent flows preserve orientations.** If the suspension of a jointly `C¹`
time-dependent vector field is complete, every time map of its time-dependent flow preserves every
orientation of the manifold, since these maps are joined to the identity through the flow. -/
theorem isOrientationPreservingAt_timeDependentFlowOf
    (hcomplete : IsCompleteVectorField (timeDependentSuspensionField X))
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    (o : Manifold.Orientation I M ι) (s t : ℝ) (x : M) :
    o.IsOrientationPreservingAt o (timeDependentFlowOf X s t) x :=
  Manifold.Orientation.isOrientationPreservingAt_of_family_eq_id (L := 𝓘(ℝ, ℝ)) o
    (F := fun p : ℝ × M ↦ timeDependentFlowOf X s p.1 p.2)
    ((contMDiff_timeDependentFlowOf hcomplete le_rfl hX).comp
      ((contMDiff_const (c := s)).prodMk contMDiff_fst |>.prodMk contMDiff_snd))
    x (fun u ↦ by
      have hc : ⇑(timeDependentFlowDiffeomorph hcomplete le_rfl hX s u) =
          timeDependentFlowOf X s u :=
        funext (timeDependentFlowDiffeomorph_apply hcomplete le_rfl hX s u)
      dsimp only
      rw [← hc]
      exact (timeDependentFlowDiffeomorph hcomplete le_rfl hX s u).isInvertible_mfderiv
        one_ne_zero)
    (p₀ := s) (funext (timeDependentFlowOf_self X s)) t

end TauCeti
