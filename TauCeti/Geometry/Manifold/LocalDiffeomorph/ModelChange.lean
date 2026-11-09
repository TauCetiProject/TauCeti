/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Linear changes of models for local diffeomorphisms

Changing the vector-space coordinates of either model by a continuous linear equivalence does
not change whether a map is a local diffeomorphism. The chart spaces and charted-space instances
stay fixed. These criteria let constructions specified by local diffeomorphisms, such as
compatible open gluing, use any linearly equivalent model.

The comparisons use Mathlib's identity diffeomorphism
`ContinuousLinearEquiv.toTransContinuousLinearEquiv`.
No manifold, boundarylessness, or finite-dimensionality assumption is needed.

## References

* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Volume I, Chapter I.
-/

public section

open scoped Manifold ContDiff

namespace ContinuousLinearEquiv

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F E' F' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' H'}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace H' N] {n : ℕ∞ω}
  {f : M → N} {x : M} {s : Set M}

/-- Linear changes of the source and target model coordinates preserve local diffeomorphy
at a point. Both the function and the charted spaces are unchanged. -/
@[simp]
theorem isLocalDiffeomorphAt_transContinuousLinearEquiv_iff
    (e : E ≃L[𝕜] F) (e' : E' ≃L[𝕜] F') :
    IsLocalDiffeomorphAt (I.transContinuousLinearEquiv e)
      (J.transContinuousLinearEquiv e') n f x ↔ IsLocalDiffeomorphAt I J n f x := by
  let d := ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := n) I M e
  let d' := ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := n) J N e'
  -- Both comparison diffeomorphisms are the identity on their carriers, so composing them
  -- with `f` does not change its values or the point at which local diffeomorphy is tested.
  exact ⟨fun h ↦ (d.isLocalDiffeomorph x).comp
      (hg := h.comp (hg := d'.symm.isLocalDiffeomorph _)),
    fun h ↦ (d.symm.isLocalDiffeomorph x).comp
      (hg := h.comp (hg := d'.isLocalDiffeomorph _))⟩

/-- Linear changes of model coordinates preserve local diffeomorphy on a set. -/
@[simp]
theorem isLocalDiffeomorphOn_transContinuousLinearEquiv_iff
    (e : E ≃L[𝕜] F) (e' : E' ≃L[𝕜] F') :
    IsLocalDiffeomorphOn (I.transContinuousLinearEquiv e)
      (J.transContinuousLinearEquiv e') n f s ↔ IsLocalDiffeomorphOn I J n f s :=
  forall_congr' fun _ ↦ isLocalDiffeomorphAt_transContinuousLinearEquiv_iff e e'

/-- Linear changes of model coordinates preserve local diffeomorphisms. -/
@[simp]
theorem isLocalDiffeomorph_transContinuousLinearEquiv_iff
    (e : E ≃L[𝕜] F) (e' : E' ≃L[𝕜] F') :
    IsLocalDiffeomorph (I.transContinuousLinearEquiv e)
      (J.transContinuousLinearEquiv e') n f ↔ IsLocalDiffeomorph I J n f :=
  forall_congr' fun _ ↦ isLocalDiffeomorphAt_transContinuousLinearEquiv_iff e e'

end ContinuousLinearEquiv
