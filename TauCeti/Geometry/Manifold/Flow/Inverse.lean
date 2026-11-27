/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.Basic

/-!
# The differentials of local flow maps are invertible

Let `v` be a `C¹` vector field on a Hausdorff boundaryless manifold modelled on a Banach space,
with maximal flow `φ` (`TauCeti.flowOf`). Wherever the trajectory of `x` is defined at time `t`,
the trajectory of `φₜ x` is defined at time `-t` and returns to `x`
(`TauCeti.flowOf_neg_flowOf`). The composition law for the differentials of local flow maps
(`TauCeti.mfderiv_flowOf_add_apply`) then makes the differential of the time-`(-t)` map at `φₜ x`
a two-sided inverse of the differential of the time-`t` map at `x`
(`TauCeti.mfderiv_flowOf_neg_mfderiv_flowOf_apply`,
`TauCeti.mfderiv_flowOf_mfderiv_flowOf_neg_apply`), so the latter is bijective
(`TauCeti.bijective_mfderiv_flowOf`). The field need not be complete: only the local flow on its
maximal domain enters.

This is what lets a linear structure on the tangent spaces preserved by a local flow, such as the
kernels of an invariant two-form, be transported both ways along the trajectories.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Theorem 9.12 (the fundamental theorem on flows).
-/

public section

open scoped Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [BoundarylessManifold I M] [IsManifold I 1 M] {v : (x : M) → TangentSpace I x}
  {t : ℝ} {x : M}

/-- Flowing back for time `-t` undoes the differential of the time-`t` map of a local flow:
`dφ₋ₜ (dφₜ w) = w` for every tangent vector `w` at `x`, wherever `φₜ x` is defined. -/
theorem mfderiv_flowOf_neg_mfderiv_flowOf_apply
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) (ht : (t, x) ∈ flowDomain v)
    (w : TangentSpace I x) :
    -- The two sides are tangent vectors at `flowOf v (-t) (flowOf v t x)` and at `x`, which are
    -- equal but not definitionally; all tangent spaces are the model space `E`.
    @Eq E (mfderiv I I (flowOf v (-t)) (flowOf v t x) (mfderiv I I (flowOf v t) x w)) w :=
  (mfderiv_flowOf_add_apply hv ht rfl (neg_mem_flowDomain_flowOf hv ht) w).trans <| by
    rw [add_neg_cancel]
    exact mfderiv_flowOf_zero_apply_eq_self v x w

/-- The differential of the time-`t` map of a local flow undoes flowing back for time `-t`:
`dφₜ (dφ₋ₜ u) = u` for every tangent vector `u` at `φₜ x`, wherever `φₜ x` is defined. -/
theorem mfderiv_flowOf_mfderiv_flowOf_neg_apply
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) (ht : (t, x) ∈ flowDomain v)
    (u : TangentSpace I (flowOf v t x)) :
    -- `dφ₋ₜ u` is a tangent vector at `flowOf v (-t) (flowOf v t x)`, which equals `x` but not
    -- definitionally; all tangent spaces are the model space, so the equation is stated in `E`.
    @Eq E (mfderiv I I (flowOf v t) x (mfderiv I I (flowOf v (-t)) (flowOf v t x) u)) u :=
  (mfderiv_flowOf_add_apply hv (neg_mem_flowDomain_flowOf hv ht) (flowOf_neg_flowOf hv ht) ht
    u).trans <| by
    rw [neg_add_cancel]
    exact mfderiv_flowOf_zero_apply_eq_self v _ u

/-- **The differential of a local flow map is bijective.** For a `C¹` vector field `v`, the
differential at `x` of the time-`t` map of its maximal flow is a bijection
`T_x M → T_(φₜ x) M` wherever `φₜ x` is defined, with inverse the differential at `φₜ x` of the
time-`(-t)` map. The field need not be complete. -/
theorem bijective_mfderiv_flowOf (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (ht : (t, x) ∈ flowDomain v) : Function.Bijective (mfderiv I I (flowOf v t) x) :=
  ⟨Function.LeftInverse.injective (g := mfderiv I I (flowOf v (-t)) (flowOf v t x))
      (mfderiv_flowOf_neg_mfderiv_flowOf_apply hv ht),
    Function.RightInverse.surjective (mfderiv_flowOf_mfderiv_flowOf_neg_apply hv ht)⟩

end TauCeti
