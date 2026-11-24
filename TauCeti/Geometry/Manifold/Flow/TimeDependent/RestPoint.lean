/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.TimeDependent
public import Mathlib.Geometry.Manifold.VectorField.Pullback
import TauCeti.Analysis.Calculus.ParametricFDeriv
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Parametric.Basic
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# The time-dependent flow near a common rest point

Let `X` be a jointly `C²` time-dependent vector field on a finite-dimensional boundaryless
manifold `M`, and let `p` be a common rest point: `X_u(p) = 0` for every time `u`. Every map
`φ_{s,t}` of the time-dependent flow (`TauCeti.timeDependentFlowOf`) fixes `p`
(`TauCeti.timeDependentFlowOf_eq_self_of_forall_eq_zero`), so its differentials
`dφ_{s,t}(p) : T_p M → T_p M` are operators on the single tangent space `T_p M`.

Read `X_u` in the preferred chart at `p`, as the inverse-chart pullback
`V_u = VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I p).symm (X u) (range I)`. Its
derivative `L_u = DV_u` at the chart image of `p` is the linearization of `X_u` at the rest point.
This file proves the **variational equation at a rest point**: the linearized flow
`A(t) = dφ_{s,t}(p)` solves the linear equation

`A'(t) = L_t ∘ A(t)`, `A(s) = 1`

(`TauCeti.hasDerivAt_mfderiv_timeDependentFlowOf_of_forall_eq_zero`). Consequently, if the
linearization vanishes at all times between `s` and `t`, that is if `X` has zero first jet at `p`
along the time interval, then `φ_{s,t}` fixes `p` to first order: its differential at `p` is the
identity (`TauCeti.mfderiv_timeDependentFlowOf_eq_id_of_forall_eq_zero`).

This is the step of the relative Moser argument which preserves the ambient differential along a
fixed submanifold: a Moser vector field built from a primitive with zero first jet along the
submanifold has zero first jet there, so its time-one map has differential the identity at every
point of the submanifold. No completeness of the flow is needed.

The proof reads the flow from time `t` in the chart at `p`. It is a jointly `C²` family of maps
`Ψ(u, z)` with `Ψ(t, ·) = id`, whose velocity at `u = t` is `V_t`; the symmetry of its second
derivative exchanges the time derivative of the spatial derivative `D_z Ψ(u, ·)` with the spatial
derivative `DV_t` of the velocity, giving `(dφ_{t,u}(p))' = L_t` at `u = t`
(`TauCeti.hasDerivAt_mfderiv_timeDependentFlowOf_self_of_forall_eq_zero`), the time-dependent
counterpart of `TauCeti.hasDerivAt_mfderiv_flowOf_of_eq_zero`. The two-time composition law
`dφ_{s,u}(p) = dφ_{t,u}(p) ∘ dφ_{s,t}(p)` then gives the equation at every time.

## Main results

* `TauCeti.hasDerivAt_mfderiv_timeDependentFlowOf_self_of_forall_eq_zero`: the differentials of
  the flow from time `t` at a common rest point have derivative `L_t` at time `t`.
* `TauCeti.hasDerivAt_mfderiv_timeDependentFlowOf_of_forall_eq_zero`: the variational equation
  `A'(t) = L_t ∘ A(t)` at a common rest point.
* `TauCeti.mfderiv_timeDependentFlowOf_eq_id_of_forall_eq_zero`: a field with zero first jet at a
  common rest point has flow maps with identity differential there.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 7 (Moser's relative theorem).
* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Theorem 9.48 (time-dependent
  flows).
-/

public section

open Filter Set
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I 2 M]
  {X : ℝ → (x : M) → TangentSpace I x} {p : M}

/-- **Linearization of the time-dependent flow at a common rest point, at the initial time.** For
a jointly `C²` time-dependent vector field `X` vanishing at `p` at all times, the differentials
`dφ_{t,u}(p) : T_p M → T_p M` of the flow maps from time `t` have derivative at `u = t` the
derivative `L_t` of the coordinate expression of `X t` in the preferred chart at `p`, so
`dφ_{t,u}(p) = 1 + (u - t) L_t + o(u - t)`. -/
theorem hasDerivAt_mfderiv_timeDependentFlowOf_self_of_forall_eq_zero
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 2
      (fun q : ℝ × M ↦ (⟨q.2, X q.1 q.2⟩ : TangentBundle I M)))
    (hp : ∀ u, X u p = 0) (t : ℝ) :
    HasDerivAt (fun u ↦ (mfderiv I I (timeDependentFlowOf X t u) p : E →L[ℝ] E))
      (fderiv ℝ (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I p).symm (X t) (range I))
        (extChartAt I p p)) t := by
  have hX₁ := hX.of_le one_le_two
  -- In the preferred chart at `p`, the flow from time `t` is a jointly `C²` family, equal to the
  -- identity at time `t`.
  have hG := Manifold.contDiffAt_extChartAt_family (ψ := fun u y ↦ timeDependentFlowOf X t u y)
    (timeDependentFlowOf_self X t p)
    (contMDiffAt_uncurry_timeDependentFlowOf (n := 2) one_le_two hX
      (mem_timeDependentFlowDomain_self hX₁ t p))
  -- In the chart, the trajectories start with the coordinate velocity of `X t`.
  have hV := eventually_hasDerivAt_extChartAt_family
    (ψ := fun u y ↦ timeDependentFlowOf X t u y) (V := X t) (t := t) (y := p)
    (Eventually.of_forall fun y ↦ timeDependentFlowOf_self X t y)
    (Eventually.of_forall fun y ↦
      hasMFDerivAt_timeDependentFlowOf hX₁ (mem_timeDependentFlowDomain_self hX₁ t y))
  refine (ContDiffAt.hasDerivAt_fderiv_slice_of_eventually_hasDerivAt
      (by rw [minSmoothness_of_isRCLikeNormedField]; exact_mod_cast hG) hV)
    |>.congr_of_eventuallyEq (Eventually.of_forall fun u ↦ ?_)
  -- Each flow map fixes `p`, so its differential is read in the single chart at `p`.
  exact (mdifferentiableAt_timeDependentFlowOf hX₁
    (mem_timeDependentFlowDomain_of_forall_eq_zero hp t u)).mfderiv_eq_fderiv_extChartAt_conj
    (timeDependentFlowOf_eq_self_of_forall_eq_zero hX₁ hp t u)

/-- **The variational equation at a common rest point.** For a jointly `C²` time-dependent vector
field `X` vanishing at `p` at all times, the linearized flow `A(u) = dφ_{s,u}(p)`, an operator on
the tangent space `T_p M`, satisfies `A'(t) = L_t A(t)`, where `L_t` is the derivative of the
coordinate expression of `X t` in the preferred chart at `p`. -/
theorem hasDerivAt_mfderiv_timeDependentFlowOf_of_forall_eq_zero
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 2
      (fun q : ℝ × M ↦ (⟨q.2, X q.1 q.2⟩ : TangentBundle I M)))
    (hp : ∀ u, X u p = 0) (s t : ℝ) :
    HasDerivAt (F := E →L[ℝ] E) (fun u ↦ mfderiv I I (timeDependentFlowOf X s u) p)
      ((fderiv ℝ (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I p).symm (X t) (range I))
        (extChartAt I p p)).comp (mfderiv I I (timeDependentFlowOf X s t) p)) t := by
  -- Name the differentials as endomorphisms of the model space `E`.
  obtain ⟨B, hB⟩ : ∃ B : ℝ → E →L[ℝ] E, B = fun u ↦ mfderiv I I (timeDependentFlowOf X t u) p :=
    ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : E →L[ℝ] E, A = mfderiv I I (timeDependentFlowOf X s t) p := ⟨_, rfl⟩
  have hBd : HasDerivAt B
      (fderiv ℝ (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I p).symm (X t) (range I))
        (extChartAt I p p)) t :=
    hB ▸ hasDerivAt_mfderiv_timeDependentFlowOf_self_of_forall_eq_zero hX hp t
  have h := hBd.clm_comp (hasDerivAt_const t A)
  rw [ContinuousLinearMap.comp_zero, add_zero] at h
  subst hA hB
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun u ↦ ?_)
  -- Both flow maps fix `p`, so the chain rule for the composition law is read at `p`.
  have hX₁ := hX.of_le one_le_two
  have hfix := timeDependentFlowOf_eq_self_of_forall_eq_zero hX₁ hp s t
  have hu := mfderiv_timeDependentFlowOf_trans_of_mem hX₁
    (mem_timeDependentFlowDomain_of_forall_eq_zero hp s t)
    (hfix ▸ mem_timeDependentFlowDomain_of_forall_eq_zero hp t u)
  rw [hfix] at hu
  exact hu

/-- **A field with zero first jet at a common rest point has flow maps fixing it to first order.**
Let `X` be a jointly `C²` time-dependent vector field vanishing at `p` at all times, whose
coordinate expression in the preferred chart at `p` has zero derivative at the chart image of `p`
at every time between `s` and `t`. Then the differential at `p` of the flow map from `s` to `t` is
the identity of `T_p M`. -/
theorem mfderiv_timeDependentFlowOf_eq_id_of_forall_eq_zero
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 2
      (fun q : ℝ × M ↦ (⟨q.2, X q.1 q.2⟩ : TangentBundle I M)))
    (hp : ∀ u, X u p = 0) {s t : ℝ}
    (hL : ∀ u ∈ uIcc s t, fderiv ℝ
      (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I p).symm (X u) (range I))
        (extChartAt I p p) = 0) :
    mfderiv I I (timeDependentFlowOf X s t) p = ContinuousLinearMap.id ℝ (TangentSpace I p) := by
  -- Name the linearized flow as a family of endomorphisms of the model space `E`.
  obtain ⟨D, hD⟩ : ∃ D : ℝ → E →L[ℝ] E, D = fun u ↦ mfderiv I I (timeDependentFlowOf X s u) p :=
    ⟨_, rfl⟩
  have hderiv (u : ℝ) (_ : u ∈ uIcc s t) : HasDerivWithinAt D
      ((fderiv ℝ (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I p).symm (X u) (range I))
        (extChartAt I p p)).comp (D u)) (uIcc s t) u := by
    subst hD
    exact (hasDerivAt_mfderiv_timeDependentFlowOf_of_forall_eq_zero hX hp s u).hasDerivWithinAt
  -- It has zero derivative along `[s, t]`, so it is constant there.
  have h := (convex_uIcc s t).norm_image_sub_le_of_norm_hasDerivWithin_le (C := 0) hderiv
    (fun u hu ↦ by rw [hL u hu, ContinuousLinearMap.zero_comp, norm_zero])
    left_mem_uIcc right_mem_uIcc
  rw [zero_mul, norm_le_zero_iff, sub_eq_zero] at h
  subst hD
  exact h.trans (mfderiv_timeDependentFlowOf_self X s p)

end TauCeti
