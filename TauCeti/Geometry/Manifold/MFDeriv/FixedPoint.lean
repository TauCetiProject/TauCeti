/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import Mathlib.Dynamics.FixedPoints.Defs
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Dynamics.FixedPoints.Topology
import Mathlib.Topology.DiscreteSubset

/-!
# Nondegenerate fixed points of maps of manifolds

A fixed point `x` of a map `f : M → M` is **nondegenerate** (`TauCeti.IsNondegenerateFixedPt`)
when `1` is not an eigenvalue of its differential `df_x : T_x M → T_x M`: the only tangent vector
fixed by `df_x` is zero. In finite dimensions this says that `df_x - 1` is invertible, or that the
graph of `f` meets the diagonal of `M × M` transversally at `(x, x)`. For the time-one map of a
time-dependent Hamiltonian this is the nondegeneracy of a 1-periodic orbit, the hypothesis under
which the orbits generate the Hamiltonian Floer complex.

A nondegenerate fixed point of a map differentiable there is isolated among the fixed points
(`TauCeti.IsNondegenerateFixedPt.eventually_not_isFixedPt`): in a chart at `x` the coordinate
expression `g` of `f` has `g - id` with injective derivative at `x`, so `g z ≠ z` for `z ≠ x` close
to `x`. The argument is carried out within the range of the model with corners, so it also applies
at boundary points. Consequently a differentiable self-map of a compact manifold all of whose fixed
points are nondegenerate has only finitely many fixed points
(`TauCeti.finite_fixedPoints_of_isNondegenerateFixedPt`): its fixed-point set is closed, hence
compact, and discrete.

## Main definitions

* `TauCeti.IsNondegenerateFixedPt I f x`: `x` is a fixed point of `f` and `df_x` fixes no nonzero
  tangent vector.

## Main results

* `TauCeti.IsNondegenerateFixedPt.eventually_not_isFixedPt`: nondegenerate fixed points are
  isolated.
* `TauCeti.finite_fixedPoints_of_isNondegenerateFixedPt`: on a compact manifold, a differentiable
  map whose fixed points are all nondegenerate has finitely many fixed points.

## References

* V. Guillemin, A. Pollack, *Differential Topology*, Prentice-Hall, 1974, Chapter 3, §4
  (Lefschetz fixed points: nondegeneracy, isolation and finiteness on compact manifolds).
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 11.1 (nondegenerate fixed points of Hamiltonian symplectomorphisms).
-/

public section

open Filter Function Set
open scoped Manifold Topology

namespace TauCeti

variable {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M]
  [ChartedSpace H M] {f : M → M} {x : M}

variable (I) in
/-- A **nondegenerate fixed point** of `f : M → M` is a fixed point `x` at which `1` is not an
eigenvalue of the differential: `df_x v = v` only for `v = 0`. In finite dimensions this says
that `df_x - 1` is invertible. -/
def IsNondegenerateFixedPt (f : M → M) (x : M) : Prop :=
  IsFixedPt f x ∧ ∀ v : TangentSpace I x, mfderiv I I f x v = v → v = 0

/-- The defining characterization of a nondegenerate fixed point. -/
theorem isNondegenerateFixedPt_iff :
    IsNondegenerateFixedPt I f x ↔
      IsFixedPt f x ∧ ∀ v : TangentSpace I x, mfderiv I I f x v = v → v = 0 :=
  Iff.rfl

namespace IsNondegenerateFixedPt

/-- A nondegenerate fixed point is a fixed point. -/
theorem isFixedPt (h : IsNondegenerateFixedPt I f x) : IsFixedPt f x :=
  h.1

/-- At a nondegenerate fixed point, the only tangent vector fixed by the differential is zero. -/
theorem eq_zero_of_mfderiv_apply_eq (h : IsNondegenerateFixedPt I f x) {v : TangentSpace I x}
    (hv : mfderiv I I f x v = v) : v = 0 :=
  h.2 v hv

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]

/-- **Nondegenerate fixed points are isolated.** If `x` is a nondegenerate fixed point of `f` and
`f` is differentiable at `x`, then no point `y ≠ x` close to `x` is fixed by `f`. The manifold may
have boundary or corners. -/
theorem eventually_not_isFixedPt (h : IsNondegenerateFixedPt I f x)
    (hf : MDifferentiableAt I I f x) : ∀ᶠ y in 𝓝[≠] x, ¬IsFixedPt f y := by
  set φ := extChartAt I x
  have hfx : f x = x := h.isFixedPt
  have hφ : extChartAt I (f x) = φ := by rw [hfx]
  -- In the chart at `x`, the coordinate expression `g` of `f` has derivative `D = df_x` within
  -- `range I`, so `z ↦ g z - z` has derivative `D - 1`, which is injective.
  set D : E →L[𝕜] E := mfderiv I I f x
  have hg : HasFDerivWithinAt (fun z ↦ φ (f (φ.symm z)) - z) (D - ContinuousLinearMap.id 𝕜 E)
      (range I) (φ x) := by
    have h2 := hf.hasMFDerivAt.2
    simp only [writtenInExtChartAt, hφ] at h2
    exact h2.sub (hasFDerivWithinAt_id _ _)
  have hinj : Injective (D - ContinuousLinearMap.id 𝕜 E) := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    exact h.eq_zero_of_mfderiv_apply_eq (sub_eq_zero.1 hv)
  obtain ⟨K, -, hK⟩ :=
    (D - ContinuousLinearMap.id 𝕜 E).toLinearMap.injective_iff_antilipschitz.1 hinj
  have hne := hg.eventually_ne (c := 0) ⟨K, hK⟩
  -- The chart sends points `y ≠ x` near `x` to points `≠ φ x` of `range I`.
  have hsource : (extChartAt I x).source ∈ 𝓝[≠] x :=
    mem_nhdsWithin_of_mem_nhds (extChartAt_source_mem_nhds x)
  have htends : Tendsto φ (𝓝[≠] x) (𝓝[range I \ {φ x}] (φ x)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨(continuousAt_extChartAt x).tendsto.mono_left
      nhdsWithin_le_nhds, ?_⟩
    filter_upwards [hsource, self_mem_nhdsWithin] with y hy hyx
    exact ⟨extChartAt_target_subset_range x ((extChartAt I x).map_source hy),
      fun hφy ↦ hyx ((extChartAt I x).injOn hy (mem_extChartAt_source x) hφy)⟩
  have hfsource : f ⁻¹' (extChartAt I x).source ∈ 𝓝[≠] x :=
    mem_nhdsWithin_of_mem_nhds (hf.continuousAt.preimage_mem_nhds
      (by rw [hfx]; exact extChartAt_source_mem_nhds x))
  filter_upwards [htends.eventually hne, hsource, hfsource] with y hy hys _ hfix
  apply hy
  rw [(extChartAt I x).left_inv hys, hfix.eq, sub_self]

end IsNondegenerateFixedPt

/-- **Finiteness of nondegenerate fixed points.** A differentiable self-map of a compact manifold,
modelled on a finite-dimensional space, all of whose fixed points are nondegenerate has only
finitely many fixed points. -/
theorem finite_fixedPoints_of_isNondegenerateFixedPt [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]
    [CompactSpace M] [T2Space M] (hf : MDifferentiable I I f)
    (h : ∀ x ∈ fixedPoints f, IsNondegenerateFixedPt I f x) : (fixedPoints f).Finite :=
  (isClosed_fixedPoints hf.continuous).isCompact.finite <| isDiscrete_iff_nhdsNE.2 fun x hx ↦
    inf_principal_eq_bot.2 ((h x hx).eventually_not_isFixedPt (hf x))

end TauCeti
