/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.IntegralCurve.GlobalFlow
public import TauCeti.Geometry.Manifold.Orientation.Family
import TauCeti.Geometry.Manifold.MFDeriv.IsInvertible

/-!
# Flows of vector fields preserve orientation

Let `v` be a `C¹` vector field on an oriented boundaryless manifold `M`. For each `x ∈ M`, the
maximal integral curve interval of `x` is a connected open subset of `ℝ` containing `0`, on which
the local flow `(t, y) ↦ flowOf v t y` is jointly `C¹` at `(t, x)` with invertible spatial
derivatives and equals the identity at `t = 0`. Hence every time-`t` map of `flowOf v` preserves
every orientation of `M` wherever `(t, x)` lies in the flow domain
(`TauCeti.Manifold.Orientation.isOrientationPreservingAt_flowOf`). In particular, when `v` is
complete, every time-`t` map of its global flow preserves every orientation of `M` at every point
(`TauCeti.Manifold.Orientation.isOrientationPreservingAt_globalFlow`).

## Main results

* `TauCeti.Manifold.Orientation.isOrientationPreservingAt_flowOf`: the time-`t` map of the local
  flow of a `C¹` vector field preserves orientation at every point `x` with `(t, x) ∈ flowDomain v`.
* `TauCeti.Manifold.Orientation.isOrientationPreservingAt_globalFlow`: the time-`t` map of the
  global flow of a complete `C¹` vector field preserves orientation at every point.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 15 (orientations and flows).
-/

public section

open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold.Orientation

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I 1 M]
  [BoundarylessManifold I M] {ι : Type*} [Fintype ι]

/-- **Local flows preserve orientation.** For a `C¹` vector field `v` on a boundaryless manifold
`M`, the time-`t` map of its flow `flowOf v` preserves every orientation of `M` at every point `x`
with `(t, x) ∈ flowDomain v`, without requiring completeness. -/
theorem isOrientationPreservingAt_flowOf (o : Manifold.Orientation I M ι)
    {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I I.tangent 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    {t : ℝ} {x : M} (ht : (t, x) ∈ flowDomain v) :
    IsOrientationPreservingAt o o (flowOf v t) x := by
  let U : TopologicalSpace.Opens ℝ :=
    ⟨maximalIntegralCurveInterval v x, isOpen_maximalIntegralCurveInterval⟩
  have : PreconnectedSpace U :=
    Subtype.preconnectedSpace isPreconnected_maximalIntegralCurveInterval
  have hF (s : U) : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I 1
      (fun q : U × M ↦ flowOf v q.1.val q.2) (s, x) :=
    ((contMDiffOn_flowOf le_rfl hv).contMDiffAt
      ((isOpen_flowDomain hv).mem_nhds (mem_flowDomain.2 s.property))).comp (s, x)
      ((contMDiff_subtypeVal.comp contMDiff_fst).prodMk contMDiff_snd).contMDiffAt
  have hD (s : U) : (mfderiv I I (flowOf v s.val) x).IsInvertible := by
    have hs : (s.val, x) ∈ flowDomain v := mem_flowDomain.2 s.property
    have hneg : (-s.val, flowOf v s.val x) ∈ flowDomain v := neg_mem_flowDomain_flowOf hv hs
    have hd₁ : MDifferentiableAt I I (flowOf v s.val) x :=
      (((contMDiffOn_flowOf le_rfl hv).contMDiffAt
        ((isOpen_flowDomain hv).mem_nhds hs)).comp x
        (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt one_ne_zero
    have hd₂ : MDifferentiableAt I I (flowOf v (-s.val)) (flowOf v s.val x) :=
      (((contMDiffOn_flowOf le_rfl hv).contMDiffAt
        ((isOpen_flowDomain hv).mem_nhds hneg)).comp (flowOf v s.val x)
        (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt one_ne_zero
    have hev : flowOf v (-s.val) ∘ flowOf v s.val =ᶠ[𝓝 x] id := by
      filter_upwards [((isOpen_flowDomain hv).preimage
        (continuous_const.prodMk continuous_id)).mem_nhds hs] with y hy
      exact flowOf_neg_flowOf hv hy
    have hcomp : (mfderiv I I (flowOf v (-s.val) ∘ flowOf v s.val) x).IsInvertible := by
      rw [hev.mfderiv_eq, mfderiv_id, ContinuousLinearMap.comp_id]
      exact ⟨tangentSpaceCast I _ _, rfl⟩
    exact (isInvertible_mfderiv_of_isInvertible_mfderiv_comp rfl hd₂ hd₁ hcomp).1
  let p₀ : U := ⟨0, mem_flowDomain.1 (mem_flowDomain_zero hv x)⟩
  exact isOrientationPreservingAt_family_of_id (L := 𝓘(ℝ, ℝ)) o x hF hD (p₀ := p₀)
    (Filter.Eventually.of_forall (flowOf_zero v)) ⟨t, mem_flowDomain.1 ht⟩

/-- **Global flows preserve orientation.** For a complete `C¹` vector field `v` on a boundaryless
manifold `M`, every time-`t` map of its global flow preserves every orientation of `M` at every
point. -/
theorem isOrientationPreservingAt_globalFlow (o : Manifold.Orientation I M ι)
    {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I I.tangent 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (hcomplete : IsCompleteVectorField v) (t : ℝ) (x : M) :
    IsOrientationPreservingAt o o (globalFlow v hv hcomplete t) x := by
  rw [← flowOf_eq_globalFlow (hv := hv) (hcomplete := hcomplete)]
  exact isOrientationPreservingAt_flowOf o hv (hcomplete.mem_flowDomain t x)

end TauCeti.Manifold.Orientation
