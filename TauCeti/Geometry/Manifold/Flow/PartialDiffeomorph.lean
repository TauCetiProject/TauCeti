/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.Flow.Basic
import TauCeti.Geometry.Manifold.IntegralCurve.Basic
import TauCeti.Topology.Order.Interval.Basic
import TauCeti.Geometry.Manifold.VectorField.Chart.PartialDiffeomorph

/-!
# Flows through partial diffeomorphisms

Let `Φ` be a partial diffeomorphism from a manifold `M` to a manifold `M'`, such as a chart, and
let it carry a vector field `X` on `M` to a vector field `Y` on `M'` on its source:
`dΦ_x (X x) = Y (Φ x)` for `x ∈ Φ.source`. Then `Φ⁻¹` carries `Y` back to `X` on the target
(`PartialDiffeomorph.mfderiv_symm_apply_eq_of_mfderiv_apply_eq`), and so it carries the pieces of
trajectories of `Y` that stay in the target to trajectories of `X`. Hence the flows correspond for
as long as the trajectory of `Y` stays in the target:

`flowOf X t x = Φ⁻¹ (flowOf Y t (Φ x))` if `flowOf Y s (Φ x) ∈ Φ.target` for `s ∈ [0, t]`

(`PartialDiffeomorph.flowOf_eq_symm_flowOf`). In contrast with a global diffeomorphism
(`Diffeomorph.apply_flowOf`), the flow of `X` may exist longer than the trajectory of `Y` stays in
the target, so only this direction holds in general. Since the trajectories of points near `x`
stay in the target for the same times, the identity holds near `x`
(`PartialDiffeomorph.eventually_flowOf_eq_symm_flowOf`), and the time-`t` maps have corresponding
derivatives (`PartialDiffeomorph.hasMFDerivAt_flowOf`).

This is how the flow of a vector field on a manifold is computed in a chart: near a point where
the field does not vanish, a straightening chart carries it to a constant field, whose flow is
translation, and a perturbation of the field supported in the chart is computed in the model
space and carried to the manifold by `PartialDiffeomorph.exists_contMDiff_mfderiv_apply_eq`.

## Main results

* `PartialDiffeomorph.flowOf_eq_symm_flowOf`: the flow of `X` is read off the flow of `Y` while
  the trajectory of `Y` stays in the target.
* `PartialDiffeomorph.eventually_flowOf_eq_symm_flowOf`: the same identity holds near the initial
  point.
* `PartialDiffeomorph.hasMFDerivAt_flowOf`: the derivative of the time-`t` map of `X` is that of
  `Y` conjugated by the differentials of `Φ`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Proposition 9.13 (naturality of flows).
-/

public section

open Filter Function Set
open scoped ContDiff Manifold Topology

namespace PartialDiffeomorph

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  (Φ : PartialDiffeomorph I I' M M' n) (hn : n ≠ 0)
  {X : (x : M) → TangentSpace I x} {Y : (y : M') → TangentSpace I' y}
  [T2Space M] [IsManifold I 1 M] [BoundarylessManifold I M]
  [T2Space M'] [IsManifold I' 1 M'] [BoundarylessManifold I' M'] [CompleteSpace E']

include hn

/-- **The flow read through a partial diffeomorphism.** Let `Φ` carry the `C¹` field `X` to the
`C¹` field `Y` on its source, and let `x ∈ Φ.source`. If the trajectory of `Y` through `Φ x` is
defined up to time `t` and stays in the target of `Φ` for the times between `0` and `t`, then the
flow of `X` is defined at `(t, x)` and `flowOf X t x = Φ⁻¹ (flowOf Y t (Φ x))`. -/
theorem flowOf_eq_symm_flowOf (hX : CMDiff 1 (fun x ↦ (⟨x, X x⟩ : TangentBundle I M)))
    (hY : CMDiff 1 (fun y ↦ (⟨y, Y y⟩ : TangentBundle I' M')))
    (hXY : ∀ x ∈ Φ.source, mfderiv I I' Φ x (X x) = Y (Φ x)) {t : ℝ} {x : M}
    (hx : x ∈ Φ.source) (ht : (t, Φ x) ∈ flowDomain Y)
    (htarget : ∀ s ∈ uIcc 0 t, flowOf Y s (Φ x) ∈ Φ.target) :
    (t, x) ∈ flowDomain X ∧ flowOf X t x = Φ.symm (flowOf Y t (Φ x)) := by
  -- The times at which the trajectory of `Y` is defined and in the target form an open set
  -- containing the compact interval between `0` and `t`, so they contain an open interval
  -- around it.
  set S := {s : ℝ | (s, Φ x) ∈ flowDomain Y ∧ flowOf Y s (Φ x) ∈ Φ.target}
  have hS : IsOpen S := (isOpen_setOf_mem_flowDomain_and_flowOf_mem hY Φ.open_target).preimage
    (continuous_id.prodMk continuous_const)
  have hIcc : uIcc 0 t ⊆ S := fun s hs ↦ ⟨uIcc_subset_setOf_mem_flowDomain ht hs, htarget s hs⟩
  obtain ⟨l, r, hlr, hsub⟩ := hS.exists_Ioo_subset_of_uIcc_subset hIcc
  have h0 : (0 : ℝ) ∈ Ioo l r := hlr left_mem_uIcc
  have ht' : t ∈ Ioo l r := hlr right_mem_uIcc
  -- On that interval, `Φ⁻¹` carries the trajectory of `Y` to an integral curve of `X` through `x`.
  have hγ : IsMIntegralCurveOn (Φ.symm ∘ fun s ↦ flowOf Y s (Φ x)) X (Ioo l r) :=
    ((isMIntegralCurveOn_flowOf hY (Φ x)).mono fun s hs ↦ (hsub hs).1).map_of_mfderiv_eq
      (fun s hs ↦ Φ.symm.mdifferentiableAt hn (hsub hs).2)
      (fun s hs ↦ Φ.mfderiv_symm_apply_eq_of_mfderiv_apply_eq hn hXY (hsub hs).2)
  have hγ0 : (Φ.symm ∘ fun s ↦ flowOf Y s (Φ x)) 0 = x := by
    simp only [comp_apply, flowOf_zero]
    exact Φ.left_inv hx
  refine ⟨mem_flowDomain.mpr (hγ.subset_maximalIntegralCurveInterval h0 hγ0 ht'), ?_⟩
  rw [flowOf_apply]
  exact hγ.eqOn_maximalIntegralCurve hX h0 hγ0 ht'

/-- **The flow read through a partial diffeomorphism, near the initial point.** Under the
hypotheses of `PartialDiffeomorph.flowOf_eq_symm_flowOf` at `x`, the identity
`flowOf X t z = Φ⁻¹ (flowOf Y t (Φ z))` holds for every `z` near `x`, with the flow of `X` defined
at `(t, z)`. -/
theorem eventually_flowOf_eq_symm_flowOf
    (hX : CMDiff 1 (fun x ↦ (⟨x, X x⟩ : TangentBundle I M)))
    (hY : CMDiff 1 (fun y ↦ (⟨y, Y y⟩ : TangentBundle I' M')))
    (hXY : ∀ x ∈ Φ.source, mfderiv I I' Φ x (X x) = Y (Φ x)) {t : ℝ} {x : M}
    (hx : x ∈ Φ.source) (ht : (t, Φ x) ∈ flowDomain Y)
    (htarget : ∀ s ∈ uIcc 0 t, flowOf Y s (Φ x) ∈ Φ.target) :
    ∀ᶠ z in 𝓝 x, (t, z) ∈ flowDomain X ∧ flowOf X t z = Φ.symm (flowOf Y t (Φ z)) := by
  have hO := isOpen_setOf_mem_flowDomain_and_flowOf_mem hY Φ.open_target
  -- By the tube lemma, the trajectories of the points near `Φ x` stay in the target for the
  -- times between `0` and `t`.
  have hev : ∀ᶠ y in 𝓝 (Φ x), ∀ s ∈ uIcc 0 t,
      (s, y) ∈ flowDomain Y ∧ flowOf Y s y ∈ Φ.target :=
    isCompact_uIcc.eventually_forall_of_forall_eventually fun s hs ↦
      (continuous_swap.tendsto (Φ x, s)).eventually
        (hO.mem_nhds ⟨uIcc_subset_setOf_mem_flowDomain ht hs, htarget s hs⟩)
  filter_upwards [(Φ.toOpenPartialHomeomorph.continuousAt hx).eventually hev,
    Φ.open_source.mem_nhds hx] with z hz hzs
  exact Φ.flowOf_eq_symm_flowOf hn hX hY hXY hzs (hz t right_mem_uIcc).1 fun s hs ↦ (hz s hs).2

/-- **The derivative of the flow read through a partial diffeomorphism.** Under the hypotheses of
`PartialDiffeomorph.flowOf_eq_symm_flowOf` at `x`, if the time-`t` map of `Y` has derivative `L` at
`Φ x`, then the time-`t` map of `X` has derivative `dΦ⁻¹ ∘ L ∘ dΦ_x` at `x`. -/
theorem hasMFDerivAt_flowOf (hX : CMDiff 1 (fun x ↦ (⟨x, X x⟩ : TangentBundle I M)))
    (hY : CMDiff 1 (fun y ↦ (⟨y, Y y⟩ : TangentBundle I' M')))
    (hXY : ∀ x ∈ Φ.source, mfderiv I I' Φ x (X x) = Y (Φ x)) {t : ℝ} {x : M}
    (hx : x ∈ Φ.source) (ht : (t, Φ x) ∈ flowDomain Y)
    (htarget : ∀ s ∈ uIcc 0 t, flowOf Y s (Φ x) ∈ Φ.target)
    {L : TangentSpace I' (Φ x) →L[ℝ] TangentSpace I' (flowOf Y t (Φ x))}
    (hL : HasMFDerivAt I' I' (flowOf Y t) (Φ x) L) :
    HasMFDerivAt I I (flowOf X t) x
      ((mfderiv I' I Φ.symm (flowOf Y t (Φ x))).comp (L.comp (mfderiv I I' Φ x))) :=
  ((Φ.symm.mdifferentiableAt hn (htarget t right_mem_uIcc)).hasMFDerivAt.comp x
    (hL.comp x (Φ.mdifferentiableAt hn hx).hasMFDerivAt)).congr_of_eventuallyEq
    ((Φ.eventually_flowOf_eq_symm_flowOf hn hX hY hXY hx ht htarget).mono fun _ hz ↦ hz.2)

end PartialDiffeomorph
