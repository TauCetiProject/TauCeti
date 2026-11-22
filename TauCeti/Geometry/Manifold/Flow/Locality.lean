/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.Basic

/-!
# Flows depend only on the field near a trajectory

Let `v` and `w` be `C¹` vector fields on a Hausdorff boundaryless manifold. If `w` agrees with
`v` at the points of a trajectory of `v`, then this trajectory is also a trajectory of `w`, since
it solves the same equation, and so by uniqueness it is the maximal trajectory of `w` through the
same point (`TauCeti.flowOf_eq_of_forall_mem_Ioo`). If `w` agrees with `v` on an open set `U`
containing the trajectory of `x` from time `0` to time `t`, the same holds for all initial points
and times near `(t, x)`, because the trajectories of nearby points stay in `U` for nearby times
(`TauCeti.eventually_flowOf_eq_of_eqOn`).

The same argument compares flows across a map. If `f` carries `v` to a field `X` on another
manifold, `df_y (v y) = X (f y)`, at the points `y` of an open set containing the trajectory of `x`
from time `0` to time `t`, then near `(t, x)` the map `f` carries the trajectories of `v` to those
of `X` (`TauCeti.eventually_apply_flowOf_of_mfderiv_eq`). The map need only be defined and related
near the trajectory, so it can be the inverse of a chart, reading a flow on a manifold through a
flow on the model space.

These statements are what makes compactly supported perturbations of a vector field local. The
local objects built from the flow near a trajectory segment depend only on the field near it:
hitting times and transitions (`TauCeti.flowHittingTime_eventuallyEq_of_eqOn` and
`TauCeti.flowTransition_eventuallyEq_of_eqOn` in `TauCeti.Geometry.Manifold.Flow.HittingTime`),
transitions whose last leg runs where the fields agree
(`TauCeti.flowTransition_eventuallyEq_comp_of_eqOn` in
`TauCeti.Geometry.Manifold.Flow.Transition`), and linearized return maps of closed orbits
(`TauCeti.returnDerivative_eq_of_eqOn` in `TauCeti.Geometry.Manifold.Flow.ReturnDerivative`).

## Main results

* `TauCeti.flowOf_eq_of_forall_mem_Ioo`: a trajectory of `v` along which `w = v` is a trajectory
  of `w`.
* `TauCeti.flowOf_eq_of_eqOn`, `TauCeti.eventually_flowOf_eq_of_eqOn`: the flows of fields
  agreeing on an open set containing the trajectory of `x` from time `0` to `t` agree at `(t, x)`
  and on a neighbourhood of `(t, x)`.
* `TauCeti.mfderiv_flowOf_add_eq_of_eqOn`: after reaching the trajectory at time `τ`, the flow of
  `w` continues as the flow of `v`, and the derivatives of the time maps compose accordingly.
* `TauCeti.exists_Ioo_eventually_forall_mem_flowDomain_flowOf_mem`: the trajectories of points
  near `x` follow that of `x` into an open set containing its segment from time `0` to `t`.
* `TauCeti.eventually_apply_flowOf_of_mfderiv_eq`: a map relating two fields near a trajectory
  segment carries the trajectories of the first to those of the second near that segment.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 9 (uniqueness of integral curves and the fundamental theorem on flows).
* J. Palis, W. de Melo, *Geometric Theory of Dynamical Systems*, Springer 1982, Chapter 3, §§3–4
  (local perturbations of closed orbits in the proof of the Kupka–Smale theorem).
* M. M. Peixoto, *On an approximation theorem of Kupka and Smale*, J. Differential Equations 3
  (1967), 214–227, §2.
-/

public section

noncomputable section

open Function Manifold Set Filter
open scoped Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [IsManifold I 1 M] [BoundarylessManifold I M]
  {v w : (x : M) → TangentSpace I x} {U : Set M} {x : M} {t : ℝ}

/-- **A trajectory along which two fields agree.** If `w` agrees with `v` at the points of the
trajectory of `x` under `v` for the times of an open interval around `0` on which this trajectory
is defined, then the trajectory of `x` under `w` is defined on that interval and equals it. -/
theorem flowOf_eq_of_forall_mem_Ioo (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (hw : CMDiff 1 (fun y ↦ (⟨y, w y⟩ : TangentBundle I M))) {a b : ℝ} (h0 : (0 : ℝ) ∈ Ioo a b)
    (hdom : ∀ s ∈ Ioo a b, (s, x) ∈ flowDomain v)
    (hvw : ∀ s ∈ Ioo a b, w (flowOf v s x) = v (flowOf v s x)) (ht : t ∈ Ioo a b) :
    (t, x) ∈ flowDomain w ∧ flowOf w t x = flowOf v t x := by
  have hγ : IsMIntegralCurveOn (fun s ↦ flowOf v s x) w (Ioo a b) := fun s hs ↦ by
    simpa only [hvw s hs] using (isMIntegralCurveOn_flowOf hv x).mono hdom s hs
  refine ⟨mem_flowDomain.mpr (hγ.subset_maximalIntegralCurveInterval h0 (flowOf_zero v x) ht), ?_⟩
  rw [flowOf_apply]
  exact hγ.eqOn_maximalIntegralCurve hw h0 (flowOf_zero v x) ht

section Tube

variable [CompleteSpace E]

/-- **Nearby trajectories follow a trajectory segment.** If the trajectory of `x` under a `C¹`
field `v` from time `0` to time `t` lies in an open set `U`, there is an open interval `Ioo a b`
containing `0` and `t` such that, for every initial point `y` near `x`, the trajectory of `y` is
defined at all times of `Ioo a b` and stays in `U`. -/
theorem exists_Ioo_eventually_forall_mem_flowDomain_flowOf_mem
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) (hU : IsOpen U)
    (ht : (t, x) ∈ flowDomain v) (htU : MapsTo (fun s ↦ flowOf v s x) (uIcc 0 t) U) :
    ∃ a b : ℝ, (0 : ℝ) ∈ Ioo a b ∧ t ∈ Ioo a b ∧
      ∀ᶠ y in 𝓝 x, ∀ s ∈ Ioo a b, (s, y) ∈ flowDomain v ∧ flowOf v s y ∈ U := by
  -- The pairs whose `v`-trajectory point lies in `U` form an open set containing the segment
  -- `uIcc 0 t × {x}`; a product neighbourhood of the segment inside it contains a product of an
  -- open interval around `uIcc 0 t` and a neighbourhood of `x`.
  set O : Set (ℝ × M) := flowDomain v ∩ (fun y : ℝ × M ↦ flowOf v y.1 y.2) ⁻¹' U
  have hO : IsOpen O := (contMDiffOn_flowOf le_rfl hv).continuousOn.isOpen_inter_preimage
    (isOpen_flowDomain hv) hU
  have hseg : uIcc 0 t ⊆ maximalIntegralCurveInterval v x :=
    ordConnected_maximalIntegralCurveInterval.uIcc_subset
      (mem_flowDomain.mp (mem_flowDomain_zero hv x)) (mem_flowDomain.mp ht)
  have hsub : uIcc 0 t ×ˢ {x} ⊆ O := by
    rintro ⟨s, y⟩ ⟨hs, rfl⟩
    exact ⟨mem_flowDomain.mpr (hseg hs), htU hs⟩
  obtain ⟨u, V, hu, hV, hKu, hxV, huV⟩ :=
    generalized_tube_lemma isCompact_uIcc isCompact_singleton hO hsub
  -- Since `u` is open, it contains an open interval `Ioo a b` around `uIcc 0 t`.
  obtain ⟨a, ha, hau⟩ := exists_Ioc_subset_of_mem_nhds (hu.mem_nhds (hKu ⟨le_rfl, inf_le_sup⟩))
    ⟨0 ⊓ t - 1, by linarith⟩
  obtain ⟨b, hb, hbu⟩ := exists_Ico_subset_of_mem_nhds (hu.mem_nhds (hKu ⟨inf_le_sup, le_rfl⟩))
    ⟨0 ⊔ t + 1, by linarith⟩
  have hab : Ioo a b ⊆ u := fun s hs ↦ by
    rcases le_or_gt s (0 ⊓ t) with hs₁ | hs₁
    · exact hau ⟨hs.1, hs₁⟩
    rcases le_or_gt s (0 ⊔ t) with hs₂ | hs₂
    · exact hKu ⟨hs₁.le, hs₂⟩
    · exact hbu ⟨hs₂.le, hs.2⟩
  refine ⟨a, b, ⟨ha.trans_le inf_le_left, le_sup_left.trans_lt hb⟩,
    ⟨ha.trans_le inf_le_right, le_sup_right.trans_lt hb⟩, ?_⟩
  filter_upwards [hV.mem_nhds (hxV rfl)] with y hy s hs
  exact huV ⟨hab hs, hy⟩

end Tube

section Flow

variable [CompleteSpace E]
  (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
  (hw : CMDiff 1 (fun y ↦ (⟨y, w y⟩ : TangentBundle I M))) (hU : IsOpen U) (hvw : EqOn w v U)
include hv hw hU hvw

/-- **Flows of fields agreeing on an open set.** Let `w` agree with `v` on an open set `U`
containing the trajectory of `x` under `v` from time `0` to time `t`. Then, for all initial points
and times near `(t, x)`, the flow of `w` is defined and equals the flow of `v`. -/
theorem eventually_flowOf_eq_of_eqOn (ht : (t, x) ∈ flowDomain v)
    (htU : MapsTo (fun s ↦ flowOf v s x) (uIcc 0 t) U) :
    ∀ᶠ y in 𝓝 (t, x), y ∈ flowDomain w ∧ flowOf w y.1 y.2 = flowOf v y.1 y.2 := by
  obtain ⟨a, b, h0, htab, hV⟩ := exists_Ioo_eventually_forall_mem_flowDomain_flowOf_mem hv hU ht htU
  filter_upwards [prod_mem_nhds (isOpen_Ioo.mem_nhds htab) hV] with y ⟨hy₁, hy₂⟩
  exact flowOf_eq_of_forall_mem_Ioo hv hw h0 (fun s hs ↦ (hy₂ s hs).1)
    (fun s hs ↦ hvw (hy₂ s hs).2) hy₁

/-- Let `w` agree with `v` on an open set `U` containing the trajectory of `x` under `v` from
time `0` to time `t`. Then the flow of `w` is defined at `(t, x)` and equals the flow of `v`. -/
theorem flowOf_eq_of_eqOn (ht : (t, x) ∈ flowDomain v)
    (htU : MapsTo (fun s ↦ flowOf v s x) (uIcc 0 t) U) :
    (t, x) ∈ flowDomain w ∧ flowOf w t x = flowOf v t x :=
  (eventually_flowOf_eq_of_eqOn hv hw hU hvw ht htU).self_of_nhds

/-- **Flowing on along a segment where the fields agree.** Let `w` carry `p` to `x` at time `τ`,
and let `w` agree with `v` on an open set `U` containing the trajectory of `x` under `v` from time
`0` to time `t`. Then `w` carries `p` at time `τ + t` to the point `flowOf v t x`, and the
derivative of its time-`(τ + t)` map at `p` is that of its time-`τ` map followed by that of the
time-`t` map of `v` at `x`. -/
theorem mfderiv_flowOf_add_eq_of_eqOn {τ : ℝ} {p : M} (hτ : (τ, p) ∈ flowDomain w)
    (hx : flowOf w τ p = x) (ht : (t, x) ∈ flowDomain v)
    (htU : MapsTo (fun s ↦ flowOf v s x) (uIcc 0 t) U) :
    (τ + t, p) ∈ flowDomain w ∧ flowOf w (τ + t) p = flowOf v t x ∧
      ∀ ξ : TangentSpace I p,
        -- The tangent spaces at the two values are both the model space `E`.
        @Eq E (mfderiv I I (flowOf w (τ + t)) p ξ)
          (mfderiv I I (flowOf v t) x (mfderiv I I (flowOf w τ) p ξ)) := by
  have h := eventually_flowOf_eq_of_eqOn hv hw hU hvw ht htU
  obtain ⟨htw, hteq⟩ := h.self_of_nhds
  obtain ⟨hdom, hval⟩ := flowOf_add hw hτ (hx ▸ htw)
  refine ⟨hdom, by rw [← hval, hx, hteq], fun ξ ↦ ?_⟩
  -- Near `x` the time-`t` maps of `w` and `v` agree, so they have the same derivative at `x`.
  have hev : flowOf w t =ᶠ[𝓝 x] flowOf v t := by
    filter_upwards [((continuous_const.prodMk continuous_id).tendsto x).eventually h] with y hy
    exact hy.2
  rw [← mfderiv_flowOf_add_apply hw hτ hx htw ξ, hev.mfderiv_eq]
  -- `tangentSpaceCast` is the identity of the model space.
  rfl

end Flow

section Related

variable [CompleteSpace E] {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M']
  [T2Space M'] [IsManifold I' 1 M'] [BoundarylessManifold I' M'] {f : M → M'}
  {X : (y : M') → TangentSpace I' y}

/-- **Flows of fields related near a trajectory.** Let `f : M → M'` be differentiable on an open
set `U` and carry `v` to `X` there, `df_y (v y) = X (f y)` for `y ∈ U`. If the trajectory of `x`
under `v` from time `0` to time `t` lies in `U`, then for all initial points and times `(s, y)`
near `(t, x)` the flow of `X` is defined at `(s, f y)` and `f` carries the trajectory of `y` to
it: `f (flowOf v s y) = flowOf X s (f y)`. Neither `f` nor the fields need be defined or related
outside `U`; for instance `f` can be the inverse of a chart, relating a field on the model space
to one on a manifold near a segment of a trajectory. -/
theorem eventually_apply_flowOf_of_mfderiv_eq
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (hX : CMDiff 1 (fun y ↦ (⟨y, X y⟩ : TangentBundle I' M'))) (hU : IsOpen U)
    (hf : ∀ y ∈ U, MDifferentiableAt I I' f y) (hvX : ∀ y ∈ U, mfderiv I I' f y (v y) = X (f y))
    (ht : (t, x) ∈ flowDomain v) (htU : MapsTo (fun s ↦ flowOf v s x) (uIcc 0 t) U) :
    ∀ᶠ y in 𝓝 (t, x),
      (y.1, f y.2) ∈ flowDomain X ∧ f (flowOf v y.1 y.2) = flowOf X y.1 (f y.2) := by
  obtain ⟨a, b, h0, htab, hV⟩ := exists_Ioo_eventually_forall_mem_flowDomain_flowOf_mem hv hU ht htU
  filter_upwards [prod_mem_nhds (isOpen_Ioo.mem_nhds htab) hV] with y ⟨hy₁, hy₂⟩
  -- On `Ioo a b` the trajectory of `y.2` runs in `U`, so `f` carries it to an integral curve of
  -- `X` through `f y.2`, which is the maximal one there by uniqueness.
  have hγ : IsMIntegralCurveOn (f ∘ fun s ↦ flowOf v s y.2) X (Ioo a b) :=
    ((isMIntegralCurveOn_flowOf hv y.2).mono fun s hs ↦ (hy₂ s hs).1).map_of_mfderiv_eq
      (fun s hs ↦ hf _ (hy₂ s hs).2) fun s hs ↦ hvX _ (hy₂ s hs).2
  have hγ0 : (f ∘ fun s ↦ flowOf v s y.2) 0 = f y.2 := by
    rw [comp_apply, flowOf_zero]
  refine ⟨mem_flowDomain.mpr (hγ.subset_maximalIntegralCurveInterval h0 hγ0 hy₁), ?_⟩
  rw [flowOf_apply X]
  exact (hγ.eqOn_maximalIntegralCurve hX h0 hγ0 hy₁).symm

end Related

end TauCeti
