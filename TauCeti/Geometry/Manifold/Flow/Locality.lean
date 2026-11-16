/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.ReturnDerivative

/-!
# Flows and return germs depend only on the field near a trajectory

Let `v` and `w` be `C¹` vector fields on a Hausdorff boundaryless manifold. If `w` agrees with
`v` at the points of a trajectory of `v`, then this trajectory is also a trajectory of `w`, since
it solves the same equation, and so by uniqueness it is the maximal trajectory of `w` through the
same point (`TauCeti.flowOf_eq_of_forall_mem_Ioo`). If `w` agrees with `v` on an open set `U`
containing the trajectory of `x` from time `0` to time `t`, the same holds for all initial points
and times near `(x, t)`, because the trajectories of nearby points stay in `U` for nearby times
(`TauCeti.eventually_flowOf_eq_of_eqOn`).

Consequently the local objects built from the flow near a trajectory segment, the hitting times of
transverse sections and the transitions between them, are the same for `v` and `w` as germs at
the initial point (`TauCeti.flowHittingTime_eventuallyEq_of_eqOn`,
`TauCeti.flowTransition_eventuallyEq_of_eqOn`). For a closed orbit through `p` with return time
`T₀`, a field `w` agreeing with `v` near the orbit has the same orbit, the same return germ and
the same linearized return map (`TauCeti.returnDerivative_eq_of_eqOn`); in particular the orbit
is nondegenerate for `w` exactly when it is for `v`.

These statements are what makes compactly supported perturbations of a vector field local. A
variation of `v` supported away from an orbit segment does not change the return germ along it.
A variation supported in a flow box, a small neighbourhood of the first part of the orbit from
`p` to `q = flowOf v T₁ p`, changes the return germ only through the transition across that box:
if `w = v` near the rest of the orbit, from `q` back to `p`, then the transition of `w` from a
section through `p` to a section through `flowOf v T₂ q` at time `T₁ + T₂` is the transition of
`w` across the box followed by the unchanged transition of `v`
(`TauCeti.flowTransition_eventuallyEq_comp_of_eqOn`), and its derivative factors accordingly
(`TauCeti.mfderiv_flowTransition_eq_comp_of_eqOn`). This is how the return map of a closed orbit
is modified by flow-box variations in the proof of the Kupka–Smale theorem.

## Main results

* `TauCeti.flowOf_eq_of_forall_mem_Ioo`: a trajectory of `v` along which `w = v` is a trajectory
  of `w`.
* `TauCeti.flowOf_eq_of_eqOn`, `TauCeti.eventually_flowOf_eq_of_eqOn`: the
  flows of fields agreeing on an open set containing a trajectory segment agree there, and near
  its initial point and time.
* `TauCeti.flowHittingTime_eventuallyEq_of_eqOn`, `TauCeti.flowTransition_eventuallyEq_of_eqOn`:
  hitting times and transitions depend only on the field near the trajectory segment.
* `TauCeti.returnDerivative_eq_of_eqOn`, `TauCeti.normalReturnDerivative_eq_of_eqOn`: so do the
  linearized and normal return maps of a closed orbit.
* `TauCeti.flowTransition_eventuallyEq_comp_of_eqOn`,
  `TauCeti.mfderiv_flowTransition_eq_comp_of_eqOn`: a transition of `w` whose last leg runs
  where `w = v` factors through the transition of `v` along that leg.

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
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [IsManifold I 1 M] [BoundarylessManifold I M]
  {v w : (x : M) → TangentSpace I x} {U : Set M} {x p q : M} {g g' : M → ℝ} {t T T₁ T₂ : ℝ}

/-- **A trajectory along which two fields agree.** If `w` agrees with `v` at the points of the
trajectory of `x` under `v` for the times of an open interval around `0` on which this trajectory
is defined, then the trajectory of `x` under `w` is defined on that interval and equals it. -/
theorem flowOf_eq_of_forall_mem_Ioo (hw : CMDiff 1 (fun y ↦ (⟨y, w y⟩ : TangentBundle I M)))
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) {a b : ℝ} (h0 : (0 : ℝ) ∈ Ioo a b)
    (hdom : ∀ s ∈ Ioo a b, (s, x) ∈ flowDomain v)
    (hvw : ∀ s ∈ Ioo a b, w (flowOf v s x) = v (flowOf v s x)) (ht : t ∈ Ioo a b) :
    (t, x) ∈ flowDomain w ∧ flowOf w t x = flowOf v t x := by
  have hγ : IsMIntegralCurveOn (fun s ↦ flowOf v s x) w (Ioo a b) := fun s hs ↦ by
    simpa only [hvw s hs] using (isMIntegralCurveOn_flowOf hv x).mono hdom s hs
  refine ⟨mem_flowDomain.mpr (hγ.subset_maximalIntegralCurveInterval h0 (flowOf_zero v x) ht), ?_⟩
  rw [flowOf_apply]
  exact hγ.eqOn_maximalIntegralCurve hw h0 (flowOf_zero v x) ht

section Flow

variable [CompleteSpace E]
  (hw : CMDiff 1 (fun y ↦ (⟨y, w y⟩ : TangentBundle I M)))
  (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) (hU : IsOpen U) (hvw : EqOn w v U)
include hw hv hU hvw

/-- **Flows of fields agreeing on an open set.** Let `w` agree with `v` on an open set `U`
containing the trajectory of `x` under `v` from time `0` to time `t`. Then, for all initial points
and times near `(t, x)`, the flow of `w` is defined and equals the flow of `v`. -/
theorem eventually_flowOf_eq_of_eqOn (ht : (t, x) ∈ flowDomain v)
    (htU : MapsTo (fun s ↦ flowOf v s x) (uIcc 0 t) U) :
    ∀ᶠ y in 𝓝 (t, x), y ∈ flowDomain w ∧ flowOf w y.1 y.2 = flowOf v y.1 y.2 := by
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
  have h0 : (0 : ℝ) ∈ Ioo a b := ⟨ha.trans_le inf_le_left, le_sup_left.trans_lt hb⟩
  have htab : t ∈ Ioo a b := ⟨ha.trans_le inf_le_right, le_sup_right.trans_lt hb⟩
  filter_upwards [prod_mem_nhds (isOpen_Ioo.mem_nhds htab) (hV.mem_nhds (hxV rfl))]
    with y ⟨hy₁, hy₂⟩
  have hO' : ∀ s ∈ Ioo a b, (s, y.2) ∈ O := fun s hs ↦ huV ⟨hab hs, hy₂⟩
  exact flowOf_eq_of_forall_mem_Ioo hw hv h0 (fun s hs ↦ (hO' s hs).1)
    (fun s hs ↦ hvw (hO' s hs).2) hy₁

/-- Let `w` agree with `v` on an open set `U` containing the trajectory of `x` under `v` from
time `0` to time `t`. Then the flow of `w` is defined at `(t, x)` and equals the flow of `v`. -/
theorem flowOf_eq_of_eqOn (ht : (t, x) ∈ flowDomain v)
    (htU : MapsTo (fun s ↦ flowOf v s x) (uIcc 0 t) U) :
    (t, x) ∈ flowDomain w ∧ flowOf w t x = flowOf v t x :=
  (eventually_flowOf_eq_of_eqOn hw hv hU hvw ht htU).self_of_nhds

variable (hT : (T, p) ∈ flowDomain v) (hTU : MapsTo (fun s ↦ flowOf v s p) (uIcc 0 T) U)
  (hg : ContMDiffAt I 𝓘(ℝ) 1 g (flowOf v T p))
  (hgv : mvfderiv I g (flowOf v T p) (v (flowOf v T p)) ≠ 0)
include hT hTU hg hgv

/-- **Hitting times depend only on the field near the trajectory.** If `w` agrees with `v` on an
open set containing the trajectory of `p` under `v` from time `0` to time `T`, then the hitting
times of a section through `flowOf v T p` transverse to `v` agree near `p`. -/
theorem flowHittingTime_eventuallyEq_of_eqOn :
    flowHittingTime w g T p =ᶠ[𝓝 p] flowHittingTime v g T p := by
  have hflow := eventually_flowOf_eq_of_eqOn hw hv hU hvw hT hTU
  obtain ⟨hTw, hpw⟩ := hflow.self_of_nhds
  have hwq : w (flowOf v T p) = v (flowOf v T p) := hvw (hTU right_mem_uIcc)
  refine (eventuallyEq_flowHittingTime hw hTw (by rwa [hpw]) (by rwa [hpw, hwq])
    continuousAt_flowHittingTime (flowHittingTime_self ..) ?_).symm
  filter_upwards [eventually_flowHittingTime hv hT hg hgv,
    (tendsto_flowHittingTime_prodMk (I := I) (v := v) (g := g)).eventually hflow] with z hz hzw
  rw [hzw.2, hz.2, hpw]

/-- **Transitions depend only on the field near the trajectory.** If `w` agrees with `v` on an
open set containing the trajectory of `p` under `v` from time `0` to time `T`, then the
transitions to a section through `flowOf v T p` transverse to `v` agree near `p`. -/
theorem flowTransition_eventuallyEq_of_eqOn :
    flowTransition w g T p =ᶠ[𝓝 p] flowTransition v g T p := by
  filter_upwards [flowHittingTime_eventuallyEq_of_eqOn hw hv hU hvw hT hTU hg hgv,
    (tendsto_flowHittingTime_prodMk (I := I) (v := v) (g := g)).eventually
      (eventually_flowOf_eq_of_eqOn hw hv hU hvw hT hTU)] with z hz hzw
  rw [flowTransition_apply, flowTransition_apply, hz]
  exact hzw.2

end Flow

section ReturnGerm

variable [FiniteDimensional ℝ E]
  (hw : CMDiff 1 (fun y ↦ (⟨y, w y⟩ : TangentBundle I M)))
  (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) (hU : IsOpen U) (hvw : EqOn w v U)
include hw hv hU hvw

section Return

variable (hT : (T, p) ∈ flowDomain v) (hTU : MapsTo (fun s ↦ flowOf v s p) (uIcc 0 T) U)
  (hg : ContMDiffAt I 𝓘(ℝ) 1 g (flowOf v T p))
  (hgv : mvfderiv I g (flowOf v T p) (v (flowOf v T p)) ≠ 0)
include hT hTU hg hgv

/-- **Linearized return maps depend only on the field near the orbit.** If `w` agrees with `v` on
an open set containing the trajectory of `p` under `v` from time `0` to time `T`, then the
derivatives at `p` of the transitions to a section through `flowOf v T p` agree. For a closed
orbit, `flowOf v T p = p`, these are the linearized return maps, so the orbit is nondegenerate for
`w` exactly when it is for `v`. -/
theorem returnDerivative_eq_of_eqOn : returnDerivative w g T p = returnDerivative v g T p := by
  ext u
  -- The cast between the tangent spaces at the two equal values of the transitions is the
  -- identity.
  have h := flowTransition_eventuallyEq_of_eqOn hw hv hU hvw hT hTU hg hgv
  rw [returnDerivative_apply, returnDerivative_apply]
  exact DFunLike.congr_fun (h.mfderiv_eq (I := I) (I' := I)) u

/-- **Normal return maps depend only on the field near the orbit.** The normal return derivatives
of `v` and `w` at `p` agree when `w` agrees with `v` on an open set containing the trajectory of
`p` under `v` from time `0` to time `T`. -/
theorem normalReturnDerivative_eq_of_eqOn
    {hrw : LinearMap.range (returnDerivative w g T p) ≤
      LinearMap.ker (mvfderiv I g p : TangentSpace I p →ₗ[ℝ] ℝ)}
    {hrv : LinearMap.range (returnDerivative v g T p) ≤
      LinearMap.ker (mvfderiv I g p : TangentSpace I p →ₗ[ℝ] ℝ)} :
    normalReturnDerivative w g T p hrw = normalReturnDerivative v g T p hrv := by
  ext u
  simp only [coe_normalReturnDerivative_apply,
    returnDerivative_eq_of_eqOn hw hv hU hvw hT hTU hg hgv]

end Return

section Composition

variable (hT₁ : (T₁, p) ∈ flowDomain w) (hq : flowOf w T₁ p = q)
  (hg' : ContMDiffAt I 𝓘(ℝ) 1 g' q) (hg'w : mvfderiv I g' q (w q) ≠ 0)
  (hT₂ : (T₂, q) ∈ flowDomain v) (hTU : MapsTo (fun s ↦ flowOf v s q) (uIcc 0 T₂) U)
  (hg : ContMDiffAt I 𝓘(ℝ) 1 g (flowOf v T₂ q))
  (hgv : mvfderiv I g (flowOf v T₂ q) (v (flowOf v T₂ q)) ≠ 0)
include hT₁ hq hg' hg'w hT₂ hTU hg hgv

/-- **A transition whose last leg runs where the fields agree.** Let the flow of `w` carry `p` to
`q` at time `T₁`, and let `w` agree with `v` on an open set containing the trajectory of `q`
under `v` from time `0` to time `T₂`. Then near `p` the transition of `w` at time `T₁ + T₂` to a
section through `flowOf v T₂ q` is the transition of `w` to a section through `q` followed by the
transition of `v` from there.

For a closed orbit of `v` through `p` with return time `T₁ + T₂`, and a variation `w` of `v`
supported in a flow box around the trajectory of `p` up to time `T₁` and agreeing with `v` on that
trajectory, this expresses the return germ of `w` as the transition of `w` across the box
followed by the unchanged transition of `v` back to the section through `p`. -/
theorem flowTransition_eventuallyEq_comp_of_eqOn :
    flowTransition w g (T₁ + T₂) p =ᶠ[𝓝 p] flowTransition v g T₂ q ∘ flowTransition w g' T₁ p := by
  obtain ⟨hT₂w, hrw⟩ := flowOf_eq_of_eqOn hw hv hU hvw hT₂ hTU
  have hwr : w (flowOf v T₂ q) = v (flowOf v T₂ q) := hvw (hTU right_mem_uIcc)
  have hh : Tendsto (flowTransition w g' T₁ p) (𝓝 p) (𝓝 q) := by
    simpa only [flowTransition_self, hq] using
      (continuousAt_flowTransition hw hT₁ (by rwa [hq]) (by rwa [hq])).tendsto
  refine (flowTransition_comp_eventuallyEq hw hT₁ hq hg' hg'w hT₂w hrw (hrw ▸ hg)
    (by rwa [hwr]) |>.symm).trans ?_
  exact (flowTransition_eventuallyEq_of_eqOn hw hv hU hvw hT₂ hTU hg hgv).comp_tendsto hh

/-- **The derivative of a transition whose last leg runs where the fields agree.** Under the
hypotheses of `TauCeti.flowTransition_eventuallyEq_comp_of_eqOn`, the derivative at `p` of the
transition of `w` at time `T₁ + T₂` is the derivative of the transition of `w` to the section
through `q` followed by the derivative at `q` of the transition of `v` from there. For a closed
orbit of `v` this computes the linearized return map of a flow-box variation `w`. -/
theorem mfderiv_flowTransition_eq_comp_of_eqOn :
    mfderiv I I (flowTransition w g (T₁ + T₂) p) p =
      mfderiv I I (flowTransition v g T₂ q) q ∘L mfderiv I I (flowTransition w g' T₁ p) p := by
  have hh := mdifferentiableAt_flowTransition hw hT₁ (by rwa [hq]) (by rwa [hq])
  have hh' := mdifferentiableAt_flowTransition hv hT₂ hg hgv
  have hcomp :=
    flowTransition_eventuallyEq_comp_of_eqOn hw hv hU hvw hT₁ hq hg' hg'w hT₂ hTU hg hgv
  ext u
  -- The cast between the tangent spaces at the two equal values of the maps is the identity.
  exact (DFunLike.congr_fun hcomp.mfderiv_eq u).trans
    (mfderiv_comp_apply_of_eq p hh' hh (by rw [flowTransition_self, hq]) u)

end Composition

end ReturnGerm

end TauCeti
