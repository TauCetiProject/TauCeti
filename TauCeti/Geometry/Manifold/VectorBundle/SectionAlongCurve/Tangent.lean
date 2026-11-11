/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.SectionAlongCurve.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import TauCeti.Geometry.Manifold.MFDeriv.ContinuousLinearMap
public import TauCeti.Geometry.Manifold.MFDeriv.Curve

/-!
# Coordinates of tangent fields along curves

For a tangent field along a curve, the coordinate readings `TauCeti.Manifold.sectionCoord` in the
preferred tangent-bundle trivializations at two points differ by the tangent coordinate change
between the two charts, wherever the curve lies in both base sets.

Transporting a tangent field along `γ` by the differential of a map `f` which is `C^n` at the base
point, with `2 ≤ n`, gives a tangent field along `f ∘ γ`, and differentiability in local
coordinates is preserved.

## Main results

* `TauCeti.Manifold.sectionCoord_coordChange`: two chart readings of a tangent field along a curve
  differ by the tangent coordinate change.
* `TauCeti.Manifold.sectionCoord_eventuallyEq_coordChange`: the same relation near a parameter
  whose image lies in both base sets.
* `TauCeti.Manifold.derivWithin_sectionCoord_eq`: the derivative along the curve of the chart
  reading of a tangent field in a fixed chart, by the product rule for the coordinate change.
* `ContMDiffAt.differentiableWithinAt_sectionCoord_mfderiv`: the differential of a map `C^n`
  (`2 ≤ n`) at `γ t` preserves differentiability of tangent fields along curves in local
  coordinates.
* `ContMDiffAt.differentiableAt_sectionCoord_mfderiv`: the unrestricted form.
-/

public section

open Bundle Filter
open scoped Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

variable (γ : 𝕜 → M) (V : Π t, TangentSpace I (γ t))

/-- The coordinate readings of a tangent field along a curve in the trivializations at two points
whose base sets contain `γ r` differ by the tangent coordinate change between them. -/
theorem sectionCoord_coordChange {x y : M} {r : 𝕜}
    (hx : γ r ∈ (trivializationAt E (TangentSpace I) x).baseSet)
    (hy : γ r ∈ (trivializationAt E (TangentSpace I) y).baseSet) :
    sectionCoord (F := E) γ V y r =
      tangentCoordChange I x y (γ r) (sectionCoord (F := E) γ V x r) := by
  rw [sectionCoord_apply, sectionCoord_apply, ← continuousLinearMapAt_symmL_coordChange hx hy,
    (trivializationAt E (TangentSpace I) x).symmL_continuousLinearMapAt (R := 𝕜) hx]

/-- Near a parameter whose image lies in two base sets, the coordinate readings of a tangent field
along a curve are related by the tangent coordinate change. -/
theorem sectionCoord_eventuallyEq_coordChange {x y : M} {s : Set 𝕜} {r : 𝕜}
    (hγ : ContinuousWithinAt γ s r)
    (hx : γ r ∈ (trivializationAt E (TangentSpace I) x).baseSet)
    (hy : γ r ∈ (trivializationAt E (TangentSpace I) y).baseSet) :
    sectionCoord (F := E) γ V y =ᶠ[𝓝[s] r]
      fun q ↦ tangentCoordChange I x y (γ q) (sectionCoord (F := E) γ V x q) := by
  filter_upwards
    [hγ.preimage_mem_nhdsWithin
      ((trivializationAt E (TangentSpace I) x).open_baseSet.mem_nhds hx),
    hγ.preimage_mem_nhdsWithin
      ((trivializationAt E (TangentSpace I) y).open_baseSet.mem_nhds hy)] with q hqx hqy
  exact sectionCoord_coordChange γ V hqx hqy

section CoordChangeDeriv

variable [IsManifold I 2 M]

/-- The derivative along the curve of the reading of `V` in the chart at `x`, where the base set
of the trivialization at `x` contains `γ t`: the product rule for the reading in the chart at `γ t`
and the tangent coordinate change, whose inhomogeneous term is the derivative of the coordinate
change applied to the fixed vector `V t` in the chart at `γ t`. -/
theorem derivWithin_sectionCoord_eq {x : M} {s : Set 𝕜} {t : 𝕜}
    (hx : γ t ∈ (trivializationAt E (TangentSpace I) x).baseSet) (hu : UniqueDiffWithinAt 𝕜 s t)
    (hγ : MDifferentiableWithinAt 𝓘(𝕜, 𝕜) I γ s t)
    (hV : DifferentiableWithinAt 𝕜 (sectionCoord (F := E) γ V (γ t)) s t) :
    derivWithin (sectionCoord (F := E) γ V x) s t
      = mvfderiv I (fun z ↦ tangentCoordChange I (γ t) x z
          (sectionCoord (F := E) γ V (γ t) t)) (γ t) (curveVelocityWithin I γ s t)
        + tangentCoordChange I (γ t) x (γ t)
            (derivWithin (sectionCoord (F := E) γ V (γ t)) s t) := by
  have hγ' : HasMFDerivWithinAt 𝓘(𝕜, 𝕜) I γ s t
      ((1 : 𝕜 →L[𝕜] 𝕜).smulRight (curveVelocityWithin I γ s t)) :=
    hasMFDerivWithinAt_curveVelocityWithin hγ
  have hc0 : γ t ∈ (trivializationAt E (TangentSpace I) (γ t)).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t)
  have hxsrc : γ t ∈ (extChartAt I x).source := by rwa [extChartAt_source]
  have hAmd : MDifferentiableAt I 𝓘(𝕜, E →L[𝕜] E) (tangentCoordChange I (γ t) x) (γ t) := by
    have : IsManifold I (1 + 1) M := inferInstanceAs (IsManifold I 2 M)
    exact (contMDiffAt_tangentCoordChange (I := I) (n := 1) (x := γ t) (y := x)
      hxsrc).mdifferentiableAt one_ne_zero
  have hAderiv : HasDerivWithinAt (fun r ↦ tangentCoordChange I (γ t) x (γ r))
      (mvfderiv I (tangentCoordChange I (γ t) x) (γ t) (curveVelocityWithin I γ s t)) s t :=
    hasDerivWithinAt_comp_curve hAmd hγ'
  rw [mvfderiv_clm_apply_const hAmd]
  exact ((hAderiv.clm_apply hV.hasDerivWithinAt).congr_of_eventuallyEq
    (sectionCoord_eventuallyEq_coordChange γ V hγ.continuousWithinAt hc0 hx)
    (sectionCoord_coordChange γ V hc0 hx)).derivWithin hu

end CoordChangeDeriv

/-! ### Transport by the differential of a map -/

section Map

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold I 2 M] [IsManifold J 2 N] {f : M → N} {n : WithTop ℕ∞}

variable {γ V}

/-- The differential of a map which is `C^n` at `γ t`, with `2 ≤ n`, carries a tangent field
along `γ` that is differentiable in local coordinates to a tangent field along `f ∘ γ` that is
differentiable in local coordinates. -/
theorem _root_.ContMDiffAt.differentiableWithinAt_sectionCoord_mfderiv {s : Set 𝕜} {t : 𝕜}
    (hf : ContMDiffAt I J n f (γ t)) (hn : 2 ≤ n)
    (hγ : MDifferentiableWithinAt 𝓘(𝕜, 𝕜) I γ s t)
    (hV : DifferentiableWithinAt 𝕜 (sectionCoord (F := E) γ V (γ t)) s t) :
    DifferentiableWithinAt 𝕜
      (sectionCoord (F := F) (f ∘ γ) (fun r ↦ mfderiv I J f (γ r) (V r)) (f (γ t))) s t := by
  let e := trivializationAt E (TangentSpace I) (γ t)
  have hbase : γ t ∈ e.baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t)
  have hnear : ∀ᶠ r in 𝓝[s] t, γ r ∈ e.baseSet :=
    hγ.continuousWithinAt.preimage_mem_nhdsWithin (e.open_baseSet.mem_nhds hbase)
  have hcoord : DifferentiableWithinAt 𝕜
      (fun r ↦ (e (TotalSpace.mk' E (γ r) (V r))).2) s t := by
    apply hV.congr_of_eventuallyEq
    · filter_upwards [hnear] with r hr
      rw [sectionCoord_apply,
        Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := 𝕜) e hr]
    · rw [sectionCoord_apply,
        Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := 𝕜) e hbase]
  have htotal : MDifferentiableWithinAt 𝓘(𝕜, 𝕜) I.tangent
      (fun r ↦ TotalSpace.mk' E (γ r) (V r)) s t := by
    rw [e.mdifferentiableWithinAt_totalSpace_iff I]
    · exact ⟨hγ, mdifferentiableWithinAt_iff_differentiableWithinAt.mpr hcoord⟩
    · exact (Bundle.Trivialization.mem_source e).2 hbase
  have htangent : MDifferentiableAt I.tangent J.tangent (tangentMap I J f)
      (TotalSpace.mk' E (γ t) (V t)) :=
    (hf.contMDiffAt_tangentMap (X := TotalSpace.mk' E (γ t) (V t)) (m := 1)
      (by rwa [one_add_one_eq_two])).mdifferentiableAt one_ne_zero
  have hmap : tangentMap I J f ∘ (fun r ↦ TotalSpace.mk' E (γ r) (V r)) =
      fun r ↦ TotalSpace.mk' F (f (γ r)) (mfderiv I J f (γ r) (V r)) := by
    funext r
    exact TotalSpace.ext tangentMap_proj (heq_of_eq tangentMap_snd)
  have htransport : MDifferentiableWithinAt 𝓘(𝕜, 𝕜) J.tangent
      (fun r ↦ TotalSpace.mk' F (f (γ r)) (mfderiv I J f (γ r) (V r))) s t := by
    simpa only [hmap] using htangent.comp_mdifferentiableWithinAt t htotal
  exact differentiableWithinAt_sectionCoord (f ∘ γ)
    (fun r ↦ mfderiv I J f (γ r) (V r)) htransport
    (FiberBundle.mem_baseSet_trivializationAt F (TangentSpace J) (f (γ t)))

/-- The unrestricted form of `ContMDiffAt.differentiableWithinAt_sectionCoord_mfderiv`. -/
theorem _root_.ContMDiffAt.differentiableAt_sectionCoord_mfderiv {t : 𝕜}
    (hf : ContMDiffAt I J n f (γ t)) (hn : 2 ≤ n)
    (hγ : MDifferentiableAt 𝓘(𝕜, 𝕜) I γ t)
    (hV : DifferentiableAt 𝕜 (sectionCoord (F := E) γ V (γ t)) t) :
    DifferentiableAt 𝕜
      (sectionCoord (F := F) (f ∘ γ) (fun r ↦ mfderiv I J f (γ r) (V r)) (f (γ t))) t := by
  rw [← differentiableWithinAt_univ]
  exact hf.differentiableWithinAt_sectionCoord_mfderiv hn hγ.mdifferentiableWithinAt
    hV.differentiableWithinAt

end Map

end TauCeti.Manifold
