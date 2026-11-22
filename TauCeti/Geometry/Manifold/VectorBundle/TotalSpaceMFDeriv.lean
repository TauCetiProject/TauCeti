/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Differentiating a map into the total space of a fibre bundle

A map `f` from a manifold into the total space of a fibre bundle is read, near a point `x`, in the
chart of the total space centred at `f x`.  By `FiberBundle.extChartAt` that chart is the
trivialization at the base point `(f x).proj` followed by the base chart there, so the reading of
`f` is the pair of its base map read in the base chart and of its fibre coordinate read in that
trivialization.  This file turns that observation into a criterion: `f` has the manifold
derivative `L₁.prod L₂` within a set exactly when its base map has the manifold derivative `L₁`
and its fibre coordinate has the derivative `L₂`.  This is the derivative form of
`Bundle.mdifferentiableWithinAt_totalSpace`.

For a curve `z` the criterion is restated with ordinary derivatives: the curve has a manifold
derivative within a parameter set exactly when it is continuous there and its base curve read in
the base chart and its fibre coordinate have derivatives.  This is the form in which a curve into a
vector bundle is compared with a pair of ordinary derivatives, and in particular the form in which
an integral curve of a vector field on a tangent bundle is unpacked into an equation on its base
curve and one on its velocity.

## Main results

* `TauCeti.Manifold.hasMFDerivWithinAt_totalSpace_iff`: the manifold derivative of a map into a
  total space, within a set, read as the pair of the manifold derivative of its base map and of
  the derivative of its fibre coordinate in the trivialization at the base point of the image.
* `TauCeti.Manifold.hasMFDerivAt_totalSpace_iff`: its unrestricted case.
* `TauCeti.Manifold.hasMFDerivWithinAt_totalSpace_curve_iff`: the case of a curve, read as the
  pair of the derivative of its base curve in the base chart and of the derivative of its fibre
  coordinate in the trivialization, both taken at the current point of the curve.
* `TauCeti.Manifold.hasMFDerivAt_totalSpace_curve_iff`: its unrestricted case.
* `TauCeti.Manifold.extChartAt_totalSpace_apply_snd`: the fibre coordinate of a point in a chart
  of the total space is its fibre coordinate in the trivialization at the centre of the chart.
* `Bundle.TotalSpace.hasMFDerivAt_smul_curve`: in a vector bundle, the velocity of a scalar
  curve `r ↦ f r • z` through the fibre of `z`.
* `TauCeti.Manifold.hasMFDerivAt_totalSpaceMk_add_smul`: in a vector bundle, the velocity of a
  straight line `r ↦ a + r • b` in the fibre over `x`.

-/

public section

open Bundle Filter Set
open scoped Manifold Topology

noncomputable section

variable
  {𝕜 B F : Type*} {V : B → Type*}
  [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
  [TopologicalSpace B] [ChartedSpace HB B] [FiberBundle F V]
  {z : 𝕜 → TotalSpace F V} {s : Set 𝕜} {t : 𝕜} {a : EB} {b : F}

namespace TauCeti.Manifold

/-- The fibre coordinate of a point `y` in the chart of the total space at `x` is its fibre
coordinate in the trivialization at `x.proj`: by `FiberBundle.extChartAt` that chart is the
trivialization followed by a chart of the base, which leaves the fibre coordinate unchanged. -/
theorem extChartAt_totalSpace_apply_snd (x y : TotalSpace F V) :
    (extChartAt (IB.prod 𝓘(𝕜, F)) x y).2 = (trivializationAt F V x.proj y).2 := by
  rw [FiberBundle.extChartAt]
  -- The second factor of `(extChartAt IB x.proj).prod (PartialEquiv.refl F)` is the identity.
  rfl

section General

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*}
  [TopologicalSpace HM] {IM : ModelWithCorners 𝕜 EM HM} {M : Type*} [TopologicalSpace M]
  [ChartedSpace HM M] {f : M → TotalSpace F V} {u : Set M} {x : M}
  {L₁ : TangentSpace IM x →L[𝕜] TangentSpace IB (f x).proj} {L₂ : TangentSpace IM x →L[𝕜] F}

/-- **The manifold derivative of a map into a total space.**  A map `f` into the total space of a
fibre bundle has the manifold derivative `L₁.prod L₂` within `u` at `x` exactly when its base map
has the manifold derivative `L₁` there and its fibre coordinate, read in the trivialization at
`(f x).proj`, has the derivative `L₂`.  This is the derivative form of
`Bundle.mdifferentiableWithinAt_totalSpace`. -/
theorem hasMFDerivWithinAt_totalSpace_iff :
    HasMFDerivWithinAt IM (IB.prod 𝓘(𝕜, F)) f u x (L₁.prod L₂) ↔
      HasMFDerivWithinAt IM IB (fun y ↦ (f y).proj) u x L₁ ∧
        HasMFDerivWithinAt IM 𝓘(𝕜, F) (fun y ↦ (trivializationAt F V (f x).proj (f y)).2) u x
          L₂ := by
  set e := trivializationAt F V (f x).proj with he
  unfold HasMFDerivWithinAt
  rw [and_and_and_comm, ← FiberBundle.continuousWithinAt_totalSpace, and_congr_right_iff]
  intro hf
  -- Read in charts, `f` is the pair of its base map read in the base chart and of its fibre
  -- coordinate, at every point whose base point lies in the base set of `e`.
  have hpt : ∀ v, ((f ((extChartAt IM x).symm v)).proj ∈ e.baseSet) →
      writtenInExtChartAt IM (IB.prod 𝓘(𝕜, F)) x f v =
        (writtenInExtChartAt IM IB x (fun y ↦ (f y).proj) v,
          writtenInExtChartAt IM 𝓘(𝕜, F) x (fun y ↦ (e (f y)).2) v) := by
    intro v hv
    simp only [writtenInExtChartAt, FiberBundle.extChartAt, extChartAt_model_space_eq_id,
      Function.comp_apply, PartialEquiv.trans_apply, PartialEquiv.prod_coe,
      PartialEquiv.refl_coe, OpenPartialHomeomorph.coe_toPartialEquiv, Trivialization.coe_coe,
      id_eq, ← he, Trivialization.coe_fst _ (e.mem_source.2 hv)]
  have hmem : (fun y ↦ (f y).proj) ⁻¹' e.baseSet ∈ 𝓝[u] x :=
    ((FiberBundle.continuous_proj F V).continuousWithinAt.comp hf (mapsTo_image f u))
      (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt F V _))
  -- Pulled back to the chart of `M`, the identification `hpt` holds near the centre.
  have hfun := Filter.eventually_of_mem (extChartAt_preimage_mem_nhdsWithin hmem) hpt
  have hx := hpt _ (by
    rw [extChartAt_to_inv]; exact FiberBundle.mem_baseSet_trivializationAt F V _)
  refine (Filter.EventuallyEq.hasFDerivWithinAt_iff hfun hx).trans ?_
  -- `tangentSpaceCastModel` is the identity of the model spaces, so the derivative of the pair is
  -- the pair of the derivatives of its components, as in `HasMFDerivWithinAt.prodMk`.
  exact ⟨fun h ↦ ⟨h.fst.congr_fderiv (ContinuousLinearMap.fst_comp_prod _ _),
    h.snd.congr_fderiv (ContinuousLinearMap.snd_comp_prod _ _)⟩, fun h ↦ h.1.prodMk h.2⟩

/-- The unrestricted case of `TauCeti.Manifold.hasMFDerivWithinAt_totalSpace_iff`. -/
theorem hasMFDerivAt_totalSpace_iff :
    HasMFDerivAt IM (IB.prod 𝓘(𝕜, F)) f x (L₁.prod L₂) ↔
      HasMFDerivAt IM IB (fun y ↦ (f y).proj) x L₁ ∧
        HasMFDerivAt IM 𝓘(𝕜, F) (fun y ↦ (trivializationAt F V (f x).proj (f y)).2) x L₂ :=
  hasMFDerivWithinAt_univ.symm.trans <| hasMFDerivWithinAt_totalSpace_iff.trans <|
    and_congr hasMFDerivWithinAt_univ hasMFDerivWithinAt_univ

end General

/-- **The manifold derivative of a curve into a total space.**  A curve into the total space of a
fibre bundle has the manifold derivative determined by `(a, b)` within the parameter set `s` at
`t` exactly when it is continuous there, its base curve read in the base chart at the current base
point has derivative `a`, and its fibre coordinate read in the trivialization at that point has
derivative `b`.  This is the case of `TauCeti.Manifold.hasMFDerivWithinAt_totalSpace_iff` for a
curve. -/
theorem hasMFDerivWithinAt_totalSpace_curve_iff :
    HasMFDerivWithinAt 𝓘(𝕜, 𝕜) (IB.prod 𝓘(𝕜, F)) z s t ((1 : 𝕜 →L[𝕜] 𝕜).smulRight (a, b)) ↔
      ContinuousWithinAt z s t ∧
        HasDerivWithinAt (fun r ↦ extChartAt IB (z t).proj (z r).proj) a s t ∧
          HasDerivWithinAt (fun r ↦ (trivializationAt F V (z t).proj (z r)).2) b s t := by
  -- The derivative of the curve is the pair of the derivatives of its two components.
  have hab : (1 : 𝕜 →L[𝕜] 𝕜).smulRight (a, b) =
      ((1 : 𝕜 →L[𝕜] 𝕜).smulRight a).prod ((1 : 𝕜 →L[𝕜] 𝕜).smulRight b) := by
    ext <;> simp
  -- The manifold derivative of the base curve is the derivative of its reading in the base chart.
  have hbase : HasMFDerivWithinAt 𝓘(𝕜, 𝕜) IB (fun r ↦ (z r).proj) s t
      ((1 : 𝕜 →L[𝕜] 𝕜).smulRight a) ↔ ContinuousWithinAt (fun r ↦ (z r).proj) s t ∧
        HasDerivWithinAt (fun r ↦ extChartAt IB (z t).proj (z r).proj) a s t := by
    unfold HasMFDerivWithinAt
    simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_symm,
      PartialEquiv.refl_coe, preimage_id_eq, id_eq, ModelWithCorners.range_eq_univ, inter_univ,
      Function.comp_id, hasDerivWithinAt_iff_hasFDerivWithinAt]
    -- `tangentSpaceCastModel` is the identity of the model spaces, so the two derivatives agree.
    rfl
  -- `rw [hab]` fails here: in the goal the derivative is typed through the tangent spaces.
  refine (iff_of_eq (congrArg (HasMFDerivWithinAt 𝓘(𝕜, 𝕜) (IB.prod 𝓘(𝕜, F)) z s t) hab)).trans
    (hasMFDerivWithinAt_totalSpace_iff.trans ?_)
  -- The fibre coordinate has values in the model fibre, where the two derivatives agree.
  have hfib : HasMFDerivWithinAt 𝓘(𝕜, 𝕜) 𝓘(𝕜, F)
      (fun r ↦ (trivializationAt F V (z t).proj (z r)).2) s t ((1 : 𝕜 →L[𝕜] 𝕜).smulRight b) ↔
        HasDerivWithinAt (fun r ↦ (trivializationAt F V (z t).proj (z r)).2) b s t := by
    rw [hasDerivWithinAt_iff_hasFDerivWithinAt,
      ← ContinuousLinearMap.smulRight_one_eq_toSpanSingleton]
    exact hasMFDerivWithinAt_iff_hasFDerivWithinAt
  refine (and_congr hbase hfib).trans ?_
  rw [FiberBundle.continuousWithinAt_totalSpace]
  -- The continuity of the fibre coordinate follows from its derivative.
  exact ⟨fun ⟨⟨h₁, h₂⟩, h₃⟩ ↦ ⟨⟨h₁, h₃.continuousWithinAt⟩, h₂, h₃⟩,
    fun ⟨⟨h₁, _⟩, h₂, h₃⟩ ↦ ⟨⟨h₁, h₂⟩, h₃⟩⟩

/-- A curve into the total space which is continuous within `s` at `t` has a manifold derivative
there exactly when its base curve, read in the base chart at the current base point, and its fibre
coordinate, read in the trivialization at that same point, have the corresponding derivatives.
This is `TauCeti.Manifold.hasMFDerivWithinAt_totalSpace_curve_iff` with the continuity of the curve
supplied as a hypothesis rather than as a conjunct. -/
theorem hasMFDerivWithinAt_totalSpace_curve_iff_of_continuousWithinAt
    (hz : ContinuousWithinAt z s t) :
    HasMFDerivWithinAt 𝓘(𝕜, 𝕜) (IB.prod 𝓘(𝕜, F)) z s t ((1 : 𝕜 →L[𝕜] 𝕜).smulRight (a, b)) ↔
      HasDerivWithinAt (fun r ↦ extChartAt IB (z t).proj (z r).proj) a s t ∧
        HasDerivWithinAt (fun r ↦ (trivializationAt F V (z t).proj (z r)).2) b s t := by
  rw [hasMFDerivWithinAt_totalSpace_curve_iff, and_iff_right hz]

/-- The unrestricted case of `TauCeti.Manifold.hasMFDerivWithinAt_totalSpace_curve_iff`. -/
theorem hasMFDerivAt_totalSpace_curve_iff :
    HasMFDerivAt 𝓘(𝕜, 𝕜) (IB.prod 𝓘(𝕜, F)) z t ((1 : 𝕜 →L[𝕜] 𝕜).smulRight (a, b)) ↔
      ContinuousAt z t ∧
        HasDerivAt (fun r ↦ extChartAt IB (z t).proj (z r).proj) a t ∧
          HasDerivAt (fun r ↦ (trivializationAt F V (z t).proj (z r)).2) b t := by
  refine hasMFDerivWithinAt_univ.symm.trans ?_
  rw [hasMFDerivWithinAt_totalSpace_curve_iff, continuousWithinAt_univ, hasDerivWithinAt_univ,
    hasDerivWithinAt_univ]

end TauCeti.Manifold

namespace Bundle.TotalSpace

section VectorBundle

variable [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)] [VectorBundle 𝕜 F V]

/-- The fibre coordinate of `c • y` is `c` times that of `y`, by linearity of the trivialization
at the base point of `y`. -/
theorem trivializationAt_smul_snd (y : TotalSpace F V) (c : 𝕜) :
    (trivializationAt F V y.proj (⟨y.proj, c • y.snd⟩ : TotalSpace F V)).2 =
      c • (trivializationAt F V y.proj y).2 :=
  ((trivializationAt F V y.proj).linear 𝕜
    (FiberBundle.mem_baseSet_trivializationAt F V y.proj)).map_smul c y.snd

/-- If `f` has derivative `f'` at `t`, then the curve `r ↦ f r • y` in the fibre of `y` has
velocity `(0, f' • ξ)` at `t`, read in the chart at `y`, where `ξ` is the fibre coordinate of
`y`. -/
theorem hasMFDerivAt_smul_curve (y : TotalSpace F V) {f : 𝕜 → 𝕜} {f' : 𝕜}
    (hf : HasDerivAt f f' t) :
    HasMFDerivAt 𝓘(𝕜) (IB.prod 𝓘(𝕜, F)) (fun r : 𝕜 ↦ (⟨y.proj, f r • y.snd⟩ : TotalSpace F V)) t
      ((1 : 𝕜 →L[𝕜] 𝕜).smulRight ((0 : EB), f' • (trivializationAt F V y.proj y).2)) := by
  rw [TauCeti.Manifold.hasMFDerivAt_totalSpace_curve_iff]
  -- Both the continuity and the derivative of the fibre coordinate reduce to those of
  -- `r ↦ f r • ξ`.
  refine ⟨(FiberBundle.continuousAt_totalSpace F _).2 ⟨continuousAt_const, ?_⟩,
    hasDerivAt_const t (extChartAt IB y.proj y.proj), ?_⟩ <;>
    rw [funext fun r ↦ trivializationAt_smul_snd y (f r)]
  exacts [hf.continuousAt.smul continuousAt_const, hf.smul_const _]

end VectorBundle

end Bundle.TotalSpace

namespace TauCeti.Manifold

variable [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)] [VectorBundle 𝕜 F V]

/-- **The velocity of a line in a fibre.** In the fibre of a vector bundle over `x`, the line
`r ↦ a + r • b` has velocity `(0, ξ)` at `r = 0`, read in the chart at `a`, where `ξ` is the fibre
coordinate of `b` in the trivialization at `x`. -/
theorem hasMFDerivAt_totalSpaceMk_add_smul (x : B) (a b : V x) :
    HasMFDerivAt 𝓘(𝕜) (IB.prod 𝓘(𝕜, F)) (fun r : 𝕜 ↦ TotalSpace.mk' F x (a + r • b)) 0
      ((1 : 𝕜 →L[𝕜] 𝕜).smulRight
        ((0 : EB), (trivializationAt F V x).continuousLinearMapAt 𝕜 x b)) := by
  set e := trivializationAt F V x
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt F V x
  -- In the trivialization at `x` the line is the affine line `r ↦ e a + r • e b`.
  have hcoord : (fun r : 𝕜 ↦ (e (TotalSpace.mk' F x (a + r • b))).2) =
      fun r ↦ e.continuousLinearMapAt 𝕜 x a + r • e.continuousLinearMapAt 𝕜 x b := by
    funext r
    rw [← Trivialization.continuousLinearMapAt_apply_of_mem (R := 𝕜) e hx, map_add, map_smul]
  -- The line stays in the fibre over `x`, by definition of its points.
  have hproj : (TotalSpace.mk' F x (a + (0 : 𝕜) • b)).proj = x := rfl
  rw [hasMFDerivAt_totalSpace_curve_iff]
  refine ⟨(FiberBundle.continuousAt_totalSpace F _).2 ⟨continuousAt_const, ?_⟩,
    hasDerivAt_const (0 : 𝕜) (extChartAt IB x x), ?_⟩
  · rw [hproj, hcoord]
    fun_prop
  · rw [hproj, hcoord]
    have h := ((hasDerivAt_id' (0 : 𝕜)).smul_const (e.continuousLinearMapAt 𝕜 x b)).const_add
      (e.continuousLinearMapAt 𝕜 x a)
    rwa [one_smul] at h

end TauCeti.Manifold

end
