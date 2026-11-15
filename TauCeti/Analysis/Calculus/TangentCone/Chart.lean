/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Topology.Algebra.Module.Determinant
public import TauCeti.Analysis.Calculus.TangentCone.Basic
public import TauCeti.Geometry.Manifold.LocallyFlat.Basic
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.Calculus.ContDiff.Operations
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import TauCeti.Analysis.InnerProductSpace.QuadraticForm.Bounds

/-!
# Tangent cones of sets flattened by a differentiable chart

A set `S` that some chart `e` flattens onto a closed linear subspace `L` (in the sense of
`TauCeti.IsSliceChart`) has, at each of its points `y`, a tangent cone which is a linear
subspace: it is the preimage of `L` under the derivative of `e` at `y`. This identifies Mathlib's
intrinsic `tangentConeAt` with the tangent space read off any flattening chart, so a condition
stated with tangent cones, such as the transversality of two submanifolds, does not depend on the
charts used to verify it.

## Main results

* `OpenPartialHomeomorph.det_fderiv_ne_zero`: a chart of a space to itself that is
  differentiable in both directions at a point has a derivative with nonzero determinant there.
* `OpenPartialHomeomorph.exists_hasFDerivAt_of_chart`: a chart that is differentiable at a
  point, with inverse differentiable at the image point, has a derivative there represented by a
  continuous linear equivalence.
* `TauCeti.image_tangentConeAt_eq_tangentConeAt_preimage_symm`: the invertible derivative `A` of a
  chart at a point carries the tangent cone of a set there onto the tangent cone of its image.
* `TauCeti.image_tangentConeAt_eq_of_preimage_eq`: the same for a homeomorphism carrying one set
  onto another.
* `TauCeti.IsSliceChart.tangentConeAt_eq_preimage`: the tangent cone of a set flattened onto a
  closed subspace is the preimage of that subspace under the derivative of the chart.
* `TauCeti.IsSliceChart.span_tangentConeAt_eq_comap`: hence the span of the tangent cone is that
  preimage, viewed as a subspace, and it has the dimension of the model subspace
  (`TauCeti.IsSliceChart.finrank_span_tangentConeAt`).
* `TauCeti.IsSliceChart.eventually_forall_mem_span_tangentConeAt_inner_nonneg`: near a point
  where a `C¹` flattening chart is tangent to the identity, the tangent spaces of the flattened
  set stay in the cone where a quadratic form coercive on the model subspace is nonnegative.
* `TauCeti.IsSliceChart.tangentConeAt_eq_empty`: at a point of the source outside the flattened
  set, its tangent cone is empty, because a neighbourhood misses the set
  (`TauCeti.IsSliceChart.exists_mem_nhds_disjoint`); near such a point a `C^n` chart with `C^n`
  inverse flattens any set missing a neighbourhood onto the zero subspace
  (`TauCeti.exists_isSliceChart_bot_of_disjoint`).
-/

public section

open Filter Set Topology

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace OpenPartialHomeomorph

/-- A chart of a space to itself which is differentiable at a point of its source, and whose
inverse is differentiable at the image point, has a derivative with nonzero determinant there. -/
theorem det_fderiv_ne_zero (e : OpenPartialHomeomorph E E) {y : E} (hy : y ∈ e.source)
    (he : DifferentiableAt 𝕜 e y) (hes : DifferentiableAt 𝕜 e.symm (e y)) :
    (fderiv 𝕜 e y).det ≠ 0 := by
  obtain ⟨A, hA⟩ := e.isInvertible_fderiv hy he hes
  rw [← hA]
  exact A.toLinearEquiv.isUnit_det'.ne_zero

/-- A chart which is differentiable at a point of its source, and whose inverse is differentiable
at the image point, has a derivative represented by a continuous linear equivalence. -/
theorem exists_hasFDerivAt_of_chart (e : OpenPartialHomeomorph E F) {y : E} (hy : y ∈ e.source)
    (he : DifferentiableAt 𝕜 e y) (hes : DifferentiableAt 𝕜 e.symm (e y)) :
    ∃ A : E ≃L[𝕜] F, HasFDerivAt e (A : E →L[𝕜] F) y := by
  obtain ⟨A, hA⟩ := e.isInvertible_fderiv hy he hes
  exact ⟨A, hA ▸ he.hasFDerivAt⟩

end OpenPartialHomeomorph

namespace TauCeti

/-- **A chart transports tangent cones.** If the chart `e` has invertible derivative `A` at a point
`y` of its source, then `A` maps the tangent cone of `S` at `y` onto the tangent cone at `e y` of
the image of `S` read through `e`. -/
theorem image_tangentConeAt_eq_tangentConeAt_preimage_symm {e : OpenPartialHomeomorph E F}
    {S : Set E} {y : E} {A : E ≃L[𝕜] F} (hy : y ∈ e.source)
    (hA : HasFDerivAt e (A : E →L[𝕜] F) y) :
    A '' tangentConeAt 𝕜 S y = tangentConeAt 𝕜 (e.symm ⁻¹' S) (e y) := by
  have hyt : e y ∈ e.target := e.map_source hy
  refine Subset.antisymm ?_ fun w hw ↦ ⟨A.symm w, ?_, A.apply_symm_apply w⟩
  · rintro _ ⟨v, hv, rfl⟩
    rw [← tangentConeAt_inter_nhds (e.open_source.mem_nhds hy)] at hv
    refine tangentConeAt_mono ?_ (hA.hasFDerivWithinAt.mapsTo_tangent_cone hv)
    rintro _ ⟨z, ⟨hzS, hz⟩, rfl⟩
    rwa [mem_preimage, e.left_inv hz]
  · have hAs : HasFDerivAt e.symm (A.symm : F →L[𝕜] E) (e y) :=
      e.hasFDerivAt_symm hyt (by rwa [e.left_inv hy])
    rw [← tangentConeAt_inter_nhds (e.open_target.mem_nhds hyt)] at hw
    have hmaps := hAs.hasFDerivWithinAt.mapsTo_tangent_cone hw
    rw [e.left_inv hy] at hmaps
    refine tangentConeAt_mono ?_ hmaps
    rintro _ ⟨w, ⟨hwS, -⟩, rfl⟩
    exact hwS

/-- **A homeomorphism transports tangent cones.** If a homeomorphism `Φ` carries `S` onto `T`, in
the sense that `Φ ⁻¹' T = S`, and has invertible derivative `A` at `y`, then `A` maps the tangent
cone of `S` at `y` onto the tangent cone of `T` at `Φ y`. -/
theorem image_tangentConeAt_eq_of_preimage_eq {Φ : E ≃ₜ F} {S : Set E} {T : Set F} {y : E}
    {A : E ≃L[𝕜] F} (hST : Φ ⁻¹' T = S) (hA : HasFDerivAt Φ (A : E →L[𝕜] F) y) :
    A '' tangentConeAt 𝕜 S y = tangentConeAt 𝕜 T (Φ y) := by
  have hA' : HasFDerivAt Φ.toOpenPartialHomeomorph (A : E →L[𝕜] F) y := by
    rwa [Homeomorph.toOpenPartialHomeomorph_apply]
  have h := image_tangentConeAt_eq_tangentConeAt_preimage_symm (S := S) (mem_univ y) hA'
  subst hST
  rwa [Homeomorph.toOpenPartialHomeomorph_symm_apply, Homeomorph.toOpenPartialHomeomorph_apply,
    Homeomorph.preimage_symm, Φ.image_preimage] at h

namespace IsSliceChart

variable {e : OpenPartialHomeomorph E F} {L : Submodule 𝕜 F} {S : Set E} {y : E}
  {A : E ≃L[𝕜] F}

/-- **The tangent cone of a flattened set.** If the chart `e` flattens `S` onto a closed linear
subspace `L` and has invertible derivative `A` at a point `y` of `S`, then the tangent cone of `S`
at `y` is `A⁻¹ L`. -/
theorem tangentConeAt_eq_preimage (h : IsSliceChart e (L : Set F) S) (hL : IsClosed (L : Set F))
    (hy : y ∈ e.source) (hyS : y ∈ S) (hA : HasFDerivAt e (A : E →L[𝕜] F) y) :
    tangentConeAt 𝕜 S y = A ⁻¹' L := by
  have hey : e y ∈ L := (h.mem_iff hy).1 hyS
  have ht : e.target ∈ 𝓝 (e y) := e.open_target.mem_nhds (e.map_source hy)
  have hS : e.symm ⁻¹' S ∩ e.target = (L : Set F) ∩ e.target := by
    ext w
    refine and_congr_left fun hw ↦ ?_
    rw [mem_preimage, h.mem_iff (e.map_target hw), e.right_inv hw, SetLike.mem_coe]
  rw [← preimage_image_eq (tangentConeAt 𝕜 S y) A.injective,
    image_tangentConeAt_eq_tangentConeAt_preimage_symm hy hA, ← tangentConeAt_inter_nhds ht, hS,
    tangentConeAt_inter_nhds ht, L.tangentConeAt_eq hL hey]

/-- The span of the tangent cone of a set flattened onto a closed subspace `L`, at a point where
the chart has invertible derivative `A`, is the subspace `A⁻¹ L`. -/
theorem span_tangentConeAt_eq_comap (h : IsSliceChart e (L : Set F) S)
    (hL : IsClosed (L : Set F)) (hy : y ∈ e.source) (hyS : y ∈ S)
    (hA : HasFDerivAt e (A : E →L[𝕜] F) y) :
    Submodule.span 𝕜 (tangentConeAt 𝕜 S y) = L.comap (A : E →ₗ[𝕜] F) := by
  rw [h.tangentConeAt_eq_preimage hL hy hyS hA]
  exact Submodule.span_eq (L.comap (A : E →ₗ[𝕜] F))

/-- The tangent space of a set flattened onto a closed subspace `L`, at a point where the chart has
invertible derivative, has the dimension of `L`. -/
theorem finrank_span_tangentConeAt (h : IsSliceChart e (L : Set F) S)
    (hL : IsClosed (L : Set F)) (hy : y ∈ e.source) (hyS : y ∈ S)
    (hA : HasFDerivAt e (A : E →L[𝕜] F) y) :
    Module.finrank 𝕜 (Submodule.span 𝕜 (tangentConeAt 𝕜 S y)) = Module.finrank 𝕜 L := by
  rw [h.span_tangentConeAt_eq_comap hL hy hyS hA]
  exact (Submodule.comap_equiv_eq_map_symm A.toLinearEquiv L) ▸
    LinearEquiv.finrank_map_eq A.symm.toLinearEquiv L

/-- The tangent cone of a flattened set vanishes at a point of the chart's source outside the
set. -/
theorem tangentConeAt_eq_empty (h : IsSliceChart e (L : Set F) S) (hL : IsClosed (L : Set F))
    (hy : y ∈ e.source) (hyS : y ∉ S) : tangentConeAt 𝕜 S y = ∅ := by
  obtain ⟨U, hU, hdisj⟩ := h.exists_mem_nhds_disjoint hL hy hyS
  rw [← tangentConeAt_inter_nhds hU, inter_comm, hdisj.inter_eq]
  refine Set.not_nonempty_iff_eq_empty.1 fun hne => ?_
  simpa using mem_closure_of_nonempty_tangentConeAt hne

end IsSliceChart

namespace IsSliceChart

open scoped RealInnerProductSpace

/-- **Tangent spaces near a point of tangency stay in a coercive cone.** Near a point `x` at which
a `C¹` chart `e` flattening `S` onto a closed subspace `L` is tangent to the identity, the tangent
spaces of `S` lie in the cone `⟪B v, v⟫ ≥ 0`, as soon as the form `⟪B u, u⟫` is coercive on `L`. -/
theorem eventually_forall_mem_span_tangentConeAt_inner_nonneg {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {e : OpenPartialHomeomorph H H} {L : Submodule ℝ H} {S : Set H}
    (hS : IsSliceChart e (L : Set H) S) (hLc : IsClosed (L : Set H)) {B : H →L[ℝ] H} {x : H}
    (hxe : x ∈ e.source) (hed : HasFDerivAt e (ContinuousLinearMap.id ℝ H) x)
    (heC : ∀ z ∈ e.source, ContDiffAt ℝ 1 e z) (heCs : ∀ z ∈ e.target, ContDiffAt ℝ 1 e.symm z)
    {c : ℝ} (hc : 0 < c) (hL : ∀ u ∈ L, c * ‖u‖ ^ 2 ≤ ⟪B u, u⟫) :
    ∀ᶠ z in 𝓝 x, z ∈ S → ∀ v ∈ Submodule.span ℝ (tangentConeAt ℝ S z), 0 ≤ ⟪B v, v⟫ := by
  set δ : ℝ := min (1 / 2) (c / (12 * (‖B‖ + 1)))
  have hδpos : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ₂ : ‖B‖ * δ ≤ c / 12 := by
    have h : δ ≤ c / (12 * (‖B‖ + 1)) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h
    nlinarith [norm_nonneg B]
  have hfd : Tendsto (fun z ↦ fderiv ℝ e z) (𝓝 x) (𝓝 (ContinuousLinearMap.id ℝ H)) := by
    have h := (heC x hxe).continuousAt_fderiv one_ne_zero
    rwa [ContinuousAt, hed.fderiv] at h
  filter_upwards [e.open_source.mem_nhds hxe, hfd.eventually (Metric.ball_mem_nhds _ hδpos)]
    with z hz hzd hzS v hv
  obtain ⟨A, hA⟩ := e.exists_hasFDerivAt_of_chart hz ((heC z hz).differentiableAt one_ne_zero)
    ((heCs _ (e.map_source hz)).differentiableAt one_ne_zero)
  rw [hS.span_tangentConeAt_eq_comap hLc hz hzS hA] at hv
  -- The vector `A v` lies in `L` and is `δ`-close to `v`.
  refine ContinuousLinearMap.re_inner_apply_nonneg_of_norm_sub_le (𝕜 := ℝ) (u := A v) hc.le
    hδpos.le (min_le_left _ _) hδ₂ (hL _ hv) ?_
  have h : A v - v = (fderiv ℝ e z - ContinuousLinearMap.id ℝ H) v := by
    rw [hA.fderiv, sub_apply, ContinuousLinearMap.id_apply, ContinuousLinearEquiv.coe_coe]
  rw [h]
  refine ((fderiv ℝ e z - _).le_opNorm v).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg v))
  simpa [dist_eq_norm] using hzd.le

end IsSliceChart

section Flatten

open scoped ContDiff

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Near a point missing a flattened set, a `C^n` chart with `C^n` inverse flattens that set onto
the zero subspace: it is empty there, and a restricted translation avoids `0`. -/
theorem exists_isSliceChart_bot_of_disjoint {n : ℕ∞ω} {A U : Set E} {y : E} [Nontrivial E]
    (hU : U ∈ 𝓝 y) (hA : Disjoint U A) :
    ∃ e : OpenPartialHomeomorph E E, y ∈ e.source ∧
      (∀ z ∈ e.source, ContDiffAt 𝕜 n e z) ∧
      (∀ z ∈ e.target, ContDiffAt 𝕜 n e.symm z) ∧
      IsSliceChart e ((⊥ : Submodule 𝕜 E) : Set E) A := by
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.1 hU
  have : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  obtain ⟨c, hc⟩ := exists_norm_eq E hr.le
  let e : OpenPartialHomeomorph E E :=
    (Homeomorph.addRight (c - y)).toOpenPartialHomeomorph.restrOpen (Metric.ball y r)
      Metric.isOpen_ball
  have he_apply (x : E) : e x = x + (c - y) := by
    simp only [e, OpenPartialHomeomorph.coe_restrOpen, Homeomorph.toOpenPartialHomeomorph_apply,
      Homeomorph.coe_addRight]
  have hesymm_apply (x : E) : e.symm x = x + -(c - y) := by
    simp only [e, OpenPartialHomeomorph.coe_restrOpen_symm,
      Homeomorph.toOpenPartialHomeomorph_symm_apply]
    refine (Homeomorph.addRight (c - y)).symm_apply_eq.2 ?_
    simp only [Homeomorph.coe_addRight]
    abel
  refine ⟨e, by simp [e, hr], fun z _ => ?_, fun z _ => ?_, isSliceChart_iff.2 fun z hz => ?_⟩
  · have : (e : E → E) = fun x => x + (c - y) := funext he_apply
    rw [this]
    exact contDiffAt_id.add contDiffAt_const
  · have : (e.symm : E → E) = fun x => x + -(c - y) := funext hesymm_apply
    rw [this]
    exact contDiffAt_id.add contDiffAt_const
  · have hz' : z ∈ Metric.ball y r := by simpa [e] using hz
    refine iff_of_false (fun hzA => Set.disjoint_left.1 hA (hrU hz') hzA) ?_
    intro h0
    have h0' : z + (c - y) = 0 := by rw [← he_apply]; exact Submodule.mem_bot 𝕜 |>.1 h0
    have hzc : z - y = -c := eq_neg_of_add_eq_zero_left (by rw [← h0']; abel)
    rw [Metric.mem_ball, dist_eq_norm, hzc, norm_neg, hc] at hz'
    exact lt_irrefl _ hz'

end Flatten

end TauCeti
