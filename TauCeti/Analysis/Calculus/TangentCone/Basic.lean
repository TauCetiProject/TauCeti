/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.TangentCone.Real
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Calculus.TangentCone.Pi
import Mathlib.Analysis.Complex.ReImTopology
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Pi.Prod

/-!
# Tangent cones of linear subspaces and of curves

Basic facts about Mathlib's tangent cone `tangentConeAt` in topological modules.
The subspace calculation lets flattening charts identify their model subspaces with intrinsic
tangent spaces, while the curve lemma places velocities of invariant flows in the tangent cones
of their invariant sets. Polyhedral cones cut out by independent linear coordinates, and their
faces inside the kernels of the coordinates defining them, determine derivatives, so that corner
charts can test germs on a face. Differentials carry positive tangent cones into positive tangent
cones, which lets chart transitions of a manifold with corners compare the corners of the model.

## Main results

* `Submodule.tangentConeAt_eq`: the tangent cone of a closed subspace at one of its points is the
  subspace itself.
* `TauCeti.uniqueDiffOn_pi_halfSpace`: a coordinate half-space is a set of unique differentiability.
* `TauCeti.uniqueDiffOn_pi_Ici`: a closed coordinate orthant is a set of unique differentiability.
* `TauCeti.uniqueDiffOn_preimage_Ici_of_surjective`: so is its preimage under a surjective
  continuous linear map, and `TauCeti.uniqueDiffOn_ker_setOf_nonneg`: a face of such a cone has
  unique derivatives within the kernel of the coordinates defining the face.
* `TauCeti.uniqueDiffOn_setOfPred_le_im`: a closed half-plane `{z : ℂ | a ≤ z.im}` is a set of
  unique differentiability.
* `TauCeti.uniqueDiffOn_closedBall`: a closed ball of positive radius is a set of unique
  differentiability.
* `TauCeti.mem_tangentConeAt_setOf_im_eq`: a real direction is tangent to a horizontal line in `ℂ`.
* `IsPreconnected.uniqueDiffOn`: a preconnected set of reals containing two distinct points is a
  set of unique differentiability.
* `HasDerivAt.mem_tangentConeAt`: the velocity of a curve lying in a set is tangent to the set.
* `HasFDerivWithinAt.mapsTo_posTangentConeAt`: a differential carries positive tangent cones into
  positive tangent cones.
* `ContinuousLinearEquiv.mem_posTangentConeAt_image_iff`: a continuous linear equivalence carries
  positive tangent cones onto positive tangent cones.
* `HasDerivWithinAt.mem_posTangentConeAt`: the right derivative of a curve which frequently lies
  in a set, just after the base time, is a positive tangent vector of that set.
* `TauCeti.fderiv_apply_eq_self_of_mem_tangentConeAt`: a map fixing a set has derivative the
  identity on the tangent cone of that set.
-/

public section

open Filter Set Topology

variable {𝕜 E : Type*}

namespace Submodule

variable [DivisionRing 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace 𝕜] [TopologicalSpace E] [ContinuousSMul 𝕜 E]
  [(𝓝[≠] (0 : 𝕜)).NeBot]

/-- Over a division ring where `0` is not isolated, the tangent cone of a closed submodule
at one of its points is the submodule itself. -/
@[simp]
theorem tangentConeAt_eq (L : Submodule 𝕜 E) (hL : IsClosed (L : Set E)) {x : E} (hx : x ∈ L) :
    tangentConeAt 𝕜 (L : Set E) x = L := by
  refine Subset.antisymm (fun v hv ↦ ?_) fun v hv ↦ ?_
  · obtain ⟨ι, l, hl, c, d, -, hdL, hcd⟩ := exists_fun_of_mem_tangentConeAt hv
    exact hL.mem_of_tendsto hcd (hdL.mono fun n hn ↦
      L.smul_mem _ ((L.add_mem_iff_right hx).1 hn))
  · exact mem_tangentConeAt_of_add_smul_mem (l := 𝓝[≠] (0 : 𝕜)) (c := id) tendsto_id
      (Eventually.of_forall fun c ↦ L.add_mem hx (L.smul_mem c hv))

end Submodule

variable [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul 𝕜 E]

/-- The velocity of a curve which stays in a set `S` near time `t` lies in the tangent cone of `S`
at the point reached at time `t`. -/
theorem HasDerivAt.mem_tangentConeAt {γ : 𝕜 → E} {v : E} {t : 𝕜} {S : Set E}
    (hγ : HasDerivAt γ v t) (hS : ∀ᶠ s in 𝓝 t, γ s ∈ S) : v ∈ tangentConeAt 𝕜 S (γ t) := by
  refine mem_tangentConeAt_of_seq (𝓝[≠] t) (fun s ↦ (s - t)⁻¹) (fun s ↦ γ s - γ t) ?_ ?_ ?_
  · simpa only [sub_eq_add_neg, add_neg_cancel] using
      (hγ.hasFDerivAt.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).add_const (-(γ t))
  · simpa using hS.filter_mono nhdsWithin_le_nhds
  · have hd : Tendsto (fun s : 𝕜 ↦ s - t) (𝓝[≠] t) (𝓝 0) := by
      simpa using (tendsto_id.mono_left nhdsWithin_le_nhds :
        Tendsto id (𝓝[≠] t) (𝓝 t)).sub_const t
    have hcd : Tendsto (fun s : 𝕜 ↦ (s - t)⁻¹ • (s - t)) (𝓝[≠] t) (𝓝 (1 : 𝕜)) :=
      tendsto_const_nhds.congr' (eventually_mem_nhdsWithin.mono fun s hs ↦ by
        simp [smul_eq_mul, sub_ne_zero.mpr hs])
    simpa only [add_sub_cancel, ContinuousLinearMap.toSpanSingleton_apply, one_smul] using
      hγ.hasFDerivAt.hasFDerivWithinAt.lim hd
        (Eventually.of_forall fun _ ↦ mem_univ _) hcd

/-- A closed coordinate half-space has unique derivatives, including at its boundary. -/
theorem TauCeti.uniqueDiffOn_pi_halfSpace {ι : Type*} (i : ι) (a : ℝ) :
    UniqueDiffOn ℝ {x : ι → ℝ | a ≤ x i} := by
  have hlinear : IsLinearMap ℝ (fun x : ι → ℝ ↦ x i) :=
    ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
  apply uniqueDiffOn_convex (convex_halfSpace_ge hlinear a)
  refine ⟨fun _ ↦ a + 1, mem_interior_iff_mem_nhds.mpr ?_⟩
  have ha : a < a + 1 := lt_add_one a
  exact mem_of_superset ((isOpen_lt continuous_const (continuous_apply i)).mem_nhds ha)
    fun x hx ↦ hx.le

/-- A closed coordinate orthant `{x | ∀ i, a i ≤ x i}` has unique derivatives, including at its
corners. -/
theorem TauCeti.uniqueDiffOn_pi_Ici {ι : Type*} (a : ι → ℝ) : UniqueDiffOn ℝ (Ici a) := by
  rw [← pi_univ_Ici]
  exact UniqueDiffOn.univ_pi fun i ↦ uniqueDiffOn_Ici (a i)

/-- The preimage of a closed orthant `{u | ∀ i, a i ≤ u i}` of finitely many real coordinates under
a surjective continuous linear map has unique derivatives, including at its corners. -/
theorem TauCeti.uniqueDiffOn_preimage_Ici_of_surjective {E ι : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Finite ι] {q : E →L[ℝ] ι → ℝ} (hq : Function.Surjective q)
    (a : ι → ℝ) : UniqueDiffOn ℝ (q ⁻¹' Ici a) := by
  apply uniqueDiffOn_convex ((convex_Ici a).linear_preimage (q : E →ₗ[ℝ] ι → ℝ))
  obtain ⟨w, hw⟩ := hq (a + 1)
  -- Near `w` every coordinate of `q` stays above the corresponding coordinate of `a`.
  have hopen : IsOpen (q ⁻¹' univ.pi fun i ↦ Ioi (a i)) :=
    (isOpen_set_pi finite_univ fun i _ ↦ isOpen_Ioi).preimage q.continuous
  have hsub : q ⁻¹' univ.pi (fun i ↦ Ioi (a i)) ⊆ q ⁻¹' Ici a :=
    fun v hv i ↦ (hv i (mem_univ i)).le
  refine ⟨w, interior_maximal hsub hopen fun i _ ↦ ?_⟩
  simp [hw]

/-- Let `q` be a surjective continuous linear map to finitely many real coordinates and `t` a set
of these coordinates. In the kernel of the coordinates in `t`, the cone on which every coordinate
of `q` is nonnegative has unique derivatives, including at its vertex `0`. This cone is the face of
`q ⁻¹' Ici 0` on which the coordinates in `t` vanish. -/
theorem TauCeti.uniqueDiffOn_ker_setOf_nonneg {E ι : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Finite ι] {q : E →L[ℝ] ι → ℝ} (hq : Function.Surjective q) (t : Set ι) :
    UniqueDiffOn ℝ
      {v : (ContinuousLinearMap.pi fun i : t ↦ (ContinuousLinearMap.proj (i : ι)).comp q).ker |
        ∀ i, 0 ≤ q v i} := by
  classical
  let qt := ContinuousLinearMap.pi fun i : t ↦ (ContinuousLinearMap.proj (i : ι)).comp q
  -- The coordinates off `t`, restricted to the kernel, are still surjective.
  let q' : qt.ker →L[ℝ] {i // i ∉ t} → ℝ := ContinuousLinearMap.pi fun i ↦
    ((ContinuousLinearMap.proj (i : ι)).comp q).comp qt.ker.subtypeL
  have hq' : Function.Surjective q' := fun u ↦ by
    obtain ⟨w, hw⟩ := hq fun i ↦ if h : i ∈ t then 0 else u ⟨i, h⟩
    refine ⟨⟨w, ContinuousLinearMap.mem_ker_pi_proj_comp.mpr fun i hi ↦ by simp [hw, hi]⟩, ?_⟩
    funext i
    simp [q', hw, i.property]
  convert uniqueDiffOn_preimage_Ici_of_surjective hq' 0 using 1
  -- On the kernel the coordinates in `t` vanish, so only the others constrain the cone.
  ext v
  refine ⟨fun h i ↦ h i, fun h i ↦ ?_⟩
  by_cases hi : i ∈ t
  · exact (ContinuousLinearMap.mem_ker_pi_proj_comp.mp v.property i hi).ge
  · exact h ⟨i, hi⟩

/-- A closed half-plane `{z : ℂ | a ≤ z.im}` has unique derivatives, including on its boundary. -/
theorem TauCeti.uniqueDiffOn_setOfPred_le_im (a : ℝ) : UniqueDiffOn ℝ {z : ℂ | a ≤ z.im} :=
  uniqueDiffOn_convex (convex_halfSpace_im_ge a)
    ⟨Complex.I * (a + 1), by rw [Complex.interior_setOfPred_le_im]; simp⟩

/-- A closed ball of positive radius in a real normed space has unique derivatives, including on
its boundary sphere. -/
theorem TauCeti.uniqueDiffOn_closedBall {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) {r : ℝ} (hr : 0 < r) : UniqueDiffOn ℝ (Metric.closedBall x r) :=
  uniqueDiffOn_convex (convex_closedBall x r)
    ⟨x, mem_interior_iff_mem_nhds.mpr (Metric.closedBall_mem_nhds x hr)⟩

/-- A real direction `v` is tangent to the horizontal line `{y : ℂ | y.im = c}` at each of its
points. -/
theorem TauCeti.mem_tangentConeAt_setOf_im_eq {c : ℝ} {v w : ℂ} (hw : w.im = c) (hv : v.im = 0) :
    v ∈ tangentConeAt ℝ {y : ℂ | y.im = c} w := by
  have hseg : segment ℝ w (w + v) ⊆ {y : ℂ | y.im = c} := by
    rw [segment_eq_image']
    rintro _ ⟨θ, -, rfl⟩
    simp [hw, hv]
  simpa using mem_tangentConeAt_of_segment_subset hseg

/-- A preconnected set of reals containing two distinct points has unique derivatives. -/
theorem IsPreconnected.uniqueDiffOn {s : Set ℝ} (hs : IsPreconnected s) {a b : ℝ} (ha : a ∈ s)
    (hb : b ∈ s) (hab : a ≠ b) : UniqueDiffOn ℝ s :=
  uniqueDiffOn_convex hs.convex <| (nonempty_Ioo.2 (min_lt_max.2 hab)).mono <| by
    simpa only [uIcc, interior_Icc] using interior_mono (hs.ordConnected.uIcc_subset ha hb)

/-- The differential of a map carries the positive tangent cone of a set into the positive tangent
cone of its image. This is the positive-cone form of `HasFDerivWithinAt.mapsTo_tangent_cone`. -/
-- The proof follows Mathlib's proof of `HasFDerivWithinAt.mapsTo_tangent_cone`.
theorem HasFDerivWithinAt.mapsTo_posTangentConeAt {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {f' : E →L[ℝ] F}
    {s : Set E} {x : E} (h : HasFDerivWithinAt f f' s x) :
    MapsTo f' (posTangentConeAt s x) (posTangentConeAt (f '' s) (f x)) := by
  intro y hy
  rcases exists_fun_of_mem_tangentConeAt hy with ⟨ι, l, hl, c, d, hd₀, hds, hcd⟩
  apply mem_tangentConeAt_of_seq l c (fun n ↦ f (x + d n) - f x)
  · rw [tendsto_sub_nhds_zero_iff]
    refine h.continuousWithinAt.tendsto.comp <| tendsto_nhdsWithin_iff.mpr ⟨?_, hds⟩
    simpa using tendsto_const_nhds.add hd₀
  · exact hds.mono fun n hn ↦ ⟨x + d n, hn, by simp⟩
  · exact h.lim hd₀ hds hcd

/-- A continuous linear equivalence `e` identifies the positive tangent cone of `e '' s` at `e x`
with the image of the positive tangent cone of `s` at `x`. -/
@[simp]
theorem ContinuousLinearEquiv.mem_posTangentConeAt_image_iff {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (e : E ≃L[ℝ] F) {s : Set E}
    {x y : E} : e y ∈ posTangentConeAt (e '' s) (e x) ↔ y ∈ posTangentConeAt s x := by
  refine ⟨fun h ↦ ?_, fun h ↦ e.hasFDerivAt.hasFDerivWithinAt.mapsTo_posTangentConeAt h⟩
  simpa [e.symm_image_image] using e.symm.hasFDerivAt.hasFDerivWithinAt.mapsTo_posTangentConeAt h

/-- If a curve `x` has right derivative `w` at `t` and lies in `s` at times arbitrarily close to
`t` from the right, then `w` is a positive tangent vector of `s` at `x t`. -/
theorem HasDerivWithinAt.mem_posTangentConeAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {x : ℝ → E} {w : E} {t : ℝ} {s : Set E}
    (hx : HasDerivWithinAt x w (Ici t) t) (hs : ∃ᶠ τ in 𝓝[>] t, x τ ∈ s) :
    w ∈ posTangentConeAt s (x t) := by
  have h1 : (1 : ℝ) ∈ posTangentConeAt (Ici t ∩ x ⁻¹' s) t :=
    one_mem_posTangentConeAt_iff_frequently.2 <| (hs.and_eventually self_mem_nhdsWithin).mono
      fun τ ⟨h, hτ⟩ ↦ ⟨le_of_lt hτ, h⟩
  refine posTangentConeAt_mono ((image_mono inter_subset_right).trans (image_preimage_subset x s))
    (by simpa using (hx.mono inter_subset_left).hasFDerivWithinAt.mapsTo_posTangentConeAt h1)

/-- A map that is differentiable at `x ∈ s` and fixes every point of `s` has derivative the
identity on the tangent cone of `s` at `x`. -/
theorem TauCeti.fderiv_apply_eq_self_of_mem_tangentConeAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {s : Set E} {r : E → E} {x v : E} (hr : DifferentiableAt 𝕜 r x)
    (hrs : EqOn r id s) (hx : x ∈ s) (hv : v ∈ tangentConeAt 𝕜 s x) : fderiv 𝕜 r x v = v :=
  hr.hasFDerivAt.hasFDerivWithinAt.unique_on
    ((hasFDerivWithinAt_id x s).congr (fun _ hy ↦ hrs hy) (hrs hx)) hv
