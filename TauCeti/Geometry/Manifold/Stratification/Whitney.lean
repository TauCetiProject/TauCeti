/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
public import Mathlib.Topology.OpenPartialHomeomorph.Continuity
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Whitney's condition (b) in local coordinates

Let `s` be the upper stratum, `t` the lower stratum, and `T x` the coordinate tangent space
of `s` at `x`. Whitney's condition (b) at `p` asks that secants `x - y`, with `x ∈ s` and
`y ∈ t` approaching `p`, have distance to `T x` negligible relative to their length.
`WhitneyB` is the coordinate predicate; its tangent-space argument is separate so it can
be supplied by an embedded stratum in any chart. The predicate is unchanged by a `C¹` change
of coordinates, with tangent spaces transported by the derivative.

See John Mather, *Notes on Topological Stability*, §5.
-/

public section

open Asymptotics Filter Metric Set
open scoped Topology

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Whitney's condition (b) at `p` for the upper set `s` with tangent spaces `T` and lower set `t`,
expressed using relative distance of secants to the tangent spaces. A zero secant imposes no
condition, since every tangent space contains zero. -/
def WhitneyB (s t : Set E) (T : E → Submodule ℝ E) (p : E) : Prop :=
  (fun q : E × E ↦ infDist (q.1 - q.2) (T q.1)) =o[𝓝[s] p ×ˢ 𝓝[t] p]
    (fun q ↦ q.1 - q.2)

namespace WhitneyB

variable {s t : Set E} {T : E → Submodule ℝ E} {p : E}

/-- The relative distance of secants to the upper tangent spaces is little-o of their length. -/
theorem iff_isLittleO : WhitneyB s t T p ↔
    (fun q : E × E ↦ infDist (q.1 - q.2) (T q.1)) =o[𝓝[s] p ×ˢ 𝓝[t] p]
      (fun q ↦ q.1 - q.2) := (Iff.rfl)

/-- Condition (b) says that the distance to the upper tangent space divided by the length of
the secant tends to zero. The ratio is zero on the diagonal. -/
theorem iff_tendsto_div : WhitneyB s t T p ↔
    Tendsto (fun q : E × E ↦ infDist (q.1 - q.2) (T q.1) / ‖q.1 - q.2‖)
      (𝓝[s] p ×ˢ 𝓝[t] p) (𝓝 0) := by
  rw [iff_isLittleO, ← isLittleO_norm_right]
  refine isLittleO_iff_tendsto fun q hq ↦ ?_
  rw [norm_eq_zero.mp hq]
  exact infDist_zero_of_mem (Submodule.zero_mem _)

/-- Equivalently, secants between points near `p` admit approximations by tangent vectors with
arbitrarily small error relative to the length of the secant. -/
theorem iff_eventually_exists : WhitneyB s t T p ↔
    ∀ ⦃ε : ℝ⦄, 0 < ε → ∀ᶠ q : E × E in 𝓝[s] p ×ˢ 𝓝[t] p,
      ∃ v ∈ T q.1, ‖q.1 - q.2 - v‖ ≤ ε * ‖q.1 - q.2‖ := by
  rw [iff_isLittleO, isLittleO_iff]
  constructor
  · intro h ε hε
    filter_upwards [h (half_pos hε)] with q hq
    by_cases hz : q.1 - q.2 = 0
    · exact ⟨0, Submodule.zero_mem _, by simp [hz]⟩
    rw [Real.norm_of_nonneg infDist_nonneg] at hq
    have hlt := hq.trans_lt (mul_lt_mul_of_pos_right (half_lt_self hε) (norm_pos_iff.2 hz))
    obtain ⟨v, hv, hdist⟩ := (infDist_lt_iff ⟨0, Submodule.zero_mem _⟩).1 hlt
    exact ⟨v, hv, by simpa only [dist_eq_norm] using hdist.le⟩
  · intro h ε hε
    filter_upwards [h hε] with q ⟨v, hv, hq⟩
    rw [Real.norm_of_nonneg infDist_nonneg]
    exact (infDist_le_dist_of_mem hv).trans (by simpa only [dist_eq_norm] using hq)

/-- If the secants already belong to the upper tangent spaces, condition (b) holds.
This applies, for example, to relative interiors of nested affine faces. -/
theorem of_eventually_sub_mem (h : ∀ᶠ q : E × E in 𝓝[s] p ×ˢ 𝓝[t] p, q.1 - q.2 ∈ T q.1) :
    WhitneyB s t T p := by
  refine iff_eventually_exists.mpr fun ε hε ↦ ?_
  filter_upwards [h] with q hq
  exact ⟨q.1 - q.2, hq, by
    simpa only [sub_self, norm_zero] using mul_nonneg hε.le (norm_nonneg (q.1 - q.2))⟩

/-- Inside an affine subspace, the direction space satisfies (b). In particular this is the
secant criterion for relative interiors of nested faces of a simplex. -/
theorem of_subset_affineSubspace {A : AffineSubspace ℝ E} (hs : s ⊆ A) (ht : t ⊆ A) :
    WhitneyB s t (fun _ ↦ A.direction) p := by
  apply of_eventually_sub_mem
  filter_upwards [eventually_mem_nhdsWithin.prod_mk eventually_mem_nhdsWithin] with q hq
  simpa only [vsub_eq_sub] using AffineSubspace.vsub_mem_direction (hs hq.1) (ht hq.2)

/-- Restriction of the two sets preserves Whitney's condition (b). -/
theorem mono (h : WhitneyB s t T p) {s' t' : Set E} (hs : s' ⊆ s) (ht : t' ⊆ t) :
    WhitneyB s' t' T p :=
  iff_isLittleO.mpr <| (iff_isLittleO.mp h).mono <|
    prod_mono (nhdsWithin_mono p hs) (nhdsWithin_mono p ht)

/-- Only the tangent spaces at upper points near the base point affect condition (b). -/
theorem congr {U : E → Submodule ℝ E} (h : T =ᶠ[𝓝[s] p] U) :
    WhitneyB s t T p ↔ WhitneyB s t U p := by
  simp only [iff_isLittleO]
  have hdist : (fun q : E × E ↦ infDist (q.1 - q.2) (T q.1)) =ᶠ[𝓝[s] p ×ˢ 𝓝[t] p]
      (fun q ↦ infDist (q.1 - q.2) (U q.1)) :=
    (h.prod_inl (𝓝[t] p)).mono fun q hq ↦
      congrArg (fun V : Submodule ℝ E ↦ infDist (q.1 - q.2) V) hq
  exact Asymptotics.isLittleO_congr hdist EventuallyEq.rfl

-- The error after transport consists of the strict derivative remainder, the variation of
-- the derivative, and the image of the original approximation error.
private theorem eventually_exists_map (h : WhitneyB s t T p) {f : E → F}
    (hf : ContDiffAt ℝ 1 f p)
    (hlength : (fun q : E × E ↦ q.1 - q.2) =O[𝓝[s] p ×ˢ 𝓝[t] p] (fun q ↦ f q.1 - f q.2))
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ q : E × E in 𝓝[s] p ×ˢ 𝓝[t] p,
      ∃ v ∈ (T q.1).map (fderiv ℝ f q.1).toLinearMap,
        ‖f q.1 - f q.2 - v‖ ≤ ε * ‖f q.1 - f q.2‖ := by
  let l := 𝓝[s] p ×ˢ 𝓝[t] p
  have hle : l ≤ 𝓝 (p, p) := by
    rw [nhds_prod_eq]
    exact prod_mono nhdsWithin_le_nhds nhdsWithin_le_nhds
  obtain ⟨C, hC, hCbound⟩ := hlength.exists_pos
  let δ := ε / (C * (‖fderiv ℝ f p‖ + 3))
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hd := (hf.hasStrictFDerivAt_fderiv one_ne_zero).isLittleO.bound hδ |>.filter_mono hle
  have hclose : ∀ᶠ x in 𝓝 p, ‖fderiv ℝ f x - fderiv ℝ f p‖ < min δ 1 := by
    have hc : Tendsto (fderiv ℝ f) (𝓝 p) (𝓝 (fderiv ℝ f p)) :=
      hf.continuousAt_fderiv one_ne_zero
    exact (hc.eventually (ball_mem_nhds _ (lt_min hδ zero_lt_one))).mono
      fun _ hx ↦ by simpa only [mem_ball, dist_eq_norm] using hx
  filter_upwards [hCbound.bound, hd, tendsto_fst.eventually (hclose.filter_mono nhdsWithin_le_nhds),
    iff_eventually_exists.mp h hδ] with q hCq hdq hcq ⟨v, hv, hvq⟩
  let u := q.1 - q.2
  let A := fderiv ℝ f p
  let B := fderiv ℝ f q.1
  have hnorm : ‖B‖ ≤ ‖A‖ + 1 :=
    (norm_le_norm_add_norm_sub' _ _).trans <|
      add_le_add_right (hcq.le.trans (min_le_right _ _)) _
  refine ⟨B v, Submodule.mem_map_of_mem hv, ?_⟩
  have hsplit : f q.1 - f q.2 - B v = (f q.1 - f q.2 - A u) - (B - A) u + B (u - v) := by
    simp only [sub_apply, map_sub]
    abel
  rw [hsplit]
  calc
    _ ≤ δ * ‖u‖ + δ * ‖u‖ + (‖A‖ + 1) * (δ * ‖u‖) :=
      norm_add_le_of_le (norm_sub_le_of_le hdq ((B - A).le_opNorm u |>.trans <|
        mul_le_mul_of_nonneg_right (hcq.le.trans (min_le_left _ _)) (norm_nonneg _)))
        ((B.le_opNorm _).trans (mul_le_mul hnorm hvq (norm_nonneg _) (by positivity)))
    _ = (δ * (‖A‖ + 3)) * ‖u‖ := by ring
    _ ≤ (δ * (‖A‖ + 3)) * (C * ‖f q.1 - f q.2‖) :=
      mul_le_mul_of_nonneg_left hCq (by positivity)
    _ = ε * ‖f q.1 - f q.2‖ := by
      dsimp [δ, A]
      field_simp

private theorem map (h : WhitneyB s t T p) (e : OpenPartialHomeomorph E F) (hp : p ∈ e.source)
    (he : ContDiffAt ℝ 1 e p) (hi : ContDiffAt ℝ 1 e.symm (e p)) :
    WhitneyB (e '' (e.source ∩ s)) (e '' (e.source ∩ t))
      (fun z ↦ (T (e.symm z)).map (fderiv ℝ e (e.symm z)).toLinearMap) (e p) := by
  rw [iff_eventually_exists, ← e.map_nhdsWithin_eq hp, ← e.map_nhdsWithin_eq hp,
    Filter.prod_map_map_eq']
  simp only [Filter.eventually_map, Prod.map_fst, Prod.map_snd]
  let l := 𝓝[s] p ×ˢ 𝓝[t] p
  have hle : l ≤ 𝓝 p ×ˢ 𝓝 p := prod_mono nhdsWithin_le_nhds nhdsWithin_le_nhds
  have hsource : ∀ᶠ x in 𝓝 p, x ∈ e.source := e.open_source.mem_nhds hp
  have hmem : ∀ᶠ q : E × E in l, q.1 ∈ e.source ∧ q.2 ∈ e.source :=
    (hsource.prod_mk hsource).filter_mono hle
  have hambient : l ≤ 𝓝 (p, p) := by simpa only [nhds_prod_eq] using hle
  have hmap : Tendsto (Prod.map e e) l (𝓝 (e p, e p)) :=
    ((e.continuousAt hp).prodMap (e.continuousAt hp)).mono_left hambient
  have hinv := (hi.hasStrictFDerivAt_fderiv one_ne_zero).isBigO_sub.comp_tendsto hmap
  have hlength : (fun q : E × E ↦ q.1 - q.2) =O[l] (fun q ↦ e q.1 - e q.2) :=
    hinv.congr' (hmem.mono fun q hq ↦ by simp [e.left_inv, hq]) EventuallyEq.rfl
  intro ε hε
  filter_upwards [hmem, h.eventually_exists_map he hlength hε] with q hq hsecant
  simpa only [e.left_inv hq.1] using hsecant

/-- Cutting both sets down to a neighbourhood of the base point does not change (b). -/
@[simp] theorem inter_nhds_iff {U : Set E} (hU : U ∈ 𝓝 p) :
    WhitneyB (U ∩ s) (U ∩ t) T p ↔ WhitneyB s t T p := by
  simp only [iff_isLittleO, nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds hU)]

/-- Whitney's condition (b) is invariant under a local `C¹` change of coordinates. Only the
germs at `p` and `e p` matter. The image strata are cut down to the source of the coordinate
change and their tangent spaces are the images under its derivative. -/
theorem map_iff (e : OpenPartialHomeomorph E F) (hp : p ∈ e.source)
    (he : ContDiffAt ℝ 1 e p) (hi : ContDiffAt ℝ 1 e.symm (e p)) :
    WhitneyB (e '' (e.source ∩ s)) (e '' (e.source ∩ t))
      (fun z ↦ (T (e.symm z)).map (fderiv ℝ e (e.symm z)).toLinearMap) (e p) ↔
      WhitneyB s t T p := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.map e hp he hi⟩
  have hr := h.map e.symm (e.map_source hp) hi (by rwa [e.left_inv hp])
  have himage (a : Set E) : e.symm '' (e.symm.source ∩ e '' (e.source ∩ a)) = e.source ∩ a := by
    have hsub : e '' (e.source ∩ a) ⊆ e.symm.source :=
      image_subset_iff.mpr (e.mapsTo.mono_left inter_subset_left)
    rw [inter_eq_right.mpr hsub, ← image_comp]
    exact (e.leftInvOn.mono inter_subset_left).eqOn.image_eq_self
  rw [himage, himage, e.left_inv hp] at hr
  refine (inter_nhds_iff (e.open_source.mem_nhds hp)).mp ((congr ?_).mp hr)
  have hnear : ∀ᶠ x in 𝓝 p, ContDiffAt ℝ 1 e x ∧ ContDiffAt ℝ 1 e.symm (e x) ∧ x ∈ e.source :=
    (he.eventually (by simp)).and
      (((e.continuousAt hp).eventually (hi.eventually (by simp))).and (e.open_source.mem_nhds hp))
  filter_upwards [hnear.filter_mono nhdsWithin_le_nhds] with x ⟨hx, hy, hs⟩
  have hcomp := (hy.differentiableAt one_ne_zero).hasFDerivAt.comp x
    (hx.differentiableAt one_ne_zero).hasFDerivAt
  have hinv : (e.symm : F → E) ∘ (e : E → F) =ᶠ[𝓝 x] id := e.eventually_left_inverse hs
  have hid := (hcomp.congr_of_eventuallyEq hinv.symm).fderiv
  rw [fderiv_id] at hid
  rw [OpenPartialHomeomorph.symm_symm, e.left_inv hs, ← Submodule.map_comp,
    ← ContinuousLinearMap.toLinearMap_comp, ← hid, ContinuousLinearMap.coe_id, Submodule.map_id]

end WhitneyB

end TauCeti
