/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Corners.Depth

/-!
# The local faces of a manifold with corners do not depend on the chart

Near a point `y` of the region `R = {z | ∀ i ∈ S, 0 ≤ z i}` of `EuclideanSpace ℝ ι`, the boundary
of `R` is the union of the *local faces* `{z ∈ R | z i = 0}` for the indices `i ∈ S` with
`y i = 0`; there are `ModelWithCorners.depthAt` of them
(`ModelWithCorners.depthAt_eq_natCard_of_range_eq`). The quadrant model `𝓡c n` (with `S` all of
`Fin n`) and the half-space model `𝓡∂ n` (with `S = {0}`) have ranges of this form. On a manifold
with corners modelled on such a region, a chart therefore presents the faces through a point `x`
as the coordinate hyperplanes through its image. These are the faces along which manifolds with
corners are cut and glued, and the points of the abstract boundary of a manifold with corners are
the pairs of a point and a local face through it.

This file proves that this presentation is intrinsic: two charts at `x` give the same faces, up to
a unique relabelling. Precisely, for charts `e` and `e'` of the maximal atlas at `x` there is a
unique bijection `σ` from the vanishing coordinates of `e.extend J x` to those of `e'.extend J x`
such that, for every point `p` near `x`, `e.extend J p i = 0` exactly when
`e'.extend J p (σ i) = 0` (`ModelWithCorners.existsUnique_equiv_extend_apply_eq_zero_iff`).

The chart independence is deduced from a statement about maps between such regions
(`ModelWithCorners.existsUnique_equiv_apply_eq_zero_iff_of_depthAt_eq`): a homeomorphism between
neighbourhoods of `y` in `R` and of `φ y` in a second such region `R'` which preserves the depth
carries each local face at `y` onto a local face at `φ y`. Chart transitions preserve the depth
(`ModelWithCorners.depthAt_extend_eq_depth`), which is where the differentiability of the charts
enters. Distinct faces through a point stay distinct near it
(`ModelWithCorners.eq_of_eventually_apply_eq_zero_imp`), which makes the matching unique.

## Main results

* `ModelWithCorners.eq_of_eventually_apply_eq_zero_imp`: if near `y` the face `z i = 0` lies in the
  face `z k = 0`, then `i = k`.
* `ModelWithCorners.existsUnique_equiv_apply_eq_zero_iff_of_depthAt_eq`: a depth-preserving local
  homeomorphism of regions of the form `{z | ∀ i ∈ S, 0 ≤ z i}` matches their local faces.
* `ModelWithCorners.existsUnique_equiv_extend_apply_eq_zero_iff`: on a `C¹` manifold modelled on
  such a region, two charts at a point present the same local faces through it.

## Implementation notes

The points of depth one near `y` on the face `z i = 0` form a convex, hence connected, set, which
a depth-preserving map `φ` carries into the points of depth one near `φ y`. Those split into
finitely many relatively open pieces, one on each face at `φ y`, so the image lies on a single
face, and so does its closure, which is the face near `y`. Applying this to the inverse map gives
the inverse bijection.

## References

* D. Joyce, *On manifolds with corners*, in *Advances in Geometric Analysis*, Adv. Lect. Math. 21,
  International Press (2012), 225–258, Section 2 (local boundary components, and their number at
  a point being its depth). [arXiv:0910.3518](https://arxiv.org/abs/0910.3518)
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer (2013), Chapter 16, section *Manifolds with Corners*.
-/

public section

open Set Filter Function
open scoped Manifold Topology

namespace ModelWithCorners

variable {ι ι' : Type*} {S : Set ι} {S' : Set ι'}

section Coordinates

/-- The path `t ↦ z + t • v` tends to `z` as `t` decreases to `0`. -/
private theorem tendsto_add_smul [Finite ι] (z v : EuclideanSpace ℝ ι) :
    Tendsto (fun t : ℝ ↦ z + t • v) (𝓝[>] 0) (𝓝 z) := by
  have := Fintype.ofFinite ι
  have h : Continuous fun t : ℝ ↦ z + t • v := by fun_prop
  simpa using (h.tendsto 0).mono_left nhdsWithin_le_nhds

/-- **Distinct local faces through a point are distinct near it.** If `y` lies on the faces
`z i = 0` and `z k = 0` of the region `{z | ∀ i ∈ S, 0 ≤ z i}`, and near `y` every point of the
region on the first face lies on the second, then `i = k`. -/
theorem eq_of_eventually_apply_eq_zero_imp [Finite ι] {y : EuclideanSpace ℝ ι}
    (hy : ∀ i ∈ S, 0 ≤ y i) {i k : ι} (hi : y i = 0) (hk : y k = 0)
    (h : ∀ᶠ z in 𝓝[{z | ∀ i ∈ S, 0 ≤ z i}] y, z i = 0 → z k = 0) : i = k := by
  classical
  by_contra hik
  -- Move off `y` in the direction of the `k`-th coordinate: this stays on the face `z i = 0`.
  set v : EuclideanSpace ℝ ι := WithLp.toLp 2 fun j ↦ if j = k then 1 else 0
  have hT : Tendsto (fun t : ℝ ↦ y + t • v) (𝓝[>] 0) (𝓝[{z | ∀ i ∈ S, 0 ≤ z i}] y) := by
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_add_smul y v, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t) j hj
    have := hy j hj
    simp only [v, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    split_ifs <;> nlinarith
  obtain ⟨t, ht, ht0⟩ := ((hT.eventually h).and self_mem_nhdsWithin).exists
  have ht0 : (0 : ℝ) < t := ht0
  -- On the path the `i`-th coordinate stays `0`, while the `k`-th one is `t`.
  have hpath (j : ι) : (y + t • v) j = y j + if j = k then t else 0 := by
    simp only [v, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    split_ifs <;> ring
  have := ht (by simp only [hpath, hi, hik, ↓reduceIte, add_zero])
  simp only [hpath, hk, ↓reduceIte, zero_add] at this
  exact ht0.ne' this

/-- Near a point of `{z | ∀ j ∈ T, 0 ≤ z j}`, the coordinates in `T` positive at the point stay
positive. -/
private theorem eventually_forall_pos {κ : Type*} [Finite κ] {T : Set κ}
    {w : EuclideanSpace ℝ κ} (hw : ∀ j ∈ T, 0 ≤ w j) :
    ∀ᶠ w' in 𝓝 w, ∀ j ∈ T, w j ≠ 0 → 0 < w' j := by
  refine eventually_all.2 fun j ↦ ?_
  by_cases hj : j ∈ T ∧ w j ≠ 0
  · have hcj : Continuous fun w' : EuclideanSpace ℝ κ ↦ w' j := by fun_prop
    filter_upwards [hcj.continuousAt.eventually (lt_mem_nhds
      (lt_of_le_of_ne (hw j hj.1) (Ne.symm hj.2)))] with w' hw' _ _
    exact hw'
  · exact Eventually.of_forall fun w' hjT hj' ↦ absurd ⟨hjT, hj'⟩ hj

/-- A depth-preserving map carries a local face into a local face. Let `φ` be continuous on a
neighbourhood `s` of `y` in `R = {z | ∀ i ∈ S, 0 ≤ z i}`, with values in
`R' = {w | ∀ j ∈ S', 0 ≤ w j}`, preserving the number of vanishing coordinates. Then for each face
`z i = 0` through `y` there is a face `w j = 0` through `φ y` into which `φ` carries the first one
near `y`. -/
private theorem exists_eventually_apply_eq_zero_of_apply_eq_zero [Finite ι] [Finite ι']
    {φ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι'} {y : EuclideanSpace ℝ ι}
    (hy : ∀ i ∈ S, 0 ≤ y i) {s : Set (EuclideanSpace ℝ ι)}
    (hs : s ∈ 𝓝[{z | ∀ i ∈ S, 0 ≤ z i}] y) (hφ : ContinuousOn φ s)
    (hφs : ∀ z ∈ s, ∀ j ∈ S', 0 ≤ φ z j)
    (hφd : ∀ z ∈ s, Nat.card {j // j ∈ S' ∧ φ z j = 0} = Nat.card {k // k ∈ S ∧ z k = 0})
    {i : ι} (hiS : i ∈ S) (hi : y i = 0) :
    ∃ j ∈ S', φ y j = 0 ∧ ∀ᶠ z in 𝓝[{z | ∀ i ∈ S, 0 ≤ z i}] y, z i = 0 → φ z j = 0 := by
  classical
  have := Fintype.ofFinite ι
  set R : Set (EuclideanSpace ℝ ι) := {z | ∀ i ∈ S, 0 ≤ z i}
  have hys : y ∈ s := mem_of_mem_nhdsWithin hy hs
  have hcont : Tendsto φ (𝓝[R] y) (𝓝 (φ y)) := (hφ y hys).mono_of_mem_nhdsWithin hs
  -- Shrink to a ball on which the coordinates positive at `y`, and at `φ y`, stay positive.
  obtain ⟨ε, hε, hεG⟩ := Metric.mem_nhdsWithin_iff.1 <| inter_mem hs <|
    inter_mem (mem_nhdsWithin_of_mem_nhds (eventually_forall_pos hy))
      (hcont.eventually (eventually_forall_pos (hφs y hys)))
  -- The points of depth one near `y` on the face `z i = 0`, and the direction leading into them.
  set A : Set (EuclideanSpace ℝ ι) :=
    {z | z ∈ Metric.ball y ε ∧ z i = 0 ∧ ∀ k ∈ S, k ≠ i → 0 < z k}
  set v : EuclideanSpace ℝ ι := WithLp.toLp 2 fun k ↦ if k = i then 0 else 1
  have hAR : A ⊆ R := fun z hz k hk ↦ by
    by_cases hki : k = i
    · rw [hki, hz.2.1]
    · exact (hz.2.2 k hk hki).le
  have hAG : A ⊆ s ∩ ({z | ∀ k ∈ S, y k ≠ 0 → 0 < z k} ∩
      φ ⁻¹' {w | ∀ j ∈ S', φ y j ≠ 0 → 0 < w j}) := fun z hz ↦ hεG ⟨hz.1, hAR hz⟩
  have hin {z : EuclideanSpace ℝ ι} (hz : z ∈ Metric.ball y ε) (hzR : z ∈ R) (hzi : z i = 0) :
      ∀ᶠ t : ℝ in 𝓝[>] 0, z + t • v ∈ A := by
    filter_upwards [(tendsto_add_smul z v).eventually (Metric.isOpen_ball.mem_nhds hz),
      self_mem_nhdsWithin] with t ht (ht0 : 0 < t)
    refine ⟨ht, by simp [v, hzi], fun k hk hki ↦ ?_⟩
    have := hzR k hk
    simp only [v, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hki, ↓reduceIte]
    linarith
  -- Each point of `A` has exactly one vanishing coordinate in `S`, so its image has exactly one
  -- in `S'`, and it vanishes at `φ y` too.
  have hone {z : EuclideanSpace ℝ ι} (hz : z ∈ A) :
      ∃ j ∈ S', φ y j = 0 ∧ φ z j = 0 ∧ ∀ k ∈ S', φ z k = 0 → k = j := by
    have hcard : Nat.card {k // k ∈ S ∧ z k = 0} = 1 :=
      Nat.card_eq_one_iff_exists.2 ⟨⟨i, hiS, hz.2.1⟩, fun ⟨k, hkS, hk⟩ ↦ Subtype.ext <| by
        by_contra hki
        exact (hz.2.2 k hkS hki).ne' hk⟩
    obtain ⟨⟨j, hjS, hj⟩, huniq⟩ :=
      Nat.card_eq_one_iff_exists.1 ((hφd z (hAG hz).1).trans hcard)
    refine ⟨j, hjS, ?_, hj, fun k hkS hk ↦ congrArg Subtype.val (huniq ⟨k, hkS, hk⟩)⟩
    by_contra hj'
    exact ((hAG hz).2.2 j hjS hj').ne' hj
  obtain ⟨t₀, ht₀⟩ := (hin (Metric.mem_ball_self hε) hy hi).exists
  obtain ⟨j₀, hj₀S, hj₀y, hj₀, -⟩ := hone ht₀
  -- `φ '' A` is connected and covered by two relatively disjoint open sets: the points whose
  -- `j₀`-th coordinate is nonzero, and those whose other coordinates in `S'` are nonzero.
  have hA : IsPreconnected (φ '' A) := by
    refine (Convex.isPreconnected ?_).image φ (hφ.mono fun z hz ↦ (hAG hz).1)
    rintro z ⟨hz, hzi, hzS⟩ z' ⟨hz', hz'i, hz'S⟩ a b ha hb hab
    refine ⟨convex_ball y ε hz hz' ha hb hab, by simp [hzi, hz'i], fun k hk hki ↦ ?_⟩
    have h₁ := hzS k hk hki
    have h₂ := hz'S k hk hki
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rcases ha.eq_or_lt with rfl | ha'
    · nlinarith [mul_pos (show (0 : ℝ) < b by linarith) h₂]
    · nlinarith [mul_pos ha' h₁, mul_nonneg hb h₂.le]
  have hcoord (j : ι') : Continuous fun w : EuclideanSpace ℝ ι' ↦ w j := by fun_prop
  have hu : IsOpen {w : EuclideanSpace ℝ ι' | w j₀ ≠ 0} :=
    isOpen_ne_fun (hcoord j₀) continuous_const
  have hv : IsOpen (⋂ k ∈ {k | k ∈ S' ∧ k ≠ j₀}, {w : EuclideanSpace ℝ ι' | w k ≠ 0}) :=
    (toFinite _).isOpen_biInter fun k _ ↦ isOpen_ne_fun (hcoord k) continuous_const
  have hcover : φ '' A ⊆ {w | w j₀ ≠ 0} ∪
      ⋂ k ∈ {k | k ∈ S' ∧ k ≠ j₀}, {w : EuclideanSpace ℝ ι' | w k ≠ 0} := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨j, -, -, hj, huniq⟩ := hone hz
    by_cases hjj : j = j₀
    · exact .inr <| mem_iInter₂.2 fun k hk hk0 ↦ hk.2 ((huniq k hk.1 hk0).trans hjj)
    · exact .inl fun h0 ↦ hjj (huniq j₀ hj₀S h0).symm
  have hdisj : φ '' A ∩ ({w | w j₀ ≠ 0} ∩
      ⋂ k ∈ {k | k ∈ S' ∧ k ≠ j₀}, {w : EuclideanSpace ℝ ι' | w k ≠ 0}) = ∅ := by
    refine eq_empty_iff_forall_notMem.2 ?_
    rintro _ ⟨⟨z, hz, rfl⟩, hu, hv⟩
    obtain ⟨j, hjS, -, hj, -⟩ := hone hz
    by_cases hjj : j = j₀
    · exact hu (hjj ▸ hj)
    · exact mem_iInter₂.1 hv j ⟨hjS, hjj⟩ hj
  have hA0 : ∀ z ∈ A, φ z j₀ = 0 := by
    rcases isPreconnected_iff_subset_of_disjoint.1 hA _ _ hu hv hcover hdisj with hsub | hsub
    · exact absurd hj₀ (hsub ⟨_, ht₀, rfl⟩)
    · intro z hz
      obtain ⟨j, hjS, -, hj, -⟩ := hone hz
      by_cases hjj : j = j₀
      · exact hjj ▸ hj
      · exact absurd hj (mem_iInter₂.1 (hsub ⟨z, hz, rfl⟩) j ⟨hjS, hjj⟩)
  -- Every point of the face near `y` is a limit of points of `A`, so `φ` carries it to the face.
  refine ⟨j₀, hj₀S, hj₀y, ?_⟩
  filter_upwards [inter_mem_nhdsWithin R (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε)),
    self_mem_nhdsWithin] with z ⟨hzR, hz⟩ _ hzi
  have hzs : z ∈ s := (hεG ⟨hz, hzR⟩).1
  have hT : Tendsto (fun t : ℝ ↦ z + t • v) (𝓝[>] 0) (𝓝[s] z) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_add_smul z v,
      (hin hz hzR hzi).mono fun _ ht ↦ (hAG ht).1⟩
  exact (isClosed_eq (hcoord j₀) continuous_const).mem_of_tendsto ((hφ z hzs).tendsto.comp hT)
    ((hin hz hzR hzi).mono fun _ ht ↦ hA0 _ ht)

variable [Fintype ι] [Fintype ι'] {H : Type*} [TopologicalSpace H]
  {J : ModelWithCorners ℝ (EuclideanSpace ℝ ι) H} {H' : Type*} [TopologicalSpace H']
  {J' : ModelWithCorners ℝ (EuclideanSpace ℝ ι') H'}

/-- **A depth-preserving local homeomorphism matches the local faces.** Let `J` and `J'` be models
with corners whose ranges are cut out by the nonnegativity of the coordinates indexed by `S` and
`S'`. Let `φ` and `ψ` be mutually inverse continuous maps between neighbourhoods `s` of `y` in
`range J` and `t` of `φ y` in `range J'`, with `φ` preserving the depth. Then there is a unique
bijection `σ` from the coordinates in `S` vanishing at `y` to those in `S'` vanishing at `φ y` such
that, near `y`, a point lies on the face `z i = 0` exactly when its image lies on the face
`w (σ i) = 0`. -/
theorem existsUnique_equiv_apply_eq_zero_iff_of_depthAt_eq
    (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}) (hJ' : range J' = {w | ∀ j ∈ S', 0 ≤ w j})
    {φ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι'} {ψ : EuclideanSpace ℝ ι' → EuclideanSpace ℝ ι}
    {y : EuclideanSpace ℝ ι} (hy : y ∈ range J) {s : Set (EuclideanSpace ℝ ι)}
    {t : Set (EuclideanSpace ℝ ι')} (hs : s ∈ 𝓝[range J] y) (ht : t ∈ 𝓝[range J'] (φ y))
    (hφ : ContinuousOn φ s) (hψ : ContinuousOn ψ t) (hφs : MapsTo φ s (range J'))
    (hψt : MapsTo ψ t (range J)) (hψφ : LeftInvOn ψ φ s) (hφψ : LeftInvOn φ ψ t)
    (hd : ∀ z ∈ s, z ∈ range J → J'.depthAt (φ z) = J.depthAt z) :
    ∃! σ : {i // i ∈ S ∧ y i = 0} ≃ {j // j ∈ S' ∧ φ y j = 0},
      ∀ᶠ z in 𝓝[range J] y, ∀ i, φ z (σ i) = 0 ↔ z i = 0 := by
  classical
  -- The depth is the number of vanishing coordinates.
  have hcard {z} (hzs : z ∈ s) (hz : z ∈ range J) :
      Nat.card {j // j ∈ S' ∧ φ z j = 0} = Nat.card {k // k ∈ S ∧ z k = 0} := by
    rw [← depthAt_eq_natCard_of_range_eq hJ' (hφs hzs), hd z hzs hz,
      depthAt_eq_natCard_of_range_eq hJ hz]
  rw [hJ] at hy hs hψt hcard ⊢
  rw [hJ'] at ht hφs
  set R : Set (EuclideanSpace ℝ ι) := {z | ∀ i ∈ S, 0 ≤ z i}
  set R' : Set (EuclideanSpace ℝ ι') := {w | ∀ j ∈ S', 0 ≤ w j}
  have hys : y ∈ s := mem_of_mem_nhdsWithin hy hs
  have hψy : ψ (φ y) = y := hψφ hys
  have hφy : φ y ∈ R' := hφs hys
  -- `φ` and `ψ` map the neighbourhoods of the two points within the regions to each other.
  have hTφ : Tendsto φ (𝓝[R] y) (𝓝[R'] (φ y)) :=
    tendsto_nhdsWithin_iff.2 ⟨(hφ y hys).mono_of_mem_nhdsWithin hs, eventually_of_mem hs hφs⟩
  have hTψ : Tendsto ψ (𝓝[R'] (φ y)) (𝓝[R] y) := by
    have h := (hψ _ (mem_of_mem_nhdsWithin hφy ht)).mono_of_mem_nhdsWithin ht
    rw [ContinuousWithinAt, hψy] at h
    exact tendsto_nhdsWithin_iff.2 ⟨h, eventually_of_mem ht hψt⟩
  -- Both maps preserve the number of vanishing coordinates, on suitable neighbourhoods.
  have hs₀ : s ∩ R ∈ 𝓝[R] y := inter_mem hs self_mem_nhdsWithin
  have ht₀ : t ∩ R' ∩ ψ ⁻¹' (s ∩ R) ∈ 𝓝[R'] (φ y) :=
    inter_mem (inter_mem ht self_mem_nhdsWithin) (hTψ hs₀)
  have hcard' {w} (hw : w ∈ t ∩ R' ∩ ψ ⁻¹' (s ∩ R)) :
      Nat.card {k // k ∈ S ∧ ψ w k = 0} = Nat.card {j // j ∈ S' ∧ w j = 0} := by
    rw [← hcard hw.2.1 hw.2.2, hφψ hw.1.1]
  -- Each face at `y` goes into a face at `φ y`, and back.
  have hσ (i : {i // i ∈ S ∧ y i = 0}) :=
    exists_eventually_apply_eq_zero_of_apply_eq_zero hy hs₀ (hφ.mono inter_subset_left)
      (fun z hz ↦ hφs hz.1) (fun z hz ↦ hcard hz.1 hz.2) i.2.1 i.2.2
  have hτ (j : {j // j ∈ S' ∧ φ y j = 0}) :=
    exists_eventually_apply_eq_zero_of_apply_eq_zero hφy ht₀
      (hψ.mono fun _ hw ↦ hw.1.1) (fun w hw ↦ hψt hw.1.1) (fun w hw ↦ hcard' hw) j.2.1 j.2.2
  choose σ hσS hσy hσ using hσ
  choose τ hτS hτy hτ using hτ
  rw [hψy] at hτy
  -- Going to `φ y` and back returns to the face one started from.
  have hback (i : {i // i ∈ S ∧ y i = 0}) :
      ∀ᶠ z in 𝓝[R] y, φ z (σ i) = 0 → z (τ ⟨σ i, hσS i, hσy i⟩) = 0 := by
    filter_upwards [hTφ.eventually (hτ ⟨σ i, hσS i, hσy i⟩), hs] with z hz hzs h
    rw [← hψφ hzs]
    exact hz h
  have hforth (j : {j // j ∈ S' ∧ φ y j = 0}) :
      ∀ᶠ w in 𝓝[R'] (φ y), ψ w (τ j) = 0 → w (σ ⟨τ j, hτS j, hτy j⟩) = 0 := by
    filter_upwards [hTψ.eventually (hσ ⟨τ j, hτS j, hτy j⟩), ht] with w hw hwt h
    rw [← hφψ hwt]
    exact hw h
  have hστ (i : {i // i ∈ S ∧ y i = 0}) : τ ⟨σ i, hσS i, hσy i⟩ = i :=
    (eq_of_eventually_apply_eq_zero_imp hy i.2.2 (hτy _) <| by
      filter_upwards [hσ i, hback i] with z h₁ h₂ h
      exact h₂ (h₁ h)).symm
  have hτσ (j : {j // j ∈ S' ∧ φ y j = 0}) : σ ⟨τ j, hτS j, hτy j⟩ = j :=
    (eq_of_eventually_apply_eq_zero_imp hφy j.2.2 (hσy _) <| by
      filter_upwards [hτ j, hforth j] with w h₁ h₂ h
      exact h₂ (h₁ h)).symm
  let e : {i // i ∈ S ∧ y i = 0} ≃ {j // j ∈ S' ∧ φ y j = 0} :=
    { toFun := fun i ↦ ⟨σ i, hσS i, hσy i⟩
      invFun := fun j ↦ ⟨τ j, hτS j, hτy j⟩
      left_inv := fun i ↦ Subtype.ext (hστ i)
      right_inv := fun j ↦ Subtype.ext (hτσ j) }
  have hiff (i : {i // i ∈ S ∧ y i = 0}) : ∀ᶠ z in 𝓝[R] y, φ z (σ i) = 0 ↔ z i = 0 := by
    filter_upwards [hσ i, hback i] with z h₁ h₂
    exact ⟨fun h ↦ hστ i ▸ h₂ h, h₁⟩
  refine ⟨e, eventually_all.2 hiff, fun e' he' ↦ Equiv.ext fun i ↦ Subtype.ext ?_⟩
  -- Two such bijections agree: pull both characterizations back along `ψ`.
  refine eq_of_eventually_apply_eq_zero_imp hφy (e' i).2.2 (hσy i) ?_
  filter_upwards [hTψ.eventually he', hTψ.eventually (hiff i), ht] with w h₁ h₂ hwt h
  rw [hφψ hwt] at h₁ h₂
  exact h₂.2 ((h₁ i).1 h)

end Coordinates

section Manifold

variable [Fintype ι] {H : Type*} [TopologicalSpace H]
  {J : ModelWithCorners ℝ (EuclideanSpace ℝ ι) H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] {n : WithTop ℕ∞} [IsManifold J n M]

/-- **The local faces of a manifold with corners do not depend on the chart.** On a `C¹`
manifold modelled on a region `{z | ∀ i ∈ S, 0 ≤ z i}`, let `e` and `e'` be charts of the maximal
atlas at `x`. There is a unique bijection `σ` from the coordinates in `S` vanishing at
`e.extend J x` to those vanishing at `e'.extend J x` such that, for every point `p` near `x`,
`e.extend J p i = 0` exactly when `e'.extend J p (σ i) = 0`: the two charts present the same local
faces through `x`. -/
theorem existsUnique_equiv_extend_apply_eq_zero_iff (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i})
    (hn : n ≠ 0) {e e' : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas J n M)
    (he' : e' ∈ IsManifold.maximalAtlas J n M) {x : M} (hx : x ∈ e.source)
    (hx' : x ∈ e'.source) :
    ∃! σ : {i // i ∈ S ∧ e.extend J x i = 0} ≃ {i // i ∈ S ∧ e'.extend J x i = 0},
      ∀ᶠ p in 𝓝 x, ∀ i, e'.extend J p (σ i) = 0 ↔ e.extend J p i = 0 := by
  set φ := J.extendCoordChange e e'
  have hφ {p : M} (hp : p ∈ e.source) : φ (e.extend J p) = e'.extend J p := by
    simp [φ, e.left_inv hp]
  have hmaps {f f' : OpenPartialHomeomorph M H} :
      MapsTo (J.extendCoordChange f f') (J.extendCoordChange f f').source (range J) :=
    (J.extendCoordChange f f').mapsTo.mono_right fun _ hz ↦ f'.extend_target_subset_range hz.1
  have h := existsUnique_equiv_apply_eq_zero_iff_of_depthAt_eq hJ hJ (φ := φ) (ψ := φ.symm)
    (by rw [e.extend_coe]; exact mem_range_self _)
    (J.extendCoordChange_source_mem_nhdsWithin' hx hx')
    (hφ hx ▸ J.extendCoordChange_source_mem_nhdsWithin' hx' hx)
    (J.contDiffOn_extendCoordChange he he').continuousOn
    (J.contDiffOn_extendCoordChange he' he).continuousOn hmaps hmaps φ.leftInvOn φ.rightInvOn ?_
  · rw [hφ hx] at h
    refine (existsUnique_congr fun σ ↦ ?_).1 h
    -- Transport the eventual statement from the model space to `M` along the chart `e`.
    rw [← e.map_extend_nhds hx, eventually_map]
    refine eventually_congr ?_
    filter_upwards [e.open_source.mem_nhds hx] with p hp
    rw [hφ hp]
  · rintro z hz -
    rw [← e.extend_image_source_inter] at hz
    obtain ⟨p, ⟨hp, hp'⟩, rfl⟩ := hz
    rw [hφ hp, depthAt_extend_eq_depth hn he' hp', depthAt_extend_eq_depth hn he hp]

end Manifold

end ModelWithCorners
