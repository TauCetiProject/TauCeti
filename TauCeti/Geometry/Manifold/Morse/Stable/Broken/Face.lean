/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Stable.Broken.TrajectorySpace
import TauCeti.Geometry.Manifold.Morse.Gluing.Compactification
import TauCeti.Geometry.Manifold.Morse.Stable.Stratum
import TauCeti.Topology.Order.OrderClosed

/-!
# The faces of the spaces of broken trajectories

Let `f` be a Morse function on a compact boundaryless manifold `M`, with an adapted
pseudo-gradient `X`, and record broken trajectories on the levels of a family `c` that avoids the
critical values of `f` and is dense between any two of them. The trajectory space `L(x, y)` from a
critical point `x` to a critical point `y`
(`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySpace`) has the boundary `∂L(x, y)` of
the broken trajectories that are not unbroken, and concatenation at a critical point `z` gives
the composition maps `L(x, z) × L(z, y) → L(x, y)`
(`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySpaceComp`). This file shows that the
boundary is assembled from faces, the images of these maps, in the way that representing chain
systems of fundamental classes require
(`TauCeti.TwistingChainSystem.exists_isRepresenting_of_subsingleton_units`).

* Every point of `∂L(x, y)` is the concatenation, at its first break `z`, of an unbroken
  trajectory and a broken one
  (`IsAdaptedPseudoGradient.exists_morseBrokenTrajectorySpaceComp_eq_of_mem_boundary`), so
  `∂L(x, y)` is the union of the faces
  (`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySpaceBoundary_eq_iUnion`).
* Concatenation at `z` is an embedding
  (`TauCeti.IsAdaptedPseudoGradient.isEmbedding_morseBrokenTrajectorySpaceComp`): restricting a
  record to the levels above and below `f z` recovers its two factors.
* The *interior* of the face at `z`, made of the concatenations of two unbroken trajectories, meets
  no face of another critical point
  (`TauCeti.IsAdaptedPseudoGradient.disjoint_range_morseBrokenTrajectorySpaceComp_image`): on a
  level just above `f z'`, a broken trajectory to `z'` lies in the stable manifold of `z'`. It is
  exactly the part of the boundary outside these other faces
  (`TauCeti.IsAdaptedPseudoGradient.image_morseBrokenTrajectorySpaceComp_compl_prod_compl`).

Under the Morse–Smale condition and on countably many levels:

* the Morse index drops from `x` to `y` whenever `L(x, y)` is nonempty
  (`IsMorseSmale.manifoldMorseIndex_lt_of_mem_morseBrokenTrajectorySpace`);
* the trajectory spaces are compact (`IsMorseSmale.isCompact_morseBrokenTrajectorySpace`), so the
  faces are closed (`IsMorseSmale.isClosed_range_morseBrokenTrajectorySpaceComp`), and so is the
  boundary, a union of finitely many faces
  (`IsMorseSmale.isClosed_morseBrokenTrajectorySpaceBoundary`): the unbroken trajectories form an
  open subset of the trajectory space;
* concatenation at `z` is an open embedding of the product of the spaces of unbroken trajectories
  into the boundary
  (`IsMorseSmale.isOpenEmbedding_morseBrokenTrajectorySpaceComp_compl_prod_compl`);
* the interiors of the faces are dense in the boundary
  (`IsMorseSmale.dense_morseBrokenTrajectorySpaceComp_image`), since a broken trajectory is a limit
  of unbroken ones (`IsMorseSmale.morseBrokenTrajectoryRecords_subset_closure`).

With the unbroken trajectories as the interiors `N x y`, these are the hypotheses `hj`, `hιj`,
`hU` and `hUι` of `TauCeti.TwistingChainSystem.exists_isRepresenting_of_subsingleton_units` for
the trajectory spaces, and `hUA` follows from the injectivity of concatenation. Of its other
hypotheses, the manifold structure and the collar of the boundary near the deeper strata come from
the gluing of broken trajectories and are not proved here.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `exists_morseBrokenTrajectorySpaceComp_eq_of_mem_boundary`: the first break of a broken
  trajectory.
* `morseBrokenTrajectorySpaceBoundary_eq_iUnion`: the boundary is the union of the faces.
* `isEmbedding_morseBrokenTrajectorySpaceComp`: concatenation is an embedding.
* `disjoint_range_morseBrokenTrajectorySpaceComp_image`,
  `image_morseBrokenTrajectorySpaceComp_compl_prod_compl`: the interior of a face.
* `IsMorseSmale.isCompact_morseBrokenTrajectorySpace`: the trajectory spaces are compact.
* `IsMorseSmale.isClosed_morseBrokenTrajectorySpaceBoundary`: the boundary is closed.
* `IsMorseSmale.isOpenEmbedding_morseBrokenTrajectorySpaceComp_compl_prod_compl`: the interiors
  of the faces are open in the boundary.
* `IsMorseSmale.dense_morseBrokenTrajectorySpaceComp_image`: they are dense in it.

## References

* J.-F. Barraud, O. Cornea, *Lagrangian intersections and the Serre spectral sequence*, Ann. of
  Math. (2) 166 (2007), 657–722, §2 and Appendix A.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 5.
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3 (spaces of broken trajectories).
-/

public section

open Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {ι : Type*}

namespace IsAdaptedPseudoGradient

variable (hX : IsAdaptedPseudoGradient f X) {c : ι → ℝ}
  (hc : ∀ i (x : criticalPoints 𝓘(ℝ, E) f), c i ≠ f x)

/-! ### The first break of a broken trajectory -/

/-- The part of a record of a broken trajectory through `xs 0, xs 1, …, xs (k + 2)` on the levels
below `f (xs 1)` records the broken trajectory through `xs 1, …, xs (k + 2)`. -/
private theorem mem_morseBrokenTrajectoryRecords_tail {x y : M} {k : ℕ}
    {xs : Fin (k + 3) → M} {zs : Fin (k + 2) → M} {w : c ⁻¹' Ioo (f y) (f x) → M}
    (hxk : xs (Fin.last (k + 2)) = y) (hxc : ∀ j, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f (xs j) = 0)
    (hxne : ∀ j : Fin (k + 2), xs j.castSucc ≠ xs j.succ)
    (hzs : ∀ j : Fin (k + 2),
      zs j ∈ hX.flow.unstableSet (xs j.castSucc) ∩ hX.flow.stableSet (xs j.succ))
    (hrec : ∀ i, f (w i) = c i ∧ ∃ j t, hX.flow t (zs j) = w i) (hzx : f (xs 1) < f x) :
    (fun i : c ⁻¹' Ioo (f y) (f (xs 1)) ↦ w ⟨i, i.property.1, i.property.2.trans hzx⟩) ∈
      hX.morseBrokenTrajectoryRecords (xs 1) y ((c ⁻¹' Ioo (f y) (f (xs 1))).domRestrict c) := by
  refine hX.mem_morseBrokenTrajectoryRecords.2 ⟨k + 1, fun j ↦ xs j.succ, fun j ↦ zs j.succ,
    rfl, by simpa using hxk, fun j ↦ hxc _, fun j ↦ by simpa using hxne j.succ,
    fun j ↦ by simpa using hzs j.succ, fun i ↦ ⟨(hrec _).1, ?_⟩⟩
  obtain ⟨hwc, j, t, ht⟩ := hrec ⟨i, i.property.1, i.property.2.trans hzx⟩
  induction j using Fin.cases with
  | zero =>
    -- The first component lies above the level of `xs 1`.
    have h := hX.mem_Icc_of_mem_unstableSet_inter_stableSet
      (hX.flow.isInvariant_unstableSet_inter_stableSet _ _ t (hzs 0))
    rw [ht, hwc] at h
    exact absurd h.1 (not_le.2 (by simpa using i.property.2))
  | succ j => exact ⟨j, t, ht⟩

include hc in
/-- **A broken trajectory breaks first at a critical point.** A point of the boundary of the
trajectory space from `x` to `y` is the concatenation, at some critical point `z`, of an unbroken
trajectory from `x` to `z` and a broken trajectory from `z` to `y`: the point `z` is the end of the
first component. -/
theorem exists_morseBrokenTrajectorySpaceComp_eq_of_mem_boundary
    {x y : criticalPoints 𝓘(ℝ, E) f} {w : hX.morseBrokenTrajectorySpace c x y}
    (hw : w ∈ hX.morseBrokenTrajectorySpaceBoundary c x y) :
    ∃ (z : criticalPoints 𝓘(ℝ, E) f) (a : hX.morseBrokenTrajectorySpace c x z)
      (b : hX.morseBrokenTrajectorySpace c z y),
      a ∉ hX.morseBrokenTrajectorySpaceBoundary c x z ∧
        hX.morseBrokenTrajectorySpaceComp hc x z y (a, b) = w := by
  obtain ⟨hxy, hw'⟩ := mem_morseBrokenTrajectorySpace.1 w.property
  obtain ⟨k, xs, zs, hx0, hxk, hxc, hxne, hzs, hrec⟩ :=
    hX.mem_morseBrokenTrajectoryRecords.1 hw'
  obtain _ | _ | k := k
  · -- A broken trajectory with no component joins a point to itself.
    exact absurd (hx0.symm.trans hxk) hxy
  · -- A broken trajectory with one component is unbroken.
    refine absurd (hX.mem_morseTrajectoryRecords.2 ⟨zs 0, ?_, fun i ↦ ⟨(hrec i).1, ?_⟩⟩)
      (mem_morseBrokenTrajectorySpaceBoundary.1 hw)
    · simpa [← hx0, ← hxk] using hzs 0
    · obtain ⟨-, j, t, ht⟩ := hrec i
      exact ⟨t, Fin.fin_one_eq_zero j ▸ ht⟩
  -- The first component runs from `x` to `z = xs 1`, the others from `z` to `y`.
  have hanti := hX.strictAnti_apply_of_chain hxne hzs
  have hzx : f (xs 1) < f x := hx0 ▸ hanti (by simp)
  have hyz : f y < f (xs 1) := hxk ▸ hanti (by simp [Fin.lt_def])
  have hzcrit : xs 1 ∈ criticalPoints 𝓘(ℝ, E) f :=
    mem_criticalPoints_iff_mfderiv_eq_zero.2 (hxc 1)
  set z : criticalPoints 𝓘(ℝ, E) f := ⟨xs 1, hzcrit⟩
  have hxz : (x : M) ≠ z := fun h ↦ hzx.ne' (congrArg f h)
  have hzy : (z : M) ≠ y := fun h ↦ hyz.ne' (congrArg f h)
  -- The part of the record above the level of `z` records an unbroken trajectory.
  have ha :
      (fun i : c ⁻¹' Ioo (f z) (f x) ↦ w.val ⟨i, hyz.trans i.property.1, i.property.2⟩) ∈
      hX.morseTrajectoryRecords x z ((c ⁻¹' Ioo (f z) (f x)).domRestrict c) := by
    refine hX.mem_morseTrajectoryRecords.2 ⟨zs 0, by simpa [← hx0] using hzs 0, fun i ↦
      ⟨(hrec _).1, hX.exists_flow_eq_of_mem_Ioo hzs hrec (j := 0) ?_⟩⟩
    rw [Fin.succ_zero_eq_one, Fin.castSucc_zero, hx0]
    exact i.property
  -- The part below the level of `z` records the broken trajectory through `xs 1, …, xs (k + 2)`.
  have hb := hX.mem_morseBrokenTrajectoryRecords_tail hxk hxc hxne hzs hrec hzx
  refine ⟨z, ⟨_, mem_morseBrokenTrajectorySpace.2 ⟨hxz,
    hX.morseTrajectoryRecords_subset_morseBrokenTrajectoryRecords
      (mem_criticalPoints_iff_mfderiv_eq_zero.1 x.property) (hxc 1) hxz _ ha⟩⟩,
    ⟨_, mem_morseBrokenTrajectorySpace.2 ⟨hzy, hb⟩⟩,
    mem_morseBrokenTrajectorySpaceBoundary.not.2 (not_not.2 ha),
    Subtype.ext (funext fun i ↦ ?_)⟩
  rw [coe_morseBrokenTrajectorySpaceComp_apply]
  by_cases h : f z < c i
  · exact concatLevelRecords_of_lt _ _ _ h
  · exact concatLevelRecords_of_gt _ _ _ (lt_of_le_of_ne (not_lt.1 h) (hc i z))

/-! ### Concatenation is an embedding -/

/-- **Concatenation at a critical point is an embedding.** A concatenation of broken trajectories
at `z` is the first one above the level of `z` and the second one below it, so restricting a
record to the levels above and below `f z` recovers the two factors. -/
theorem isEmbedding_morseBrokenTrajectorySpaceComp (x z y : criticalPoints 𝓘(ℝ, E) f) :
    IsEmbedding (hX.morseBrokenTrajectorySpaceComp hc x z y) := by
  rcases isEmpty_or_nonempty
    (hX.morseBrokenTrajectorySpace c x z × hX.morseBrokenTrajectorySpace c z y) with h | ⟨a, b⟩
  · exact .of_subsingleton _
  have hzx := value_lt_of_mem_morseBrokenTrajectorySpace a.property
  have hyz := value_lt_of_mem_morseBrokenTrajectorySpace b.property
  -- Restriction to the levels above and below `f z`.
  let G (w : c ⁻¹' Ioo (f y) (f x) → M) :
      (c ⁻¹' Ioo (f z) (f x) → M) × (c ⁻¹' Ioo (f y) (f z) → M) :=
    (fun i ↦ w ⟨i, hyz.trans i.property.1, i.property.2⟩,
      fun i ↦ w ⟨i, i.property.1, i.property.2.trans hzx⟩)
  have hG : Continuous G :=
    (continuous_pi fun _ ↦ continuous_apply _).prodMk (continuous_pi fun _ ↦ continuous_apply _)
  have hGcomp : (G ∘ Subtype.val) ∘ hX.morseBrokenTrajectorySpaceComp hc x z y =
      Prod.map Subtype.val Subtype.val := by
    funext p
    refine Prod.ext (funext fun i ↦ ?_) (funext fun i ↦ ?_)
    · simp only [Function.comp_apply, coe_morseBrokenTrajectorySpaceComp_apply, G]
      exact concatLevelRecords_of_lt (fun j ↦ hc j z) p.1.val p.2.val
        (i := ⟨i, hyz.trans i.property.1, i.property.2⟩) i.property.1
    · simp only [Function.comp_apply, coe_morseBrokenTrajectorySpaceComp_apply, G]
      exact concatLevelRecords_of_gt (fun j ↦ hc j z) p.1.val p.2.val
        (i := ⟨i, i.property.1, i.property.2.trans hzx⟩) i.property.2
  exact .of_comp (map_continuous _) (hG.comp continuous_subtypeVal)
    (hGcomp ▸ IsEmbedding.subtypeVal.prodMap IsEmbedding.subtypeVal)

/-! ### The faces of the boundary -/

section Faces

variable (hdense : ∀ x y : criticalPoints 𝓘(ℝ, E) f, Ioo (f y) (f x) ⊆ closure (range c))

include hc hdense in
/-- **The boundary is the union of the faces.** The boundary of the trajectory space from `x` to
`y` is the union, over the critical points `z`, of the images of the composition maps at `z`. -/
theorem morseBrokenTrajectorySpaceBoundary_eq_iUnion (x y : criticalPoints 𝓘(ℝ, E) f) :
    hX.morseBrokenTrajectorySpaceBoundary c x y =
      ⋃ z, range (hX.morseBrokenTrajectorySpaceComp hc x z y) := by
  ext w
  simp only [mem_iUnion, mem_range]
  constructor
  · intro hw
    obtain ⟨z, a, b, -, hab⟩ :=
      hX.exists_morseBrokenTrajectorySpaceComp_eq_of_mem_boundary hc hw
    exact ⟨z, (a, b), hab⟩
  · rintro ⟨z, p, rfl⟩
    exact hX.morseBrokenTrajectorySpaceComp_mem_morseBrokenTrajectorySpaceBoundary hc hdense x z y p

include hdense in
/-- Just above the level of its end `z`, a broken trajectory to `z` lies in the stable manifold
of `z`: on some level `c i` above `f z`, the last component of the trajectory crosses it. -/
private theorem exists_apply_mem_stableSet {x z : criticalPoints 𝓘(ℝ, E) f}
    (a : hX.morseBrokenTrajectorySpace c x z) :
    ∃ i, ∃ (hi : f z < c i) (hix : c i < f x),
      a.val ⟨i, hi, hix⟩ ∈ hX.flow.stableSet z := by
  obtain ⟨hxz, ha⟩ := mem_morseBrokenTrajectorySpace.1 a.property
  obtain ⟨k, xs, zs, hx0, hxk, hxc, hxne, hzs, hrec⟩ := hX.mem_morseBrokenTrajectoryRecords.1 ha
  obtain _ | k := k
  · exact absurd (hx0.symm.trans hxk) hxz
  -- The last component runs from `xs k` to `z`; take a level `c i` between them.
  have hlast : f z < f (xs (Fin.last k).castSucc) :=
    hxk ▸ hX.strictAnti_apply_of_chain hxne hzs (Fin.castSucc_lt_last (Fin.last k))
  obtain ⟨i, hi⟩ := exists_mem_Ioo_of_Ioo_subset_closure_range hlast
    (hdense ⟨_, mem_criticalPoints_iff_mfderiv_eq_zero.2 (hxc _)⟩ z)
  have hix : c i < f x :=
    hi.2.trans_le ((hX.antitone_apply_of_chain hzs (Fin.zero_le _)).trans_eq (congrArg f hx0))
  obtain ⟨t, ht⟩ := hX.exists_flow_eq_of_mem_Ioo hzs hrec (i := ⟨i, hi.1, hix⟩)
    (j := Fin.last k) (by rw [Fin.succ_last, hxk]; exact hi)
  refine ⟨i, hi.1, hix, ?_⟩
  rw [← ht, Flow.apply_mem_stableSet_iff]
  simpa [Fin.succ_last, hxk] using (hzs (Fin.last k)).2

include hc hdense in
/-- **The interior of a face meets no other face.** A concatenation at `z` of two unbroken
trajectories is a concatenation at no other critical point `z'`. On a level just above `f z'`, a
broken trajectory to `z'` lies in the stable manifold of `z'`, while the concatenation at `z` lies
in that of `z` or of `y`. -/
theorem disjoint_range_morseBrokenTrajectorySpaceComp_image
    {x z z' y : criticalPoints 𝓘(ℝ, E) f} (hz : z' ≠ z) :
    Disjoint (range (hX.morseBrokenTrajectorySpaceComp hc x z' y))
      (hX.morseBrokenTrajectorySpaceComp hc x z y ''
        ((hX.morseBrokenTrajectorySpaceBoundary c x z)ᶜ ×ˢ
          (hX.morseBrokenTrajectorySpaceBoundary c z y)ᶜ)) := by
  refine disjoint_left.2 ?_
  rintro w ⟨⟨a, b⟩, rfl⟩ ⟨⟨u₁, u₂⟩, ⟨hu₁, hu₂⟩, he⟩
  have hz'y : (z' : M) ≠ y := (mem_morseBrokenTrajectorySpace.1 b.property).1
  have hyz' := value_lt_of_mem_morseBrokenTrajectorySpace b.property
  -- Just above the level of `z'`, `a` lies in the stable manifold of `z'`.
  obtain ⟨i, hi, hix, ha_i⟩ := hX.exists_apply_mem_stableSet hdense a
  have hw_i : (hX.morseBrokenTrajectorySpaceComp hc x z' y (a, b)).val ⟨i, hyz'.trans hi, hix⟩ =
      a.val ⟨i, hi, hix⟩ := by
    rw [coe_morseBrokenTrajectorySpaceComp_apply]
    exact concatLevelRecords_of_lt (fun j ↦ hc j z') a.val b.val
      (i := ⟨i, hyz'.trans hi, hix⟩) hi
  -- On the same level the concatenation at `z` lies in the stable manifold of `z` or of `y`.
  rw [← he, coe_morseBrokenTrajectorySpaceComp_apply] at hw_i
  have hu₁ : u₁.val ∈
      hX.morseTrajectoryRecords x z ((c ⁻¹' Ioo (f z) (f x)).domRestrict c) :=
    not_not.1 (mt mem_morseBrokenTrajectorySpaceBoundary.2 hu₁)
  have hu₂ : u₂.val ∈
      hX.morseTrajectoryRecords z y ((c ⁻¹' Ioo (f y) (f z)).domRestrict c) :=
    not_not.1 (mt mem_morseBrokenTrajectorySpaceBoundary.2 hu₂)
  by_cases hzi : f z < c i
  · rw [concatLevelRecords_of_lt (fun j ↦ hc j z) u₁.val u₂.val
      (i := ⟨i, hyz'.trans hi, hix⟩) hzi] at hw_i
    obtain ⟨y₁, hy₁, hrec₁⟩ := hX.mem_morseTrajectoryRecords.1 hu₁
    obtain ⟨-, t, ht⟩ := hrec₁ ⟨i, hzi, hix⟩
    have : a.val ⟨i, hi, hix⟩ ∈ hX.flow.stableSet z := by
      rw [← hw_i, ← ht, Flow.apply_mem_stableSet_iff]
      exact hy₁.2
    exact disjoint_left.1 (Flow.disjoint_stableSet (Subtype.coe_injective.ne hz)) ha_i this
  · have hiz : c i < f z := lt_of_le_of_ne (not_lt.1 hzi) (hc i z)
    rw [concatLevelRecords_of_gt (fun j ↦ hc j z) u₁.val u₂.val
      (i := ⟨i, hyz'.trans hi, hix⟩) hiz] at hw_i
    obtain ⟨y₂, hy₂, hrec₂⟩ := hX.mem_morseTrajectoryRecords.1 hu₂
    obtain ⟨-, t, ht⟩ := hrec₂ ⟨i, hyz'.trans hi, hiz⟩
    have : a.val ⟨i, hi, hix⟩ ∈ hX.flow.stableSet y := by
      rw [← hw_i, ← ht, Flow.apply_mem_stableSet_iff]
      exact hy₂.2
    exact disjoint_left.1 (Flow.disjoint_stableSet hz'y) ha_i this

include hc hdense in
/-- **The interior of a face.** The concatenations at `z` of unbroken trajectories, the
trajectories broken exactly once at `z`, are the points of the boundary that lie on no face of
another critical point. -/
theorem image_morseBrokenTrajectorySpaceComp_compl_prod_compl
    (x z y : criticalPoints 𝓘(ℝ, E) f) :
    hX.morseBrokenTrajectorySpaceComp hc x z y ''
        ((hX.morseBrokenTrajectorySpaceBoundary c x z)ᶜ ×ˢ
          (hX.morseBrokenTrajectorySpaceBoundary c z y)ᶜ) =
      hX.morseBrokenTrajectorySpaceBoundary c x y \
        ⋃ (z' : criticalPoints 𝓘(ℝ, E) f) (_ : z' ≠ z),
          range (hX.morseBrokenTrajectorySpaceComp hc x z' y) := by
  ext w
  simp only [mem_sdiff, mem_iUnion, not_exists]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨hX.morseBrokenTrajectorySpaceComp_mem_morseBrokenTrajectorySpaceBoundary hc hdense
      x z y p, fun z' hz' hw ↦ disjoint_left.1
        (hX.disjoint_range_morseBrokenTrajectorySpaceComp_image hc hdense hz') hw
        ⟨p, hp, rfl⟩⟩
  rintro ⟨hw, hw'⟩
  rw [hX.morseBrokenTrajectorySpaceBoundary_eq_iUnion hc hdense] at hw
  obtain ⟨z₀, ⟨a, b⟩, rfl⟩ := mem_iUnion.1 hw
  obtain rfl : z₀ = z := by_contra fun h ↦ hw' z₀ h ⟨_, rfl⟩
  refine ⟨(a, b), ⟨fun ha ↦ ?_, fun hb ↦ ?_⟩, rfl⟩
  · -- A break of the first factor at `z''` is a break of the concatenation at `z''`.
    obtain ⟨z'', a₁, a₂, -, rfl⟩ :=
      hX.exists_morseBrokenTrajectorySpaceComp_eq_of_mem_boundary hc ha
    exact hw' z''
      (fun h ↦ (mem_morseBrokenTrajectorySpace.1 a₂.property).1 (congrArg Subtype.val h))
      ⟨(a₁, hX.morseBrokenTrajectorySpaceComp hc z'' z₀ y (a₂, b)),
        (hX.morseBrokenTrajectorySpaceComp_assoc hc x z'' z₀ y a₁ a₂ b).symm⟩
  · -- A break of the second factor at `z''` is a break of the concatenation at `z''`.
    obtain ⟨z'', b₁, b₂, -, rfl⟩ :=
      hX.exists_morseBrokenTrajectorySpaceComp_eq_of_mem_boundary hc hb
    exact hw' z''
      (fun h ↦ (mem_morseBrokenTrajectorySpace.1 b₁.property).1 (congrArg Subtype.val h.symm))
      ⟨(hX.morseBrokenTrajectorySpaceComp hc x z₀ z'' (a, b₁), b₂),
        hX.morseBrokenTrajectorySpaceComp_assoc hc x z₀ z'' y a b₁ b₂⟩

end Faces

/-! ### Topology of the faces under the Morse–Smale condition -/

namespace IsMorseSmale

variable {hX} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)

include h hf in
/-- **The Morse index drops along a broken trajectory.** Under the Morse–Smale condition, the
trajectory space from `x` to `y` is empty unless the Morse index of `y` is smaller than that of
`x`. -/
theorem manifoldMorseIndex_lt_of_mem_morseBrokenTrajectorySpace {x y : M}
    {w : c ⁻¹' Ioo (f y) (f x) → M} (hw : w ∈ hX.morseBrokenTrajectorySpace c x y) :
    manifoldMorseIndex 𝓘(ℝ, E) f y < manifoldMorseIndex 𝓘(ℝ, E) f x := by
  obtain ⟨hxy, hw⟩ := mem_morseBrokenTrajectorySpace.1 hw
  obtain ⟨k, xs, zs, rfl, rfl, -, hxne, hzs, -⟩ := hX.mem_morseBrokenTrajectoryRecords.1 hw
  exact h.strictAnti_manifoldMorseIndex_of_chain hf hxne hzs
    ((Fin.zero_le _).lt_of_ne fun h ↦ hxy (congrArg xs h))

include h hf hc in
/-- **The trajectory spaces are compact.** On countably many levels, the trajectory space from `x`
to `y` is the closure of the records of unbroken trajectories in the compact space of records. -/
theorem isCompact_morseBrokenTrajectorySpace [Countable ι] (x y : criticalPoints 𝓘(ℝ, E) f) :
    IsCompact (hX.morseBrokenTrajectorySpace c x y) := by
  by_cases hxy : (x : M) = y
  · rw [eq_empty_of_forall_notMem fun w hw ↦ (mem_morseBrokenTrajectorySpace.1 hw).1 hxy]
    exact isCompact_empty
  have : hX.morseBrokenTrajectorySpace c x y =
      closure (hX.morseTrajectoryRecords x y ((c ⁻¹' Ioo (f y) (f x)).domRestrict c)) := by
    rw [h.closure_morseTrajectoryRecords hf hxy (c := (c ⁻¹' Ioo (f y) (f x)).domRestrict c)
      (fun i y' hy' hd ↦ hc i ⟨y', mem_criticalPoints_iff_mfderiv_eq_zero.2 hd⟩ hy'.symm)
      fun i ↦ i.property]
    ext w
    simp [hxy]
  rw [this]
  exact isClosed_closure.isCompact

include h hf hc in
/-- The trajectory spaces are compact spaces. -/
theorem compactSpace_morseBrokenTrajectorySpace [Countable ι]
    (x y : criticalPoints 𝓘(ℝ, E) f) :
    CompactSpace (hX.morseBrokenTrajectorySpace c x y) :=
  isCompact_iff_compactSpace.1 (h.isCompact_morseBrokenTrajectorySpace hc hf x y)

include h hf hc in
/-- **The faces are closed**, as compact images of compact spaces. -/
theorem isClosed_range_morseBrokenTrajectorySpaceComp [Countable ι]
    (x z y : criticalPoints 𝓘(ℝ, E) f) :
    IsClosed (range (hX.morseBrokenTrajectorySpaceComp hc x z y)) := by
  have := h.compactSpace_morseBrokenTrajectorySpace hc hf x z
  have := h.compactSpace_morseBrokenTrajectorySpace hc hf z y
  exact (isCompact_range (map_continuous _)).isClosed

variable (hdense : ∀ x y : criticalPoints 𝓘(ℝ, E) f, Ioo (f y) (f x) ⊆ closure (range c))

include h hf hc hdense in
/-- **The boundary is closed**, as the union of the finitely many faces. Equivalently, the
unbroken trajectories form an open subset of the trajectory space. -/
theorem isClosed_morseBrokenTrajectorySpaceBoundary [Countable ι]
    (x y : criticalPoints 𝓘(ℝ, E) f) :
    IsClosed (hX.morseBrokenTrajectorySpaceBoundary c x y) := by
  have := hf.finite_criticalPoints.to_subtype
  rw [hX.morseBrokenTrajectorySpaceBoundary_eq_iUnion hc hdense]
  exact isClosed_iUnion_of_finite fun z ↦
    h.isClosed_range_morseBrokenTrajectorySpaceComp hc hf x z y

include h hf hc hdense in
/-- **Concatenation is an open embedding of the products of unbroken trajectory spaces into the
boundary.** Its image, the interior of the face at `z`, is the part of the boundary outside the
finitely many closed faces of the other critical points
(`TauCeti.IsAdaptedPseudoGradient.image_morseBrokenTrajectorySpaceComp_compl_prod_compl`). -/
theorem isOpenEmbedding_morseBrokenTrajectorySpaceComp_compl_prod_compl [Countable ι]
    (x z y : criticalPoints 𝓘(ℝ, E) f) :
    IsOpenEmbedding fun r : ↥(hX.morseBrokenTrajectorySpaceBoundary c x z)ᶜ ×
        ↥(hX.morseBrokenTrajectorySpaceBoundary c z y)ᶜ ↦
      (⟨hX.morseBrokenTrajectorySpaceComp hc x z y (r.1, r.2),
        hX.morseBrokenTrajectorySpaceComp_mem_morseBrokenTrajectorySpaceBoundary hc hdense x z y
          _⟩ : hX.morseBrokenTrajectorySpaceBoundary c x y) := by
  have := hf.finite_criticalPoints.to_subtype
  refine ⟨((hX.isEmbedding_morseBrokenTrajectorySpaceComp hc x z y).comp
    (IsEmbedding.subtypeVal.prodMap IsEmbedding.subtypeVal)).codRestrict _ _, ?_⟩
  have hrange : range (fun r : ↥(hX.morseBrokenTrajectorySpaceBoundary c x z)ᶜ ×
        ↥(hX.morseBrokenTrajectorySpaceBoundary c z y)ᶜ ↦
      (⟨hX.morseBrokenTrajectorySpaceComp hc x z y (r.1, r.2),
        hX.morseBrokenTrajectorySpaceComp_mem_morseBrokenTrajectorySpaceBoundary hc hdense x z y
          _⟩ : hX.morseBrokenTrajectorySpaceBoundary c x y)) =
      Subtype.val ⁻¹' (⋃ (z' : criticalPoints 𝓘(ℝ, E) f) (_ : z' ≠ z),
        range (hX.morseBrokenTrajectorySpaceComp hc x z' y))ᶜ := by
    ext w
    have hw := congrArg (w.val ∈ ·)
      (hX.image_morseBrokenTrajectorySpaceComp_compl_prod_compl hc hdense x z y)
    simp only [mem_sdiff, w.property, true_and, eq_iff_iff] at hw
    rw [mem_preimage, mem_compl_iff, ← hw]
    constructor
    · rintro ⟨r, rfl⟩
      exact ⟨(r.1, r.2), ⟨r.1.property, r.2.property⟩, rfl⟩
    · rintro ⟨p, hp, he⟩
      exact ⟨(⟨p.1, hp.1⟩, ⟨p.2, hp.2⟩), Subtype.ext he⟩
  rw [hrange]
  exact (isClosed_iUnion_of_finite fun z' ↦ isClosed_iUnion_of_finite fun _ ↦
    h.isClosed_range_morseBrokenTrajectorySpaceComp hc hf x z' y).isOpen_compl.preimage
      continuous_subtypeVal

include h hf hc hdense in
/-- **The interiors of the faces are dense in the boundary.** A broken trajectory is the
concatenation of an unbroken trajectory and a broken one at its first break, and the broken
factor is a limit of unbroken trajectories by gluing
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseBrokenTrajectoryRecords_subset_closure`). -/
theorem dense_morseBrokenTrajectorySpaceComp_image (x y : criticalPoints 𝓘(ℝ, E) f) :
    Dense {w : hX.morseBrokenTrajectorySpaceBoundary c x y | ∃ z,
      (w : hX.morseBrokenTrajectorySpace c x y) ∈ hX.morseBrokenTrajectorySpaceComp hc x z y ''
        ((hX.morseBrokenTrajectorySpaceBoundary c x z)ᶜ ×ˢ
          (hX.morseBrokenTrajectorySpaceBoundary c z y)ᶜ)} := by
  refine Subtype.dense_iff.2 fun w hw ↦ ?_
  obtain ⟨z, a, b, ha, rfl⟩ := hX.exists_morseBrokenTrajectorySpaceComp_eq_of_mem_boundary hc hw
  obtain ⟨hzy, hb⟩ := mem_morseBrokenTrajectorySpace.1 b.property
  -- The second factor is a limit of unbroken trajectories.
  have hbcl : b ∈ closure (hX.morseBrokenTrajectorySpaceBoundary c z y)ᶜ := by
    rw [closure_subtype]
    refine closure_mono (fun v hv ↦ ?_)
      (h.morseBrokenTrajectoryRecords_subset_closure hf hzy (fun i ↦ i.property) hb)
    exact ⟨⟨v, mem_morseBrokenTrajectorySpace.2 ⟨hzy,
      hX.morseTrajectoryRecords_subset_morseBrokenTrajectoryRecords
        (mem_criticalPoints_iff_mfderiv_eq_zero.1 z.property)
        (mem_criticalPoints_iff_mfderiv_eq_zero.1 y.property) hzy _ hv⟩⟩,
      mem_morseBrokenTrajectorySpaceBoundary.not.2 (not_not.2 hv), rfl⟩
  refine map_mem_closure (f := fun b' ↦ hX.morseBrokenTrajectorySpaceComp hc x z y (a, b'))
    ((map_continuous _).comp (Continuous.prodMk_right a)) hbcl fun b' hb' ↦ ?_
  exact ⟨⟨_, hX.morseBrokenTrajectorySpaceComp_mem_morseBrokenTrajectorySpaceBoundary hc hdense
    x z y _⟩, ⟨z, (a, b'), ⟨ha, hb'⟩, rfl⟩, rfl⟩

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti
