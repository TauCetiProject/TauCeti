/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Stable.Broken.Boundary
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
(`TauCeti.TwistingChainSystem.exists_isRepresenting_of_subsingleton_units`), refining the
point-set facts of `TauCeti.Geometry.Manifold.Morse.Stable.Broken.Boundary`.

* Every point of `∂L(x, y)` is the concatenation, at its first break `z`, of an unbroken
  trajectory and a broken one
  (`exists_morseBrokenTrajectorySpaceComp_eq_of_mem_morseBrokenTrajectorySpaceBoundary`
  in `IsAdaptedPseudoGradient`), refining
  `TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySpaceBoundary_eq_iUnion_range`.
* Concatenation at any point `z` whose value is not a level is an embedding
  (`TauCeti.IsAdaptedPseudoGradient.isEmbedding_morseBrokenTrajectorySpaceConcat`): restricting a
  record to the levels above and below `f z` recovers its two factors. In particular, so are the
  composition maps (`TauCeti.IsAdaptedPseudoGradient.isEmbedding_morseBrokenTrajectorySpaceComp`).
* The *interior* of the face at `z`, made of the concatenations of two unbroken trajectories, meets
  no face of another critical point
  (`TauCeti.IsAdaptedPseudoGradient.disjoint_range_morseBrokenTrajectorySpaceComp_image`), and
  it is exactly the part of the boundary outside these other faces
  (`TauCeti.IsAdaptedPseudoGradient.image_morseBrokenTrajectorySpaceComp_compl_prod_compl`).

Under the Morse–Smale condition and on countably many levels:

* the Morse index drops from `x` to `y` whenever `L(x, y)` is nonempty
  (`IsMorseSmale.manifoldMorseIndex_lt_of_mem_morseBrokenTrajectorySpace`);
* the trajectory spaces are compact (`IsMorseSmale.compactSpace_morseBrokenTrajectorySpace`), so
  the faces are closed (`IsMorseSmale.isClosed_range_morseBrokenTrajectorySpaceComp`);
* concatenation at `z` is an open embedding of the product of the spaces of unbroken trajectories
  into the boundary
  (`IsMorseSmale.isOpenEmbedding_morseBrokenTrajectorySpaceComp_compl_prod_compl`);
* the interiors of the faces are dense in the boundary
  (`IsMorseSmale.dense_morseBrokenTrajectorySpaceComp_image_compl_prod_compl`), since a broken
  trajectory is a limit of unbroken ones
  (`IsMorseSmale.morseBrokenTrajectoryRecords_subset_closure`).

With the unbroken trajectories as the interiors `N x y`, the facts above are the
hypotheses `hj`, `hιj`, `hU` and `hUι` of
`TauCeti.TwistingChainSystem.exists_isRepresenting_of_subsingleton_units` for the trajectory
spaces, and `hUA` follows from the injectivity of concatenation. Of its other hypotheses, the
charts on the unbroken trajectories hold in every index difference
(`IsMorseSmale.nonempty_chartedSpace_compl_morseBrokenTrajectorySpaceBoundary`, in
`TauCeti.Geometry.Manifold.Morse.Stable.Broken.Boundary`), and the charts on the boundary and its
collar are understood in index difference at most two. There:

* the boundary is empty when `ind x ≤ ind y + 1`
  (`IsMorseSmale.morseBrokenTrajectorySpaceBoundary_eq_empty`, in
  `TauCeti.Geometry.Manifold.Morse.Stable.Broken.TrajectorySpace`), since then every broken
  trajectory is unbroken;
* when `ind x ≤ ind y + 2`, every broken trajectory breaks once, into two unbroken trajectories
  (`IsMorseSmale.exists_morseBrokenTrajectorySpaceComp_eq_of_le_add_two`), and the boundary is
  discrete (`IsMorseSmale.discreteTopology_morseBrokenTrajectorySpaceBoundary`);
* the boundary is collared in index difference two
  (`IsMorseSmale.isCollared_morseBrokenTrajectorySpaceBoundary`, in
  `TauCeti.Geometry.Manifold.Morse.Stable.Broken.Collar`).

`TauCeti.Geometry.Manifold.Morse.Stable.Broken.Representing` puts these together into
representing chain systems in index difference at most two. In larger index differences, the
charts and the collar of the boundary near the deeper strata come from the gluing of trajectories
broken several times and are not proved here.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `exists_morseBrokenTrajectorySpaceComp_eq_of_mem_morseBrokenTrajectorySpaceBoundary`: the
  first break of a broken trajectory.
* `isEmbedding_morseBrokenTrajectorySpaceConcat`, `isEmbedding_morseBrokenTrajectorySpaceComp`:
  concatenation is an embedding.
* `range_morseBrokenTrajectorySpaceComp_compl_prod_compl`: the concatenations of pairs of
  unbroken trajectories.
* `image_morseBrokenTrajectorySpaceComp_compl_prod_compl`: the interior of a face.
* `IsMorseSmale.manifoldMorseIndex_lt_of_mem_morseBrokenTrajectorySpace`: the index drops.
* `IsMorseSmale.isClosed_range_morseBrokenTrajectorySpaceComp`: the faces are closed.
* `IsMorseSmale.isOpenEmbedding_morseBrokenTrajectorySpaceComp_compl_prod_compl`: the interiors
  of the faces are open in the boundary.
* `IsMorseSmale.dense_morseBrokenTrajectorySpaceComp_image_compl_prod_compl`: they are dense in it.
* `IsMorseSmale.exists_morseBrokenTrajectorySpaceComp_eq_of_le_add_two`: in index difference at
  most two, a broken trajectory breaks once, into two unbroken trajectories.
* `IsMorseSmale.discreteTopology_morseBrokenTrajectorySpaceBoundary`: the broken trajectories form
  a discrete space in index difference at most two.

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

include hc in
/-- **A broken trajectory breaks first at a critical point.** A point of the boundary of the
trajectory space from `x` to `y` is the concatenation, at some critical point `z`, of an unbroken
trajectory from `x` to `z` and a broken trajectory from `z` to `y`: the point `z` is the end of the
first component. -/
theorem exists_morseBrokenTrajectorySpaceComp_eq_of_mem_morseBrokenTrajectorySpaceBoundary
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
    exact absurd (hX.mem_morseTrajectoryRecords_of_chain hx0 hxk hzs hrec fun i ↦ i.property)
      (mem_morseBrokenTrajectorySpaceBoundary.1 hw)
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
      hX.morseTrajectoryRecords x z ((c ⁻¹' Ioo (f z) (f x)).domRestrict c) :=
    hX.mem_morseTrajectoryRecords_of_chain hx0 rfl hzs (fun i ↦ hrec _) fun i ↦ i.property
  -- The part below the level of `z` records the broken trajectory through `xs 1, …, xs (k + 2)`.
  have hb :
      (fun i : c ⁻¹' Ioo (f y) (f z) ↦ w.val ⟨i, i.property.1, i.property.2.trans hzx⟩) ∈
      hX.morseBrokenTrajectoryRecords z y ((c ⁻¹' Ioo (f y) (f z)).domRestrict c) :=
    hX.mem_morseBrokenTrajectoryRecords_of_chain rfl hxk hxc hxne hzs (fun i ↦ hrec _)
      fun i ↦ i.property.2
  refine ⟨z, ⟨_, mem_morseBrokenTrajectorySpace.2 ⟨hxz,
    hX.morseTrajectoryRecords_subset_morseBrokenTrajectoryRecords
      (mem_criticalPoints_iff_mfderiv_eq_zero.1 x.property) (hxc 1) hxz _ ha⟩⟩,
    ⟨_, mem_morseBrokenTrajectorySpace.2 ⟨hzy, hb⟩⟩,
    notMem_morseBrokenTrajectorySpaceBoundary.2 ha,
    Subtype.ext (funext fun i ↦ ?_)⟩
  rw [coe_morseBrokenTrajectorySpaceComp_apply]
  by_cases h : f z < c i
  · exact concatLevelRecords_of_lt _ _ _ h
  · exact concatLevelRecords_of_gt _ _ _ (lt_of_le_of_ne (not_lt.1 h) (hc i z))

/-! ### Concatenation is an embedding -/

/-- **Concatenation at `z` is an embedding.** A concatenation of broken trajectories at `z` is the
first one above the level of `z` and the second one below it, so restricting a record to the levels
above and below `f z` recovers the two factors. -/
theorem isEmbedding_morseBrokenTrajectorySpaceConcat {x z y : M} (hz : ∀ i, c i ≠ f z) :
    IsEmbedding (hX.morseBrokenTrajectorySpaceConcat (x := x) (y := y) hz) := by
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
  have hGcomp : (G ∘ Subtype.val) ∘ hX.morseBrokenTrajectorySpaceConcat hz =
      Prod.map Subtype.val Subtype.val := by
    funext p
    refine Prod.ext (funext fun i ↦ ?_) (funext fun i ↦ ?_)
    · simp only [Function.comp_apply, coe_morseBrokenTrajectorySpaceConcat_apply, G]
      exact concatLevelRecords_of_lt hz p.1.val p.2.val
        (i := ⟨i, hyz.trans i.property.1, i.property.2⟩) i.property.1
    · simp only [Function.comp_apply, coe_morseBrokenTrajectorySpaceConcat_apply, G]
      exact concatLevelRecords_of_gt hz p.1.val p.2.val
        (i := ⟨i, i.property.1, i.property.2.trans hzx⟩) i.property.2
  exact .of_comp (map_continuous _) (hG.comp continuous_subtypeVal)
    (hGcomp ▸ IsEmbedding.subtypeVal.prodMap IsEmbedding.subtypeVal)

/-- **Concatenation at a critical point is an embedding.** -/
theorem isEmbedding_morseBrokenTrajectorySpaceComp (x z y : criticalPoints 𝓘(ℝ, E) f) :
    IsEmbedding (hX.morseBrokenTrajectorySpaceComp hc x z y) := by
  convert hX.isEmbedding_morseBrokenTrajectorySpaceConcat fun i ↦ hc i z using 1
  funext w
  exact Subtype.ext (by simp)

/-- The concatenations at `z` of pairs of unbroken trajectories, as the image of the product of the
interiors. -/
theorem range_morseBrokenTrajectorySpaceComp_compl_prod_compl
    (x z y : criticalPoints 𝓘(ℝ, E) f) :
    (range fun r : ↥(hX.morseBrokenTrajectorySpaceBoundary c x z)ᶜ ×
        ↥(hX.morseBrokenTrajectorySpaceBoundary c z y)ᶜ ↦
      hX.morseBrokenTrajectorySpaceComp hc x z y (r.1, r.2)) =
    hX.morseBrokenTrajectorySpaceComp hc x z y ''
      ((hX.morseBrokenTrajectorySpaceBoundary c x z)ᶜ ×ˢ
        (hX.morseBrokenTrajectorySpaceBoundary c z y)ᶜ) := by
  ext w
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨(r.1, r.2), ⟨r.1.property, r.2.property⟩, rfl⟩
  · rintro ⟨p, ⟨h₁, h₂⟩, rfl⟩
    exact ⟨(⟨p.1, h₁⟩, ⟨p.2, h₂⟩), rfl⟩

/-! ### The faces of the boundary -/

section Faces

variable (hdense : ∀ x y : criticalPoints 𝓘(ℝ, E) f, Ioo (f y) (f x) ⊆ closure (range c))

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
  rw [hX.morseBrokenTrajectorySpaceBoundary_eq_iUnion_range hc hdense] at hw
  obtain ⟨z₀, ⟨a, b⟩, rfl⟩ := mem_iUnion.1 hw
  obtain rfl : z₀ = z := by_contra fun h ↦ hw' z₀ h ⟨_, rfl⟩
  refine ⟨(a, b), ⟨fun ha ↦ ?_, fun hb ↦ ?_⟩, rfl⟩
  · -- A break of the first factor at `z''` is a break of the concatenation at `z''`.
    obtain ⟨z'', a₁, a₂, -, rfl⟩ :=
      hX.exists_morseBrokenTrajectorySpaceComp_eq_of_mem_morseBrokenTrajectorySpaceBoundary hc ha
    exact hw' z''
      (fun h ↦ (mem_morseBrokenTrajectorySpace.1 a₂.property).1 (congrArg Subtype.val h))
      ⟨(a₁, hX.morseBrokenTrajectorySpaceComp hc z'' z₀ y (a₂, b)),
        (hX.morseBrokenTrajectorySpaceComp_assoc hc x z'' z₀ y a₁ a₂ b).symm⟩
  · -- A break of the second factor at `z''` is a break of the concatenation at `z''`.
    obtain ⟨z'', b₁, b₂, -, rfl⟩ :=
      hX.exists_morseBrokenTrajectorySpaceComp_eq_of_mem_morseBrokenTrajectorySpaceBoundary hc hb
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
/-- **The faces are closed**, as compact images of compact spaces. -/
theorem isClosed_range_morseBrokenTrajectorySpaceComp [Countable ι]
    (x z y : criticalPoints 𝓘(ℝ, E) f) :
    IsClosed (range (hX.morseBrokenTrajectorySpaceComp hc x z y)) := by
  have := h.compactSpace_morseBrokenTrajectorySpace hf hc x z
  have := h.compactSpace_morseBrokenTrajectorySpace hf hc z y
  exact (isCompact_range (map_continuous _)).isClosed

variable (hdense : ∀ x y : criticalPoints 𝓘(ℝ, E) f, Ioo (f y) (f x) ⊆ closure (range c))

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
  -- The range is the part of the boundary outside the closed faces of the other critical points.
  convert (isClosed_iUnion_of_finite fun z' ↦ isClosed_iUnion_of_finite fun (_ : z' ≠ z) ↦
    h.isClosed_range_morseBrokenTrajectorySpaceComp hc hf x z' y).isOpen_compl.preimage
      continuous_subtypeVal using 1
  ext w
  have hw := congrArg (w.val ∈ ·)
    (hX.image_morseBrokenTrajectorySpaceComp_compl_prod_compl hc hdense x z y)
  simp only [mem_sdiff, w.property, true_and, eq_iff_iff] at hw
  rw [mem_preimage, mem_compl_iff, ← hw,
    ← hX.range_morseBrokenTrajectorySpaceComp_compl_prod_compl hc]
  exact ⟨fun ⟨r, hr⟩ ↦ ⟨r, congrArg Subtype.val hr⟩, fun ⟨r, hr⟩ ↦ ⟨r, Subtype.ext hr⟩⟩

include h hf hc in
/-- **In index difference at most two, a broken trajectory breaks once.** When
`ind x ≤ ind y + 2`, every point of the boundary of `L(x, y)` is the concatenation of two unbroken
trajectories, at a critical point `z` with `ind x = ind z + 1 = ind y + 2`. -/
theorem exists_morseBrokenTrajectorySpaceComp_eq_of_le_add_two
    {x y : criticalPoints 𝓘(ℝ, E) f}
    (hxy : manifoldMorseIndex 𝓘(ℝ, E) f x ≤ manifoldMorseIndex 𝓘(ℝ, E) f y + 2)
    {w : hX.morseBrokenTrajectorySpace c x y}
    (hw : w ∈ hX.morseBrokenTrajectorySpaceBoundary c x y) :
    ∃ (z : criticalPoints 𝓘(ℝ, E) f) (a : hX.morseBrokenTrajectorySpace c x z)
      (b : hX.morseBrokenTrajectorySpace c z y),
      manifoldMorseIndex 𝓘(ℝ, E) f x = manifoldMorseIndex 𝓘(ℝ, E) f z + 1 ∧
      manifoldMorseIndex 𝓘(ℝ, E) f z = manifoldMorseIndex 𝓘(ℝ, E) f y + 1 ∧
      a ∉ hX.morseBrokenTrajectorySpaceBoundary c x z ∧
      b ∉ hX.morseBrokenTrajectorySpaceBoundary c z y ∧
      hX.morseBrokenTrajectorySpaceComp hc x z y (a, b) = w := by
  obtain ⟨z, a, b, ha, hab⟩ :=
    hX.exists_morseBrokenTrajectorySpaceComp_eq_of_mem_morseBrokenTrajectorySpaceBoundary hc hw
  have hxz := h.manifoldMorseIndex_lt_of_mem_morseBrokenTrajectorySpace hf a.property
  have hzy := h.manifoldMorseIndex_lt_of_mem_morseBrokenTrajectorySpace hf b.property
  refine ⟨z, a, b, by omega, by omega, ha, ?_, hab⟩
  rw [h.morseBrokenTrajectorySpaceBoundary_eq_empty hf (mem_criticalPoints_iff_mfderiv_eq_zero.1
    z.property) (mem_criticalPoints_iff_mfderiv_eq_zero.1 y.property) (by omega)]
  exact notMem_empty b

include h hf hc hdense in
/-- **In index difference at most two, the broken trajectories form a discrete space.** Every
broken trajectory from `x` to `y` breaks once, at a critical point `z` with
`ind x = ind z + 1 = ind y + 2`, and the face of `z` is an open copy of the product of the discrete
spaces of trajectories from `x` to `z` and from `z` to `y`. -/
theorem discreteTopology_morseBrokenTrajectorySpaceBoundary [Countable ι]
    {x y : criticalPoints 𝓘(ℝ, E) f}
    (hxy : manifoldMorseIndex 𝓘(ℝ, E) f x ≤ manifoldMorseIndex 𝓘(ℝ, E) f y + 2) :
    DiscreteTopology (hX.morseBrokenTrajectorySpaceBoundary c x y) := by
  refine discreteTopology_iff_isOpen_singleton.2 fun w ↦ ?_
  obtain ⟨z, a, b, hxz, hzy, ha, hb, hw⟩ :=
    h.exists_morseBrokenTrajectorySpaceComp_eq_of_le_add_two hc hf hxy w.property
  -- Both factors are rigid.
  obtain ⟨C₁⟩ := h.nonempty_chartedSpace_compl_morseBrokenTrajectorySpaceBoundary hf hc hdense
    (x := x) (y := z) (d := 0) fun _ ↦ by omega
  obtain ⟨C₂⟩ := h.nonempty_chartedSpace_compl_morseBrokenTrajectorySpaceBoundary hf hc hdense
    (x := z) (y := y) (d := 0) fun _ ↦ by omega
  have := ChartedSpace.discreteTopology (EuclideanSpace ℝ (Fin 0))
    ↥(hX.morseBrokenTrajectorySpaceBoundary c x z)ᶜ
  have := ChartedSpace.discreteTopology (EuclideanSpace ℝ (Fin 0))
    ↥(hX.morseBrokenTrajectorySpaceBoundary c z y)ᶜ
  -- The face of `z` is open, and so is the image of a point under it.
  have hopen := h.isOpenEmbedding_morseBrokenTrajectorySpaceComp_compl_prod_compl hc hf hdense
    x z y
  convert hopen.isOpenMap {(⟨a, ha⟩, ⟨b, hb⟩)} (isOpen_discrete _)
  rw [image_singleton]
  exact congrArg singleton (Subtype.ext hw.symm)

include h hf hc hdense in
/-- **The interiors of the faces are dense in the boundary.** A broken trajectory is the
concatenation of an unbroken trajectory and a broken one at its first break, and the broken
factor is a limit of unbroken trajectories by gluing
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseBrokenTrajectoryRecords_subset_closure`). -/
theorem dense_morseBrokenTrajectorySpaceComp_image_compl_prod_compl
    (x y : criticalPoints 𝓘(ℝ, E) f) :
    Dense {w : hX.morseBrokenTrajectorySpaceBoundary c x y | ∃ z,
      (w : hX.morseBrokenTrajectorySpace c x y) ∈ hX.morseBrokenTrajectorySpaceComp hc x z y ''
        ((hX.morseBrokenTrajectorySpaceBoundary c x z)ᶜ ×ˢ
          (hX.morseBrokenTrajectorySpaceBoundary c z y)ᶜ)} := by
  refine Subtype.dense_iff.2 fun w hw ↦ ?_
  obtain ⟨z, a, b, ha, rfl⟩ :=
    hX.exists_morseBrokenTrajectorySpaceComp_eq_of_mem_morseBrokenTrajectorySpaceBoundary hc hw
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
      notMem_morseBrokenTrajectorySpaceBoundary.2 hv, rfl⟩
  refine map_mem_closure (f := fun b' ↦ hX.morseBrokenTrajectorySpaceComp hc x z y (a, b'))
    ((map_continuous _).comp (Continuous.prodMk_right a)) hbcl fun b' hb' ↦ ?_
  exact ⟨⟨_, hX.morseBrokenTrajectorySpaceComp_mem_morseBrokenTrajectorySpaceBoundary hc hdense
    x z y _⟩, ⟨z, (a, b'), ⟨ha, hb'⟩, rfl⟩, rfl⟩

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti
