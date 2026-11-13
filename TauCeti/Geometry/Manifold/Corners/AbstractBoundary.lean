/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.Germ.Basic
public import TauCeti.Geometry.Manifold.Boundary.Charts
public import TauCeti.Geometry.Manifold.Corners.Face

/-!
# The abstract boundary of a manifold with corners

The boundary `I.boundary M` of a manifold with corners is only a set, and at a corner it is not a
manifold: the boundary of the quadrant `[0, ∞)²` has no smooth structure making its inclusion an
immersion at the origin. It also forgets how many faces meet at a point, which is what Stokes'
theorem and gluing along faces need. The *abstract boundary* `∂ₐM` repairs both defects. Its points
are the pairs of a point `x` of `M` and a local face through `x`, so the fibre of `∂ₐM → M` over
`x` has as many points as `x` has local faces, that is `depth x` of them; and near each of its
points it looks like a single face of a chart, which is what makes it a manifold with corners one
dimension down.

This file constructs `∂ₐM` as a topological space; its charts are not constructed here. It works
for models with corners `J` on `EuclideanSpace ℝ ι` whose range is cut out by the nonnegativity of
some coordinates, such as the quadrant `𝓡c n` and the half-space `𝓡∂ n`. In a chart `e`, the
faces of `range J` through `e.extend J x` are the hyperplanes `z i = 0` for the vanishing
coordinates `i` that are nonnegative on `range J`. The corresponding local face of `M` through `x`
is the germ at `x` of the set `{p | e.extend J p i = 0}` (`ModelWithCorners.faceGerm`), and
`ModelWithCorners.localFaces J x` is the set of these germs, over all charts of the atlas.

* `ModelWithCorners.AbstractBoundary J M`, written `∂ₐM` above, has as points the pairs of a point
  `x` and a germ in `J.localFaces x`; `ModelWithCorners.AbstractBoundary.point` is the map to `M`.
* For a chart `e` of the atlas and a coordinate `i` nonnegative on `range J`,
  `ModelWithCorners.AbstractBoundary.faceSection` sends each point `p` of the face
  `{p ∈ e.source | e.extend J p i = 0}` to the point `(p, faceGerm e i p)` of `∂ₐM`. The topology
  of `∂ₐM` is the finest one making all these maps continuous.

With this topology each face section is an open embedding
(`ModelWithCorners.AbstractBoundary.isOpenEmbedding_faceSection`), their ranges cover `∂ₐM`, and the
map to `M` is continuous. The open embedding rests on germs propagating: if two face germs agree
at `x`, the two face sets agree near `x`, so the germs agree at every nearby point
(`ModelWithCorners.isOpen_setOf_faceGerm_eq`).

On a `C¹` manifold the local faces do not depend on the chart
(`ModelWithCorners.existsUnique_equiv_extend_apply_eq_zero_iff`). Hence any single chart `e` of
the maximal atlas at `x` lists the local faces through `x` without repetition
(`ModelWithCorners.faceGermEquiv`), the fibre of `∂ₐM → M` over `x` has exactly `depth x` points
(`ModelWithCorners.AbstractBoundary.natCard_preimage_point`), and `∂ₐM` is Hausdorff when `M` is
(`ModelWithCorners.AbstractBoundary.t2Space`). On a manifold with boundary modelled on the
half-space every boundary point has exactly one local face, and the abstract boundary is the
boundary (`ModelWithCorners.AbstractBoundary.homeomorphBoundary`).

## Main definitions

* `ModelWithCorners.faceGerm J e i x`: the germ at `x` of the face `{p | e.extend J p i = 0}` of
  a chart.
* `ModelWithCorners.localFaces J x`: the local faces through `x`.
* `ModelWithCorners.AbstractBoundary J M`: the abstract boundary, with its map
  `ModelWithCorners.AbstractBoundary.point` to `M`.
* `ModelWithCorners.AbstractBoundary.faceSection`: a face of a chart, as an open subset of the
  abstract boundary.
* `ModelWithCorners.faceGermEquiv`: the vanishing face coordinates of a chart at `x` enumerate
  the local faces through `x`.

## Main results

* `ModelWithCorners.AbstractBoundary.isOpenEmbedding_faceSection`: the face sections are open
  embeddings.
* `ModelWithCorners.AbstractBoundary.continuous_point`: the map to `M` is continuous.
* `ModelWithCorners.natCard_localFaces`,
  `ModelWithCorners.AbstractBoundary.natCard_preimage_point`: a point of depth `d` has `d` local
  faces, and `d` preimages in the abstract boundary.
* `ModelWithCorners.AbstractBoundary.range_point`: the image of the abstract boundary is the
  boundary.
* `ModelWithCorners.AbstractBoundary.t2Space`: the abstract boundary of a Hausdorff manifold is
  Hausdorff.
* `ModelWithCorners.AbstractBoundary.homeomorphBoundary`: for the half-space model, the map to `M`
  is a homeomorphism onto the boundary.

## References

* D. Joyce, *On manifolds with corners*, in *Advances in Geometric Analysis*, Adv. Lect. Math. 21,
  International Press (2012), 225–258, Section 2 (local boundary components, and the boundary
  `∂X` as the set of pairs of a point and a local boundary component through it).
  [arXiv:0910.3518](https://arxiv.org/abs/0910.3518)
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer (2013), Chapter 16, section *Manifolds with Corners*.
-/

public section

noncomputable section

open Set Filter Function Topology
open scoped Manifold

namespace ModelWithCorners

variable {ι : Type*} [Fintype ι] {H : Type*} [TopologicalSpace H]
  {J : ModelWithCorners ℝ (EuclideanSpace ℝ ι) H} {S : Set ι} {M : Type*} [TopologicalSpace M]

/-! ### Face germs -/

variable (J) in
/-- The **face germ** of a chart `e` along the coordinate `i` at `x`: the germ at `x` of the set
`{p | e.extend J p i = 0}`. When `i` is a coordinate nonnegative on `range J` and
`e.extend J x i = 0`, this is the local face of `M` through `x` which the chart presents as the
hyperplane `z i = 0`. -/
def faceGerm (e : OpenPartialHomeomorph M H) (i : ι) (x : M) : Germ (𝓝 x) Prop :=
  ↑(fun p ↦ e.extend J p i = 0)

/-- Two face germs agree at `x` exactly when the two face sets agree near `x`. -/
theorem faceGerm_eq_faceGerm_iff {e e' : OpenPartialHomeomorph M H} {i j : ι} {x : M} :
    J.faceGerm e i x = J.faceGerm e' j x ↔
      ∀ᶠ p in 𝓝 x, e.extend J p i = 0 ↔ e'.extend J p j = 0 := by
  simp only [faceGerm, Germ.coe_eq, EventuallyEq, eq_iff_iff]

/-- **Face germs propagate**: if two face germs agree at `x`, they agree at every point near `x`.
So the set of points where they agree is open. -/
theorem isOpen_setOf_faceGerm_eq (e e' : OpenPartialHomeomorph M H) (i j : ι) :
    IsOpen {x | J.faceGerm e i x = J.faceGerm e' j x} := by
  refine isOpen_iff_mem_nhds.2 fun x hx ↦ ?_
  have h : (fun p ↦ e.extend J p i = 0) =ᶠ[𝓝 x] fun p ↦ e'.extend J p j = 0 := Germ.coe_eq.1 hx
  filter_upwards [h.eventuallyEq_nhds] with y hy using Germ.coe_eq.2 hy

/-- A point lies on the face of a chart whose germ at that point is the germ of a face through
it. -/
theorem extend_apply_eq_zero_of_faceGerm_eq {e e' : OpenPartialHomeomorph M H} {i j : ι} {x : M}
    (h : J.faceGerm e i x = J.faceGerm e' j x) (hx : e'.extend J x j = 0) :
    e.extend J x i = 0 :=
  ((faceGerm_eq_faceGerm_iff.1 h).self_of_nhds).2 hx

/-- **A chart presents distinct faces through a point as distinct germs.** If two vanishing
coordinates of a chart at `x` give the same face germ, they are equal. -/
theorem eq_of_faceGerm_eq (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i})
    {e : OpenPartialHomeomorph M H} {x : M} (hx : x ∈ e.source) {i k : ι}
    (hi : e.extend J x i = 0) (hk : e.extend J x k = 0)
    (h : J.faceGerm e i x = J.faceGerm e k x) : i = k := by
  have hy : e.extend J x ∈ range J := by rw [e.extend_coe]; exact mem_range_self _
  rw [hJ] at hy
  refine TauCeti.eq_of_eventually_apply_eq_zero_imp hy hi hk ?_
  -- Read the eventual equality of the face sets in the chart.
  rw [← hJ, ← e.map_extend_nhds hx, eventually_map]
  filter_upwards [faceGerm_eq_faceGerm_iff.1 h] with p hp using hp.1

variable [ChartedSpace H M] {n : WithTop ℕ∞} [IsManifold J n M]

/-- **Every chart sees every local face.** On a `C¹` manifold, a face of one chart of the maximal
atlas through `x` is, near `x`, a face of any other chart of the maximal atlas at `x`. -/
theorem exists_faceGerm_eq (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}) (hn : n ≠ 0)
    {e e' : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas J n M)
    (he' : e' ∈ IsManifold.maximalAtlas J n M) {x : M} (hx : x ∈ e.source) (hx' : x ∈ e'.source)
    {j : ι} (hj : j ∈ S) (hj' : e'.extend J x j = 0) :
    ∃ i ∈ S, e.extend J x i = 0 ∧ J.faceGerm e' j x = J.faceGerm e i x := by
  obtain ⟨σ, hσ, -⟩ := existsUnique_equiv_extend_apply_eq_zero_iff hJ hn he he' hx hx'
  refine ⟨σ.symm ⟨j, hj, hj'⟩, (σ.symm _).2.1, (σ.symm _).2.2, faceGerm_eq_faceGerm_iff.2 ?_⟩
  filter_upwards [hσ] with p hp
  have h := hp (σ.symm ⟨j, hj, hj'⟩)
  rwa [Equiv.apply_symm_apply] at h

end ModelWithCorners

/-! ### Local faces -/

namespace ModelWithCorners

variable {ι : Type*} [Fintype ι] {H : Type*} [TopologicalSpace H]
  {J : ModelWithCorners ℝ (EuclideanSpace ℝ ι) H} {S : Set ι}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable (J) in
/-- The **local faces** of `M` through `x`: the face germs `J.faceGerm e i x` of the charts `e`
of the atlas at `x`, along the coordinates `i` nonnegative on `range J` that vanish at the image
of `x`. On a `C¹` manifold one chart of the maximal atlas already lists them all
(`ModelWithCorners.faceGermEquiv`), and there are `J.depth x` of them
(`ModelWithCorners.natCard_localFaces`). -/
def localFaces (x : M) : Set (Germ (𝓝 x) Prop) :=
  {F | ∃ e ∈ atlas H M, x ∈ e.source ∧ ∃ i, (∀ z ∈ range J, 0 ≤ z i) ∧ e.extend J x i = 0 ∧
    F = J.faceGerm e i x}

/-- The defining property of the local faces. -/
theorem mem_localFaces_iff {x : M} {F : Germ (𝓝 x) Prop} :
    F ∈ J.localFaces x ↔ ∃ e ∈ atlas H M, x ∈ e.source ∧ ∃ i, (∀ z ∈ range J, 0 ≤ z i) ∧
      e.extend J x i = 0 ∧ F = J.faceGerm e i x :=
  Iff.rfl

/-- The face germ of a chart of the atlas along a face coordinate vanishing at `x` is a local
face through `x`. -/
theorem faceGerm_mem_localFaces {e : OpenPartialHomeomorph M H} (he : e ∈ atlas H M) {x : M}
    (hx : x ∈ e.source) {i : ι} (hi : ∀ z ∈ range J, 0 ≤ z i) (hix : e.extend J x i = 0) :
    J.faceGerm e i x ∈ J.localFaces x :=
  ⟨e, he, hx, i, hi, hix, rfl⟩

variable {n : WithTop ℕ∞} [IsManifold J n M]

/-- On a `C¹` manifold the local faces through `x` are the face germs of any single chart `e` of
the maximal atlas at `x`, along the coordinates of `S` vanishing at the image of `x`. -/
theorem mem_localFaces_iff_of_mem_maximalAtlas (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i})
    (hn : n ≠ 0) {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas J n M) {x : M}
    (hx : x ∈ e.source) {F : Germ (𝓝 x) Prop} :
    F ∈ J.localFaces x ↔ ∃ i ∈ S, e.extend J x i = 0 ∧ F = J.faceGerm e i x := by
  constructor
  · rintro ⟨e', he', hx', j, hj, hj', rfl⟩
    exact exists_faceGerm_eq hJ hn he (IsManifold.subset_maximalAtlas he') hx hx'
      ((forall_mem_range_nonneg_iff hJ).1 hj) hj'
  · rintro ⟨i, hi, hix, rfl⟩
    -- Move the face to the preferred chart, which belongs to the atlas.
    obtain ⟨k, hk, hkx, hF⟩ := exists_faceGerm_eq hJ hn (IsManifold.chart_mem_maximalAtlas x) he
      (mem_chart_source H x) hx hi hix
    rw [hF]
    exact faceGerm_mem_localFaces (chart_mem_atlas H x) (mem_chart_source H x)
      ((forall_mem_range_nonneg_iff hJ).2 hk) hkx

/-- **A chart enumerates the local faces.** On a `C¹` manifold, for a chart `e` of the maximal
atlas at `x`, the coordinates of `S` vanishing at `e.extend J x` correspond bijectively to the
local faces through `x`, by `i ↦ J.faceGerm e i x`. -/
def faceGermEquiv (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}) (hn : n ≠ 0)
    {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas J n M) {x : M}
    (hx : x ∈ e.source) :
    {i // i ∈ S ∧ e.extend J x i = 0} ≃ J.localFaces x :=
  Equiv.ofBijective
    (fun i ↦ ⟨J.faceGerm e i x,
      (mem_localFaces_iff_of_mem_maximalAtlas hJ hn he hx).2 ⟨i, i.2.1, i.2.2, rfl⟩⟩)
    ⟨fun i k h ↦ Subtype.ext (eq_of_faceGerm_eq hJ hx i.2.2 k.2.2 (congrArg Subtype.val h)),
      fun F ↦ by
        obtain ⟨i, hi, hix, hF⟩ := (mem_localFaces_iff_of_mem_maximalAtlas hJ hn he hx).1 F.2
        exact ⟨⟨i, hi, hix⟩, Subtype.ext hF.symm⟩⟩

/-- The local face of the vanishing coordinate `i` is the face germ of `e` along `i`. -/
theorem coe_faceGermEquiv_apply (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}) (hn : n ≠ 0)
    {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas J n M) {x : M}
    (hx : x ∈ e.source) (i : {i // i ∈ S ∧ e.extend J x i = 0}) :
    (faceGermEquiv hJ hn he hx i : Germ (𝓝 x) Prop) = J.faceGerm e i x :=
  (rfl)

/-- **A point of depth `d` has `d` local faces.** -/
theorem natCard_localFaces (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}) (hn : n ≠ 0) (x : M) :
    Nat.card (J.localFaces x) = J.depth x := by
  have hx : (chartAt H x).extend J x ∈ range J := ⟨_, rfl⟩
  rw [← Nat.card_congr (faceGermEquiv hJ hn (IsManifold.chart_mem_maximalAtlas x)
    (mem_chart_source H x)), depth_def, extChartAt, depthAt_eq_natCard_of_range_eq hJ hx]

/-- Every point has finitely many local faces. -/
theorem finite_localFaces (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}) (hn : n ≠ 0) (x : M) :
    (J.localFaces x).Finite :=
  Set.finite_coe_iff.1 <| Finite.of_equiv _
    (faceGermEquiv hJ hn (IsManifold.chart_mem_maximalAtlas x) (mem_chart_source H x))

/-- A point has a local face exactly when it is a boundary point. -/
theorem localFaces_nonempty_iff (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}) (hn : n ≠ 0) {x : M} :
    (J.localFaces x).Nonempty ↔ J.IsBoundaryPoint x := by
  have := (finite_localFaces hJ hn x).to_subtype
  rw [← depth_pos_iff, ← natCard_localFaces hJ hn, Nat.card_pos_iff, and_iff_left this,
    Set.nonempty_coe_sort]

/-- An interior point has no local faces. -/
theorem localFaces_eq_empty_iff (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}) (hn : n ≠ 0) {x : M} :
    J.localFaces x = ∅ ↔ J.IsInteriorPoint x := by
  rw [← not_nonempty_iff_eq_empty, localFaces_nonempty_iff hJ hn,
    ← isInteriorPoint_iff_not_isBoundaryPoint]

end ModelWithCorners

/-! ### The abstract boundary -/

namespace ModelWithCorners

variable {ι : Type*} [Fintype ι] {H : Type*} [TopologicalSpace H]
  (J : ModelWithCorners ℝ (EuclideanSpace ℝ ι) H) (M : Type*) [TopologicalSpace M]
  [ChartedSpace H M]

/-- The **abstract boundary** of a manifold with corners modelled on a region of
`EuclideanSpace ℝ ι`: the pairs of a point of `M` and a local face through it. Over a point of
depth `d` it has `d` points (`ModelWithCorners.AbstractBoundary.natCard_preimage_point`), and its
topology makes every face of a chart an open subset
(`ModelWithCorners.AbstractBoundary.isOpenEmbedding_faceSection`). -/
@[ext]
structure AbstractBoundary where
  /-- The underlying point of `M`. -/
  point : M
  /-- A local face through the point. -/
  face : Germ (𝓝 point) Prop
  /-- The face is a local face through the point. -/
  face_mem : face ∈ J.localFaces point

namespace AbstractBoundary

variable {J M} {S : Set ι}

/-- The points of the abstract boundary over `x` are the local faces through `x`. -/
def preimagePointEquiv (x : M) : (point : J.AbstractBoundary M → M) ⁻¹' {x} ≃ J.localFaces x where
  toFun b := ⟨b.2 ▸ b.1.face, by obtain ⟨⟨y, F, hF⟩, rfl : y = x⟩ := b; exact hF⟩
  invFun F := ⟨⟨x, F.1, F.2⟩, rfl⟩
  left_inv b := by obtain ⟨⟨y, F, hF⟩, rfl : y = x⟩ := b; rfl
  right_inv F := rfl

@[simp]
theorem coe_preimagePointEquiv_symm_apply (x : M) (F : J.localFaces x) :
    ((preimagePointEquiv x).symm F : J.AbstractBoundary M) = ⟨x, F, F.2⟩ :=
  (rfl)

/-! #### Face sections -/

/-- The **face section** of a chart `e` of the atlas along a coordinate `i` nonnegative on
`range J`: each point `p` of the face `{p ∈ e.source | e.extend J p i = 0}` goes to the point of
the abstract boundary over `p` given by this face. -/
def faceSection {e : OpenPartialHomeomorph M H} (he : e ∈ atlas H M) {i : ι}
    (hi : ∀ z ∈ range J, 0 ≤ z i) (p : {p : M // p ∈ e.source ∧ e.extend J p i = 0}) :
    J.AbstractBoundary M :=
  ⟨p, J.faceGerm e i p, faceGerm_mem_localFaces he p.2.1 hi p.2.2⟩

variable {e e' : OpenPartialHomeomorph M H} {he : e ∈ atlas H M} {he' : e' ∈ atlas H M} {i j : ι}
  {hi : ∀ z ∈ range J, 0 ≤ z i} {hj : ∀ z ∈ range J, 0 ≤ z j}

@[simp]
theorem point_faceSection (p : {p : M // p ∈ e.source ∧ e.extend J p i = 0}) :
    (faceSection he hi p).point = p :=
  (rfl)

/-- Two face sections meet over `p` exactly when their face germs agree at `p`. -/
theorem faceSection_eq_faceSection_iff {p : {p : M // p ∈ e.source ∧ e.extend J p i = 0}}
    {q : {q : M // q ∈ e'.source ∧ e'.extend J q j = 0}} :
    faceSection he hi p = faceSection he' hj q ↔
      (p : M) = q ∧ J.faceGerm e i p = J.faceGerm e' j p := by
  obtain ⟨p, hp⟩ := p
  obtain ⟨q, hq⟩ := q
  constructor
  · intro h
    simp only [faceSection, AbstractBoundary.mk.injEq] at h
    obtain ⟨rfl, h⟩ := h
    exact ⟨rfl, eq_of_heq h⟩
  · rintro ⟨rfl, h⟩
    simp only [faceSection, h]

/-- Every point of the abstract boundary lies on a face section. -/
theorem exists_faceSection_eq (b : J.AbstractBoundary M) :
    ∃ (e : OpenPartialHomeomorph M H) (he : e ∈ atlas H M) (i : ι)
      (hi : ∀ z ∈ range J, 0 ≤ z i) (p : {p : M // p ∈ e.source ∧ e.extend J p i = 0}),
      faceSection he hi p = b := by
  obtain ⟨x, F, e, he, hx, i, hi, hix, rfl⟩ := b
  exact ⟨e, he, i, hi, ⟨x, hx, hix⟩, rfl⟩

/-! #### The topology -/

/-- The topology of the abstract boundary: the finest one making every face section
continuous. -/
instance : TopologicalSpace (J.AbstractBoundary M) :=
  ⨆ (e : atlas H M) (i : {i : ι // ∀ z ∈ range J, 0 ≤ z i}),
    TopologicalSpace.coinduced (faceSection e.2 i.2) inferInstance

/-- A set of the abstract boundary is open exactly when its preimage under every face section is
open. -/
theorem isOpen_iff {U : Set (J.AbstractBoundary M)} :
    IsOpen U ↔ ∀ (e : OpenPartialHomeomorph M H) (he : e ∈ atlas H M) (i : ι)
      (hi : ∀ z ∈ range J, 0 ≤ z i), IsOpen (faceSection he hi ⁻¹' U) := by
  simp only [isOpen_iSup_iff, isOpen_coinduced, Subtype.forall]

/-- The face sections are continuous. -/
@[fun_prop]
theorem continuous_faceSection : Continuous (faceSection he hi) :=
  continuous_iff_coinduced_le.2 <| le_iSup₂_of_le (f := fun (e : atlas H M)
    (i : {i : ι // ∀ z ∈ range J, 0 ≤ z i}) ↦
      TopologicalSpace.coinduced (faceSection e.2 i.2) inferInstance) ⟨e, he⟩ ⟨i, hi⟩ le_rfl

/-- The map from the abstract boundary to `M` is continuous. -/
@[fun_prop]
theorem continuous_point : Continuous (point : J.AbstractBoundary M → M) := by
  refine continuous_def.2 fun U hU ↦ isOpen_iff.2 fun e _ i _ ↦ ?_
  exact hU.preimage continuous_subtype_val

/-- The face sections are injective: a face section remembers its point of `M`. -/
theorem faceSection_injective : Injective (faceSection he hi) := fun _ _ h ↦
  Subtype.ext (congrArg point h)

/-- The face sections are open maps: a relatively open piece of a face of a chart is an open
subset of the abstract boundary. -/
theorem isOpenMap_faceSection : IsOpenMap (faceSection he hi) := by
  intro V hV
  obtain ⟨O, hO, rfl⟩ := isOpen_induced_iff.1 hV
  refine isOpen_iff.2 fun e' he' j hj ↦ ?_
  -- Over a point `q` of the face of `e'`, the image is hit exactly when `q ∈ O ∩ e.source` and the
  -- two face germs agree at `q`; both conditions are open in `M`.
  have hset : faceSection he' hj ⁻¹' (faceSection he hi '' (Subtype.val ⁻¹' O)) =
      Subtype.val ⁻¹' (O ∩ e.source ∩ {x | J.faceGerm e i x = J.faceGerm e' j x}) := by
    ext ⟨q, hq⟩
    simp only [mem_preimage, mem_image, Subtype.exists, mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨p, hp, hpO, h⟩
      obtain ⟨hpq, hgerm⟩ := faceSection_eq_faceSection_iff.1 h
      obtain rfl : p = q := hpq
      exact ⟨⟨hpO, hp.1⟩, hgerm⟩
    · rintro ⟨⟨hqO, hqe⟩, h⟩
      exact ⟨q, ⟨hqe, extend_apply_eq_zero_of_faceGerm_eq h hq.2⟩, hqO,
        faceSection_eq_faceSection_iff.2 ⟨rfl, h⟩⟩
  rw [hset]
  exact ((hO.inter e.open_source).inter (isOpen_setOf_faceGerm_eq e e' i j)).preimage
    continuous_subtype_val

/-- **The faces of a chart are open pieces of the abstract boundary**: every face section is an
open embedding. -/
theorem isOpenEmbedding_faceSection : IsOpenEmbedding (faceSection he hi) :=
  .of_continuous_injective_isOpenMap continuous_faceSection faceSection_injective
    isOpenMap_faceSection

/-- The ranges of the face sections are open. -/
theorem isOpen_range_faceSection : IsOpen (range (faceSection he hi)) :=
  isOpenEmbedding_faceSection.isOpen_range

/-! #### The fibres of the map to `M` -/

variable {n : WithTop ℕ∞} [IsManifold J n M]

/-- **The fibre of the abstract boundary over a point of depth `d` has `d` points.** -/
theorem natCard_preimage_point (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}) (hn : n ≠ 0) (x : M) :
    Nat.card (point ⁻¹' {x} : Set (J.AbstractBoundary M)) = J.depth x := by
  rw [Nat.card_congr (preimagePointEquiv x), natCard_localFaces hJ hn]

/-- **The abstract boundary lies over the boundary**: the image of the map to `M` is
`J.boundary M`. -/
theorem range_point (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}) (hn : n ≠ 0) :
    range (point : J.AbstractBoundary M → M) = J.boundary M := by
  ext x
  -- Membership in `J.boundary M` is, by definition, being a boundary point.
  refine Iff.trans ?_ (localFaces_nonempty_iff hJ hn)
  exact ⟨fun ⟨b, hb⟩ ↦ hb ▸ ⟨b.face, b.face_mem⟩, fun ⟨F, hF⟩ ↦ ⟨⟨x, F, hF⟩, rfl⟩⟩

/-- Every point of the abstract boundary lies over a boundary point. -/
theorem point_mem_boundary (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}) (hn : n ≠ 0)
    (b : J.AbstractBoundary M) : b.point ∈ J.boundary M := by
  rw [← range_point hJ hn]
  exact mem_range_self b

/-- **The abstract boundary of a Hausdorff manifold with corners is Hausdorff.** -/
theorem t2Space [T2Space M] (hJ : range J = {z | ∀ i ∈ S, 0 ≤ z i}) (hn : n ≠ 0) :
    T2Space (J.AbstractBoundary M) := by
  refine ⟨fun b₁ b₂ hb ↦ ?_⟩
  by_cases hx : b₁.point = b₂.point
  · obtain ⟨e, he, i, hi, ⟨x, hxe, hix⟩, rfl⟩ := exists_faceSection_eq b₁
    obtain ⟨e', he', j, hj, ⟨y, hye, hjy⟩, rfl⟩ := exists_faceSection_eq b₂
    obtain rfl : x = y := hx
    -- The second face is, near `x`, a face `k ≠ i` of the first chart.
    obtain ⟨k, hk, hkx, hjk⟩ := exists_faceGerm_eq hJ hn (IsManifold.subset_maximalAtlas he)
      (IsManifold.subset_maximalAtlas he') hxe hye ((forall_mem_range_nonneg_iff hJ).1 hj) hjy
    refine ⟨range (faceSection he hi),
      range (faceSection he' hj) ∩
        point ⁻¹' (e.source ∩ {y | J.faceGerm e' j y = J.faceGerm e k y}),
      isOpen_range_faceSection, isOpen_range_faceSection.inter
        ((e.open_source.inter (isOpen_setOf_faceGerm_eq e' e j k)).preimage continuous_point),
      mem_range_self _, ⟨mem_range_self _, hxe, hjk⟩, ?_⟩
    rw [Set.disjoint_left]
    rintro _ ⟨⟨p, hp⟩, rfl⟩ ⟨⟨⟨q, hq⟩, hpq⟩, _, hp'⟩
    obtain ⟨hpq, hgerm⟩ := faceSection_eq_faceSection_iff.1 hpq.symm
    obtain rfl : p = q := hpq
    simp only [point_faceSection, mem_ofPred_eq] at hp'
    -- At `p` the faces `i` and `k` of `e` have the same germ, so `i = k`; then `b₁ = b₂`.
    have hik : i = k := eq_of_faceGerm_eq hJ hp.1 hp.2
      (extend_apply_eq_zero_of_faceGerm_eq hp'.symm hq.2) (hgerm.trans hp')
    subst hik
    exact hb (faceSection_eq_faceSection_iff.2 ⟨rfl, hjk.symm⟩)
  · obtain ⟨U, V, hU, hV, hbU, hbV, hUV⟩ := t2_separation hx
    exact ⟨_, _, hU.preimage continuous_point, hV.preimage continuous_point, hbU, hbV,
      hUV.preimage _⟩

end AbstractBoundary

/-! ### Manifolds with boundary -/

section HalfSpace

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (m + 1)) M] {n : WithTop ℕ∞} [IsManifold (𝓡∂ (m + 1)) n M]

/-- **On a manifold with boundary every point has at most one local face.** -/
theorem subsingleton_localFaces_modelWithCornersEuclideanHalfSpace (hn : n ≠ 0) (x : M) :
    ((𝓡∂ (m + 1)).localFaces x).Subsingleton := by
  have : Subsingleton
      {i // i ∈ ({0} : Set (Fin (m + 1))) ∧ (chartAt _ x).extend (𝓡∂ (m + 1)) x i = 0} :=
    ⟨fun a b ↦ Subtype.ext (a.2.1.trans b.2.1.symm)⟩
  exact Set.subsingleton_coe _ |>.1 <| (faceGermEquiv
    (range_modelWithCornersEuclideanHalfSpace_eq _) hn (IsManifold.chart_mem_maximalAtlas x)
    (mem_chart_source _ x)).symm.injective.subsingleton

namespace AbstractBoundary

/-- On a manifold with boundary, a point of the abstract boundary is determined by its point
of `M`. -/
theorem point_injective_modelWithCornersEuclideanHalfSpace (hn : n ≠ 0) :
    Injective (point : (𝓡∂ (m + 1)).AbstractBoundary M → M) := by
  rintro ⟨x, F, hF⟩ ⟨y, F', hF'⟩ (rfl : x = y)
  obtain rfl := subsingleton_localFaces_modelWithCornersEuclideanHalfSpace hn x hF hF'
  rfl

/-- On a manifold with boundary, the map from the abstract boundary to the boundary of `M` is
open. -/
theorem isOpenMap_codRestrict_point_modelWithCornersEuclideanHalfSpace (hn : n ≠ 0) :
    IsOpenMap (codRestrict (point : (𝓡∂ (m + 1)).AbstractBoundary M → M) _
      (point_mem_boundary (range_modelWithCornersEuclideanHalfSpace_eq _) hn)) := by
  have hJ := range_modelWithCornersEuclideanHalfSpace_eq (m + 1)
  intro U hU
  refine isOpen_iff_mem_nhds.2 ?_
  rintro _ ⟨b, hbU, rfl⟩
  obtain ⟨e, he, i, hi, p, rfl⟩ := exists_faceSection_eq b
  -- The only face coordinate of the half-space is `0`.
  obtain rfl : i = 0 := (forall_mem_range_nonneg_iff hJ).1 hi
  obtain ⟨O, hO, hOU⟩ := isOpen_induced_iff.1 (hU.preimage (continuous_faceSection (he := he)
    (hi := hi)))
  -- Near `p`, every boundary point in the chart and in `O` is the image of a point of `U`.
  refine mem_of_superset ((hO.inter e.open_source).preimage continuous_subtype_val
    |>.mem_nhds ⟨(hOU ▸ hbU : p ∈ Subtype.val ⁻¹' O), p.2.1⟩) ?_
  rintro ⟨y, hy⟩ ⟨hyO, hye⟩
  have hy0 : e.extend (𝓡∂ (m + 1)) y 0 = 0 := by
    simpa [OpenPartialHomeomorph.extend_coe] using
      (TauCeti.ModelWithCorners.mem_boundary_euclideanHalfSpace_iff_of_mem_atlas hn he hye).1 hy
  refine ⟨faceSection he hi ⟨y, hye, hy0⟩, ?_, rfl⟩
  rw [← mem_preimage, ← hOU]
  exact hyO

/-- **The abstract boundary of a manifold with boundary is its boundary.** For a manifold
modelled on the half-space, the map from the abstract boundary to `M` is a homeomorphism onto
the boundary `(𝓡∂ (m + 1)).boundary M`. -/
def homeomorphBoundary (hn : n ≠ 0) :
    (𝓡∂ (m + 1)).AbstractBoundary M ≃ₜ (𝓡∂ (m + 1)).boundary M :=
  Equiv.toHomeomorphOfContinuousOpen
    (.ofBijective _
      ⟨(injective_codRestrict _).2 (point_injective_modelWithCornersEuclideanHalfSpace hn),
        (surjective_codRestrict _).2
          (range_point (range_modelWithCornersEuclideanHalfSpace_eq _) hn)⟩)
    (continuous_point.codRestrict _)
    (isOpenMap_codRestrict_point_modelWithCornersEuclideanHalfSpace hn)

@[simp]
theorem coe_homeomorphBoundary_apply (hn : n ≠ 0) (b : (𝓡∂ (m + 1)).AbstractBoundary M) :
    (homeomorphBoundary hn b : M) = b.point :=
  (rfl)

end AbstractBoundary

end HalfSpace

end ModelWithCorners
