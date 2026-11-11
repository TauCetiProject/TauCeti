/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.AffineSpace.Transverse
public import TauCeti.Geometry.ScatteringDiagram.Path.Generic
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
public import Mathlib.Analysis.Convex.PathConnected
public import TauCeti.Combinatorics.Quiver.Prefunctor
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Admissible polygonal paths through wall families

These are the generic paths along which the ordered wall crossings of a
scattering diagram, and hence its wall-crossing words and path-ordered
products, are read off.

Vertices lie off every wall. Edges avoid singular support and are transverse
to each wall they meet. Admissible polygonal paths are Mathlib quiver paths
on these vertices: constant paths, concatenation and reversal use the existing
`Quiver.Path` operations and laws. Their continuous realizations concatenate
`Path.segment`s. By `Convex.admissibleSegment_of_disjoint_singularSupport`,
segments between off-wall points of a convex set avoiding singular support are admissible.

For a finite family, the crossing events (segment index, wall index and affine
parameter) form a finite set. Thus repeated visits and simultaneous coplanar
crossings are retained. Every crossing lies in the relative
interior of its wall. In finite dimension, finite families of codimension-one
polyhedra admit such paths between any two allowed endpoints, with two edges
sufficing and all vertices in any prescribed open set containing the endpoints.
A function that is locally constant off the walls takes equal values at the
endpoints of a segment meeting no wall, by connectedness of the unit interval.

Adapted from `Mei/Geometry/Convex/Polyhedron/AdmissiblePath.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`a79c57178cc83666fc244ca6e6eeaa722e9b8bc7` (Apache 2.0).
Original copyright (c) 2026 Mei contributors; original author: Codex.
-/

public section

open Set
open scoped unitInterval

namespace TauCeti

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A vertex outside every member of a wall family. -/
@[ext]
structure WallComplement (W : ι → Set V) where
  /-- The ambient point. -/
  val : V
  /-- The point lies on no wall. -/
  notMem : ∀ i, val ∉ W i

namespace WallComplement

variable {W : ι → Set V}

/-- An admissible segment avoids singular support and is transverse to each
wall it meets. Disjoint segments, including constant segments, need no rank condition. -/
structure AdmissibleSegment (x y : WallComplement W) : Prop where
  /-- A meeting segment has direction outside the wall direction. -/
  transverse : ∀ i, (∃ t ∈ Icc (0 : ℝ) 1, AffineMap.lineMap x.val y.val t ∈ W i) →
    y.val - x.val ∉ (affineSpan ℝ (W i)).direction
  /-- All points of the segment avoid the actual singular support. -/
  regular : ∀ t ∈ Icc (0 : ℝ) 1,
    AffineMap.lineMap x.val y.val t ∉ singularSupport W

/-- Admissible segments are the edges of the quiver of allowed vertices. -/
instance : Quiver (WallComplement W) where
  Hom x y := PLift (AdmissibleSegment x y)

/-- The wall indices and affine crossing parameters of one segment. -/
def crossings (x y : WallComplement W) : Set (ι × ℝ) :=
  {p | p.2 ∈ Icc (0 : ℝ) 1 ∧ AffineMap.lineMap x.val y.val p.2 ∈ W p.1}

/-- The characteristic membership test for segment crossings. -/
@[simp]
theorem mem_crossings (x y : WallComplement W) (i : ι) (t : ℝ) :
    (i, t) ∈ crossings x y ↔
      t ∈ Icc (0 : ℝ) 1 ∧ AffineMap.lineMap x.val y.val t ∈ W i := Iff.rfl

/-- A segment between off-wall vertices crosses walls only at strictly interior parameters. -/
theorem mem_Ioo_of_mem_crossings {x y : WallComplement W} {i : ι} {t : ℝ}
    (h : (i, t) ∈ crossings x y) : t ∈ Ioo (0 : ℝ) 1 := by
  obtain ⟨ht, hi⟩ := (mem_crossings _ _ _ _).mp h
  have hzero : t ≠ 0 := by intro he; exact x.notMem i (by simpa [he] using hi)
  have hone : t ≠ 1 := by intro he; exact y.notMem i (by simpa [he] using hi)
  exact ⟨lt_of_le_of_ne ht.1 (Ne.symm hzero), lt_of_le_of_ne ht.2 hone⟩

/-- Traversing a segment backwards replaces each crossing parameter `t` by `1 - t`. -/
theorem mem_crossings_swap (x y : WallComplement W) (i : ι) (t : ℝ) :
    (i, t) ∈ crossings y x ↔ (i, 1 - t) ∈ crossings x y := by
  simp only [mem_crossings, AffineMap.lineMap_apply_one_sub, mem_Icc]
  constructor <;> rintro ⟨⟨h₀, h₁⟩, hi⟩ <;> exact ⟨⟨by linarith, by linarith⟩, hi⟩

/-- A crossing at `t` gives a crossing at `1 - t` when the segment is reversed. -/
theorem mem_crossings_swap_of_mem {x y : WallComplement W} {i : ι} {t : ℝ}
    (h : (i, t) ∈ crossings x y) : (i, 1 - t) ∈ crossings y x :=
  (mem_crossings_swap x y i (1 - t)).mpr (by simpa only [sub_sub_cancel] using h)

/-- Reversing a segment preserves the existence of a crossing of each wall. -/
theorem exists_mem_crossings_swap {x y : WallComplement W} {i : ι} :
    (∃ t, (i, t) ∈ crossings y x) ↔ ∃ t, (i, t) ∈ crossings x y :=
  ⟨fun ⟨t, ht⟩ => ⟨1 - t, mem_crossings_swap_of_mem ht⟩,
    fun ⟨t, ht⟩ => ⟨1 - t, mem_crossings_swap_of_mem ht⟩⟩

/-- The crossings of the reversed segment are those of the segment, with
parameter `t` replaced by `1 - t`. -/
theorem crossings_swap (x y : WallComplement W) :
    crossings y x = (fun a : ι × ℝ => (a.1, 1 - a.2)) '' crossings x y := by
  ext ⟨i, t⟩
  rw [mem_crossings_swap]
  constructor
  · intro h
    exact ⟨(i, 1 - t), h, by simp⟩
  · rintro ⟨⟨j, s⟩, hs, he⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    simpa only [sub_sub_cancel] using hs

namespace AdmissibleSegment

variable {x y : WallComplement W}

/-- A segment meeting no closed wall is admissible, with no transversality condition. -/
theorem of_crossings_eq_empty (hclosed : ∀ i, IsClosed (W i))
    (he : crossings x y = ∅) : AdmissibleSegment x y where
  transverse i hi := by
    obtain ⟨t, ht, hi⟩ := hi
    have hm : (i, t) ∈ crossings x y := ⟨ht, hi⟩
    simp [he] at hm
  regular t ht hs := by
    obtain ⟨i, hi⟩ := mem_iUnion.mp (singularSupport_subset_iUnion W hclosed hs)
    have hm : (i, t) ∈ crossings x y := ⟨ht, hi⟩
    simp [he] at hm

/-- A stationary segment at an allowed point outside singular support is admissible. -/
theorem refl (x : WallComplement W) (hx : x.val ∉ singularSupport W) :
    AdmissibleSegment x x where
  transverse i hi := by
    obtain ⟨t, _, hi⟩ := hi
    exact (x.notMem i (by simpa using hi)).elim
  regular t _ := by simpa only [AffineMap.lineMap_same_apply] using hx

/-- Reversing an admissible segment preserves its geometric conditions. -/
theorem symm (h : AdmissibleSegment x y) : AdmissibleSegment y x where
  transverse i hi := by
    obtain ⟨t, ht, hti⟩ := hi
    have ht' : 1 - t ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [ht.1, ht.2]
    have hd := h.transverse i
      ⟨1 - t, ht', by simpa only [AffineMap.lineMap_apply_one_sub] using hti⟩
    intro hh
    apply hd
    simpa only [neg_sub] using (affineSpan ℝ (W i)).direction.neg_mem hh
  regular t ht := by
    have ht' : 1 - t ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [ht.1, ht.2]
    simpa only [AffineMap.lineMap_apply_one_sub] using h.regular (1 - t) ht'

/-- An edge crosses a given wall at at most one affine parameter. -/
theorem subsingleton_crossing (h : AdmissibleSegment x y) (i : ι) :
    {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ AffineMap.lineMap x.val y.val t ∈ W i}.Subsingleton := by
  intro s hs t ht
  exact (affineSpan ℝ (W i)).subsingleton_preimage_lineMap
    (h.transverse i ⟨s, hs.1, hs.2⟩)
    (subset_affineSpan ℝ (W i) hs.2) (subset_affineSpan ℝ (W i) ht.2)

/-- Every crossing is at a strictly interior parameter and in the relative
interior of its wall. -/
theorem crossing_mem_intrinsicInterior (h : AdmissibleSegment x y)
    {i : ι} {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hi : AffineMap.lineMap x.val y.val t ∈ W i) :
    t ∈ Ioo (0 : ℝ) 1 ∧ AffineMap.lineMap x.val y.val t ∈ intrinsicInterior ℝ (W i) := by
  refine ⟨mem_Ioo_of_mem_crossings ((mem_crossings _ _ _ _).mpr ⟨ht, hi⟩), ?_⟩
  rw [← intrinsicClosure_sdiff_intrinsicFrontier]
  refine ⟨subset_intrinsicClosure hi, ?_⟩
  intro hb
  exact h.regular t ht (mem_singularSupport.mpr (Or.inl ⟨i, hb⟩))

/-- A list of distinct actual crossing events cannot repeat a wall index on one
admissible segment. Simultaneous crossings of different walls are allowed. -/
theorem nodup_crossing_indices (h : AdmissibleSegment x y) {l : List (ι × ℝ)}
    (hl : l.Nodup) (hmem : ∀ c ∈ l, c ∈ crossings x y) :
    (l.map Prod.fst).Nodup := by
  apply hl.map_on
  rintro ⟨i, t⟩ ht ⟨j, s⟩ hs hij
  dsimp at hij
  subst j
  exact Prod.ext rfl (h.subsingleton_crossing i
    ((mem_crossings x y i t).mp (hmem _ ht)) ((mem_crossings x y i s).mp (hmem _ hs)))

/-- A segment has countably many indexed crossings for a countable wall family. -/
theorem countable_crossings [Countable ι] (h : AdmissibleSegment x y) :
    (crossings x y).Countable := by
  refine Set.countable_of_injective_of_countable_image (f := Prod.fst) ?_ (Set.to_countable _)
  rintro ⟨i, t⟩ ht ⟨j, s⟩ hs hij
  dsimp at hij
  subst j
  exact Prod.ext rfl (h.subsingleton_crossing i
    ((mem_crossings x y i t).mp ht) ((mem_crossings x y i s).mp hs))

/-- A segment has finitely many indexed crossings for a finite wall family. -/
theorem finite_crossings [Finite ι] (h : AdmissibleSegment x y) : (crossings x y).Finite := by
  have heq : crossings x y = ⋃ i, Prod.mk i ''
      {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ AffineMap.lineMap x.val y.val t ∈ W i} := by
    ext ⟨i, t⟩
    simp
  rw [heq]
  exact Set.finite_iUnion fun i => (h.subsingleton_crossing i).finite.image _

end AdmissibleSegment

/-- A chosen crossing parameter of wall `i` along `[x, y]`, or zero if there is no crossing.
On an admissible segment this is the unique crossing parameter whenever the wall is met. -/
noncomputable def crossingTime (x y : WallComplement W) (i : ι) : ℝ := by
  classical
  exact if h : ∃ t, (i, t) ∈ crossings x y then h.choose else 0

/-- The chosen crossing parameter is a crossing whenever the wall is met. -/
theorem mem_crossings_crossingTime {x y : WallComplement W} {i : ι}
    (h : ∃ t, (i, t) ∈ crossings x y) : (i, crossingTime x y i) ∈ crossings x y := by
  classical
  simpa only [crossingTime, h, dite_true] using h.choose_spec

/-- The crossing parameter defaults to zero for walls not met by the segment. -/
theorem crossingTime_eq_zero_of_not_exists {x y : WallComplement W} {i : ι}
    (h : ¬∃ t, (i, t) ∈ crossings x y) : crossingTime x y i = 0 := by
  classical
  simp only [crossingTime, h, dite_false]

/-- Every crossing on an admissible segment occurs at the chosen crossing parameter. -/
theorem eq_crossingTime_of_mem {x y : WallComplement W} (e : x ⟶ y) {i : ι} {t : ℝ}
    (ht : (i, t) ∈ crossings x y) : t = crossingTime x y i :=
  e.down.subsingleton_crossing i ((mem_crossings _ _ _ _).mp ht)
    ((mem_crossings _ _ _ _).mp (mem_crossings_crossingTime ⟨t, ht⟩))

/-- A function that is locally constant at every point off the walls takes the same
value at the two endpoints of a segment meeting no wall. -/
theorem apply_eq_of_crossings_eq_empty {Y : Type*} {F : V → Y}
    (hF : ∀ θ, (∀ i, θ ∉ W i) → ∀ᶠ φ in nhds θ, F φ = F θ) {x y : WallComplement W}
    (he : crossings x y = ∅) : F x.val = F y.val := by
  have hc : Continuous fun r : I => AffineMap.lineMap x.val y.val (r : ℝ) :=
    AffineMap.lineMap_continuous.comp continuous_subtype_val
  have hf : IsLocallyConstant fun r : I => F (AffineMap.lineMap x.val y.val (r : ℝ)) := by
    refine (IsLocallyConstant.iff_eventually_eq _).mpr fun r =>
      (hc.tendsto r).eventually (p := fun φ => F φ = F _) (hF _ fun i hi => ?_)
    have hr : (i, (r : ℝ)) ∈ crossings x y := ⟨r.property, hi⟩
    simp [he] at hr
  simpa using hf.apply_eq_of_preconnectedSpace 0 1

/-- Forget walls along an index map, keeping the same vertices and affine segments.
Mathlib's `Prefunctor.mapPath` extends this operation to polygonal paths. -/
-- Objects must compute when comparing the same path in nested wall families.
abbrev restrictPrefunctor {κ : Type*} (W : ι → Set V) (f : κ → ι) :
    WallComplement W ⥤q WallComplement (W ∘ f) where
  obj x := ⟨x.val, fun j => x.notMem (f j)⟩
  map e := ⟨{
    transverse j hj := e.down.transverse (f j) hj
    regular t ht := fun hs => e.down.regular t ht (singularSupport_comp_subset W f hs) }⟩

/-- Forgetting walls leaves every vertex at the same ambient point. -/
@[simp]
theorem restrictPrefunctor_obj_val {κ : Type*} (W : ι → Set V) (f : κ → ι)
    (x : WallComplement W) : ((restrictPrefunctor W f).obj x).val = x.val := (rfl)

/-- Forgetting walls preserves the entire ambient vertex list. -/
theorem vertices_restrictPrefunctor {κ : Type*} (W : ι → Set V) (f : κ → ι)
    {x y : WallComplement W} (p : Quiver.Path x y) :
    ((restrictPrefunctor W f).mapPath p).vertices.map WallComplement.val =
      p.vertices.map WallComplement.val := by
  simp only [Prefunctor.vertices_mapPath, List.map_map, Function.comp_def]

/-- Reversal of segments makes the allowed-vertex quiver symmetric. -/
instance : Quiver.HasInvolutiveReverse (WallComplement W) where
  reverse' e := ⟨e.down.symm⟩
  inv' _ := PLift.ext (Subsingleton.elim _ _)

end WallComplement

/-- A finite chain of admissible affine segments between allowed endpoints.
The zero-edge path is the constant path. Concatenation and reversal are the
operations `Quiver.Path.comp` and `Quiver.Path.reverse`. -/
abbrev AdmissiblePLPath {W : ι → Set V} (x y : WallComplement W) := Quiver.Path x y

end TauCeti

namespace Quiver.Path

open TauCeti

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {W : ι → Set V} {x y z : WallComplement W}

/-- Realize a finite admissible chain as a continuous path. -/
noncomputable def toContinuousPath :
    {y : WallComplement W} → AdmissiblePLPath x y → _root_.Path x.val y.val
  | _, .nil => Path.refl x.val
  | _, @Quiver.Path.cons _ _ _ u v p _ => (toContinuousPath p).trans (Path.segment u.val v.val)

/-- The realization of the zero-edge chain is constant. -/
@[simp]
theorem toContinuousPath_nil :
    toContinuousPath (Quiver.Path.nil : AdmissiblePLPath x x) = Path.refl x.val := (rfl)

/-- Appending an edge realizes as concatenation with its straight segment. -/
@[simp]
theorem toContinuousPath_cons (p : AdmissiblePLPath x y) (e : y ⟶ z) :
    toContinuousPath (p.cons e) = (toContinuousPath p).trans (Path.segment y.val z.val) := (rfl)

/-- Forgetting walls preserves the continuous realization of a path. -/
@[simp]
theorem toContinuousPath_restrictPrefunctor {κ : Type*} (f : κ → ι)
    (p : AdmissiblePLPath x y) :
    toContinuousPath ((WallComplement.restrictPrefunctor W f).mapPath p) =
      toContinuousPath p := by
  induction p with
  | nil => rfl
  | cons p e ih => simp only [Prefunctor.mapPath_cons, toContinuousPath_cons, ih]

/-- Realizing concatenation agrees with continuous path concatenation up to
the usual homotopies of reparametrization. -/
theorem toContinuousPath_comp_homotopic (p : AdmissiblePLPath x y) (q : AdmissiblePLPath y z) :
    (toContinuousPath (p.comp q)).Homotopic ((toContinuousPath p).trans (toContinuousPath q)) := by
  induction q with
  | nil =>
    rw [Quiver.Path.comp_nil, toContinuousPath_nil]
    exact (Path.Homotopic.trans_refl _).symm
  | @cons u v q e ih =>
    rw [Quiver.Path.comp_cons, toContinuousPath_cons, toContinuousPath_cons]
    exact (ih.hcomp (.refl (Path.segment u.val v.val))).trans
      (Path.Homotopic.trans_assoc _ _ _)

/-- Realizing reversal agrees, up to reparametrization homotopy, with reversal
of the continuous realization. -/
theorem toContinuousPath_reverse_homotopic (p : AdmissiblePLPath x y) :
    (toContinuousPath p.reverse).Homotopic (toContinuousPath p).symm := by
  induction p with
  | nil => exact .refl _
  | @cons u v p e ih =>
    have he : (toContinuousPath (Quiver.reverse e).toPath).Homotopic
        (Path.segment v.val u.val) := by
      rw [Quiver.Hom.toPath, toContinuousPath_cons, toContinuousPath_nil]
      exact Path.Homotopic.refl_trans _
    have h := (toContinuousPath_comp_homotopic (Quiver.reverse e).toPath p.reverse).trans
      (he.hcomp ih)
    simpa only [Quiver.Path.reverse, toContinuousPath_cons, Path.trans_symm,
      Path.segment_symm] using h

/-- A continuous realization starting off singular support avoids it. -/
theorem toContinuousPath_notMem_singularSupport (p : AdmissiblePLPath x y)
    (hx : x.val ∉ singularSupport W) (t : unitInterval) :
    toContinuousPath p t ∉ singularSupport W := by
  induction p generalizing t with
  | nil =>
    rw [toContinuousPath_nil, Path.refl_apply]
    exact hx
  | @cons u v p e ih =>
    have hr : (toContinuousPath p).trans (Path.segment u.val v.val) t ∈
        Set.range (toContinuousPath p) ∪ Set.range (Path.segment u.val v.val) := by
      rw [← Path.trans_range]
      exact Set.mem_range_self t
    rcases hr with ⟨s, hs⟩ | ⟨s, hs⟩
    · simpa only [toContinuousPath_cons, ← hs] using ih s
    · simpa only [toContinuousPath_cons, ← hs, Path.segment_apply] using
        e.down.regular s.val s.property

/-- For closed walls, the continuous realization avoids singular support. -/
theorem toContinuousPath_notMem_singularSupport_of_isClosed (p : AdmissiblePLPath x y)
    (hclosed : ∀ i, IsClosed (W i)) (t : unitInterval) :
    toContinuousPath p t ∉ singularSupport W := by
  refine p.toContinuousPath_notMem_singularSupport (fun hs => ?_) t
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (singularSupport_subset_iUnion W hclosed hs)
  exact x.notMem i hi

/-- Indexed crossing events retain the edge number, wall index and affine
parameter. Distinct visits to the same geometric point remain distinct. -/
def crossingEvents : {y : WallComplement W} → AdmissiblePLPath x y → Set (ℕ × (ι × ℝ))
  | _, .nil => ∅
  | _, @Quiver.Path.cons _ _ _ u v p _ => crossingEvents p ∪
      Prod.mk p.length '' WallComplement.crossings u v

/-- A constant chain has no crossing events. -/
@[simp]
theorem crossingEvents_nil :
    crossingEvents (Quiver.Path.nil : AdmissiblePLPath x x) = ∅ := (rfl)

/-- Appending an edge adds exactly its indexed crossings. -/
@[simp]
theorem mem_crossingEvents_cons (p : AdmissiblePLPath x y) (e : y ⟶ z)
    (j : ℕ) (i : ι) (t : ℝ) :
    (j, i, t) ∈ crossingEvents (p.cons e) ↔
      (j, i, t) ∈ crossingEvents p ∨ j = p.length ∧ (i, t) ∈ WallComplement.crossings y z := by
  simp [crossingEvents, eq_comm, and_assoc, and_left_comm, and_comm]

/-- Restricting the wall family retains exactly the crossings of the selected walls,
with the same edge indices and affine parameters. -/
@[simp]
theorem mem_crossingEvents_restrictPrefunctor {κ : Type*} (f : κ → ι)
    (p : AdmissiblePLPath x y) (j : ℕ) (k : κ) (t : ℝ) :
    (j, k, t) ∈ crossingEvents ((WallComplement.restrictPrefunctor W f).mapPath p) ↔
      (j, f k, t) ∈ crossingEvents p := by
  induction p with
  | nil => simp
  | cons p e ih =>
    simp only [Prefunctor.mapPath_cons, mem_crossingEvents_cons, ih,
      Prefunctor.length_mapPath, WallComplement.mem_crossings, Function.comp_apply]

/-- A single edge records exactly its segment crossings, all at edge index zero. -/
@[simp]
theorem crossingEvents_toPath (e : x ⟶ y) :
    e.toPath.crossingEvents = Prod.mk 0 '' WallComplement.crossings x y := by
  ext ⟨j, i, t⟩
  simp [Quiver.Hom.toPath, mem_crossingEvents_cons, and_comm, eq_comm]

/-- Concatenation shifts the second path's edge indices by the first path's
length and retains all crossings of both paths. -/
@[simp]
theorem crossingEvents_comp (p : AdmissiblePLPath x y) (q : AdmissiblePLPath y z) :
    crossingEvents (p.comp q) = crossingEvents p ∪
      (fun a : ℕ × (ι × ℝ) => (p.length + a.1, a.2)) '' crossingEvents q := by
  induction q with
  | nil => simp
  | @cons u v q e ih =>
    simp only [Quiver.Path.comp_cons, crossingEvents, ih, Set.image_union,
      Set.image_image, Quiver.Path.length_comp, Set.union_assoc]

/-- Every crossing event occurs on one of the path's edges. -/
theorem lt_length_of_mem_crossingEvents (p : AdmissiblePLPath x y)
    {a : ℕ × (ι × ℝ)} (ha : a ∈ crossingEvents p) : a.1 < p.length := by
  induction p with
  | nil => simp at ha
  | cons p e ih =>
    rw [Quiver.Path.length_cons]
    simp only [crossingEvents] at ha
    rcases ha with ha | ⟨b, _, rfl⟩
    · exact Nat.lt_succ_of_lt (ih ha)
    · exact Nat.lt_succ_self _

/-- Reversal sends the crossing at parameter `t` on edge `j` to the crossing at
parameter `1 - t` on edge `p.length - 1 - j`. -/
@[simp]
theorem mem_crossingEvents_reverse (p : AdmissiblePLPath x y) (j : ℕ) (i : ι) (t : ℝ) :
    (j, i, t) ∈ crossingEvents p.reverse ↔
      j < p.length ∧ (p.length - 1 - j, i, 1 - t) ∈ crossingEvents p := by
  induction p generalizing j with
  | nil => simp [Quiver.Path.reverse]
  | @cons u v p e ih =>
    simp only [Quiver.Path.reverse, crossingEvents_comp, Quiver.Hom.toPath, Set.mem_union,
      mem_crossingEvents_cons, Quiver.Path.length_cons, crossingEvents_nil,
      Quiver.Path.length_nil]
    rw [WallComplement.mem_crossings_swap]
    rcases j with _ | j
    · simp only [Set.mem_empty_iff_false, false_or, Nat.zero_lt_succ, true_and,
        Nat.add_one_sub_one, Nat.sub_zero, Set.mem_image, Prod.mk.injEq]
      constructor
      · rintro (h | ⟨⟨k, b⟩, -, hk, -⟩)
        · exact Or.inr h
        · omega
      · rintro (h | h)
        · exact absurd (lt_length_of_mem_crossingEvents p h) (lt_irrefl _)
        · exact Or.inl h
    · simp only [Set.mem_empty_iff_false, false_or, Nat.add_one_ne_zero, false_and,
        Set.mem_image, Prod.mk.injEq, Nat.add_lt_add_iff_right]
      have hindex : p.length + 1 - 1 - (j + 1) = p.length - 1 - j := by omega
      constructor
      · rintro ⟨⟨k, b⟩, hk, hj, rfl⟩
        obtain rfl : j = k := by omega
        obtain ⟨hjl, hk⟩ := (ih j).mp hk
        refine ⟨hjl, Or.inl ?_⟩
        rwa [hindex]
      · rintro ⟨hjl, h | ⟨h, -⟩⟩
        · refine ⟨(j, i, t), (ih j).mpr ⟨hjl, ?_⟩, by omega, rfl⟩
          rwa [hindex] at h
        · omega

/-- A finite wall family gives finitely many crossing events along every
admissible polygonal path, even with repeated visits or coincident walls. -/
theorem finite_crossingEvents [Finite ι] (p : AdmissiblePLPath x y) :
    (crossingEvents p).Finite := by
  induction p with
  | nil => exact Set.finite_empty
  | cons p e ih =>
    exact ih.union (e.down.finite_crossings.image (Prod.mk p.length))

end Quiver.Path

namespace TauCeti.AdmissiblePLPath

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {W : ι → Set V}

/-- Allowed endpoints in an open set, for a finite family of codimension-one
polyhedra, admit an admissible chain with exactly two edges whose vertices all lie
in that set. The set need not be convex. -/
theorem exists_length_eq_two_vertices_mem_of_isOpen [FiniteDimensional ℝ V] [Finite ι]
    (hpoly : ∀ i, TauCeti.IsConvexPolyhedron (W i))
    (hdim : ∀ i, Module.finrank ℝ (affineSpan ℝ (W i)).direction + 1 = Module.finrank ℝ V)
    {U : Set V} (hU : IsOpen U) {x y : WallComplement W} (hx : x.val ∈ U) (hy : y.val ∈ U) :
    ∃ p : AdmissiblePLPath x y, p.length = 2 ∧ ∀ z ∈ p.vertices, z.val ∈ U := by
  obtain ⟨v, hvU, hv, htrans, hreg⟩ := exists_mem_open_two_transverse_lineMaps
    W hpoly hdim x.notMem y.notMem hU ⟨x.val, hx⟩
  let z : WallComplement W := ⟨v, hv⟩
  have hxz : WallComplement.AdmissibleSegment x z :=
    ⟨fun i _ => (htrans i).1, fun t _ => (hreg t).1⟩
  have hyz : WallComplement.AdmissibleSegment y z :=
    ⟨fun i _ => (htrans i).2, fun t _ => (hreg t).2⟩
  refine ⟨((Quiver.Path.nil : AdmissiblePLPath x x).cons (PLift.up hxz)).cons
    (PLift.up hyz.symm), rfl, ?_⟩
  simp only [Quiver.Path.mem_vertices_cons, Quiver.Path.vertices_nil, List.mem_singleton]
  rintro w ((rfl | rfl) | rfl)
  · exact hx
  · exact hvU
  · exact hy

/-- Allowed endpoints in a finite family of codimension-one polyhedra admit
an admissible chain with exactly two edges. -/
theorem exists_length_eq_two [FiniteDimensional ℝ V] [Finite ι]
    (hpoly : ∀ i, TauCeti.IsConvexPolyhedron (W i))
    (hdim : ∀ i, Module.finrank ℝ (affineSpan ℝ (W i)).direction + 1 = Module.finrank ℝ V)
    (x y : WallComplement W) : ∃ p : AdmissiblePLPath x y, p.length = 2 :=
  (exists_length_eq_two_vertices_mem_of_isOpen hpoly hdim isOpen_univ
    (mem_univ x.val) (mem_univ y.val)).imp fun _ hp => hp.1

end TauCeti.AdmissiblePLPath

namespace Convex

open TauCeti TauCeti.WallComplement

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {W : ι → Set V} {K : Set V}

/-- A segment between off-wall points of a convex set missing the singular support of a
wall family is admissible. -/
theorem admissibleSegment_of_disjoint_singularSupport (hK : Convex ℝ K)
    (hKW : Disjoint K (singularSupport W))
    {x y : WallComplement W} (hx : x.val ∈ K)
    (hy : y.val ∈ K) : AdmissibleSegment x y where
  transverse i := by
    rintro ⟨t, ht, hti⟩ hd
    have hmeet : (K ∩ W i).Nonempty := ⟨_, hK.lineMap_mem hx hy ht, hti⟩
    apply x.notMem i
    apply hK.inter_affineSpan_subset hmeet
      (Set.disjoint_left.mpr fun w hw hf =>
        hKW.notMem_of_mem_left hw (mem_singularSupport.mpr (Or.inl ⟨i, hf⟩)))
    refine ⟨hx, ?_⟩
    have hx' : x.val = (-t) • (y.val - x.val) +ᵥ AffineMap.lineMap x.val y.val t := by
      simp only [AffineMap.lineMap_apply_module, vadd_eq_add]
      module
    rw [hx']
    exact AffineSubspace.vadd_mem_of_mem_direction
      ((affineSpan ℝ (W i)).direction.smul_mem _ hd) (subset_affineSpan ℝ _ hti)
  regular t ht := hKW.notMem_of_mem_left (hK.lineMap_mem hx hy ht)

end Convex
