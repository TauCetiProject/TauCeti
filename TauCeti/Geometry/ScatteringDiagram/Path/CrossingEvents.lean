/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Geometry.ScatteringDiagram.Path.Basic
public import Mathlib.Data.Finset.Sort

/-!
# Simultaneous signed wall crossings

For an arbitrary finite wall family, an admissible segment may cross several
coplanar walls at once. The strictly ordered crossing times index nonempty finite
sets of signed wall indices. Coincident indexed walls remain distinct members of
one event; no ordering of the wall indices is chosen. Every wall in an event has
the same affine span, and a wall occurs at at most one time on a segment.

Signs are the exponents for left wall actions: positive normal velocity gives
`-1`, and negative normal velocity gives `1`. Reversal reverses the event list
and negates every sign. Polygonal paths concatenate the lists, retaining separate
visits, so these events can be used to form products of commuting coplanar labels.

The construction uses the existing geometric `WallComplement.crossings` and
Mathlib's `Finset.sort`; its order is on crossing times alone.

## Attribution

Adapted in full from `Mei/Geometry/Convex/Polyhedron/CrossingEvents.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), at
`9cf969cdee9748087aae45dbf4888a130890655c` (Apache 2.0).
Original author credit is retained.
-/

public section

noncomputable section

open Set

namespace TauCeti.WallComplement

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite ι]
  {W : ι → Set V} (x y : WallComplement W)

/-- All wall indices crossed at the specified affine parameter, including coincident walls. -/
def crossingWalls (t : ℝ) : Finset ι :=
  (Set.toFinite {i | (i, t) ∈ crossings x y}).toFinset

/-- Event membership records the actual indexed geometric crossing. -/
@[simp]
theorem mem_crossingWalls (t : ℝ) (i : ι) :
    i ∈ crossingWalls x y t ↔ (i, t) ∈ crossings x y := by
  simp [crossingWalls]

/-- Segment reversal reflects event times, without changing their wall indices. -/
theorem crossingWalls_swap (t : ℝ) :
    crossingWalls y x t = crossingWalls x y (1 - t) := by
  ext i
  exact (mem_crossingWalls y x t i).trans
    ((mem_crossings_swap x y i t).trans (mem_crossingWalls x y (1 - t) i).symm)

variable {x y}

/-- The distinct crossing times in strictly increasing order. -/
def orderedCrossingTimes (e : x ⟶ y) : List ℝ :=
  ((e.down.finite_crossings.image Prod.snd).toFinset).sort (· ≤ ·)

/-- Each time appears once, regardless of the number of walls crossed there. -/
@[simp]
theorem mem_orderedCrossingTimes (e : x ⟶ y) (t : ℝ) :
    t ∈ orderedCrossingTimes e ↔ ∃ i, (i, t) ∈ crossings x y := by
  simp [orderedCrossingTimes, Set.mem_image, Prod.exists, eq_comm]

/-- Events have strictly increasing times. -/
theorem pairwise_orderedCrossingTimes (e : x ⟶ y) :
    (orderedCrossingTimes e).Pairwise (· < ·) := by
  exact (Finset.sortedLT_sort ((e.down.finite_crossings.image Prod.snd).toFinset)).pairwise

/-- Every listed event crosses at least one wall. -/
theorem crossingWalls_nonempty (e : x ⟶ y) {t : ℝ}
    (ht : t ∈ orderedCrossingTimes e) : (crossingWalls x y t).Nonempty := by
  simpa only [Finset.nonempty_def, mem_crossingWalls] using
    (mem_orderedCrossingTimes e t).mp ht

/-- Crossings occur strictly between the allowed endpoints. -/
theorem mem_Ioo_of_mem_orderedCrossingTimes (e : x ⟶ y) {t : ℝ}
    (ht : t ∈ orderedCrossingTimes e) : t ∈ Ioo (0 : ℝ) 1 := by
  obtain ⟨i, hi⟩ := (mem_orderedCrossingTimes e t).mp ht
  obtain ⟨ht, hi⟩ := (mem_crossings x y i t).mp hi
  exact (e.down.crossing_mem_intrinsicInterior ht hi).1

/-- Two different event times have disjoint wall-index sets on a segment. -/
theorem disjoint_crossingWalls (e : x ⟶ y) {s t : ℝ} (hst : s ≠ t) :
    Disjoint (crossingWalls x y s) (crossingWalls x y t) := by
  classical
  apply Finset.disjoint_left.mpr
  intro i hs ht
  exact hst (e.down.subsingleton_crossing i
    ((mem_crossings x y i s).mp ((mem_crossingWalls x y s i).mp hs))
    ((mem_crossings x y i t).mp ((mem_crossingWalls x y t i).mp ht)))

/-- Simultaneous crossings have equal affine spans, since the path avoids singular support. -/
theorem affineSpan_eq_of_mem_crossingWalls (e : x ⟶ y) {t : ℝ} {i j : ι}
    (hi : i ∈ crossingWalls x y t) (hj : j ∈ crossingWalls x y t) :
    affineSpan ℝ (W i) = affineSpan ℝ (W j) := by
  obtain ⟨ht, hi⟩ := (mem_crossings x y i t).mp ((mem_crossingWalls x y t i).mp hi)
  obtain ⟨_, hj⟩ := (mem_crossings x y j t).mp ((mem_crossingWalls x y t j).mp hj)
  exact affineSpan_eq_of_notMem_singularSupport (e.down.regular t ht) hi hj

/-- Reversal reverses the distinct crossing times and reflects each parameter in `1/2`. -/
theorem orderedCrossingTimes_reverse (e : x ⟶ y) :
    orderedCrossingTimes (Quiver.reverse e) =
      (orderedCrossingTimes e).reverse.map (fun t => 1 - t) := by
  have hp : ((orderedCrossingTimes e).reverse.map (fun t => 1 - t)).Pairwise (· < ·) := by
    apply List.pairwise_map.mpr
    exact (pairwise_orderedCrossingTimes e).reverse.imp (by intros; linarith)
  apply (pairwise_orderedCrossingTimes (Quiver.reverse e)).eq_of_mem_iff hp
  intro t
  rw [mem_orderedCrossingTimes]
  simp only [List.mem_map, List.mem_reverse]
  have hm : (∃ i, (i, t) ∈ crossings y x) ↔ ∃ i, (i, 1 - t) ∈ crossings x y :=
    exists_congr fun i => mem_crossings_swap x y i t
  rw [hm]
  constructor
  · intro ht
    exact ⟨1 - t, (mem_orderedCrossingTimes e _).mpr ht, by simp⟩
  · rintro ⟨s, hs, rfl⟩
    simpa only [sub_sub_cancel] using (mem_orderedCrossingTimes e s).mp hs

variable (ν : ι → V →ₗ[ℝ] ℝ)

/-- The finite signed set at a crossing time; signs are exponents for left actions. -/
def signedCrossingEvent (x y : WallComplement W) (t : ℝ) : Finset (ι × ℤ) := by
  classical
  exact (crossingWalls x y t).image
    (fun i => (i, if 0 < ν i (y.val - x.val) then -1 else 1))

open Classical in
/-- A signed event is the image of the crossed wall indices with their prescribed exponents. -/
theorem signedCrossingEvent_def (x y : WallComplement W) (t : ℝ) :
    signedCrossingEvent ν x y t = (crossingWalls x y t).image
      (fun i => (i, if 0 < ν i (y.val - x.val) then -1 else 1)) := (rfl)

/-- A signed event retains every wall index and its prescribed crossing exponent. -/
@[simp]
theorem mem_signedCrossingEvent (x y : WallComplement W) (t : ℝ) (i : ι) (s : ℤ) :
    (i, s) ∈ signedCrossingEvent ν x y t ↔
      (i, t) ∈ crossings x y ∧ s = if 0 < ν i (y.val - x.val) then -1 else 1 := by
  classical
  simp [signedCrossingEvent, eq_comm]

/-- Positive rescaling of the normal representatives preserves each signed event. -/
@[simp]
theorem signedCrossingEvent_smul (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (x y : WallComplement W) (t : ℝ) :
    signedCrossingEvent (fun i => r i • ν i) x y t = signedCrossingEvent ν x y t := by
  ext ⟨i, s⟩
  simp [mul_pos_iff_of_pos_left (hr i)]

/-- Reversal negates all crossing exponents while retaining the event's wall indices. -/
theorem signedCrossingEvent_swap
    (hν : ∀ i, LinearMap.ker (ν i) = (affineSpan ℝ (W i)).direction)
    (e : x ⟶ y) (t : ℝ) :
    signedCrossingEvent ν y x t =
      (signedCrossingEvent ν x y (1 - t)).map
        (Equiv.prodCongr (Equiv.refl ι) (Equiv.neg ℤ)).toEmbedding := by
  classical
  ext ⟨i, s⟩
  have hv (hi : (i, 1 - t) ∈ crossings x y) : ν i (y.val - x.val) ≠ 0 := by
    intro hz
    obtain ⟨ht, hi⟩ := (mem_crossings x y i (1 - t)).mp hi
    apply e.down.transverse i ⟨_, ht, hi⟩
    rw [← hν i]
    exact hz
  have he : ν i (x.val - y.val) = -ν i (y.val - x.val) := by simp [map_sub]
  simp only [Finset.mem_map, Prod.exists, Equiv.toEmbedding_apply, Equiv.prodCongr_apply,
    Prod.map_apply, Equiv.refl_apply, Equiv.neg_apply, Prod.mk.injEq, mem_signedCrossingEvent]
  rw [mem_crossings_swap x y i t]
  constructor
  · rintro ⟨hi, rfl⟩
    refine ⟨i, (if 0 < ν i (y.val - x.val) then -1 else 1), ⟨hi, rfl⟩, rfl, ?_⟩
    rcases lt_or_gt_of_ne (hv hi) with hn | hn
    · simp only [he, neg_pos.mpr hn, not_lt_of_ge hn.le, ↓reduceIte]
    · simp only [he, not_lt_of_ge (neg_nonpos.mpr hn.le), hn, ↓reduceIte, neg_neg]
  · rintro ⟨j, r, ⟨hi, rfl⟩, rfl, rfl⟩
    refine ⟨hi, ?_⟩
    rcases lt_or_gt_of_ne (hv hi) with hn | hn
    · simp only [he, neg_pos.mpr hn, not_lt_of_ge hn.le, ↓reduceIte]
    · simp only [he, not_lt_of_ge (neg_nonpos.mpr hn.le), hn, ↓reduceIte, neg_neg]

/-- The signed crossing events of a segment in traversal order, grouped by time. -/
def segmentCrossingEvents (e : x ⟶ y) : List (Finset (ι × ℤ)) :=
  (orderedCrossingTimes e).map (signedCrossingEvent ν x y)

/-- Read the signed set at each successive crossing time, in increasing time order. -/
theorem segmentCrossingEvents_def (e : x ⟶ y) :
    segmentCrossingEvents ν e =
      (orderedCrossingTimes e).map (signedCrossingEvent ν x y) := (rfl)

/-- A segment has no crossing events exactly when it meets no wall. -/
@[simp]
theorem segmentCrossingEvents_eq_nil_iff (e : x ⟶ y) :
    segmentCrossingEvents ν e = [] ↔ crossings x y = ∅ := by
  rw [segmentCrossingEvents_def, List.map_eq_nil_iff, List.eq_nil_iff_forall_not_mem,
    Set.eq_empty_iff_forall_notMem]
  simp only [mem_orderedCrossingTimes, not_exists, Prod.forall]
  exact forall_comm

/-- An event on the list is precisely the signed set at one actual crossing time. -/
theorem mem_segmentCrossingEvents (e : x ⟶ y) (S : Finset (ι × ℤ)) :
    S ∈ segmentCrossingEvents ν e ↔
      ∃ t ∈ orderedCrossingTimes e, signedCrossingEvent ν x y t = S := by
  simp [segmentCrossingEvents]

/-- No empty event is inserted in a segment's event list. -/
theorem nonempty_of_mem_segmentCrossingEvents (e : x ⟶ y) {S : Finset (ι × ℤ)}
    (hS : S ∈ segmentCrossingEvents ν e) : S.Nonempty := by
  classical
  obtain ⟨t, ht, rfl⟩ := (mem_segmentCrossingEvents ν e S).mp hS
  simpa only [signedCrossingEvent, Finset.image_nonempty] using crossingWalls_nonempty e ht

/-- Every indexed crossing is retained in a signed event, and no new crossing is added. -/
theorem exists_mem_segmentCrossingEvents_iff (e : x ⟶ y) (i : ι) (s : ℤ) :
    (∃ S ∈ segmentCrossingEvents ν e, (i, s) ∈ S) ↔
      (∃ t, (i, t) ∈ crossings x y) ∧
        s = if 0 < ν i (y.val - x.val) then -1 else 1 := by
  simp only [mem_segmentCrossingEvents]
  constructor
  · rintro ⟨S, ⟨t, _, rfl⟩, hi⟩
    obtain ⟨hi, hs⟩ := (mem_signedCrossingEvent ν x y t i s).mp hi
    exact ⟨⟨t, hi⟩, hs⟩
  · rintro ⟨⟨t, ht⟩, hs⟩
    exact ⟨_, ⟨t, (mem_orderedCrossingTimes e t).mpr ⟨i, ht⟩, rfl⟩,
      (mem_signedCrossingEvent ν x y t i s).mpr ⟨ht, hs⟩⟩

/-- A reversed segment traverses the events backwards with every exponent negated. -/
theorem segmentCrossingEvents_reverse
    (hν : ∀ i, LinearMap.ker (ν i) = (affineSpan ℝ (W i)).direction)
    (e : x ⟶ y) :
    segmentCrossingEvents ν (Quiver.reverse e) =
      (segmentCrossingEvents ν e).reverse.map
        (fun S => S.map (Equiv.prodCongr (Equiv.refl ι) (Equiv.neg ℤ)).toEmbedding) := by
  simp only [segmentCrossingEvents, orderedCrossingTimes_reverse, List.map_map,
    List.map_reverse, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro t _
  simpa only [sub_sub_cancel] using signedCrossingEvent_swap ν hν e (1 - t)

/-- A segment's events depend on coorientations, independently of their positive scale. -/
@[simp]
theorem segmentCrossingEvents_smul (r : ι → ℝ) (hr : ∀ i, 0 < r i) (e : x ⟶ y) :
    segmentCrossingEvents (fun i => r i • ν i) e = segmentCrossingEvents ν e := by
  simp only [segmentCrossingEvents_def]
  apply List.map_congr_left
  intro t _
  exact signedCrossingEvent_smul ν r hr x y t

end TauCeti.WallComplement

namespace Quiver.Path

open TauCeti WallComplement

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite ι]
  {W : ι → Set V} {x y z : WallComplement W}

/-- Signed events along a polygonal path; simultaneous walls form one event, while
successive visits remain separate entries. -/
def signedCrossingEvents (ν : ι → V →ₗ[ℝ] ℝ) :
    {y : WallComplement W} → AdmissiblePLPath x y → List (Finset (ι × ℤ))
  | _, .nil => []
  | _, .cons p e => signedCrossingEvents ν p ++ segmentCrossingEvents ν e

@[simp]
theorem signedCrossingEvents_nil (ν : ι → V →ₗ[ℝ] ℝ) :
    (Quiver.Path.nil : AdmissiblePLPath x x).signedCrossingEvents ν = [] := (rfl)

@[simp]
theorem signedCrossingEvents_cons (ν : ι → V →ₗ[ℝ] ℝ)
    (p : AdmissiblePLPath x y) (e : y ⟶ z) :
    (p.cons e).signedCrossingEvents ν =
      p.signedCrossingEvents ν ++ segmentCrossingEvents ν e := (rfl)

/-- Concatenation appends the event lists in traversal order. -/
@[simp]
theorem signedCrossingEvents_comp (ν : ι → V →ₗ[ℝ] ℝ)
    (p : AdmissiblePLPath x y) (q : AdmissiblePLPath y z) :
    (p.comp q).signedCrossingEvents ν =
      p.signedCrossingEvents ν ++ q.signedCrossingEvents ν := by
  induction q with
  | nil => simp
  | cons q e ih => simp [ih, List.append_assoc]

/-- Every event of a polygonal path contains at least one signed wall index. -/
theorem nonempty_of_mem_signedCrossingEvents (ν : ι → V →ₗ[ℝ] ℝ)
    (p : AdmissiblePLPath x y) {S : Finset (ι × ℤ)}
    (hS : S ∈ p.signedCrossingEvents ν) : S.Nonempty := by
  induction p with
  | nil => simp at hS
  | cons p e ih =>
    rcases List.mem_append.mp hS with hp | he
    · exact ih hp
    · exact nonempty_of_mem_segmentCrossingEvents ν e he

/-- A wall recorded by a path in a convex region meets that region. It suffices
to check the vertices, since every crossing lies on one of the path's segments. -/
theorem inter_nonempty_of_mem_signedCrossingEvents (p : AdmissiblePLPath x y)
    (ν : ι → V →ₗ[ℝ] ℝ) {U : Set V} (hU : Convex ℝ U)
    (hp : ∀ z ∈ p.vertices, z.val ∈ U) {S : Finset (ι × ℤ)}
    (hS : S ∈ p.signedCrossingEvents ν) {a : ι × ℤ} (ha : a ∈ S) :
    (U ∩ W a.1).Nonempty := by
  induction p with
  | nil => simp at hS
  | @cons y z p e ih =>
    have hp' : ∀ w ∈ p.vertices, w.val ∈ U :=
      fun w hw => hp w ((Quiver.Path.mem_vertices_cons p e).mpr (Or.inl hw))
    rcases List.mem_append.mp hS with hS | hS
    · exact ih hp' hS
    · obtain ⟨t, _, rfl⟩ := (mem_segmentCrossingEvents ν e S).mp hS
      obtain ⟨ht, _⟩ := (mem_signedCrossingEvent ν y z t a.1 a.2).mp ha
      obtain ⟨ht, hwall⟩ := (mem_crossings y z a.1 t).mp ht
      exact ⟨_, hU.lineMap_mem (hp' y p.end_mem_vertices)
        (hp z ((Quiver.Path.mem_vertices_cons p e).mpr (Or.inr rfl))) ht, hwall⟩

/-- Reversing a polygonal path reverses its events and negates their exponents. -/
@[simp]
theorem signedCrossingEvents_reverse (ν : ι → V →ₗ[ℝ] ℝ)
    (hν : ∀ i, LinearMap.ker (ν i) = (affineSpan ℝ (W i)).direction)
    (p : AdmissiblePLPath x y) :
    p.reverse.signedCrossingEvents ν =
      (p.signedCrossingEvents ν).reverse.map
        (fun S => S.map (Equiv.prodCongr (Equiv.refl ι) (Equiv.neg ℤ)).toEmbedding) := by
  induction p with
  | nil => simp [Quiver.Path.reverse]
  | cons p e ih =>
    simp [Quiver.Path.reverse, Quiver.Hom.toPath, ih,
      segmentCrossingEvents_reverse ν hν]

/-- Positive rescaling of each coorientation preserves all polygonal signed events. -/
@[simp]
theorem signedCrossingEvents_smul (ν : ι → V →ₗ[ℝ] ℝ)
    (r : ι → ℝ) (hr : ∀ i, 0 < r i) (p : AdmissiblePLPath x y) :
    p.signedCrossingEvents (fun i => r i • ν i) = p.signedCrossingEvents ν := by
  induction p with
  | nil => simp
  | cons p e ih => simp [ih, segmentCrossingEvents_smul ν r hr]

end Quiver.Path
