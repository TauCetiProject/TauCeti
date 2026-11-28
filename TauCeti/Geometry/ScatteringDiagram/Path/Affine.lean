/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Antigravity (Gemini 4 Carbon)
-/
module

public import TauCeti.Geometry.ScatteringDiagram.Path.Basic

/-!
# Affine transport of admissible polygonal paths

A continuous affine equivalence sends an admissible segment to an admissible
segment for the image wall family, optionally reindexed along a wall-index
equivalence. The resulting quiver prefunctors transport polygonal paths using
Mathlib's `Prefunctor.mapPath`. Wall indices (up to the chosen equivalence),
affine crossing parameters and edge indices are retained, including repeated
visits and simultaneous crossings. No finiteness, closedness, codimension or
lattice hypothesis on the wall family is needed.

The construction uses Mathlib's affine-span transport and
`ContinuousAffineEquiv.intrinsicFrontier_image` to transport singular support.
It provides the geometric part of coordinate transport for wall crossings.

Adapted from `Mei/Geometry/Convex/Polyhedron/AffinePath.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`a79c57178cc83666fc244ca6e6eeaa722e9b8bc7` (Apache 2.0), with reindexed
wall-family transport added here.
Original copyright (c) 2026 Mei contributors; original author: Codex.
-/

public section

open Set

namespace TauCeti.WallComplement

variable {V U ι : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  {W : ι → Set V}

/-- Send an allowed vertex to the complement of the image wall family.
This abbreviation keeps the endpoints of transported continuous paths reducible. -/
abbrev map (x : WallComplement W) (e : V ≃ᴬ[ℝ] U) :
    WallComplement (fun i => e '' W i) where
  val := e x.val
  notMem i := by simpa only [e.injective.mem_set_image] using x.notMem i

@[simp]
theorem map_val (x : WallComplement W) (e : V ≃ᴬ[ℝ] U) :
    (x.map e).val = e x.val := (rfl)

/-- Coordinate transport preserves the entire indexed crossing set, at the same parameters. -/
@[simp]
theorem crossings_map (x y : WallComplement W) (e : V ≃ᴬ[ℝ] U) :
    crossings (x.map e) (y.map e) = crossings x y := by
  ext ⟨i, t⟩
  have hline : e (AffineMap.lineMap x.val y.val t) =
      AffineMap.lineMap (e x.val) (e y.val) t := e.toAffineEquiv.apply_lineMap _ _ _
  simp only [mem_crossings, ← hline, e.injective.mem_set_image]

/-- Affine coordinate changes preserve segment transversality and singular-support avoidance. -/
theorem AdmissibleSegment.map {x y : WallComplement W}
    (a : AdmissibleSegment x y) (e : V ≃ᴬ[ℝ] U) :
    AdmissibleSegment (x.map e) (y.map e) where
  transverse i hi := by
    obtain ⟨t, ht, hi⟩ := hi
    have hmeet := (mem_crossings (x.map e) (y.map e) i t).mpr ⟨ht, hi⟩
    rw [crossings_map, mem_crossings] at hmeet
    have htrans := a.transverse i ⟨t, hmeet⟩
    -- Convert the equivalence coercion to the affine-map coercion used by span transport.
    have hcoe : (e.toAffineEquiv.toAffineMap : V → U) = e := by rfl
    rw [map_val, map_val, ← hcoe, ← AffineSubspace.map_span e.toAffineEquiv.toAffineMap,
      AffineSubspace.map_direction]
    have hv : e.toAffineEquiv.linear (y.val - x.val) = e y.val - e x.val :=
      e.toAffineEquiv.toAffineMap.linear_apply_vsub _ _
    rw [hcoe, ← hv]
    exact fun hh => htrans (by simpa only [AffineEquiv.linear_toAffineMap,
      Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply] using hh)
  regular t ht := by
    have hline : e (AffineMap.lineMap x.val y.val t) =
        AffineMap.lineMap (e x.val) (e y.val) t := e.toAffineEquiv.apply_lineMap _ _ _
    have hs : singularSupport (fun i => e '' W i) = e '' singularSupport W :=
      e.singularSupport_image (Equiv.refl ι) (fun _ => rfl)
    simpa only [map_val, ← hline, hs, e.injective.mem_set_image] using a.regular t ht

section Reindex

variable {ι' : Type*} {W' : ι' → Set U}

/-- Transport an allowed vertex along a continuous affine equivalence together with a wall-index
equivalence `r : ι ≃ ι'` satisfying `∀ i, W' (r i) = e '' W i`. -/
abbrev mapReindex (x : WallComplement W) (e : V ≃ᴬ[ℝ] U) (r : ι ≃ ι')
    (hW : ∀ i, W' (r i) = e '' W i) : WallComplement W' where
  val := e x.val
  notMem i' := by
    obtain ⟨i, rfl⟩ := r.surjective i'
    rw [hW i, e.injective.mem_set_image]
    exact x.notMem i

/-- Reindexed affine transport sends each vertex to its ambient image under `e`. -/
@[simp]
theorem mapReindex_val (x : WallComplement W) (e : V ≃ᴬ[ℝ] U) (r : ι ≃ ι')
    (hW : ∀ i, W' (r i) = e '' W i) : (x.mapReindex e r hW).val = e x.val := (rfl)

/-- Reindexed affine coordinate transport maps wall crossings along `r : ι ≃ ι'` at the same
parameters. -/
theorem mem_crossings_mapReindex (x y : WallComplement W) (e : V ≃ᴬ[ℝ] U) (r : ι ≃ ι')
    (hW : ∀ i, W' (r i) = e '' W i) (i : ι) (t : ℝ) :
    (r i, t) ∈ crossings (x.mapReindex e r hW) (y.mapReindex e r hW) ↔
      (i, t) ∈ crossings x y := by
  obtain rfl := (r.eq_comp_symm W' _).mpr (funext hW)
  exact (mem_crossings_restrictPrefunctor (W := fun j => e '' W j) r.symm
    (x.map e) (y.map e) (r i) t).trans (by simp [crossings_map])

/-- Transporting along a continuous affine equivalence and a wall bijection preserves segment
admissibility. -/
theorem AdmissibleSegment.mapReindex {x y : WallComplement W} (a : AdmissibleSegment x y)
    (e : V ≃ᴬ[ℝ] U) (r : ι ≃ ι') (hW : ∀ i, W' (r i) = e '' W i) :
    AdmissibleSegment (x.mapReindex e r hW) (y.mapReindex e r hW) := by
  obtain rfl := (r.eq_comp_symm W' _).mpr (funext hW)
  exact ((restrictPrefunctor (fun j => e '' W j) r.symm).map ⟨a.map e⟩).down

/-- The quiver prefunctor transporting admissible segments along `e : V ≃ᴬ[ℝ] U` and `r : ι ≃ ι'`.
-/
abbrev mapReindexPrefunctor (e : V ≃ᴬ[ℝ] U) (r : ι ≃ ι') (hW : ∀ i, W' (r i) = e '' W i) :
    WallComplement W ⥤q WallComplement W' where
  obj x := x.mapReindex e r hW
  map a := ⟨a.down.mapReindex e r hW⟩

/-- Reindexed affine transport preserves reversal of segments. -/
instance (e : V ≃ᴬ[ℝ] U) (r : ι ≃ ι') (hW : ∀ i, W' (r i) = e '' W i) :
    (mapReindexPrefunctor e r hW).MapReverse where
  map_reverse' _ := Subsingleton.elim _ _

end Reindex

end TauCeti.WallComplement

namespace ContinuousAffineEquiv

open TauCeti

variable {V U ι : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  {W : ι → Set V}

/-- The quiver prefunctor that sends vertices and actual segments to their affine images.
Its object map is reducible so transported edges have the expected endpoints. -/
abbrev wallComplementPrefunctor (e : V ≃ᴬ[ℝ] U) :
    WallComplement W ⥤q WallComplement (fun i => e '' W i) where
  obj x := x.map e
  map a := ⟨a.down.map e⟩

@[simp]
theorem wallComplementPrefunctor_obj (e : V ≃ᴬ[ℝ] U) (x : WallComplement W) :
    (e.wallComplementPrefunctor).obj x = x.map e := (rfl)

/-- Affine transport preserves reversal of segments. -/
instance (e : V ≃ᴬ[ℝ] U) : (e.wallComplementPrefunctor (W := W)).MapReverse where
  map_reverse' _ := Subsingleton.elim _ _

end ContinuousAffineEquiv

namespace Quiver.Path

open TauCeti

variable {V U ι : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  {W : ι → Set V} {x y z : WallComplement W}

/-- Transport the actual segments of an admissible polygonal path to an image wall family. -/
def affineMap (p : AdmissiblePLPath x y) (e : V ≃ᴬ[ℝ] U) :
    AdmissiblePLPath (x.map e) (y.map e) :=
  e.wallComplementPrefunctor.mapPath p

/-- `affineMap` is `Prefunctor.mapPath` along `e.wallComplementPrefunctor`. -/
theorem affineMap_def (p : AdmissiblePLPath x y) (e : V ≃ᴬ[ℝ] U) :
    p.affineMap e = e.wallComplementPrefunctor.mapPath p := (rfl)

/-- Constant paths remain constant after transport. -/
@[simp]
theorem affineMap_nil (e : V ≃ᴬ[ℝ] U) :
    (nil : AdmissiblePLPath x x).affineMap e = nil := (rfl)

/-- Transport acts on each actual segment in a chain. -/
@[simp]
theorem affineMap_cons (p : AdmissiblePLPath x y) (a : y ⟶ z) (e : V ≃ᴬ[ℝ] U) :
    (p.cons a).affineMap e =
      (p.affineMap e).cons (e.wallComplementPrefunctor.map a) := (rfl)

/-- Transporting a single-edge path gives the single-edge path of the transported edge. -/
@[simp]
theorem affineMap_toPath (a : x ⟶ y) (e : V ≃ᴬ[ℝ] U) :
    a.toPath.affineMap e = (e.wallComplementPrefunctor.map a).toPath := (rfl)

/-- Affine transport commutes with path concatenation. -/
@[simp]
theorem affineMap_comp (p : AdmissiblePLPath x y) (q : AdmissiblePLPath y z)
    (e : V ≃ᴬ[ℝ] U) :
    (p.comp q).affineMap e = (p.affineMap e).comp (q.affineMap e) :=
  Prefunctor.mapPath_comp _ _ _

/-- Transport retains the number of segments. -/
@[simp]
theorem length_affineMap (p : AdmissiblePLPath x y) (e : V ≃ᴬ[ℝ] U) :
    (p.affineMap e).length = p.length :=
  Prefunctor.length_mapPath _ _

/-- Affine transport maps the path's vertices by `WallComplement.map`. -/
@[simp]
theorem vertices_affineMap (p : AdmissiblePLPath x y) (e : V ≃ᴬ[ℝ] U) :
    (p.affineMap e).vertices = p.vertices.map (·.map e) :=
  Prefunctor.vertices_mapPath _ _

/-- Affine transport maps the ambient vertex list by `e`. -/
theorem map_val_vertices_affineMap (p : AdmissiblePLPath x y) (e : V ≃ᴬ[ℝ] U) :
    (p.affineMap e).vertices.map WallComplement.val =
      (p.vertices.map WallComplement.val).map e := by
  simp only [vertices_affineMap, List.map_map, Function.comp_def]

/-- Reversing the transported chain is the transport of the reversed chain. -/
@[simp]
theorem affineMap_reverse (p : AdmissiblePLPath x y) (e : V ≃ᴬ[ℝ] U) :
    p.reverse.affineMap e = (p.affineMap e).reverse :=
  Prefunctor.mapPath_reverse e.wallComplementPrefunctor p

/-- Every crossing event retains its edge index, wall index and affine parameter. -/
@[simp]
theorem crossingEvents_affineMap (p : AdmissiblePLPath x y) (e : V ≃ᴬ[ℝ] U) :
    (p.affineMap e).crossingEvents = p.crossingEvents := by
  induction p with
  | nil => simp
  | cons p a ih =>
    ext ⟨j, i, t⟩
    simp only [affineMap_cons, mem_crossingEvents_cons, ih, length_affineMap,
      WallComplement.crossings_map]

/-- The continuous realization of a transported chain is the image of its realization. -/
@[simp]
theorem toContinuousPath_affineMap (p : AdmissiblePLPath x y) (e : V ≃ᴬ[ℝ] U) :
    (p.affineMap e).toContinuousPath = p.toContinuousPath.map e.continuous := by
  induction p with
  | nil => ext t; simp [Path.map_coe]
  | @cons y z p a ih =>
    rw [affineMap_cons, toContinuousPath_cons, toContinuousPath_cons, Path.map_trans, ih]
    congr 1
    ext t
    exact (e.toAffineEquiv.apply_lineMap y.val z.val t).symm

section Reindex

variable {ι' : Type*} {W' : ι' → Set U}

/-- Transport an admissible polygonal path along `e : V ≃ᴬ[ℝ] U` and a wall bijection `r : ι ≃ ι'`.
-/
abbrev affineMapReindex (p : AdmissiblePLPath x y) (e : V ≃ᴬ[ℝ] U) (r : ι ≃ ι')
    (hW : ∀ i, W' (r i) = e '' W i) :
    AdmissiblePLPath (x.mapReindex e r hW) (y.mapReindex e r hW) :=
  (WallComplement.mapReindexPrefunctor e r hW).mapPath p

/-- Reindexed affine transport maps the ambient vertex list by `e`. -/
theorem map_val_vertices_affineMapReindex (p : AdmissiblePLPath x y) (e : V ≃ᴬ[ℝ] U) (r : ι ≃ ι')
    (hW : ∀ i, W' (r i) = e '' W i) :
    (p.affineMapReindex e r hW).vertices.map WallComplement.val =
      (p.vertices.map WallComplement.val).map e := by
  simp only [Prefunctor.vertices_mapPath, List.map_map, Function.comp_def]

/-- When the target wall family is `(fun i => e '' W i) ∘ r.symm`, reindexed affine transport
factors as `affineMap e` followed by `WallComplement.restrictPrefunctor _ r.symm`. -/
theorem affineMapReindex_eq_restrictPrefunctor_mapPath_affineMap (p : AdmissiblePLPath x y)
    (e : V ≃ᴬ[ℝ] U) (r : ι ≃ ι') (hW : ∀ i, ((fun j => e '' W j) ∘ r.symm) (r i) = e '' W i) :
    p.affineMapReindex e r hW =
      (WallComplement.restrictPrefunctor (fun i => e '' W i) r.symm).mapPath (p.affineMap e) :=
  Prefunctor.mapPath_comp_apply e.wallComplementPrefunctor
    (WallComplement.restrictPrefunctor (fun i => e '' W i) r.symm) p

/-- Reindexed affine transport maps the wall index of every crossing event along `r : ι ≃ ι'` while
retaining its edge index and affine parameter. -/
@[simp]
theorem mem_crossingEvents_affineMapReindex (p : AdmissiblePLPath x y)
    (e : V ≃ᴬ[ℝ] U) (r : ι ≃ ι') (hW : ∀ i, W' (r i) = e '' W i)
    (j : ℕ) (i' : ι') (t : ℝ) :
    (j, i', t) ∈ (p.affineMapReindex e r hW).crossingEvents ↔
      (j, r.symm i', t) ∈ p.crossingEvents := by
  obtain rfl := (r.eq_comp_symm W' _).mpr (funext hW)
  rw [affineMapReindex_eq_restrictPrefunctor_mapPath_affineMap,
    mem_crossingEvents_restrictPrefunctor, crossingEvents_affineMap]

/-- Reindexed affine transport maps the continuous realization of a path by `e`. -/
@[simp]
theorem toContinuousPath_affineMapReindex (p : AdmissiblePLPath x y)
    (e : V ≃ᴬ[ℝ] U) (r : ι ≃ ι') (hW : ∀ i, W' (r i) = e '' W i) :
    (p.affineMapReindex e r hW).toContinuousPath = p.toContinuousPath.map e.continuous := by
  obtain rfl := (r.eq_comp_symm W' _).mpr (funext hW)
  rw [affineMapReindex_eq_restrictPrefunctor_mapPath_affineMap,
    toContinuousPath_restrictPrefunctor, toContinuousPath_affineMap]

/-- Reindexed affine transport along `Equiv.refl ι` agrees with `affineMap`. -/
@[simp]
theorem affineMapReindex_refl (p : AdmissiblePLPath x y) (e : V ≃ᴬ[ℝ] U) :
    p.affineMapReindex e (Equiv.refl ι) (fun _ => rfl) = p.affineMap e := (rfl)

end Reindex

end Quiver.Path

