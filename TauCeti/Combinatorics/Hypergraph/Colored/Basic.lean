/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Set.PowersetCard

/-!
# Totally colored three-uniform hypergraphs

A `Colored3Graph κ V` assigns one color to each unordered three-element set of vertices.
In particular, symmetry is built into the domain of the coloring. An absent edge can be
represented by a distinguished palette value, so color-preserving injections preserve
nonedges as well as edges. No finiteness assumption on the vertex type or palette is needed.

Restriction along a vertex embedding is provided by `Colored3Graph.comap`.
`Colored3Graph.extend` adds vertices on top of a background coloring, which colors every new
triple; padding by one default color is the case of a constant background.
-/

public section

namespace TauCeti

/-- A total coloring of unordered triples. Nonedges, when present, are palette values. -/
@[ext]
structure Colored3Graph (κ : Type*) (V : Type*) where
  /-- The color of each three-element vertex set. -/
  color : Set.powersetCard V 3 → κ

namespace Colored3Graph

variable {κ V W U : Type*}

/-- The coloring in which every triple has color `c`. -/
def const (c : κ) : Colored3Graph κ V := ⟨fun _ ↦ c⟩

@[simp]
theorem color_const (c : κ) (s : Set.powersetCard V 3) :
    (const c : Colored3Graph κ V).color s = c := (rfl)

/-- Restrict a coloring along an injective vertex map. -/
def comap (H : Colored3Graph κ V) (f : W ↪ V) : Colored3Graph κ W where
  color s := H.color (Set.powersetCard.map 3 f s)

@[simp]
theorem color_comap (H : Colored3Graph κ V) (f : W ↪ V)
    (s : Set.powersetCard W 3) :
    (H.comap f).color s = H.color (Set.powersetCard.map 3 f s) := (rfl)

@[simp]
theorem comap_refl (H : Colored3Graph κ V) : H.comap (Function.Embedding.refl V) = H := by
  ext s
  simp

@[simp]
theorem comap_comap (H : Colored3Graph κ V) (f : W ↪ V) (g : U ↪ W) :
    (H.comap f).comap g = H.comap (g.trans f) := by
  ext s
  simp

@[simp]
theorem comap_const (c : κ) (f : W ↪ V) : (const c).comap f = const c := by
  ext s
  simp

/-- Extend a coloring along a vertex embedding on top of a background coloring `B` of the
larger vertex set: triples in the image keep their original color, and every triple not wholly
in the image takes its color in `B`. Padding by a single color `c` is the case `B = const c`. -/
noncomputable def extend (H : Colored3Graph κ V) (f : V ↪ W) (B : Colored3Graph κ W) :
    Colored3Graph κ W where
  color := Function.extend (Set.powersetCard.map 3 f) H.color B.color

/-- Extension preserves the color of every original triple. -/
@[simp]
theorem color_extend_map (H : Colored3Graph κ V) (f : V ↪ W) (B : Colored3Graph κ W)
    (s : Set.powersetCard V 3) :
    (H.extend f B).color (Set.powersetCard.map 3 f s) = H.color s := by
  simp only [extend]
  exact (Set.powersetCard.map_injective 3 f).extend_apply _ _ s

/-- A triple outside the image of the induced triple map receives its background color. -/
@[simp]
theorem color_extend_of_notMem_range (H : Colored3Graph κ V) (f : V ↪ W)
    (B : Colored3Graph κ W) (s : Set.powersetCard W 3)
    (hs : s ∉ Set.range (Set.powersetCard.map 3 f)) :
    (H.extend f B).color s = B.color s := by
  simp only [extend]
  exact Function.extend_apply' _ _ _ hs

/-- Restricting an extension to the original vertices recovers the original coloring. -/
@[simp]
theorem comap_extend (H : Colored3Graph κ V) (f : V ↪ W) (B : Colored3Graph κ W) :
    (H.extend f B).comap f = H := by
  ext s
  simp

/-- Extending along the identity embedding adds no triples. -/
@[simp]
theorem extend_refl (H B : Colored3Graph κ V) :
    H.extend (Function.Embedding.refl V) B = H := by
  simpa using H.comap_extend (Function.Embedding.refl V) B

/-- Extending the restriction of a coloring on top of that same coloring recovers it. -/
@[simp]
theorem extend_comap_self (B : Colored3Graph κ W) (f : V ↪ W) : (B.comap f).extend f B = B := by
  ext s
  by_cases hs : s ∈ Set.range (Set.powersetCard.map 3 f)
  · obtain ⟨t, rfl⟩ := hs
    simp
  · exact color_extend_of_notMem_range _ f B s hs

/-- Extending a constant coloring on top of the same constant coloring remains constant. -/
@[simp]
theorem extend_const (c : κ) (f : V ↪ W) :
    (const c : Colored3Graph κ V).extend f (const c) = const c := by
  simpa only [comap_const] using (const c : Colored3Graph κ W).extend_comap_self f

end Colored3Graph

end TauCeti
