/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.PowersetCard

/-!
# Totally colored three-uniform hypergraphs

A `Colored3Graph κ V` assigns one color to each unordered three-element set of vertices.
In particular, symmetry is built into the domain of the coloring. An absent edge can be
represented by a distinguished palette value, so color-preserving injections preserve
nonedges as well as edges. No finiteness assumption on the vertex type or palette is needed.

Restriction along a vertex embedding is provided by `Colored3Graph.comap`.
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
  simp [Set.powersetCard.map]

@[simp]
theorem comap_comap (H : Colored3Graph κ V) (f : W ↪ V) (g : U ↪ W) :
    (H.comap f).comap g = H.comap (g.trans f) := by
  ext s
  simp [Set.powersetCard.map, Finset.map_map]

@[simp]
theorem comap_const (c : κ) (f : W ↪ V) : (const c).comap f = const c := by
  ext s
  simp

end Colored3Graph

end TauCeti
