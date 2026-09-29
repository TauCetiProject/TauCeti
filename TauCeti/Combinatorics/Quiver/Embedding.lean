/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Quiver.Path

/-!
# Embeddings of quivers

A `TauCeti.QuiverEmbedding` is a prefunctor injective on vertices and on each set of arrows.
Its image is a subquiver, which need not be full. The fiber over a vertex has at most one point.
-/

public section

namespace TauCeti

universe v w v' w'

/-- A prefunctor injective on vertices and on arrows between each pair of vertices. Its image is a
subquiver that need not be full. -/
structure QuiverEmbedding (Q' : Type v') [Quiver.{w'} Q'] (Q : Type v) [Quiver.{w} Q] extends
    Prefunctor Q' Q where
  /-- The embedding is injective on vertices. -/
  obj_injective : Function.Injective obj
  /-- The embedding is injective on the arrows between each pair of vertices. -/
  map_injective {a b : Q'} : Function.Injective (map : (a ⟶ b) → (obj a ⟶ obj b))

namespace QuiverEmbedding

variable {Q' : Type v'} [Quiver.{w'} Q'] {Q : Type v} [Quiver.{w} Q] (φ : QuiverEmbedding Q' Q)

/-- The vertices of `Q'` over a vertex `v` of `Q`. There is at most one, since `φ` is injective
on vertices. -/
abbrev Fiber (v : Q) : Type v' := {u : Q' // φ.obj u = v}

instance (v : Q) : Subsingleton (φ.Fiber v) :=
  ⟨fun a b ↦ Subtype.ext (φ.obj_injective (a.2.trans b.2.symm))⟩

end QuiverEmbedding

end TauCeti
