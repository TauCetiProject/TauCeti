/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Quiver.Prefunctor

/-!
# Embeddings of quivers

A `TauCeti.QuiverEmbedding` models a subquiver, which need not be full, by a prefunctor injective
on vertices and on each set of arrows. Its vertex fibers have at most one point; this lets
constructions such as extension by zero index their values over a vertex without choosing a
preimage.
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

/-- Two quiver embeddings are equal when their vertex and arrow maps agree. -/
@[ext (iff := false)]
theorem ext {ψ : QuiverEmbedding Q' Q} (h_obj : ∀ u, φ.obj u = ψ.obj u)
    (h_map : ∀ (u u' : Q') (a : u ⟶ u'),
      φ.map a = Eq.recOn (h_obj u').symm (Eq.recOn (h_obj u).symm (ψ.map a))) : φ = ψ := by
  have h : φ.toPrefunctor = ψ.toPrefunctor := Prefunctor.ext h_obj h_map
  cases φ with
  | mk φ hp ha =>
    cases ψ with
    | mk ψ hp' ha' =>
      cases h
      rfl

/-- The vertices of `Q'` over a vertex `v` of `Q`. There is at most one, since `φ` is injective
on vertices. -/
abbrev Fiber (v : Q) : Type v' := {u : Q' // φ.obj u = v}

/-- Each vertex fiber of an embedding contains at most one point. -/
instance (v : Q) : Subsingleton (φ.Fiber v) :=
  ⟨fun a b ↦ Subtype.ext (φ.obj_injective (a.2.trans b.2.symm))⟩

end QuiverEmbedding

end TauCeti
