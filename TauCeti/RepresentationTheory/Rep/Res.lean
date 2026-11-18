/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Rep.Res

/-!
# Functoriality lemmas for restriction of representations

In `Mathlib.RepresentationTheory.Rep.Res`, `Rep.resFunctor` is an abbreviation whose morphism map
reduces under `simp` to `Rep.resMap`. Once `(Rep.resFunctor f).map` unfolds to `Rep.resMap f`, the
generic functor lemmas `CategoryTheory.Functor.map_id`, `CategoryTheory.Functor.map_comp`, and
`CategoryTheory.eqToHom_map` no longer match. This file records those three laws directly for
`Rep.resMap` (avoiding the name `Rep.resMap_id`, which Mathlib uses for restriction along
`MonoidHom.id`).
-/

public section

universe t u v₁ v₂

variable {k : Type u} [Semiring k] {G : Type v₁} {H : Type v₂} [Monoid G] [Monoid H]

open CategoryTheory

namespace Rep

/-- Restricting the identity morphism of a representation gives the identity morphism of the
restricted representation. -/
@[simp]
theorem resMap_id' (f : H →* G) (X : Rep.{t} k G) :
    resMap f (𝟙 X) = 𝟙 (res f X) :=
  (resFunctor f).map_id X

/-- Restricting a composite of representation morphisms gives the composite of their
restrictions. -/
@[reassoc, simp]
theorem resMap_comp (f : H →* G) {X Y Z : Rep.{t} k G} (p : X ⟶ Y) (q : Y ⟶ Z) :
    resMap f (p ≫ q) = resMap f p ≫ resMap f q :=
  (resFunctor f).map_comp p q

/-- Restricting a transport morphism `eqToHom` gives the transport between the restricted
representations. Like `CategoryTheory.eqToHom_map`, this is not a `simp` lemma because rewriting
away `resMap` prevents naturality lemmas for restriction from matching. -/
theorem resMap_eqToHom (f : H →* G) {X Y : Rep.{t} k G} (h : X = Y) :
    resMap f (eqToHom h) = eqToHom (congrArg (res f) h) :=
  eqToHom_map (resFunctor f) h

end Rep
