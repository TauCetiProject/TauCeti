/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import TauCeti.CategoryTheory.Monoidal.Grp.Basic

/-!
# Monomorphisms of group objects over a base

A morphism of group objects in a slice category is a monomorphism whenever its underlying
morphism in the original category is a monomorphism. This follows by reflecting monomorphisms
through the two faithful forgetful functors. In particular, closed immersions of group schemes
are monomorphisms without any affineness assumption.
-/

public section

universe v u

namespace CategoryTheory.Grp

/-- A morphism of group objects over a base is monic if its underlying morphism is monic. -/
instance (priority := 900) mono_of_mono_left {C : Type u} [Category.{v} C] {X : C}
    [CartesianMonoidalCategory (Over X)] {G H : Grp (Over X)} (f : G ⟶ H)
    [Mono f.hom.hom.left] : Mono f :=
  -- Forgetting inverses maps `f` to `f.hom` by definition.
  (Grp.forget₂Mon _).mono_of_mono_map (Mon.mono_of_mono_left f.hom)

end CategoryTheory.Grp
