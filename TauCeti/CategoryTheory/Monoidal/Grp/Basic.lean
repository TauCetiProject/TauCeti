/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Mon

/-!
# Monomorphisms of group objects

A morphism of group objects is a monomorphism whenever its underlying morphism is a
monomorphism. The faithful forgetful functor reflects monomorphisms, so subobject constructions
can use monicity in the ambient category.
-/

public section

universe v u

namespace CategoryTheory.Grp

/-- A morphism of group objects is monic if its underlying morphism is monic. -/
instance (priority := 900) mono_of_mono_hom {C : Type u} [Category.{v} C]
    [CartesianMonoidalCategory C] {G H : Grp C} (f : G ⟶ H) [Mono f.hom.hom] : Mono f :=
  -- Forgetting inverses maps `f` to `f.hom` by definition.
  (Grp.forget₂Mon C).mono_of_mono_map (Mon.mono_of_mono_hom f.hom)

end CategoryTheory.Grp
