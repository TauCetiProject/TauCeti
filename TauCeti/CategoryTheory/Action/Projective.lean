/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import TauCeti.CategoryTheory.Action.Basic

/-!
# The left regular `G`-set is projective

For a monoid `G`, a map of `G`-sets out of the left regular `G`-set is the orbit map of the image
of `1` (`CategoryTheory.Action.leftRegularHom_hom_one`), and a point lifts along any epimorphism of
`G`-sets, since epimorphisms of `G`-sets are surjective. Hence `Action.leftRegular G` is a
projective object of `Action (Type u) G` (`TauCeti.projective_leftRegular`).
-/

public section

open CategoryTheory

universe u

namespace TauCeti

variable {G : Type u} [Monoid G]

/-- The left regular `G`-set is projective: a map out of it is the orbit map of the image of `1`,
and this point lifts along any epimorphism. -/
instance projective_leftRegular : Projective (Action.leftRegular G) where
  factors {X Y} f e _ := by
    -- The forgetful functor preserves epimorphisms, so `e` is surjective.
    obtain ⟨x, hx⟩ : ∃ x, e.hom x = f.hom (1 : G) :=
      surjective_of_epi ((Action.forget (Type u) G).map e) _
    refine ⟨Action.leftRegularHom x, ?_⟩
    rw [Action.leftRegularHom_comp, hx, Action.leftRegularHom_hom_one]

end TauCeti
