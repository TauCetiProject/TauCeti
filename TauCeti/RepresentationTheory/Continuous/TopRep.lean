/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude, Codex
-/
module

public import Mathlib.RepresentationTheory.Continuous.TopRep

/-!
# Transports between equal topological representations

This file supplements Mathlib's category `TopRep k G` of continuous representations with the
action of the transports `eqToHom h` along equalities `h : X = Y` of objects: on underlying
vectors they are casts of the carriers.

## Main results

* `TopRep.eqToHom_hom_apply`: a transport between equal objects casts the carrier.
* `TopRep.eqToHom_hom_comp_comp_eqToHom_hom_apply`: conjugating a morphism by transports between
  equal objects conjugates its underlying map by casts of the carriers.
-/

public section

namespace TopRep

open CategoryTheory

variable {k G : Type*} [Ring k] [TopologicalSpace k] [Monoid G]

-- Neither lemma is `@[simp]`: Mathlib's simp set turns casts of morphisms into `eqToHom`
-- (`CategoryTheory.congrArg_cast_hom_left`), and keeping `eqToHom` lets `eqToHom_refl` and
-- `eqToHom_trans` fire, so these are for explicit rewriting.

/-- For an equality `h : X = Y` of topological representations, the transport `eqToHom h` sends
`x : X` to its cast along the induced equality `X.V = Y.V` of carriers. -/
theorem eqToHom_hom_apply {X Y : TopRep k G} (h : X = Y) (x : X) :
    (eqToHom h).hom x = cast (congrArg TopRep.V h) x := by
  subst h
  rfl

/-- For equalities `hX : X' = X` and `hY : Y = Y'` of topological representations and a morphism
`f : X ⟶ Y`, the underlying map of `eqToHom hX ≫ f ≫ eqToHom hY` sends `x : X'` to the cast into
`Y'.V` of `f` applied to the cast of `x` into `X.V`. -/
theorem eqToHom_hom_comp_comp_eqToHom_hom_apply {X X' Y Y' : TopRep k G} (hX : X' = X)
    (hY : Y = Y') (f : X ⟶ Y) (x : X') :
    (((eqToHom hY).hom.comp f.hom).comp (eqToHom hX).hom) x =
      cast (congrArg TopRep.V hY) (f.hom (cast (congrArg TopRep.V hX) x)) := by
  subst hX hY
  rfl

end TopRep
