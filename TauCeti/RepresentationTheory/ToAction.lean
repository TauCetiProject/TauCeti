/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Action.Concrete
public import Mathlib.RepresentationTheory.Basic

/-!
# The `G`-set underlying a representation

A representation `ρ` of a monoid `G` on a `Λ`-module `M` makes `M` a `G`-set, with `g` acting by
`ρ g`. This is `Representation.toAction ρ : Action (Type u) G`.

## Main definitions

* `Representation.toAction ρ`: the `G`-set underlying a representation.
-/

public section

open CategoryTheory

universe u

namespace Representation

variable {G : Type u} [Monoid G] {Λ : Type*} [CommSemiring Λ] {M : Type u} [AddCommMonoid M]
  [Module Λ M] (ρ : Representation Λ G M)

/-- The `G`-set underlying a representation `ρ` of `G`: `g` acts on `M` by `ρ g`. -/
@[expose]
def toAction : Action (Type u) G :=
  letI := MulAction.compHom M ρ
  Action.ofMulAction G M

/-- The underlying type of `ρ.toAction` is the module of `ρ`. -/
theorem toAction_V : ρ.toAction.V = M :=
  (rfl)

/-- In `ρ.toAction`, `g` acts by `ρ g`. -/
@[simp]
theorem toAction_ρ_apply (g : G) (m : ρ.toAction.V) : ρ.toAction.ρ g m = ρ g m :=
  (rfl)

end Representation
