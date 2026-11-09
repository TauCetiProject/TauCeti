/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.CategoryTheory.Endomorphism

/-!
# Morphisms in a groupoid form a torsor under the vertex group

In any category the endomorphisms of `Y` act on the morphisms `X ⟶ Y` by postcomposition,
`r • f = f ≫ r` (Mathlib's `CategoryTheory.End.mulActionRight`). In a groupoid this action is
free and transitive: two morphisms `f g : X ⟶ Y` differ by the unique endomorphism
`f /ₛ g = g⁻¹ ≫ f` of `Y`. So whenever `X ⟶ Y` is nonempty it is a torsor under the vertex group
`End Y` (`CategoryTheory.End.torsorRight`).

For the fundamental groupoid of a space this says that the homotopy classes of paths from `x` to
`y` form a torsor under the fundamental group at `y`. Applied to the fundamental groupoid of a loop
space, it says that the homotopy classes of null-homotopies of a contractible loop form a torsor
under the second homotopy group.
-/

public section

namespace CategoryTheory.End

variable {C : Type*} [Groupoid C] {X Y : C}

/-- The endomorphism of `Y` relating two morphisms `f g : X ⟶ Y` of a groupoid:
`f /ₛ g = g⁻¹ ≫ f`, so that `(f /ₛ g) • g = f`. -/
instance sdivRight : SDiv (End Y) (X ⟶ Y) where
  sdiv f g := .of (Groupoid.inv g ≫ f)

@[simp]
theorem sdiv_asHom (f g : X ⟶ Y) : (f /ₛ g).asHom = inv g ≫ f :=
  congrArg (· ≫ f) (Groupoid.inv_eq_inv g)

/-- **Morphisms in a groupoid form a torsor under the vertex group.** If there is a morphism
`X ⟶ Y`, then `End Y` acts freely and transitively on `X ⟶ Y` by postcomposition. -/
instance torsorRight [Nonempty (X ⟶ Y)] : Torsor (End Y) (X ⟶ Y) where
  sdiv_smul' f g := by simp [End.smul_right]
  smul_sdiv' r f := by ext; simp [End.smul_right]

end CategoryTheory.End
