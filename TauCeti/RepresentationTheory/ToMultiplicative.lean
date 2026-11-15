/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Basic

/-!
# Representations as multiplicative automorphisms

`Representation.toMulAut` views a representation of a group on a module
as an action by automorphisms on its multiplicative type tag. This lets the representation act
on exponents in a group algebra via `MonoidAlgebra.domCongrAut`.
-/

public section

namespace Representation

variable {R G M : Type*} [Semiring R] [Group G] [AddCommMonoid M] [Module R M]

/-- A representation, acting by automorphisms in multiplicative notation: `g` acts on
`Multiplicative M` by `ofAdd m ↦ ofAdd (ρ g m)`. -/
def toMulAut (ρ : Representation R G M) : G →* MulAut (Multiplicative M) where
  toFun g :=
    { toFun m := .ofAdd (ρ g m.toAdd)
      invFun m := .ofAdd (ρ g⁻¹ m.toAdd)
      left_inv m := by simp
      right_inv m := by simp
      map_mul' m n := map_add (ρ g) m.toAdd n.toAdd }
  map_one' := by ext; simp
  -- `simp` reduces the left side to `ofAdd (ρ g (ρ h m.toAdd))`; the right side is the
  -- composite of the two automorphisms just built, which agrees with it by definition.
  map_mul' g h := by ext; simp; rfl

/-- The multiplicative automorphism acts by the representation on the underlying module. -/
@[simp]
theorem toMulAut_apply (ρ : Representation R G M) (g : G) (m : Multiplicative M) :
    toMulAut ρ g m = .ofAdd (ρ g m.toAdd) :=
  (rfl)

/-- The inverse multiplicative automorphism acts by the representation of the inverse element. -/
@[simp]
theorem toMulAut_symm_apply (ρ : Representation R G M) (g : G) (m : Multiplicative M) :
    (toMulAut ρ g).symm m = .ofAdd (ρ g⁻¹ m.toAdd) :=
  (rfl)

end Representation
