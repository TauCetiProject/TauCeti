/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# The representation of a homomorphism into `GL_n(A)`

A homomorphism `ρ : Γ →* GL_n(A)`, where `GL_n(A) = Matrix.GeneralLinearGroup n A`, defines the
linear representation `Representation.ofGL ρ` of `Γ` on `n → A`, in which `g` acts by the matrix
`ρ g`.

## Main definitions

* `Representation.ofGL ρ`: the linear representation on `n → A` of a homomorphism
  `ρ : Γ →* GL_n(A)`.
-/

public section

noncomputable section

open Matrix

namespace Representation

variable {Γ A : Type*} [Monoid Γ] [CommSemiring A] {n : Type*} [Fintype n] [DecidableEq n]

/-- The linear representation on `n → A` of a homomorphism `Γ →* GL_n(A)`, by matrix
multiplication. -/
def ofGL (ρ : Γ →* GL n A) : Representation A Γ (n → A) :=
  (Matrix.toLinAlgEquiv'.toMonoidHom.comp (Units.coeHom (Matrix n n A))).comp ρ

@[simp]
theorem ofGL_apply (ρ : Γ →* GL n A) (g : Γ) : ofGL ρ g = Matrix.toLin' (ρ g : Matrix n n A) :=
  (rfl)

end Representation
