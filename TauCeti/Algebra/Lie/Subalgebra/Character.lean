/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Character
public import Mathlib.Algebra.Lie.Subalgebra

/-!
# Restricting a linear form to a character of a Lie subalgebra

A linear form `χ` on a Lie algebra `L` restricts to a character of a Lie subalgebra `B` exactly
when it vanishes on the brackets of elements of `B`. This file packages that restriction as a
`LieAlgebra.LieCharacter` of `B`. A single linear form on `L` vanishing on the brackets of each
member of a family of Lie subalgebras thereby gives compatible characters of all of them, as used
for the left ideals induced along a directed family of Lie subalgebras in
`TauCeti/Algebra/Lie/UniversalEnveloping/PBW/Character.lean`.

## Main definitions

* `LieSubalgebra.restrictCharacter`: the restriction of a linear form on `L`, vanishing on the
  brackets of `B`, as a character of `B`.
-/

public section

namespace LieSubalgebra

open LieAlgebra

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The restriction of a linear form on `L` to a Lie subalgebra on whose brackets it vanishes, as a
character of the subalgebra. -/
def restrictCharacter (B : LieSubalgebra R L) (χ : L →ₗ[R] R)
    (hχ : ∀ x ∈ B, ∀ y ∈ B, χ ⁅x, y⁆ = 0) : LieCharacter R B where
  toLinearMap := χ ∘ₗ B.incl.toLinearMap
  map_lie' {x y} := by
    simpa [LieRing.of_associative_ring_bracket, mul_comm] using hχ x x.2 y y.2

/-- The restricted character takes the values of the linear form. -/
@[simp]
theorem restrictCharacter_apply (B : LieSubalgebra R L) (χ : L →ₗ[R] R)
    (hχ : ∀ x ∈ B, ∀ y ∈ B, χ ⁅x, y⁆ = 0) (x : B) : B.restrictCharacter χ hχ x = χ x :=
  (rfl)

end LieSubalgebra
