/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.OfAssociative

/-!
# The general linear Lie algebra `𝔤𝔩(M)` of a module

For a module `M` over a commutative ring `R`, Mathlib makes `Module.End R M` a Lie algebra under
the commutator bracket only through the local instances `LieRing.ofAssociativeRing` and
`LieAlgebra.ofAssociativeAlgebra`. This file names that Lie algebra as a type of its own, so that
it can carry global Lie algebra and Lie module instances.

## Main definitions

* `TauCeti.EndLie R M`: `End(M)` as the Lie algebra `𝔤𝔩(M)` acting on `M`.
* `TauCeti.EndLie.equiv R M`: the identification of `𝔤𝔩(M)` with the algebra `Module.End R M`.

## Main statements

* `TauCeti.EndLie.lie_apply`: an element of `𝔤𝔩(M)` acts on `M` as the corresponding
  endomorphism.
* `TauCeti.EndLie.equiv_lie`: the bracket of `𝔤𝔩(M)` is the commutator of endomorphisms.
-/

public section

namespace TauCeti

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]

/-- `End(M)` as the Lie algebra `𝔤𝔩(M)`, with the commutator bracket, acting on `M`. It is
identified with the algebra `Module.End R M` by `TauCeti.EndLie.equiv`. -/
-- The body is exposed because the module system unfolds only exposed definitions when checking
-- public declarations, and the instances below are those of `Module.End R M`.
@[expose] def EndLie : Type _ := Module.End R M

namespace EndLie

instance instRing : Ring (EndLie R M) := inferInstanceAs (Ring (Module.End R M))
instance instAlgebra : Algebra R (EndLie R M) :=
  inferInstanceAs (Algebra R (Module.End R M))
instance instLieRing : LieRing (EndLie R M) := LieRing.ofAssociativeRing
instance instLieAlgebra : LieAlgebra R (EndLie R M) :=
  LieAlgebra.ofAssociativeAlgebra
instance instLieRingModule : LieRingModule (EndLie R M) M :=
  Module.End.instLieRingModule
instance instLieModule : LieModule R (EndLie R M) M :=
  Module.End.instLieModule

/-- The identification of `𝔤𝔩(M)` with the algebra `Module.End R M`. -/
def equiv : EndLie R M ≃ₐ[R] Module.End R M :=
  AlgEquiv.refl

variable {R M}

/-- An element of `𝔤𝔩(M)` acts on `M` as the corresponding endomorphism. -/
@[simp]
theorem lie_apply (X : EndLie R M) (m : M) : ⁅X, m⁆ = equiv R M X m :=
  (rfl)

/-- The bracket of `𝔤𝔩(M)` is the commutator of endomorphisms. -/
@[simp]
theorem equiv_lie (X Y : EndLie R M) :
    equiv R M ⁅X, Y⁆ = equiv R M X * equiv R M Y - equiv R M Y * equiv R M X := by
  rw [LieRing.of_associative_ring_bracket, map_sub, map_mul, map_mul]

end EndLie

end TauCeti
