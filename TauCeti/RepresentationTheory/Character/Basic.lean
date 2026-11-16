/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Character
public import TauCeti.LinearAlgebra.Trace.Basic

/-!
# Characters in infinite dimension and conjugation invariance of traces

The trace character vanishes when the representation space is not finite-dimensional.

The trace of the action is a class function for a representation over a commutative semiring on
any additive commutative monoid (`Representation.trace_conj`). `Representation.character` and
`Representation.char_conj` ask for an additive group structure on the carrier, so this form
applies to representations such as `Representation.symmetricPower`, which is built on the
additive monoid instance of the symmetric power rather than on the one underlying its additive
group.
-/

public section

namespace Representation

/-- The character vanishes on a representation space that is not finite-dimensional. -/
theorem character_eq_zero_of_not_finite {k G V : Type*} [Field k] [Monoid G]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V) (h : ¬ FiniteDimensional k V) :
    ρ.character = 0 := by
  funext g
  simp [character, TauCeti.LinearMap.trace_eq_zero_of_not_finite h]

/-- The trace of the action is constant on conjugacy classes. This is `Representation.char_conj`
for a representation on an additive commutative monoid. -/
theorem trace_conj {R G M : Type*} [CommSemiring R] [Group G] [AddCommMonoid M] [Module R M]
    (ρ : Representation R G M) (g h : G) :
    LinearMap.trace R M (ρ (h * g * h⁻¹)) = LinearMap.trace R M (ρ g) := by
  rw [map_mul, LinearMap.trace_mul_comm, ← map_mul, inv_mul_cancel_left]

end Representation
