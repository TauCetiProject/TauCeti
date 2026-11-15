/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Basic
public import TauCeti.Algebra.Ring.Commutator

/-!
# Nilpotency of represented central brackets

A bracket commuting with both of its factors has nilpotent image in a rational algebra
whenever the first factor does. This is the enveloping-algebra form of
`TauCeti.Associative.isNilpotent_of_commutator_eq`; it supplies nilpotency for the
class-two root-subgroup exponential without requiring the bracket to be a root generator.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

variable {R L B F : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [Ring B] [Algebra ℚ B] [FunLike F (_root_.UniversalEnvelopingAlgebra R L) B]
  [NonUnitalRingHomClass F (_root_.UniversalEnvelopingAlgebra R L) B]

/-- Under a ring homomorphism from an enveloping algebra to a rational algebra, a bracket
centralizing both factors has nilpotent image if its first factor has nilpotent image. -/
theorem isNilpotent_map_ι_lie_of_isNilpotent (ρ : F) {x y : L}
    (hx : ⁅x, ⁅x, y⁆⁆ = 0) (hy : ⁅y, ⁅x, y⁆⁆ = 0)
    (hn : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι R x))) :
    IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι R ⁅x, y⁆)) :=
  Associative.isNilpotent_of_commutator_eq
    ((sub_eq_iff_eq_add').mp (mul_sub_mul_eq_map_ι_lie ρ x y))
    (commute_of_lie_eq_zero ρ hx) (commute_of_lie_eq_zero ρ hy) hn

end TauCeti.UniversalEnvelopingAlgebra
