/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.Ring
public import TauCeti.RepresentationTheory.LinearCharacter.Tensor

/-!
# Linear characters in the exact Grothendieck ring

The class of a one-dimensional representation is multiplicative in its linear character.
This lets induction calculations use character multiplication within the integral exact
Grothendieck ring, in arbitrary characteristic.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Part III, §14.
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti

universe u

-- These are named rewrite rules: `fdRepK0RingEquiv_of` simplifies their left sides, so
-- registering them as simp lemmas would violate `simpNF`.
/-- The trivial linear character represents the unit of the exact Grothendieck ring. -/
theorem exactK0_ofLinearCharacter_one {k G : Type u} [Field k] [Monoid G] [Finite G] :
    fdRepK0RingEquiv k G
      (ExactK0.of (FDRep.ofLinearCharacter (1 : G →* kˣ))) = 1 := by
  rw [FDRep.ofLinearCharacter_one, ← ExactK0.one_def, map_one]

/-- The product of the classes of two linear characters is the class of their product. -/
theorem exactK0_ofLinearCharacter_mul {k G : Type u} [Field k] [Monoid G] [Finite G]
    (χ ψ : G →* kˣ) :
    fdRepK0RingEquiv k G (ExactK0.of (FDRep.ofLinearCharacter χ)) *
      fdRepK0RingEquiv k G (ExactK0.of (FDRep.ofLinearCharacter ψ)) =
        fdRepK0RingEquiv k G (ExactK0.of (FDRep.ofLinearCharacter (χ * ψ))) := by
  rw [← map_mul, ExactK0.of_mul_of, ExactK0.of_congr (FDRep.ofLinearCharacterTensorIso χ ψ)]

end TauCeti
