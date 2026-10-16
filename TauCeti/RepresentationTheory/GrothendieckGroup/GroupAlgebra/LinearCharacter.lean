/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.Ring
public import TauCeti.RepresentationTheory.CharacterTwist
import TauCeti.RepresentationTheory.AsModule

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
open scoped MonoidAlgebra

namespace TauCeti

universe u

-- These are named rewrite rules: `fdRepK0RingEquiv_of` simplifies their left sides, so
-- registering them as simp lemmas would violate `simpNF`.
/-- The trivial linear character represents the unit of the exact Grothendieck ring. -/
theorem exactK0_ofLinearCharacter_one {k G : Type u} [Field k] [Monoid G] [Finite G] :
    fdRepK0RingEquiv k G
      (ExactK0.of (FDRep.ofLinearCharacter (1 : G →* kˣ))) = 1 := by
  rw [FDRep.ofLinearCharacter_def, Representation.ofLinearCharacter_one,
    fdRepK0RingEquiv_of, FDRep.of_ρ']
  exact (exactK0_one_eq_of_trivial (k := k) (G := G)).symm

/-- The product of the classes of two linear characters is the class of their product. -/
theorem exactK0_ofLinearCharacter_mul {k G : Type u} [Field k] [Monoid G] [Finite G]
    (χ ψ : G →* kˣ) :
    fdRepK0RingEquiv k G (ExactK0.of (FDRep.ofLinearCharacter χ)) *
      fdRepK0RingEquiv k G (ExactK0.of (FDRep.ofLinearCharacter ψ)) =
        fdRepK0RingEquiv k G (ExactK0.of (FDRep.ofLinearCharacter (χ * ψ))) := by
  have h : Representation.charTwist χ (Representation.ofLinearCharacter ψ) =
      Representation.ofLinearCharacter (χ * ψ) := by
    rw [← Representation.charTwist_trivial ψ,
      Representation.charTwist_charTwist, Representation.charTwist_trivial]
  let e : ((Representation.ofLinearCharacter χ).tprod
      (Representation.ofLinearCharacter ψ)).Equiv
      (Representation.ofLinearCharacter (χ * ψ)) := by
    simpa only [h] using
      Representation.tprodEquivCharTwist χ (Representation.ofLinearCharacter ψ)
  have : Module.Finite k[G] (Representation.asModule
      (FDRep.of (Representation.ofLinearCharacter χ) ⊗
        FDRep.of (Representation.ofLinearCharacter ψ)).ρ) :=
    Module.Finite.of_restrictScalars_finite k k[G] _
  have : Module.Finite k[G] (Representation.asModule
      (FDRep.of (Representation.ofLinearCharacter (χ * ψ))).ρ) :=
    Module.Finite.of_restrictScalars_finite k k[G] _
  rw [FDRep.ofLinearCharacter_def, FDRep.ofLinearCharacter_def,
    FDRep.ofLinearCharacter_def, fdRepK0RingEquiv_of, fdRepK0RingEquiv_of,
    fdRepK0RingEquiv_of, of_asModule_mul_of_asModule]
  exact ExactK0.of_congr (Representation.asModuleLinearEquivOfEquiv e).toFGModuleCatIso

end TauCeti
