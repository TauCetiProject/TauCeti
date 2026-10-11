/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.Ring
public import TauCeti.RepresentationTheory.LinearCharacter.Basic
public import TauCeti.RepresentationTheory.Symmetric.SignCharacter
import TauCeti.RepresentationTheory.AsModule
import TauCeti.RepresentationTheory.CharacterTwist

/-!
# Linear-character classes in the exact Grothendieck ring

The product of two one-dimensional representation classes is the class of the product of
their linear characters. In particular, the sign class of any finite symmetric group squares
to the trivial class over every field. These identities allow tensor calculations in the
group-algebra Grothendieck ring without expanding its representation-to-module dictionary.

The tensor identification uses `Representation.tprodEquivCharTwist` and the multiplication
law for character twists, `Representation.charTwist_charTwist`.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Part III, §14.
-/

public section

open CategoryTheory
open scoped MonoidalCategory

namespace TauCeti

universe u

variable {k G : Type u} [Field k] [Monoid G] [Finite G]

/-- The product of two linear-character classes is the class of their product character
in the exact Grothendieck ring of a finite monoid algebra. -/
-- Simplify before the representation-to-module dictionary expands the factors.
@[simp↓]
theorem fdRepK0RingEquiv_of_ofLinearCharacter_mul (χ ψ : G →* kˣ) :
    fdRepK0RingEquiv k G (ExactK0.of (FDRep.ofLinearCharacter χ)) *
      fdRepK0RingEquiv k G (ExactK0.of (FDRep.ofLinearCharacter ψ)) =
      fdRepK0RingEquiv k G (ExactK0.of (FDRep.ofLinearCharacter (χ * ψ))) := by
  have e := Representation.tprodEquivCharTwist χ (Representation.ofLinearCharacter ψ)
  have htwist : Representation.charTwist χ (Representation.ofLinearCharacter ψ) =
      Representation.ofLinearCharacter (χ * ψ) := by
    rw [← Representation.charTwist_trivial ψ, Representation.charTwist_charTwist,
      Representation.charTwist_trivial]
  rw [htwist] at e
  have he : Nonempty (FDRep.ofLinearCharacter χ ⊗ FDRep.ofLinearCharacter ψ ≅
      FDRep.ofLinearCharacter (χ * ψ)) := by
    apply nonempty_fdRepIso_iff.mpr
    rw [FDRep.ofLinearCharacter_def, FDRep.ofLinearCharacter_def,
      FDRep.ofLinearCharacter_def]
    -- The tensor action on bundled finite-dimensional representations is `tprod`.
    exact ⟨e⟩
  rw [← map_mul, ExactK0.of_mul_of, ExactK0.of_congr he.some]

/-- The sign class of a finite symmetric group squares to the trivial class in the exact
Grothendieck ring over every field. -/
-- Reduce the sign product before the general linear-character multiplication rule.
@[simp↓ 1100]
theorem fdRepK0RingEquiv_of_ofLinearCharacter_signLinearCharacter_mul_self
    {α : Type u} [Fintype α] [DecidableEq α] :
    fdRepK0RingEquiv k (Equiv.Perm α)
        (ExactK0.of (FDRep.ofLinearCharacter (signLinearCharacter k α))) *
      fdRepK0RingEquiv k (Equiv.Perm α)
        (ExactK0.of (FDRep.ofLinearCharacter (signLinearCharacter k α))) = 1 := by
  have hχ : signLinearCharacter k α * signLinearCharacter k α = 1 := by
    ext g
    simp only [MonoidHom.mul_apply, Units.val_mul, MonoidHom.one_apply, Units.val_one,
      coe_signLinearCharacter_apply, ← Int.cast_mul]
    simp only [← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  rw [fdRepK0RingEquiv_of_ofLinearCharacter_mul, hχ, FDRep.ofLinearCharacter_def,
    Representation.ofLinearCharacter_one, fdRepK0RingEquiv_of, FDRep.of_ρ',
    ← exactK0_one_eq_of_trivial]

end TauCeti
