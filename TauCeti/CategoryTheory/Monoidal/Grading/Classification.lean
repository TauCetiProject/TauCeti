/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Grading.Character
public import TauCeti.CategoryTheory.Monoidal.Grading.MonoidalAut

/-!
# Monoidal automorphisms and universal grading characters

In a finite semisimple linear monoidal category over an algebraically closed field, with
simple unit and finite-dimensional endomorphism spaces of simple objects, monoidal natural
automorphisms of the identity are exactly characters of the universal grading group.

The maps `monoidalAutCharacter` (extracting the scalar on each simple object) and
`characterMonoidalAut` (extending those scalars to all objects) are inverse group
homomorphisms. We package them as `monoidalAutCharacterEquiv`. Neither rigidity, finiteness of
the set of simple classes, nor characteristic zero is needed for this identification.

## References

* V. Drinfeld, S. Gelaki, D. Nikshych, V. Ostrik, *On braided fusion categories I*,
  Selecta Math. **16** (2010), §2.3
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §4.14
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory

universe v u

namespace TauCeti

variable (k : Type*) [Field k] [IsAlgClosed k]
  {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [Linear k C] [MonoidalLinear k C]
  [hfin : ∀ (X : C) [Simple X], FiniteDimensional k (X ⟶ X)]
  [IsFiniteSemisimpleCategory C] [Simple (𝟙_ C)]

/-- Extracting the character of the automorphism extended from a character recovers that
character. -/
@[simp]
theorem monoidalAutCharacter_characterMonoidalAut (χ : universalGradingGroup C →* kˣ) :
    monoidalAutCharacter (hfin := hfin) k (characterMonoidalAut k χ) = χ := by
  apply universalGradingGroup.hom_ext
  intro S
  apply Units.ext
  apply smul_left_injective k (id_ne_zero S.repr)
  simpa only [characterMonoidalAut_app_of_simple, SimpleClasses.classOf_repr] using
    monoidalAutCharacter_degree_smul_id (hfin := hfin) k (characterMonoidalAut k χ) S.repr

/-- Extending the character extracted from an automorphism recovers that automorphism. -/
@[simp]
theorem characterMonoidalAut_monoidalAutCharacter (a : Aut (LaxMonoidalFunctor.of (𝟭 C))) :
    characterMonoidalAut k (monoidalAutCharacter (hfin := hfin) k a) = a := by
  apply monoidalAutCharacter_injective (hfin := hfin) k
  simp only [monoidalAutCharacter_characterMonoidalAut]

/-- Monoidal natural automorphisms of the identity are the characters of the universal grading
group, as groups. The forward map extracts the scalar on each simple object; the inverse
extends a character to every object using finite semisimplicity. -/
def monoidalAutCharacterEquiv :
    Aut (LaxMonoidalFunctor.of (𝟭 C)) ≃* (universalGradingGroup C →* kˣ) :=
  { monoidalAutCharacter (hfin := hfin) k with
    invFun := characterMonoidalAut k
    left_inv := characterMonoidalAut_monoidalAutCharacter (hfin := hfin) k
    right_inv := monoidalAutCharacter_characterMonoidalAut (hfin := hfin) k }

/-- The classification sends an automorphism to its character on simple degrees. -/
@[simp]
theorem monoidalAutCharacterEquiv_apply (a : Aut (LaxMonoidalFunctor.of (𝟭 C))) :
    monoidalAutCharacterEquiv (hfin := hfin) k a = monoidalAutCharacter (hfin := hfin) k a :=
  (rfl)

/-- The inverse classification extends a character to a monoidal automorphism. -/
@[simp]
theorem monoidalAutCharacterEquiv_symm_apply (χ : universalGradingGroup C →* kˣ) :
    (monoidalAutCharacterEquiv (hfin := hfin) k).symm χ = characterMonoidalAut k χ :=
  (rfl)

end TauCeti
