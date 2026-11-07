/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Grading.Classification
public import TauCeti.CategoryTheory.Monoidal.Pivotal.Torsor

/-!
# Classifying pivotal structures by universal grading characters

Fix a pivotal structure `P` on a finite semisimple rigid linear monoidal category over an
algebraically closed field, with simple unit and finite-dimensional endomorphism spaces of
simple objects. Every other pivotal structure is uniquely the twist of `P` by a character of
the universal grading group. The equivalence `PivotalCategory.characterEquiv` sends `Q` to the
character of the monoidal automorphism `Q /ₛ P`; its inverse twists `P` by a character.

Concretely, twisting a pivotal structure by a character `χ` multiplies its component at each
simple object `X` by `χ (degree [X])`
(`PivotalCategory.characterMonoidalAut_smul_pivotalIso_hom_app_of_simple`).

The base pivotal structure is explicit: this does not assert that every fusion category has
a pivotal structure. No finiteness assumption on the set of simple classes or characteristic
assumption on the field is needed.

## References

* V. Drinfeld, S. Gelaki, D. Nikshych, V. Ostrik, *On braided fusion categories I*,
  Selecta Math. **16** (2010), §2.3
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §§4.7, 4.14
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory

universe v u w

namespace TauCeti.PivotalCategory

section Twist

variable {R : Type w} [CommSemiring R] {C : Type u} [Category.{v} C] [Abelian C]
  [MonoidalCategory C] [MonoidalPreadditive C] [Linear R C] [MonoidalLinear R C]
  [IsFiniteSemisimpleCategory C] [Simple (𝟙_ C)] [RigidCategory C]

/-- Twisting a pivotal structure by a character `χ` of the universal grading group multiplies
its component at a simple object `X` by `χ (degree [X])`. -/
theorem characterMonoidalAut_smul_pivotalIso_hom_app_of_simple
    (χ : universalGradingGroup C →* Rˣ) (P : PivotalCategory C) (X : C) [Simple X] :
    (characterMonoidalAut R χ • P).pivotalIso.hom.app X =
      (χ (universalGradingGroup.degree (SimpleClasses.classOf X)) : R) •
        P.pivotalIso.hom.app X := by
  rw [smul_pivotalIso, Iso.trans_hom, NatTrans.comp_app, characterMonoidalAut_app_of_simple,
    Linear.smul_comp]
  -- The identity sits on `(LaxMonoidalFunctor.of (𝟭 C)).obj X`, which is `X` only up to
  -- unfolding, so `Category.id_comp` is applied up to definitional equality.
  exact congrArg _ (Category.id_comp _)

end Twist

section Classification

variable (k : Type*) [Field k] [IsAlgClosed k]
  {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [RigidCategory C]
  [MonoidalPreadditive C] [Linear k C] [MonoidalLinear k C]
  [hfin : ∀ (X : C) [Simple X], FiniteDimensional k (X ⟶ X)]
  [IsFiniteSemisimpleCategory C] [Simple (𝟙_ C)]

/-- Relative to a chosen pivotal structure `P`, pivotal structures are parametrized by the
characters of the universal grading group. -/
def characterEquiv (P : PivotalCategory C) :
    PivotalCategory C ≃ (universalGradingGroup C →* kˣ) := by
  letI : Nonempty (PivotalCategory C) := ⟨P⟩
  exact (Equiv.smulConst P).symm.trans (monoidalAutCharacterEquiv (hfin := hfin) k).toEquiv

/-- The character of `Q` relative to `P` is that of the automorphism `Q /ₛ P`. -/
@[simp]
theorem characterEquiv_apply (P Q : PivotalCategory C) :
    characterEquiv (hfin := hfin) k P Q =
      monoidalAutCharacter (hfin := hfin) k (Q /ₛ P) := by
  simp [characterEquiv]

/-- A character parametrizes the pivotal structure obtained by twisting the base structure. -/
@[simp]
theorem characterEquiv_symm_apply (P : PivotalCategory C)
    (χ : universalGradingGroup C →* kˣ) :
    (characterEquiv (hfin := hfin) k P).symm χ = characterMonoidalAut k χ • P := by
  simp [characterEquiv]

/-- Any two pivotal structures differ by exactly one universal grading character. -/
theorem existsUnique_character_smul_eq (P Q : PivotalCategory C) :
    ∃! χ : universalGradingGroup C →* kˣ, characterMonoidalAut k χ • P = Q := by
  simpa only [characterEquiv_symm_apply] using
    (characterEquiv (hfin := hfin) k P).symm.bijective.existsUnique Q

end Classification

end TauCeti.PivotalCategory
