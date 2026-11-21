/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Grading.Groupoid.Character
public import TauCeti.CategoryTheory.Monoidal.Pivotal.Torsor

/-!
# Classifying pivotal structures by universal grading characters

Fix a pivotal structure `P` on a finite semisimple rigid linear monoidal category over a field `k`
such that every simple object has scalar endomorphisms
(`Function.Surjective (algebraMap k (End X))`) — for example, over an algebraically closed field
with finite-dimensional simple endomorphism spaces. Every other pivotal structure is uniquely the
twist of `P` by a character of `universalGradingGroup C`, or equivalently by a `kˣ`-valued groupoid
character `universalGradingGroupoid C ⥤ SingleObj kˣ` (Penneys, Lemma 3.19(2)). Simplicity of the
tensor unit `𝟙_ C` is not required, so both classifications apply to arbitrary multitensor and
multifusion categories.

Concretely, twisting a pivotal structure by a groupoid character `F` multiplies its component at
each simple object `X` by `F.map (degreeOf X)`
(`PivotalCategory.groupoidCharacterMonoidalAut_smul_pivotalIso_hom_app_of_simple`), and twisting by
a group character `χ` multiplies it by `χ (degree [X])`
(`PivotalCategory.characterMonoidalAut_smul_pivotalIso_hom_app_of_simple`).

The base pivotal structure is explicit: this does not assert that every multitensor category has a
pivotal structure. No finiteness assumption on the set of simple classes or characteristic
assumption on the field is needed.

## References

* V. Drinfeld, S. Gelaki, D. Nikshych, V. Ostrik, *On braided fusion categories I*,
  Selecta Math. **16** (2010), §2.3
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §§4.7, 4.14
* D. Penneys, *Unitary dual functors for unitary multitensor categories*,
  Higher Structures **4** (2020), no. 2, 22–56 (arXiv:1808.00323), §3.3, Lemma 3.19
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory

universe v u w

namespace TauCeti.PivotalCategory

section Twist

variable {R : Type w} [CommSemiring R] {C : Type u} [Category.{v} C] [Abelian C]
  [MonoidalCategory C] [MonoidalPreadditive C] [Linear R C] [MonoidalLinear R C]
  [IsFiniteSemisimpleCategory C] [RigidCategory C]

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

/-- Twisting a pivotal structure by an `Rˣ`-valued character `F` of `universalGradingGroupoid C`
multiplies its component at a simple object `X` by `F.map (degreeOf X)`. -/
theorem groupoidCharacterMonoidalAut_smul_pivotalIso_hom_app_of_simple
    (F : universalGradingGroupoid C ⥤ SingleObj Rˣ) (P : PivotalCategory C) (X : C) [Simple X] :
    (groupoidCharacterMonoidalAut R F • P).pivotalIso.hom.app X =
      Units.val (F.map (universalGradingGroupoid.degreeOf X)) • P.pivotalIso.hom.app X := by
  rw [groupoidCharacterMonoidalAut_eq_characterMonoidalAut,
    characterMonoidalAut_smul_pivotalIso_hom_app_of_simple,
    universalGradingGroupoid.singleObjFunctorMulEquiv_apply_degree_classOf]

end Twist

section SurjectiveClassification

variable (k : Type*) [Field k]
  {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [RigidCategory C]
  [MonoidalPreadditive C] [Linear k C] [MonoidalLinear k C]
  [IsFiniteSemisimpleCategory C]

/-- Relative to a chosen pivotal structure `P`, pivotal structures are parametrized by the
characters of the universal grading group whenever simple objects have scalar endomorphisms. -/
def characterEquivOfSurjective
    (hsurj : ∀ (X : C) [Simple X], Function.Surjective (algebraMap k (End X)))
    (P : PivotalCategory C) :
    PivotalCategory C ≃ (universalGradingGroup C →* kˣ) := by
  letI : Nonempty (PivotalCategory C) := ⟨P⟩
  exact (Equiv.smulConst P).symm.trans (monoidalAutCharacterEquivOfSurjective k hsurj).toEquiv

/-- The character of `Q` relative to `P` is that of the automorphism `Q /ₛ P`. -/
@[simp]
theorem characterEquivOfSurjective_apply
    (hsurj : ∀ (X : C) [Simple X], Function.Surjective (algebraMap k (End X)))
    (P Q : PivotalCategory C) :
    characterEquivOfSurjective k hsurj P Q =
      monoidalAutCharacterOfSurjective k hsurj (Q /ₛ P) := by
  simp [characterEquivOfSurjective]

/-- A character parametrizes the pivotal structure obtained by twisting the base structure. -/
@[simp]
theorem characterEquivOfSurjective_symm_apply
    (hsurj : ∀ (X : C) [Simple X], Function.Surjective (algebraMap k (End X)))
    (P : PivotalCategory C) (χ : universalGradingGroup C →* kˣ) :
    (characterEquivOfSurjective k hsurj P).symm χ = characterMonoidalAut k χ • P := by
  simp [characterEquivOfSurjective]

/-- Any two pivotal structures differ by exactly one universal grading character whenever simple
objects have scalar endomorphisms. -/
theorem existsUnique_character_smul_eq_of_surjective
    (hsurj : ∀ (X : C) [Simple X], Function.Surjective (algebraMap k (End X)))
    (P Q : PivotalCategory C) :
    ∃! χ : universalGradingGroup C →* kˣ, characterMonoidalAut k χ • P = Q := by
  simpa only [characterEquivOfSurjective_symm_apply] using
    (characterEquivOfSurjective k hsurj P).symm.bijective.existsUnique Q

/-- Relative to a chosen pivotal structure `P`, pivotal structures on a multitensor category `C`
are parametrized by `kˣ`-valued characters `universalGradingGroupoid C ⥤ SingleObj kˣ` of its
universal grading groupoid whenever simple objects have scalar endomorphisms (Penneys,
Lemma 3.19(2)). -/
def groupoidCharacterEquivOfSurjective
    (hsurj : ∀ (X : C) [Simple X], Function.Surjective (algebraMap k (End X)))
    (P : PivotalCategory C) :
    PivotalCategory C ≃ (universalGradingGroupoid C ⥤ SingleObj kˣ) := by
  letI : Nonempty (PivotalCategory C) := ⟨P⟩
  exact (Equiv.smulConst P).symm.trans
    (monoidalAutGroupoidCharacterEquivOfSurjective k hsurj).toEquiv

/-- The groupoid character of `Q` relative to `P` is that of the monoidal automorphism
`Q /ₛ P`. -/
@[simp]
theorem groupoidCharacterEquivOfSurjective_apply
    (hsurj : ∀ (X : C) [Simple X], Function.Surjective (algebraMap k (End X)))
    (P Q : PivotalCategory C) :
    groupoidCharacterEquivOfSurjective k hsurj P Q =
      monoidalAutGroupoidCharacterOfSurjective k hsurj (Q /ₛ P) := by
  simp [groupoidCharacterEquivOfSurjective]

/-- A groupoid character parametrizes the pivotal structure obtained by twisting `P`. -/
@[simp]
theorem groupoidCharacterEquivOfSurjective_symm_apply
    (hsurj : ∀ (X : C) [Simple X], Function.Surjective (algebraMap k (End X)))
    (P : PivotalCategory C) (F : universalGradingGroupoid C ⥤ SingleObj kˣ) :
    (groupoidCharacterEquivOfSurjective k hsurj P).symm F =
      groupoidCharacterMonoidalAut k F • P := by
  simp [groupoidCharacterEquivOfSurjective]

/-- Any two pivotal structures on a multitensor category differ by a unique `kˣ`-valued character of
`universalGradingGroupoid C` whenever simple objects have scalar endomorphisms. -/
theorem existsUnique_groupoidCharacter_smul_eq_of_surjective
    (hsurj : ∀ (X : C) [Simple X], Function.Surjective (algebraMap k (End X)))
    (P Q : PivotalCategory C) :
    ∃! F : universalGradingGroupoid C ⥤ SingleObj kˣ, groupoidCharacterMonoidalAut k F • P = Q := by
  simpa only [groupoidCharacterEquivOfSurjective_symm_apply] using
    (groupoidCharacterEquivOfSurjective k hsurj P).symm.bijective.existsUnique Q

end SurjectiveClassification

section Classification

variable (k : Type*) [Field k] [IsAlgClosed k]
  {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [RigidCategory C]
  [MonoidalPreadditive C] [Linear k C] [MonoidalLinear k C]
  [hfin : ∀ (X : C) [Simple X], FiniteDimensional k (X ⟶ X)]
  [IsFiniteSemisimpleCategory C]

/-- Relative to a chosen pivotal structure `P`, pivotal structures are parametrized by the
characters of the universal grading group. -/
def characterEquiv (P : PivotalCategory C) :
    PivotalCategory C ≃ (universalGradingGroup C →* kˣ) :=
  characterEquivOfSurjective k
    (fun X _ ↦ (bijective_algebraMap_end_of_simple k X).surjective) P

/-- The character of `Q` relative to `P` is that of the automorphism `Q /ₛ P`. -/
@[simp]
theorem characterEquiv_apply (P Q : PivotalCategory C) :
    characterEquiv (hfin := hfin) k P Q =
      monoidalAutCharacter (hfin := hfin) k (Q /ₛ P) :=
  characterEquivOfSurjective_apply k
    (fun X _ ↦ (bijective_algebraMap_end_of_simple k X).surjective) P Q

/-- A character parametrizes the pivotal structure obtained by twisting the base structure. -/
@[simp]
theorem characterEquiv_symm_apply (P : PivotalCategory C)
    (χ : universalGradingGroup C →* kˣ) :
    (characterEquiv (hfin := hfin) k P).symm χ = characterMonoidalAut k χ • P :=
  characterEquivOfSurjective_symm_apply k
    (fun X _ ↦ (bijective_algebraMap_end_of_simple k X).surjective) P χ

/-- Any two pivotal structures differ by exactly one universal grading character. -/
theorem existsUnique_character_smul_eq (P Q : PivotalCategory C) :
    ∃! χ : universalGradingGroup C →* kˣ, characterMonoidalAut k χ • P = Q :=
  existsUnique_character_smul_eq_of_surjective k
    (fun X _ ↦ (bijective_algebraMap_end_of_simple k X).surjective) P Q

/-- Relative to a chosen pivotal structure `P`, pivotal structures on a multitensor category `C`
are parametrized by `kˣ`-valued characters `universalGradingGroupoid C ⥤ SingleObj kˣ` of its
universal grading groupoid (Penneys, Lemma 3.19(2)). -/
def groupoidCharacterEquiv (P : PivotalCategory C) :
    PivotalCategory C ≃ (universalGradingGroupoid C ⥤ SingleObj kˣ) :=
  groupoidCharacterEquivOfSurjective k
    (fun X _ ↦ (bijective_algebraMap_end_of_simple k X).surjective) P

/-- The groupoid character of `Q` relative to `P` is that of the monoidal automorphism `Q /ₛ P`. -/
@[simp]
theorem groupoidCharacterEquiv_apply (P Q : PivotalCategory C) :
    groupoidCharacterEquiv (hfin := hfin) k P Q =
      monoidalAutGroupoidCharacter (hfin := hfin) k (Q /ₛ P) :=
  groupoidCharacterEquivOfSurjective_apply k
    (fun X _ ↦ (bijective_algebraMap_end_of_simple k X).surjective) P Q

/-- A groupoid character parametrizes the pivotal structure obtained by twisting `P`. -/
@[simp]
theorem groupoidCharacterEquiv_symm_apply (P : PivotalCategory C)
    (F : universalGradingGroupoid C ⥤ SingleObj kˣ) :
    (groupoidCharacterEquiv (hfin := hfin) k P).symm F = groupoidCharacterMonoidalAut k F • P :=
  groupoidCharacterEquivOfSurjective_symm_apply k
    (fun X _ ↦ (bijective_algebraMap_end_of_simple k X).surjective) P F

/-- Any two pivotal structures on a multitensor category differ by a unique `kˣ`-valued character of
`universalGradingGroupoid C`. -/
theorem existsUnique_groupoidCharacter_smul_eq (P Q : PivotalCategory C) :
    ∃! F : universalGradingGroupoid C ⥤ SingleObj kˣ, groupoidCharacterMonoidalAut k F • P = Q :=
  existsUnique_groupoidCharacter_smul_eq_of_surjective k
    (fun X _ ↦ (bijective_algebraMap_end_of_simple k X).surjective) P Q

end Classification

end TauCeti.PivotalCategory
