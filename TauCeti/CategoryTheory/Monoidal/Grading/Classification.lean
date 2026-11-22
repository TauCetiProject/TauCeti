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

In a finite semisimple linear monoidal category over a field `k` such that every simple object
has scalar endomorphisms (`Function.Surjective (algebraMap k (End X))`), monoidal natural
automorphisms of the identity are exactly characters of the universal grading group.

The maps `monoidalAutCharacterOfSurjective` (extracting the scalar on each simple object) and
`characterMonoidalAut` (extending those scalars to all objects) are inverse group homomorphisms,
packaged as `monoidalAutCharacterEquivOfSurjective`. When `k` is algebraically closed and simple
objects have finite-dimensional endomorphisms, `monoidalAutCharacterEquiv` specializes this
identification. Simplicity of the tensor unit, rigidity, finiteness of the set of simple classes,
and characteristic zero are not needed.

## References

* V. Drinfeld, S. Gelaki, D. Nikshych, V. Ostrik, *On braided fusion categories I*,
  Selecta Math. **16** (2010), §2.3
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §4.14
* D. Penneys, *Unitary dual functors for unitary multitensor categories*,
  Higher Structures **4** (2020), no. 2, 22–56 (arXiv:1808.00323), Lemma 3.19
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory

universe v u

namespace TauCeti

section Surjective

variable (k : Type*) [Field k]
  {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [Linear k C] [MonoidalLinear k C]
  [IsFiniteSemisimpleCategory C]

/-- Extracting the character of the automorphism extended from a character recovers that
character. -/
@[simp]
theorem monoidalAutCharacterOfSurjective_characterMonoidalAut
    (hsurj : ∀ (X : C) [Simple X], Function.Surjective (algebraMap k (End X)))
    (χ : universalGradingGroup C →* kˣ) :
    monoidalAutCharacterOfSurjective k hsurj (characterMonoidalAut k χ) = χ := by
  apply universalGradingGroup.hom_ext
  intro S
  apply Units.ext
  apply smul_left_injective k (id_ne_zero S.repr)
  simpa only [characterMonoidalAut_app_of_simple, SimpleClasses.classOf_repr] using
    monoidalAutCharacterOfSurjective_degree_smul_id k hsurj (characterMonoidalAut k χ) S.repr

/-- Extending the character extracted from an automorphism recovers that automorphism. -/
@[simp]
theorem characterMonoidalAut_monoidalAutCharacterOfSurjective
    (hsurj : ∀ (X : C) [Simple X], Function.Surjective (algebraMap k (End X)))
    (a : Aut (LaxMonoidalFunctor.of (𝟭 C))) :
    characterMonoidalAut k (monoidalAutCharacterOfSurjective k hsurj a) = a := by
  apply monoidalAutCharacterOfSurjective_injective k hsurj
  simp only [monoidalAutCharacterOfSurjective_characterMonoidalAut]

/-- Monoidal natural automorphisms of the identity are the characters of the universal grading
group, as groups, whenever simple objects have scalar endomorphisms. The forward map extracts the
scalar on each simple object; the inverse extends a character to every object using finite
semisimplicity. -/
def monoidalAutCharacterEquivOfSurjective
    (hsurj : ∀ (X : C) [Simple X], Function.Surjective (algebraMap k (End X))) :
    Aut (LaxMonoidalFunctor.of (𝟭 C)) ≃* (universalGradingGroup C →* kˣ) :=
  { monoidalAutCharacterOfSurjective k hsurj with
    invFun := characterMonoidalAut k
    left_inv := characterMonoidalAut_monoidalAutCharacterOfSurjective k hsurj
    right_inv := monoidalAutCharacterOfSurjective_characterMonoidalAut k hsurj }

/-- The classification sends an automorphism to its character on simple degrees. -/
@[simp]
theorem monoidalAutCharacterEquivOfSurjective_apply
    (hsurj : ∀ (X : C) [Simple X], Function.Surjective (algebraMap k (End X)))
    (a : Aut (LaxMonoidalFunctor.of (𝟭 C))) :
    monoidalAutCharacterEquivOfSurjective k hsurj a =
      monoidalAutCharacterOfSurjective k hsurj a :=
  (rfl)

/-- The inverse classification extends a character to a monoidal automorphism. -/
@[simp]
theorem monoidalAutCharacterEquivOfSurjective_symm_apply
    (hsurj : ∀ (X : C) [Simple X], Function.Surjective (algebraMap k (End X)))
    (χ : universalGradingGroup C →* kˣ) :
    (monoidalAutCharacterEquivOfSurjective k hsurj).symm χ = characterMonoidalAut k χ :=
  (rfl)

end Surjective

section AlgClosed

variable (k : Type*) [Field k] [IsAlgClosed k]
  {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [Linear k C] [MonoidalLinear k C]
  [hfin : ∀ (X : C) [Simple X], FiniteDimensional k (X ⟶ X)]
  [IsFiniteSemisimpleCategory C]

/-- Extracting the character of the automorphism extended from a character recovers that
character. -/
@[simp]
theorem monoidalAutCharacter_characterMonoidalAut (χ : universalGradingGroup C →* kˣ) :
    monoidalAutCharacter (hfin := hfin) k (characterMonoidalAut k χ) = χ := by
  rw [monoidalAutCharacter_eq_monoidalAutCharacterOfSurjective]
  exact monoidalAutCharacterOfSurjective_characterMonoidalAut k _ χ

/-- Extending the character extracted from an automorphism recovers that automorphism. -/
@[simp]
theorem characterMonoidalAut_monoidalAutCharacter (a : Aut (LaxMonoidalFunctor.of (𝟭 C))) :
    characterMonoidalAut k (monoidalAutCharacter (hfin := hfin) k a) = a := by
  rw [monoidalAutCharacter_eq_monoidalAutCharacterOfSurjective]
  exact characterMonoidalAut_monoidalAutCharacterOfSurjective k _ a

/-- Monoidal natural automorphisms of the identity are the characters of the universal grading
group, as groups. The forward map extracts the scalar on each simple object; the inverse
extends a character to every object using finite semisimplicity. -/
def monoidalAutCharacterEquiv :
    Aut (LaxMonoidalFunctor.of (𝟭 C)) ≃* (universalGradingGroup C →* kˣ) :=
  monoidalAutCharacterEquivOfSurjective k
    fun X _ ↦ (bijective_algebraMap_end_of_simple k X).surjective

/-- `monoidalAutCharacterEquiv` is the specialization of `monoidalAutCharacterEquivOfSurjective`
to an algebraically closed field via Schur's lemma. -/
theorem monoidalAutCharacterEquiv_eq_monoidalAutCharacterEquivOfSurjective :
    monoidalAutCharacterEquiv (hfin := hfin) k (C := C) =
      monoidalAutCharacterEquivOfSurjective k fun X _ ↦
        (bijective_algebraMap_end_of_simple k X).surjective :=
  (rfl)

/-- The classification sends an automorphism to its character on simple degrees. -/
@[simp]
theorem monoidalAutCharacterEquiv_apply (a : Aut (LaxMonoidalFunctor.of (𝟭 C))) :
    monoidalAutCharacterEquiv (hfin := hfin) k a = monoidalAutCharacter (hfin := hfin) k a := by
  rw [monoidalAutCharacterEquiv_eq_monoidalAutCharacterEquivOfSurjective,
    monoidalAutCharacter_eq_monoidalAutCharacterOfSurjective]
  exact monoidalAutCharacterEquivOfSurjective_apply k _ a

/-- The inverse classification extends a character to a monoidal automorphism. -/
@[simp]
theorem monoidalAutCharacterEquiv_symm_apply (χ : universalGradingGroup C →* kˣ) :
    (monoidalAutCharacterEquiv (hfin := hfin) k).symm χ = characterMonoidalAut k χ := by
  rw [monoidalAutCharacterEquiv_eq_monoidalAutCharacterEquivOfSurjective]
  exact monoidalAutCharacterEquivOfSurjective_symm_apply k _ χ

end AlgClosed

end TauCeti
