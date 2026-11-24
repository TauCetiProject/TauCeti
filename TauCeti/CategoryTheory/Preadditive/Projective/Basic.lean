/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import TauCeti.CategoryTheory.ObjectProperty.FiniteProducts

/-!
# Projective objects: closure properties and coproducts

The object property `CategoryTheory.isProjective C` of being projective is closed under
isomorphisms, so it can serve as the resolving property of finite resolutions, which are
transported along isomorphisms. It is also stable under retracts, contains a zero object, and,
in a category with binary or finite biproducts, is closed under binary and finite products.
These are the closure properties under which the ideal of morphisms factoring through a projective
object has an elementwise description (`CategoryTheory.ObjectProperty.mem_factorIdeal_iff`).

The point of any colimit cofan of a family of projective objects is projective. Mathlib's
instance for the chosen coproduct `∐ X` requires the index type to live in the universe of the
morphisms of the category; the version here accepts any colimit cofan with any index type, for
instance a coproduct of a sequence of modules indexed by `ℕ` in `ModuleCat.{v} R`. In particular,
any biproduct `⨁ f` of projective objects over an arbitrary index type is projective
(`CategoryTheory.Projective.of_hasBiproduct`).

Objects that are both projective and injective are closed under binary biproducts
(`CategoryTheory.projective_and_injective_biprod`).
-/

public section

open CategoryTheory Limits ZeroObject

namespace CategoryTheory

variable {C : Type*} [Category* C]

/-- Being projective is invariant under isomorphism. -/
instance isClosedUnderIsomorphisms_isProjective : (isProjective C).IsClosedUnderIsomorphisms :=
  ⟨fun e h => @Projective.of_iso _ _ _ _ e h⟩

/-- A retract of a projective object is projective. -/
instance isStableUnderRetracts_isProjective : (isProjective C).IsStableUnderRetracts :=
  ⟨fun r h => @Retract.projective _ _ _ _ r h⟩

/-- A zero object is projective. -/
instance containsZero_isProjective [HasZeroObject C] : (isProjective C).ContainsZero :=
  ⟨⟨0, isZero_zero C, Projective.zero_projective⟩⟩

/-- In a category with binary biproducts, a binary product of projective objects is projective,
since it is a biproduct. -/
instance isClosedUnderBinaryProducts_isProjective [HasZeroMorphisms C] [HasBinaryBiproducts C] :
    (isProjective C).IsClosedUnderBinaryProducts :=
  ObjectProperty.isClosedUnderBinaryProducts_of_prop_biprod _
    fun _ _ (_ : Projective _) (_ : Projective _) => inferInstance

section FiniteBiproducts

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts
  hasFiniteProducts_of_hasFiniteBiproducts

/-- In a category with zero morphisms and finite biproducts, projective objects are closed under
finite products. -/
instance isClosedUnderFiniteProducts_isProjective [HasZeroMorphisms C] [HasFiniteBiproducts C] :
    (isProjective C).IsClosedUnderFiniteProducts :=
  .mk'

end FiniteBiproducts

namespace Projective

/-- The point of a colimit cofan of projective objects is projective. -/
theorem of_isColimit_cofan {ι : Type*} {X : ι → C} [∀ i, Projective (X i)] {c : Cofan X}
    (hc : IsColimit c) : Projective c.pt where
  factors f e _ := ⟨Cofan.IsColimit.desc hc fun i ↦ factorThru (c.inj i ≫ f) e,
    Cofan.IsColimit.hom_ext hc _ _ fun i ↦ by simp⟩

/-- A biproduct of projective objects indexed by any type is projective. Unlike Mathlib's instance
on `⨁ f`, the index type need not live in the morphism universe of `C`. -/
theorem of_hasBiproduct [HasZeroMorphisms C] {ι : Type*} (f : ι → C) [HasBiproduct f]
    [∀ i, Projective (f i)] : Projective (⨁ f) :=
  of_isColimit_cofan (biproduct.isColimit f)

end Projective

/-- Objects that are both projective and injective are closed under binary biproducts. -/
theorem projective_and_injective_biprod {C : Type*} [Category* C] [HasZeroMorphisms C] (A B : C)
    [HasBinaryBiproduct A B] (hA : Projective A ∧ Injective A) (hB : Projective B ∧ Injective B) :
    Projective (A ⊞ B) ∧ Injective (A ⊞ B) := by
  obtain ⟨_, _⟩ := hA
  obtain ⟨_, _⟩ := hB
  exact ⟨inferInstance, inferInstance⟩

end CategoryTheory
