/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.KrullSchmidt.Basic
public import TauCeti.CategoryTheory.Preadditive.KrullSchmidt.Uniqueness
public import Mathlib.CategoryTheory.Retract
public import TauCeti.CategoryTheory.Preadditive.AdditiveClosure
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Additive generators

An object `G` of a preadditive category with finite biproducts is an **additive generator** if
`add G = C`: every object is a direct summand of a finite biproduct `Gⁿ` of copies of `G`, that is,
lies in the additive closure `TauCeti.additiveClosure G`. In the category `mod A` of finitely
generated modules over an Artin algebra, an additive generator exists exactly when `A` is
representation-finite; its endomorphism ring is the Auslander algebra of `A`.

Additive generators are invariant under isomorphism and under adding direct summands, and an
equivalence of categories carries them to additive generators. In a Krull-Schmidt category, `G` is
an additive generator exactly when every indecomposable object is a direct summand of `G`: an
indecomposable direct summand of `Gⁿ` has a local endomorphism ring, so it is isomorphic to a
summand of a decomposition of `G` (`TauCeti.exists_isIso_comp_π_of_retract`), and every object is
a finite biproduct of indecomposable objects. Hence a biproduct of objects representing every
indecomposable object is an additive generator, and a Krull-Schmidt category has an additive
generator exactly when it has finitely many indecomposable objects up to isomorphism. Outside
Krull-Schmidt categories the indecomposable condition is weaker: in a category with no
indecomposable objects every object satisfies it.

## Main definitions

* `TauCeti.IsAdditiveGenerator`: `add G = C`, every object is a direct summand of some `Gⁿ`.

## Main results

* `TauCeti.isAdditiveGenerator_iff`: the unfolded definition.
* `CategoryTheory.Retract.isAdditiveGenerator` and `TauCeti.IsAdditiveGenerator.of_iso`: invariance
  under adding direct summands and under isomorphism.
* `CategoryTheory.Equivalence.isAdditiveGenerator_functor_obj_iff`: invariance under equivalence of
  categories.
* `TauCeti.isAdditiveGenerator_iff_forall_indecomposable`: in a Krull-Schmidt category, `G` is an
  additive generator exactly when every indecomposable object is a direct summand of `G`.
* `TauCeti.isAdditiveGenerator_biproduct`: in a Krull-Schmidt category, a biproduct of objects
  representing every indecomposable object is an additive generator.
* `TauCeti.exists_isAdditiveGenerator_iff`: a Krull-Schmidt category has an additive generator
  exactly when finitely many objects represent every indecomposable object up to isomorphism.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  University Press (1995).
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe w v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

/-- An object `G` is an **additive generator** if `add G = C`: every object is a direct summand of
a finite biproduct of copies of `G`. -/
def IsAdditiveGenerator (G : C) : Prop :=
  ∀ X : C, additiveClosure G X

/-- The unfolded definition of an additive generator: every object is a retract of some `Gⁿ`. -/
theorem isAdditiveGenerator_iff {G : C} :
    IsAdditiveGenerator G ↔ ∀ X : C, ∃ n : ℕ, Nonempty (Retract X (⨁ fun _ : Fin n ↦ G)) :=
  forall_congr' fun _ ↦ additiveClosure_iff

/-- Every object lies in the additive closure of an additive generator. -/
theorem IsAdditiveGenerator.additiveClosure {G : C} (hG : IsAdditiveGenerator G) (X : C) :
    TauCeti.additiveClosure G X :=
  hG X

/-- **An object having an additive generator as a direct summand is an additive generator.** -/
theorem _root_.CategoryTheory.Retract.isAdditiveGenerator {G G' : C} (h : Retract G G')
    (hG : IsAdditiveGenerator G) : IsAdditiveGenerator G' :=
  fun X ↦ additiveClosure_le_iff.2
    ((additiveClosure G').prop_of_retract h (additiveClosure_self G')) X (hG X)

namespace IsAdditiveGenerator

variable {G G' : C}

/-- **Additive generators are invariant under isomorphism.** -/
theorem of_iso (hG : IsAdditiveGenerator G) (e : G ≅ G') : IsAdditiveGenerator G' :=
  (Retract.ofIso e).isAdditiveGenerator hG

/-- Adding a direct summand to an additive generator gives an additive generator. -/
theorem biprod_left (hG : IsAdditiveGenerator G) : IsAdditiveGenerator (G ⊞ G') :=
  Retract.isAdditiveGenerator ⟨biprod.inl, biprod.fst, by simp⟩ hG

/-- Adding a direct summand to an additive generator gives an additive generator. -/
theorem biprod_right (hG : IsAdditiveGenerator G) : IsAdditiveGenerator (G' ⊞ G) :=
  Retract.isAdditiveGenerator ⟨biprod.inr, biprod.snd, by simp⟩ hG

end IsAdditiveGenerator

/-- **Additive generators of a Krull-Schmidt category**: `G` is an additive generator exactly when
every indecomposable object is a direct summand of `G`. An indecomposable direct summand of `Gⁿ`
is isomorphic to a summand of a decomposition of `G`, since its endomorphism ring is local; and
every object is a finite biproduct of indecomposable objects. -/
theorem isAdditiveGenerator_iff_forall_indecomposable [IsKrullSchmidt C] {G : C} :
    IsAdditiveGenerator G ↔ ∀ X : C, Indecomposable X → Nonempty (Retract X G) := by
  refine ⟨fun hG X hX ↦ ?_, fun hG X ↦ ?_⟩
  · obtain ⟨n, ⟨h⟩⟩ := additiveClosure_iff.1 (hG X)
    obtain ⟨m, P, hP, ⟨φ⟩⟩ := IsKrullSchmidt.exists_iso_biproduct G
    have := (IsKrullSchmidt.indecomposable_iff_isLocalRing_end X).1 hX
    -- `Gⁿ` is a biproduct of copies of the summands `P j` of `G`.
    let h' := h.trans (.ofIso (biproduct.mapIso (fun _ ↦ φ) ≪≫
      biproductBiproductIso (fun _ : Fin n ↦ Fin m) fun _ j ↦ P j))
    obtain ⟨j, hj⟩ := exists_isIso_comp_π_of_retract (fun p : Σ _ : Fin n, Fin m ↦ P p.2)
      (fun p ↦ hP p.2) h'
    exact ⟨((Retract.ofIso (asIso (h'.i ≫ biproduct.π _ j))).trans
      ⟨biproduct.ι P j.2, biproduct.π P j.2, by simp⟩).trans (.ofIso φ.symm)⟩
  · obtain ⟨m, P, hP, ⟨φ⟩⟩ := IsKrullSchmidt.exists_iso_biproduct X
    refine (additiveClosure G).prop_of_iso φ.symm
      ((additiveClosure G).prop_of_isLimit (biproduct.isLimit _) fun ⟨i⟩ ↦ ?_)
    obtain ⟨h⟩ := hG (P i) indecomposable_of_isLocalRing_end
    exact (additiveClosure G).prop_of_retract h (additiveClosure_self G)

/-- In a Krull-Schmidt category, every indecomposable object is a retract of an additive
generator. -/
theorem IsAdditiveGenerator.nonempty_retract [IsKrullSchmidt C] {G : C}
    (hG : IsAdditiveGenerator G) {X : C} (hX : Indecomposable X) : Nonempty (Retract X G) :=
  isAdditiveGenerator_iff_forall_indecomposable.1 hG X hX

/-- **Representatives of the indecomposable objects give an additive generator**: in a
Krull-Schmidt category, if every indecomposable object is isomorphic to one of the objects `P i`,
their biproduct is an additive generator. -/
theorem isAdditiveGenerator_biproduct [IsKrullSchmidt C] {ι : Type w} (P : ι → C)
    [HasBiproduct P] (hP : ∀ X : C, Indecomposable X → ∃ i, Nonempty (X ≅ P i)) :
    IsAdditiveGenerator (⨁ P) :=
  isAdditiveGenerator_iff_forall_indecomposable.2 fun X hX ↦ by
    obtain ⟨i, ⟨e⟩⟩ := hP X hX
    exact ⟨(Retract.ofIso e).trans ⟨biproduct.ι P i, biproduct.π P i, by simp⟩⟩

/-- **A Krull-Schmidt category has an additive generator exactly when it has finitely many
indecomposable objects up to isomorphism.** The summands of a decomposition of an additive
generator represent every indecomposable object, and conversely the biproduct of representatives
is an additive generator. -/
theorem exists_isAdditiveGenerator_iff [IsKrullSchmidt C] :
    (∃ G : C, IsAdditiveGenerator G) ↔
      ∃ (n : ℕ) (P : Fin n → C), ∀ X : C, Indecomposable X → ∃ i, Nonempty (X ≅ P i) := by
  refine ⟨fun ⟨G, hG⟩ ↦ ?_, fun ⟨n, P, hP⟩ ↦ ⟨⨁ P, isAdditiveGenerator_biproduct P hP⟩⟩
  obtain ⟨n, P, hP, ⟨φ⟩⟩ := IsKrullSchmidt.exists_iso_biproduct G
  refine ⟨n, P, fun X hX ↦ ?_⟩
  -- An indecomposable summand has a local endomorphism ring, so it is one of the `P i`.
  have := (IsKrullSchmidt.indecomposable_iff_isLocalRing_end X).1 hX
  obtain ⟨h⟩ := hG.nonempty_retract hX
  obtain ⟨i, hi⟩ := exists_isIso_comp_π_of_retract P hP (h.trans (.ofIso φ))
  exact ⟨i, ⟨asIso ((h.trans (.ofIso φ)).i ≫ biproduct.π P i)⟩⟩

end TauCeti

namespace CategoryTheory.Equivalence

open Limits TauCeti

variable {C : Type*} [Category* C] [Preadditive C] [HasFiniteBiproducts C]
  {D : Type*} [Category* D] [Preadditive D] [HasFiniteBiproducts D]

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

/-- An equivalence of categories carries an additive generator to an additive generator. -/
theorem isAdditiveGenerator_functor_obj (e : C ≌ D) {G : C} (hG : IsAdditiveGenerator G) :
    IsAdditiveGenerator (e.functor.obj G) := by
  have : ((additiveClosure (e.functor.obj G)).inverseImage e.functor).IsStableUnderRetracts :=
    ⟨fun h hY ↦ (additiveClosure _).prop_of_retract (h.map e.functor) hY⟩
  have : ((additiveClosure (e.functor.obj G)).inverseImage e.functor).IsClosedUnderFiniteProducts :=
    ⟨fun _ _ ↦ ObjectProperty.IsClosedUnderLimitsOfShape.inverseImage _ _ _⟩
  have hQ : additiveClosure G ≤ (additiveClosure (e.functor.obj G)).inverseImage e.functor :=
    additiveClosure_le_iff.2 (additiveClosure_self _)
  exact fun Y ↦ (additiveClosure _).prop_of_iso (e.counitIso.app Y) (hQ _ (hG _))

/-- **Additive generators are invariant under equivalence of categories.** -/
theorem isAdditiveGenerator_functor_obj_iff (e : C ≌ D) (G : C) :
    IsAdditiveGenerator (e.functor.obj G) ↔ IsAdditiveGenerator G :=
  ⟨fun hG ↦ (e.symm.isAdditiveGenerator_functor_obj hG).of_iso (e.unitIso.app G).symm,
    e.isAdditiveGenerator_functor_obj⟩

end CategoryTheory.Equivalence
