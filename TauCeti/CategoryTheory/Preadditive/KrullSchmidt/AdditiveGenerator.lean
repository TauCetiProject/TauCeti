/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.KrullSchmidt.Basic
public import TauCeti.CategoryTheory.Preadditive.KrullSchmidt.Uniqueness
public import Mathlib.CategoryTheory.Retract

/-!
# Additive generators

An object `G` of a preadditive category is an **additive generator** if every indecomposable
object is a direct summand of `G`. In the category `mod A` of finitely generated modules over an
Artin algebra, an additive generator exists exactly when `A` is representation-finite; its
endomorphism ring is the Auslander algebra of `A`.

Additive generators are invariant under isomorphism and under adding direct summands, and an
equivalence of categories carries them to additive generators. A biproduct of objects representing
every indecomposable object up to isomorphism is an additive generator. Conversely, in a
Krull-Schmidt category the summands of a decomposition of an additive generator represent every
indecomposable object: an indecomposable direct summand has a local endomorphism ring, so it is
isomorphic to one of the summands (`TauCeti.exists_isIso_comp_π_of_retract`). Hence a
Krull-Schmidt category has an additive generator exactly when it has finitely many
indecomposable objects up to isomorphism.

## Main definitions

* `TauCeti.IsAdditiveGenerator`: every indecomposable object is a direct summand of `G`.

## Main results

* `TauCeti.isAdditiveGenerator_iff` and `TauCeti.IsAdditiveGenerator.nonempty_retract`: the
  defining property.
* `CategoryTheory.Retract.isAdditiveGenerator` and `TauCeti.IsAdditiveGenerator.of_iso`: invariance
  under adding direct summands and under isomorphism.
* `CategoryTheory.Equivalence.isAdditiveGenerator_functor_obj_iff`: invariance under equivalence of
  categories.
* `TauCeti.isAdditiveGenerator_biproduct`: a biproduct of objects representing every
  indecomposable object is an additive generator.
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

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]

/-- An object `G` is an **additive generator** if every indecomposable object is a direct summand
of `G`. -/
def IsAdditiveGenerator (G : C) : Prop :=
  ∀ X : C, Indecomposable X → Nonempty (Retract X G)

/-- The defining property of an additive generator: every indecomposable object is a retract of
it. -/
theorem isAdditiveGenerator_iff {G : C} :
    IsAdditiveGenerator G ↔ ∀ X : C, Indecomposable X → Nonempty (Retract X G) :=
  Iff.rfl

/-- **An object having an additive generator as a direct summand is an additive generator.** -/
theorem _root_.CategoryTheory.Retract.isAdditiveGenerator {G G' : C} (h : Retract G G')
    (hG : IsAdditiveGenerator G) : IsAdditiveGenerator G' :=
  fun X hX ↦ (hG X hX).map (·.trans h)

namespace IsAdditiveGenerator

variable {G G' : C}

/-- Every indecomposable object is a retract of an additive generator. -/
theorem nonempty_retract (hG : IsAdditiveGenerator G) {X : C} (hX : Indecomposable X) :
    Nonempty (Retract X G) :=
  hG X hX

/-- **Additive generators are invariant under isomorphism.** -/
theorem of_iso (hG : IsAdditiveGenerator G) (e : G ≅ G') : IsAdditiveGenerator G' :=
  (Retract.ofIso e).isAdditiveGenerator hG

/-- Adding a direct summand to an additive generator gives an additive generator. -/
theorem biprod_left [HasBinaryBiproduct G G'] (hG : IsAdditiveGenerator G) :
    IsAdditiveGenerator (G ⊞ G') :=
  Retract.isAdditiveGenerator ⟨biprod.inl, biprod.fst, by simp⟩ hG

/-- Adding a direct summand to an additive generator gives an additive generator. -/
theorem biprod_right [HasBinaryBiproduct G' G] (hG : IsAdditiveGenerator G) :
    IsAdditiveGenerator (G' ⊞ G) :=
  Retract.isAdditiveGenerator ⟨biprod.inr, biprod.snd, by simp⟩ hG

end IsAdditiveGenerator

/-- **Representatives of the indecomposable objects give an additive generator**: if every
indecomposable object is isomorphic to one of the objects `P i`, their biproduct is an additive
generator. -/
theorem isAdditiveGenerator_biproduct {ι : Type w} (P : ι → C) [HasBiproduct P]
    (hP : ∀ X : C, Indecomposable X → ∃ i, Nonempty (X ≅ P i)) : IsAdditiveGenerator (⨁ P) :=
  fun X hX ↦ by
    obtain ⟨i, ⟨e⟩⟩ := hP X hX
    exact ⟨(Retract.ofIso e).trans ⟨biproduct.ι P i, biproduct.π P i, by simp⟩⟩

/-- **A Krull-Schmidt category has an additive generator exactly when it has finitely many
indecomposable objects up to isomorphism.** The summands of a decomposition of an additive
generator represent every indecomposable object, and conversely the biproduct of representatives
is an additive generator. -/
theorem exists_isAdditiveGenerator_iff [HasFiniteBiproducts C] [IsKrullSchmidt C] :
    (∃ G : C, IsAdditiveGenerator G) ↔
      ∃ (n : ℕ) (P : Fin n → C), ∀ X : C, Indecomposable X → ∃ i, Nonempty (X ≅ P i) := by
  refine ⟨fun ⟨G, hG⟩ ↦ ?_, fun ⟨n, P, hP⟩ ↦ ⟨⨁ P, isAdditiveGenerator_biproduct P hP⟩⟩
  obtain ⟨n, P, hP, ⟨φ⟩⟩ := IsKrullSchmidt.exists_iso_biproduct G
  refine ⟨n, P, fun X hX ↦ ?_⟩
  -- An indecomposable summand has a local endomorphism ring, so it is one of the `P i`.
  have := (IsKrullSchmidt.indecomposable_iff_isLocalRing_end X).1 hX
  obtain ⟨h⟩ := hG X hX
  obtain ⟨i, hi⟩ := exists_isIso_comp_π_of_retract P hP (h.trans (.ofIso φ))
  exact ⟨i, ⟨asIso ((h.trans (.ofIso φ)).i ≫ biproduct.π P i)⟩⟩

end TauCeti

namespace CategoryTheory.Equivalence

open Limits TauCeti

variable {C : Type*} [Category* C] [Preadditive C] [HasBinaryBiproducts C]
  {D : Type*} [Category* D] [Preadditive D] [HasBinaryBiproducts D]

/-- **Additive generators are invariant under equivalence of categories.** -/
theorem isAdditiveGenerator_functor_obj_iff (e : C ≌ D) (G : C) :
    IsAdditiveGenerator (e.functor.obj G) ↔ IsAdditiveGenerator G := by
  refine ⟨fun hG X hX ↦ ?_, fun hG X hX ↦ ?_⟩
  · obtain ⟨h⟩ := hG _ (e.indecomposable_functor_obj hX)
    exact ⟨((Retract.ofIso (e.unitIso.app X)).trans (h.map e.inverse)).trans
      (.ofIso (e.unitIso.app G).symm)⟩
  · obtain ⟨h⟩ := hG _ (e.symm.indecomposable_functor_obj hX)
    exact ⟨(Retract.ofIso (e.counitIso.app X).symm).trans (h.map e.functor)⟩

end CategoryTheory.Equivalence
