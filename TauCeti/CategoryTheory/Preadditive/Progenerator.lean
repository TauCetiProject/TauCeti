/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Generator.Preadditive
public import TauCeti.CategoryTheory.Preadditive.AdditiveGenerator
public import TauCeti.CategoryTheory.Preadditive.Projective.Retract

/-!
# Progenerators of preadditive categories

An object `P` of a preadditive category `C` with finite biproducts is a **progenerator**
(`TauCeti.IsProgenerator P`) when it is projective and every object of `C` admits an epimorphism
from a finite biproduct `Pⁿ` of copies of `P`. Equivalently, `P` is projective and every object is
a quotient of an object in the additive closure `add P` (`TauCeti.additiveClosure P`).

A progenerator controls all projective objects of `C`: every finite biproduct `Pⁿ` and its retracts
are projective, and conversely any projective object `X` lifts its identity along an epimorphism
`Pⁿ ⟶ X` to become a direct summand of `Pⁿ`. Thus `proj C = add P`
(`TauCeti.IsProgenerator.isProjective_eq_additiveClosure`), `C` has enough projectives
(`TauCeti.IsProgenerator.enoughProjectives`), and `P` is a separator of `C`
(`TauCeti.IsProgenerator.isSeparator`).

Every projective additive generator is a progenerator, and the two notions coincide when every
object of `C` is projective. Like additive generators, progenerators are preserved by isomorphisms,
by adding projective direct summands, by positive finite powers, and by equivalences of categories.
In an abelian category, `Hom(P, -)` identifies `C` with the finitely presented right
`End P`-modules (`TauCeti.CategoryTheory.Abelian.Progenerator.Basic`).

## Main definitions

* `TauCeti.IsProgenerator P`: `P` is projective and every object of `C` is a quotient of some `Pⁿ`.

## Main results

* `TauCeti.isProgenerator_iff` and `TauCeti.isProgenerator_iff_exists_additiveClosure`: the
  biproduct and additive-closure characterizations.
* `TauCeti.IsProgenerator.isProjective_eq_additiveClosure`,
  `TauCeti.IsProgenerator.projective_iff_additiveClosure`, and
  `TauCeti.isProgenerator_iff_isProjective_eq_additiveClosure`: `proj C = add P`.
* `TauCeti.IsProgenerator.enoughProjectives` and `TauCeti.IsProgenerator.isSeparator`: a category
  with a progenerator has enough projectives, and any progenerator is a separator.
* `TauCeti.IsAdditiveGenerator.isProgenerator` and
  `TauCeti.isProgenerator_iff_isAdditiveGenerator_of_forall_projective`: comparison with additive
  generators.
* `TauCeti.IsProgenerator.of_additiveClosure`, `CategoryTheory.Retract.isProgenerator`,
  `TauCeti.IsProgenerator.of_iso`, `TauCeti.IsProgenerator.biprod_left`,
  `TauCeti.IsProgenerator.biprod_right`, `TauCeti.IsProgenerator.biproduct` and
  `CategoryTheory.Functor.isProgenerator_obj_iff`: closure and equivalence invariance.

## References

* Henning Krause, *Krull-Schmidt categories and projective covers*, Expo. Math. 33 (2015),
  535–549, Section 3.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

/-- An object `P` of a preadditive category with finite biproducts is a **progenerator** when it is
projective and every object of `C` admits an epimorphism from a finite biproduct `Pⁿ` of copies of
`P`. -/
structure IsProgenerator (P : C) : Prop where
  /-- A progenerator is a projective object. -/
  projective : Projective P := by infer_instance
  /-- Every object is a quotient of a finite biproduct of copies of `P`. -/
  exists_epi_biproduct (X : C) : ∃ (n : ℕ) (π : (⨁ fun _ : Fin n ↦ P) ⟶ X), Epi π

/-- Unfolded characterization of a progenerator. -/
theorem isProgenerator_iff {P : C} :
    IsProgenerator P ↔
      Projective P ∧ ∀ X : C, ∃ (n : ℕ) (π : (⨁ fun _ : Fin n ↦ P) ⟶ X), Epi π :=
  ⟨fun h ↦ ⟨h.projective, h.exists_epi_biproduct⟩, fun ⟨h₁, h₂⟩ ↦ ⟨h₁, h₂⟩⟩

/-- `P` is a progenerator if and only if `P` is projective and every object of `C` admits an
epimorphism from an object in `add P`. -/
theorem isProgenerator_iff_exists_additiveClosure {P : C} :
    IsProgenerator P ↔
      Projective P ∧ ∀ X : C, ∃ (Q : C) (π : Q ⟶ X), additiveClosure P Q ∧ Epi π := by
  rw [isProgenerator_iff]
  refine and_congr_right fun _ ↦ ⟨fun h X ↦ ?_, fun h X ↦ ?_⟩
  · obtain ⟨n, π, hπ⟩ := h X
    exact ⟨_, π, additiveClosure_biproduct n, hπ⟩
  · obtain ⟨Q, π, hQ, hπ⟩ := h X
    obtain ⟨n, ⟨r⟩⟩ := additiveClosure_iff.mp hQ
    have : IsSplitEpi r.r := ⟨⟨r.i, r.retract⟩⟩
    exact ⟨n, r.r ≫ π, epi_comp _ _⟩

namespace IsProgenerator

variable {P P' Q : C}

/-- Every object of `C` admits an epimorphism from an object in the additive closure of a
progenerator. -/
theorem exists_epi_additiveClosure (hP : IsProgenerator P) (X : C) :
    ∃ (Q : C) (π : Q ⟶ X), additiveClosure P Q ∧ Epi π :=
  (isProgenerator_iff_exists_additiveClosure.mp hP).2 X

/-- Every object in the additive closure of a progenerator is projective. -/
theorem additiveClosure_le_isProjective (hP : IsProgenerator P) :
    additiveClosure P ≤ isProjective C :=
  additiveClosure_le_iff.mpr hP.projective

/-- Every projective object lies in the additive closure of a progenerator: its identity lifts
along an epimorphism `Pⁿ ⟶ X`. -/
theorem isProjective_le_additiveClosure (hP : IsProgenerator P) :
    isProjective C ≤ additiveClosure P := by
  intro X hX
  obtain ⟨n, π, hπ⟩ := hP.exists_epi_biproduct X
  exact additiveClosure_iff.mpr
    ⟨n, ⟨{ i := Projective.factorThru (𝟙 X) π, r := π }⟩⟩

/-- **For a progenerator `P`, the projective objects of `C` are precisely `add P`.** -/
theorem isProjective_eq_additiveClosure (hP : IsProgenerator P) :
    isProjective C = additiveClosure P :=
  le_antisymm hP.isProjective_le_additiveClosure hP.additiveClosure_le_isProjective

/-- For a progenerator `P`, an object of `C` is projective if and only if it lies in `add P`. -/
theorem projective_iff_additiveClosure (hP : IsProgenerator P) {X : C} :
    Projective X ↔ additiveClosure P X :=
  ⟨fun h ↦ hP.isProjective_le_additiveClosure X h, fun h ↦ hP.additiveClosure_le_isProjective X h⟩

/-- A category possessing a progenerator has enough projectives. -/
theorem enoughProjectives (hP : IsProgenerator P) : EnoughProjectives C where
  presentation X := by
    have := hP.projective
    obtain ⟨n, π, hπ⟩ := hP.exists_epi_biproduct X
    have : Projective (⨁ fun _ : Fin n ↦ P) := Projective.of_hasBiproduct _
    exact ⟨{ p := _, f := π }⟩

/-- A progenerator is a separator: morphisms out of `P` jointly detect zero morphisms. -/
theorem isSeparator (hP : IsProgenerator P) : IsSeparator P :=
  (Preadditive.isSeparator_iff P).mpr fun X _ f hf ↦ by
    obtain ⟨n, π, hπ⟩ := hP.exists_epi_biproduct X
    have hπf : π ≫ f = 0 := biproduct.hom_ext' _ _ fun i ↦ by
      simpa using hf (biproduct.ι (fun _ : Fin n ↦ P) i ≫ π)
    exact (cancel_epi π).mp (by simpa using hπf)

/-- If a progenerator `P` lies in `add P'` for a projective object `P'`, then `P'` is also a
progenerator. -/
theorem of_additiveClosure (hP : IsProgenerator P) [Projective P'] (h : additiveClosure P' P) :
    IsProgenerator P' :=
  isProgenerator_iff_exists_additiveClosure.mpr ⟨inferInstance, fun X ↦ by
    obtain ⟨Q, π, hQ, hπ⟩ := hP.exists_epi_additiveClosure X
    exact ⟨Q, π, additiveClosure_le_iff.mpr h Q hQ, hπ⟩⟩

end IsProgenerator

/-- In a category with enough projectives, `P` is a progenerator if and only if the projective
objects of `C` are precisely `add P`. -/
theorem isProgenerator_iff_isProjective_eq_additiveClosure [EnoughProjectives C] {P : C} :
    IsProgenerator P ↔ isProjective C = additiveClosure P := by
  refine ⟨IsProgenerator.isProjective_eq_additiveClosure, fun h ↦ ?_⟩
  have hP : Projective P := by
    change isProjective C P
    rw [h]
    exact additiveClosure_self P
  refine isProgenerator_iff_exists_additiveClosure.mpr ⟨hP, fun X ↦ ?_⟩
  refine ⟨Projective.over X, Projective.π X, ?_, inferInstance⟩
  rw [← h]
  exact (inferInstance : Projective (Projective.over X))

/-- A projective object admitting a progenerator as a retract is itself a progenerator. -/
theorem _root_.CategoryTheory.Retract.isProgenerator {P P' : C} (h : Retract P P')
    (hP : IsProgenerator P) [Projective P'] : IsProgenerator P' :=
  hP.of_additiveClosure ((additiveClosure P').prop_of_retract h (additiveClosure_self P'))

namespace IsProgenerator

variable {P P' Q : C}

/-- Progenerators are invariant under isomorphism. -/
theorem of_iso (hP : IsProgenerator P) (e : P ≅ P') : IsProgenerator P' :=
  have := Projective.of_iso e hP.projective
  (Retract.ofIso e).isProgenerator hP

/-- Adding a projective direct summand on the right preserves being a progenerator. -/
theorem biprod_left (hP : IsProgenerator P) [Projective Q] : IsProgenerator (P ⊞ Q) :=
  have := hP.projective
  Retract.isProgenerator ⟨biprod.inl, biprod.fst, by simp⟩ hP

/-- Adding a projective direct summand on the left preserves being a progenerator. -/
theorem biprod_right (hP : IsProgenerator P) [Projective Q] : IsProgenerator (Q ⊞ P) :=
  have := hP.projective
  Retract.isProgenerator ⟨biprod.inr, biprod.snd, by simp⟩ hP

/-- Any positive finite biproduct power `Pⁿ` (`n ≠ 0`) of a progenerator is a progenerator. -/
theorem biproduct (hP : IsProgenerator P) (n : ℕ) [NeZero n] :
    IsProgenerator (⨁ fun _ : Fin n ↦ P) :=
  have := hP.projective
  have := Projective.of_hasBiproduct fun _ : Fin n ↦ P
  Retract.isProgenerator ⟨biproduct.ι _ 0, biproduct.π _ 0, by simp⟩ hP

/-- When every object of `C` is projective, a progenerator is an additive generator. -/
theorem isAdditiveGenerator_of_forall_projective (hP : IsProgenerator P)
    (hC : ∀ X : C, Projective X) : IsAdditiveGenerator P :=
  isAdditiveGenerator_def.mpr fun X ↦ hP.projective_iff_additiveClosure.mp (hC X)

end IsProgenerator

/-- Every projective additive generator is a progenerator: each object is a retract, hence a split
quotient, of a finite biproduct of copies of `G`. -/
theorem IsAdditiveGenerator.isProgenerator {G : C} (hG : IsAdditiveGenerator G) [Projective G] :
    IsProgenerator G where
  exists_epi_biproduct X := by
    obtain ⟨n, ⟨r⟩⟩ := additiveClosure_iff.mp (hG.additiveClosure X)
    have : IsSplitEpi r.r := ⟨⟨r.i, r.retract⟩⟩
    exact ⟨n, r.r, inferInstance⟩

/-- When every object of `C` is projective, progenerators and additive generators coincide. -/
theorem isProgenerator_iff_isAdditiveGenerator_of_forall_projective
    (hC : ∀ X : C, Projective X) {P : C} :
    IsProgenerator P ↔ IsAdditiveGenerator P :=
  have := hC P
  ⟨fun h ↦ h.isAdditiveGenerator_of_forall_projective hC, fun h ↦ h.isProgenerator⟩

end TauCeti

namespace CategoryTheory.Functor

open Limits TauCeti

variable {C : Type*} [Category* C] [Preadditive C] [HasFiniteBiproducts C]
  {D : Type*} [Category* D] [Preadditive D] [HasFiniteBiproducts D]

/-- An equivalence of categories carries progenerators to progenerators. -/
theorem isProgenerator_obj (F : C ⥤ D) [F.IsEquivalence] {P : C} (hP : IsProgenerator P) :
    IsProgenerator (F.obj P) where
  projective := (F.asEquivalence.map_projective_iff P).mpr hP.projective
  exists_epi_biproduct Y := by
    obtain ⟨n, π, hπ⟩ := hP.exists_epi_biproduct (F.inv.obj Y)
    have : Epi (F.map π ≫ F.asEquivalence.counitIso.hom.app Y) := epi_comp _ _
    exact ⟨n, (F.mapBiproduct fun _ : Fin n ↦ P).inv ≫ F.map π ≫
      F.asEquivalence.counitIso.hom.app Y, epi_comp _ _⟩

/-- **Progenerators are invariant under equivalences of categories.** -/
@[simp]
theorem isProgenerator_obj_iff (F : C ⥤ D) [F.IsEquivalence] (P : C) :
    IsProgenerator (F.obj P) ↔ IsProgenerator P :=
  ⟨fun hP ↦ (F.inv.isProgenerator_obj hP).of_iso (F.asEquivalence.unitIso.app P).symm,
    F.isProgenerator_obj⟩

end CategoryTheory.Functor
