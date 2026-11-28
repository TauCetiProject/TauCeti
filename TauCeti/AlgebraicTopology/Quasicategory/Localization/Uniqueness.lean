/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.Localization

/-!
# Uniqueness of localizations

The functor-space universal property of a localization gives factorization of functors
inverting the marked edges, and detects equivalences between such factorizations. Consequently
two localizations with quasicategory targets are related by a categorical equivalence,
compatible with their maps from the original simplicial set up to an equivalence edge.
The source simplicial set need not be a quasicategory. For maps between quasicategories,
localizing at the empty marking is equivalent to being a categorical equivalence.

## References

* J. Lurie, *Higher Algebra*, Definition 1.3.4.1.
* J. Lurie, *Higher Topos Theory*, §1.2.7.
-/

public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed Simplicial

namespace SSet.IsLocalization

variable {C D E : SSet.{u}} {W : Set (C _⦋1⦌)} {f : C ⟶ D}

/-- Two functors out of a localization are equivalent exactly when their restrictions are. -/
lemma nonempty_iso_comp_iff (hf : IsLocalization f W) [Quasicategory E] (g h : D ⟶ E) :
    Nonempty (HomotopyCategory.mk ((ihomObj₀Equiv _ _).symm (f ≫ g)) ≅
      HomotopyCategory.mk ((ihomObj₀Equiv _ _).symm (f ≫ h))) ↔
    Nonempty (HomotopyCategory.mk ((ihomObj₀Equiv _ _).symm g) ≅
      HomotopyCategory.mk ((ihomObj₀Equiv _ _).symm h)) := by
  let F := mapHomotopyCategory ((pre f).app E)
  obtain ⟨_, _⟩ := hf.full_faithful_mapHomotopyCategory_pre_app E
  let hF := Functor.FullyFaithful.ofFullyFaithful F
  have hg : F.obj (HomotopyCategory.mk ((ihomObj₀Equiv _ _).symm g)) =
      HomotopyCategory.mk ((ihomObj₀Equiv _ _).symm (f ≫ g)) := by
    simp [F]
  have hh : F.obj (HomotopyCategory.mk ((ihomObj₀Equiv _ _).symm h)) =
      HomotopyCategory.mk ((ihomObj₀Equiv _ _).symm (f ≫ h)) := by
    simp [F]
  exact ⟨fun ⟨e⟩ ↦ ⟨hF.preimageIso (eqToIso hg ≪≫ e ≪≫ (eqToIso hh).symm)⟩,
    fun ⟨e⟩ ↦ ⟨(eqToIso hg).symm ≪≫ F.mapIso e ≪≫ eqToIso hh⟩⟩

/-- Every functor inverting the marked edges factors through a localization, up to an
equivalence edge in the functor quasicategory. -/
theorem exists_comp_isEquivalence (hf : IsLocalization f W) [Quasicategory E]
    (g : C ⟶ E) (hg : ∀ w ∈ W, ((Edge.mk' w).map g).IsEquivalence) :
    ∃ (h : D ⟶ E) (e : Edge ((ihomObj₀Equiv _ _).symm (f ≫ h))
      ((ihomObj₀Equiv _ _).symm g)), e.IsEquivalence := by
  let v : (functorsInverting W E : SSet) _⦋0⦌ :=
    ⟨(ihomObj₀Equiv _ _).symm g, (ihomObj₀Equiv_symm_mem_functorsInverting_iff W g).2 hg⟩
  obtain ⟨x, e, he⟩ := (hf.isCategoricalEquivalence E).exists_isEquivalence v
  obtain ⟨h, rfl⟩ := (ihomObj₀Equiv _ _).symm.surjective x
  have hsrc : (functorsInverting W E).ι.app _
      ((functorsInverting.precomp f hf.isIso_homotopyCategoryHomMk_map E).app _
        ((ihomObj₀Equiv _ _).symm h)) = (ihomObj₀Equiv _ _).symm (f ≫ h) := by
    rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, functorsInverting.precomp_ι,
      pre_app_app_ihomObj₀Equiv_symm]
  exact ⟨h, (e.map (functorsInverting W E).ι).ofEq hsrc rfl,
    (Edge.isEquivalence_ofEq_iff _ _).2 (he.map _)⟩

/-- Any two localizations into quasicategories are related by a categorical equivalence
compatible, up to an equivalence edge, with the maps from the original simplicial set. -/
theorem exists_isCategoricalEquivalence [Quasicategory D] [Quasicategory E]
    (hf : IsLocalization f W) {f' : C ⟶ E} (hf' : IsLocalization f' W) :
    ∃ g : D ⟶ E,
      QCat.IsCategoricalEquivalence (X := ⟨D, inferInstance⟩) (Y := ⟨E, inferInstance⟩)
        (ObjectProperty.homMk g) ∧
      ∃ e : Edge ((ihomObj₀Equiv _ _).symm (f ≫ g)) ((ihomObj₀Equiv _ _).symm f'),
        e.IsEquivalence := by
  obtain ⟨g, α, hα⟩ := hf.exists_comp_isEquivalence f' hf'.isEquivalence_map
  obtain ⟨h, β, hβ⟩ := hf'.exists_comp_isEquivalence f hf.isEquivalence_map
  have hcomp {A B : SSet.{u}} [Quasicategory B] {a b : C ⟶ A}
      (e : Edge ((ihomObj₀Equiv _ _).symm a) ((ihomObj₀Equiv _ _).symm b))
      (he : e.IsEquivalence) (k : A ⟶ B) :
      Nonempty (HomotopyCategory.mk ((ihomObj₀Equiv _ _).symm (a ≫ k)) ≅
        HomotopyCategory.mk ((ihomObj₀Equiv _ _).symm (b ≫ k))) := by
    have hi := he.map ((ihom C).map k)
    have hv (a : C ⟶ A) : ((ihom C).map k).app _ ((ihomObj₀Equiv _ _).symm a) =
        (ihomObj₀Equiv _ _).symm (a ≫ k) :=
      (Equiv.eq_symm_apply _).2 (by simp)
    simpa only [hv] using
      (HomotopyCategory.nonempty_iso_mk_iff.2 ⟨e.map ((ihom C).map k), hi⟩)
  have hgh : Nonempty (HomotopyCategory.mk ((ihomObj₀Equiv _ _).symm (g ≫ h)) ≅
      HomotopyCategory.mk ((ihomObj₀Equiv _ _).symm (𝟙 D))) := by
    apply (hf.nonempty_iso_comp_iff _ _).1
    obtain ⟨i⟩ := hcomp α hα h
    obtain ⟨j⟩ := HomotopyCategory.nonempty_iso_mk_iff.2 ⟨β, hβ⟩
    simpa only [Category.assoc, Category.comp_id] using Nonempty.intro (i ≪≫ j)
  have hhg : Nonempty (HomotopyCategory.mk ((ihomObj₀Equiv _ _).symm (h ≫ g)) ≅
      HomotopyCategory.mk ((ihomObj₀Equiv _ _).symm (𝟙 E))) := by
    apply (hf'.nonempty_iso_comp_iff _ _).1
    obtain ⟨i⟩ := hcomp β hβ g
    obtain ⟨j⟩ := HomotopyCategory.nonempty_iso_mk_iff.2 ⟨α, hα⟩
    simpa only [Category.assoc, Category.comp_id] using Nonempty.intro (i ≪≫ j)
  let X : QCat := ⟨D, inferInstance⟩
  let Y : QCat := ⟨E, inferInstance⟩
  let g' : X ⟶ Y := ObjectProperty.homMk g
  let h' : Y ⟶ X := ObjectProperty.homMk h
  obtain ⟨η, hη⟩ := HomotopyCategory.nonempty_iso_mk_iff.1 hgh
  obtain ⟨ε, hε⟩ := HomotopyCategory.nonempty_iso_mk_iff.1 hhg
  have η' := QCat.nonempty_iso_of_isEquivalence (f := g' ≫ h') (g := 𝟙 X) (α := η) hη
  have ε' := QCat.nonempty_iso_of_isEquivalence (f := h' ≫ g') (g := 𝟙 Y) (α := ε) hε
  exact ⟨g, (QCat.isCategoricalEquivalence_iff_exists_equivalence _).2
    ⟨.mkOfAdjointifyCounit η'.some.symm ε'.some, rfl⟩, α, hα⟩

end SSet.IsLocalization

namespace SSet

/-- Between quasicategories, localizations at the empty marking are exactly categorical
equivalences. -/
@[simp]
theorem isLocalization_empty_iff {C D : SSet.{u}} [Quasicategory C] [Quasicategory D]
    (f : C ⟶ D) : IsLocalization f ∅ ↔
      QCat.IsCategoricalEquivalence (X := ⟨C, inferInstance⟩) (Y := ⟨D, inferInstance⟩)
        (ObjectProperty.homMk f) := by
  have hid : IsLocalization (𝟙 C) ∅ := isLocalization_id ∅ (by simp)
  refine ⟨fun hf ↦ ?_, fun hf ↦ ?_⟩
  · obtain ⟨g, hg, e, he⟩ := hid.exists_isCategoricalEquivalence hf
    have hs : (ihomObj₀Equiv C D).symm (𝟙 C ≫ g) = (ihomObj₀Equiv C D).symm g := by simp
    exact hg.of_isEquivalence (e.ofEq hs rfl) ((Edge.isEquivalence_ofEq_iff _ _).2 he)
  · simpa only [Category.id_comp] using (IsLocalization.comp_iff (f := 𝟙 C) hf).2 hid

end SSet
