/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.HomologicalComplex.Projective.Replacement
public import TauCeti.Algebra.Homology.Periodic.GlobalDimension

/-!
# Periodic complexes of projectives model the periodic derived category

In an abelian category with enough projectives, every periodic complex whose terms have bounded
projective dimension receives a quasi-isomorphism from a periodic complex with projective terms,
as a special case of `HomologicalComplex.exists_quasiIso_of_hasProjectiveDimensionLT` for complexes
of any shape in which every index is both the source and the target of a relation. When every
object has projective dimension `< d`, periodic complexes of projectives are moreover homotopically
projective, so passage to the periodic derived category is fully faithful on them. Together these
give the equivalence `K_n(proj C) ≌ D_n(C)` between the full subcategory of the periodic homotopy
category on the complexes with projective terms and the periodic derived category
(`TauCeti.PeriodicComplex.DerivedCategory.projectiveEquivalence`). For a finite-dimensional
algebra `Λ` of finite global dimension, applied to finitely generated modules, this is the
equivalence `D_n(mod Λ) ≌ K_n(proj Λ)` of Stai.

The finite global dimension hypothesis cannot be dropped from the equivalence: over the dual
numbers `k[ε]`, multiplication by `ε` on `k[ε]` is a periodic complex of free modules which is
acyclic but not contractible, so it is nonzero in the periodic homotopy category and zero in the
periodic derived category (`TauCeti.not_isHomotopicallyProjective_dualNumberPeriodicComplex`).

## Main definitions

* `TauCeti.PeriodicComplex.subcategoryDegreewiseProjective`: the periodic complexes with
  projective terms, as objects of the periodic homotopy category.
* `TauCeti.PeriodicComplex.DerivedCategory.projectiveEquivalence`: in finite global dimension, the
  equivalence between that full subcategory and the periodic derived category.

## Main results

* `TauCeti.PeriodicComplex.DerivedCategory.isEquivalence_ι_comp_Qh`: in finite global dimension,
  the periodic Verdier localization restricts to an equivalence on complexes of projectives.

## References

* T. Stai, *The triangulated hull of periodic complexes*, Mathematical Research Letters **25**
  (2018), 199–236, Section 3.
-/

public section

universe v u

namespace TauCeti.PeriodicComplex

open CategoryTheory CategoryTheory.Limits HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C] {n : ℕ}

variable (C n) in
/-- The periodic complexes with projective terms, as objects of the periodic homotopy category.
Its full subcategory models the periodic homotopy category `K_n(proj C)` of the projective
objects of `C`: its morphisms are the chain maps up to homotopy. -/
def subcategoryDegreewiseProjective :
    ObjectProperty (HomotopyCategory C (ComplexShape.up (ZMod n))) :=
  fun K ↦ ∀ i, Projective (K.as.X i)

/-- Membership in `subcategoryDegreewiseProjective` is projectivity of every term. -/
theorem mem_subcategoryDegreewiseProjective_iff
    (K : HomotopyCategory C (ComplexShape.up (ZMod n))) :
    subcategoryDegreewiseProjective C n K ↔ ∀ i, Projective (K.as.X i) :=
  Iff.rfl

/-- The class of a periodic complex has projective terms exactly when the complex does. -/
@[simp]
theorem quotient_obj_mem_subcategoryDegreewiseProjective_iff (K : CochainComplex C (ZMod n)) :
    subcategoryDegreewiseProjective C n
        ((HomotopyCategory.quotient C (ComplexShape.up (ZMod n))).obj K) ↔
      ∀ i, Projective (K.X i) :=
  Iff.rfl

variable [EnoughProjectives C]

/-- In finite global dimension, the classes of periodic complexes of projectives are left
orthogonal to the acyclic objects of the periodic homotopy category. -/
theorem subcategoryDegreewiseProjective_le_leftOrthogonal (d : ℕ)
    (hd : ∀ X : C, HasProjectiveDimensionLT X d) :
    subcategoryDegreewiseProjective C n ≤ (subcategoryAcyclic C n).leftOrthogonal := by
  rintro ⟨K⟩ (hK : ∀ i, Projective (K.X i))
  have := isHomotopicallyProjective_of_projective d hd K
  exact IsHomotopicallyProjective.leftOrthogonal K

namespace DerivedCategory

variable (C n)

/-- In an abelian category with enough projectives in which every object has projective dimension
`< d`, the periodic Verdier localization restricts to an equivalence from the full subcategory of
periodic complexes of projectives to the periodic derived category. -/
theorem isEquivalence_ι_comp_Qh (d : ℕ) (hd : ∀ X : C, HasProjectiveDimensionLT X d) :
    ((subcategoryDegreewiseProjective C n).ι ⋙ Qh C n).IsEquivalence := by
  have hP := subcategoryDegreewiseProjective_le_leftOrthogonal (n := n) d hd
  -- Full faithfulness is inherited from the homotopically projective objects.
  let e : ObjectProperty.ιOfLE hP ⋙ (subcategoryAcyclic C n).leftOrthogonal.ι ⋙ Qh C n ≅
      (subcategoryDegreewiseProjective C n).ι ⋙ Qh C n :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (ObjectProperty.ιOfLECompιIso hP) _
  have := Functor.Full.of_iso e
  have := Functor.Faithful.of_iso e
  have hsurj : ((subcategoryDegreewiseProjective C n).ι ⋙ Qh C n).EssSurj :=
    ⟨fun Y ↦ by
      obtain ⟨⟨K⟩, ⟨e'⟩⟩ :=
        (Localization.essSurj (Qh C n) (subcategoryAcyclic C n).trW).mem_essImage Y
      obtain ⟨P, hP, π, _⟩ := HomologicalComplex.exists_quasiIso_of_hasProjectiveDimensionLT
        (fun i ↦ ⟨i + 1, rfl⟩) (fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩) K d fun _ ↦ hd _
      let π' := (HomotopyCategory.quotient C (ComplexShape.up (ZMod n))).map π
      have : IsIso ((Qh C n).map π') := by
        have h : IsIso ((Q C n).map π) := inferInstance
        rw [← quotient_comp_Qh] at h
        rwa [← Functor.comp_map]
      exact ⟨⟨(HomotopyCategory.quotient C (ComplexShape.up (ZMod n))).obj P, hP⟩,
        ⟨asIso ((Qh C n).map π') ≪≫ e'⟩⟩⟩
  exact { }

/-- In an abelian category with enough projectives in which every object has projective dimension
`< d`, the full subcategory `K_n(proj C)` of the periodic homotopy category on the complexes with
projective terms is equivalent to the periodic derived category `D_n(C)`, by the periodic Verdier
localization. -/
noncomputable def projectiveEquivalence (d : ℕ) (hd : ∀ X : C, HasProjectiveDimensionLT X d) :
    (subcategoryDegreewiseProjective C n).FullSubcategory ≌ DerivedCategory C n :=
  have := isEquivalence_ι_comp_Qh C n d hd
  ((subcategoryDegreewiseProjective C n).ι ⋙ Qh C n).asEquivalence

/-- The functor of `projectiveEquivalence` is the periodic Verdier localization. -/
@[simp]
theorem projectiveEquivalence_functor (d : ℕ) (hd : ∀ X : C, HasProjectiveDimensionLT X d) :
    (projectiveEquivalence C n d hd).functor = (subcategoryDegreewiseProjective C n).ι ⋙ Qh C n :=
  (rfl)

end DerivedCategory

end TauCeti.PeriodicComplex
