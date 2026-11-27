/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Triangulated.Generators
public import TauCeti.Algebra.Homology.Periodic.Compression.Gradable
public import TauCeti.Algebra.Homology.Periodic.FlagResolution

/-!
# Compression generates the periodic derived category

In an abelian category with enough projectives and a uniform finite bound on projective
dimensions, every isomorphism-closed triangulated subcategory containing the compressions of
bounded complexes, the gradable objects, is the entire positive-period derived category. This
is generation by shifts and cones, without taking retracts or passing to an idempotent
completion. In particular the thick envelope of the gradable objects is also the entire
category. The gradable objects are the essential image of the derived orbit functor
(`essImage_orbitDerivedCompressionFunctor`), so both statements apply to that image.

The proof uses projective flag resolutions. Every zero-differential layer of such a flag is
itself the compression of a bounded complex, and degreewise split extensions give distinguished
triangles. A flag resolution is a quasi-isomorphism, so every periodic derived object belongs to
the generated subcategory. The categorical hypotheses apply in particular to finitely generated
modules over a finite-dimensional algebra of finite global dimension.

## References

* T. Stai, *The triangulated hull of periodic complexes*, Mathematical Research Letters **25**
  (2018), 199–236, Theorem 4.3.
* L. L. Avramov, R.-O. Buchweitz and S. Iyengar, *Class and rank of differential modules*,
  Inventiones Mathematicae **169** (2007), 1–35, Section 2 (projective flags).
-/

public section

open CategoryTheory Limits HomologicalComplex ZeroObject

universe v u

namespace TauCeti.PeriodicComplex

variable {C : Type u} [Category.{v} C] [Abelian C] {n : ℕ} [NeZero n]

private lemma mem_of_hasProjectiveFlag
    (P : ObjectProperty (DerivedCategory C n)) [P.IsTriangulated]
    [P.IsClosedUnderIsomorphisms] (hP : gradable C n ≤ P)
    {K : CochainComplex C (ZMod n)} (hK : HasProjectiveFlag K) :
    P ((DerivedCategory.Qh C n).obj ((HomotopyCategory.quotient C _).obj K)) := by
  let R := P.inverseImage (DerivedCategory.Qh C n)
  induction hK with
  | of_isZero hK =>
    exact P.prop_of_isZero ((DerivedCategory.Qh C n).map_isZero
      ((HomotopyCategory.quotient C _).map_isZero hK))
  | extension S hS _ hd ih =>
    let := ExactStructure.homologicalComplex_split_isFrobenius (C := C)
      (c := ComplexShape.up (ZMod n)) (fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩)
      (fun i ↦ ⟨i + 1, rfl⟩) |>.stableHasShift
    let := stableToHomotopyCommShift C n
    have hT := homotopyCategory_map_stableConflationTriangle_mem_distTriang C n S
      ((ExactStructure.homologicalComplex_conflation_iff _ _ S).mpr
        fun i ↦ (ExactStructure.split_conflation _).mpr (hS i))
    -- The vertices of this distinguished triangle are the homotopy classes of the three
    -- complexes in the degreewise split sequence.
    simpa [R] using R.ext_of_isTriangulatedClosed₂ _ hT
      (by simpa [R] using ih)
      (by simpa [R] using hP _ (gradable_Qh_obj_quotient_obj_of_d_eq_zero S.X₃ hd))

variable [EnoughProjectives C]

/-- **Generation by compression, before idempotent completion.** In finite global dimension,
every isomorphism-closed triangulated subcategory containing the gradable objects, the image of
bounded derived compression, is the entire positive-period derived category. Only shifts and
cones, not closure under retracts, are assumed of the subcategory. -/
theorem eq_top_of_gradable_le (d : ℕ) (hd : ∀ X : C, HasProjectiveDimensionLT X d)
    (P : ObjectProperty (DerivedCategory C n)) [P.IsTriangulated]
    [P.IsClosedUnderIsomorphisms] (hP : gradable C n ≤ P) : P = ⊤ := by
  apply top_unique
  intro Y _
  obtain ⟨⟨K⟩, ⟨e⟩⟩ :=
    (Localization.essSurj (DerivedCategory.Qh C n) (subcategoryAcyclic C n).trW).mem_essImage Y
  obtain ⟨F, f, hF, hf⟩ := exists_hasProjectiveFlag_quasiIso d K fun _ ↦ hd _
  let φ := (HomotopyCategory.quotient C (ComplexShape.up (ZMod n))).map f
  have : IsIso ((DerivedCategory.Qh C n).map φ) := by
    have h : IsIso ((DerivedCategory.Q C n).map f) := inferInstance
    rwa [← DerivedCategory.quotient_comp_Qh, Functor.comp_map] at h
  exact P.prop_of_iso (asIso ((DerivedCategory.Qh C n).map φ) ≪≫ e)
    (mem_of_hasProjectiveFlag P hP hF)

/-- In finite global dimension, the thick envelope of the gradable objects is the entire
positive-period derived category. The stronger shift-and-cone generation statement is
`eq_top_of_gradable_le`. -/
theorem triangEnvelope_gradable_eq_top (d : ℕ) (hd : ∀ X : C, HasProjectiveDimensionLT X d) :
    (gradable C n).triangEnvelope = ⊤ :=
  eq_top_of_gradable_le d hd _ (ObjectProperty.le_triangEnvelope _)

end TauCeti.PeriodicComplex
