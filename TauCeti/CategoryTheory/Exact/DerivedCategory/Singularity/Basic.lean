/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.DerivedCategory.Basic
public import TauCeti.CategoryTheory.Exact.Projective
public import TauCeti.Algebra.Homology.HomotopyCategory.Bounded.Generation
public import TauCeti.CategoryTheory.Exact.HomologicalComplex.Projective.Basic
public import TauCeti.Algebra.Homology.HomotopyCategory.Bounded.MappingCone
public import Mathlib.CategoryTheory.Triangulated.Orthogonal

/-!
# The singularity category of an exact category

Let `E` be an exact structure on an additive category `C`. The bounded complexes of `E`-projective
objects define a triangulated subcategory `Kᵇ(proj E)` of the bounded derived category `Dᵇ(E)`
(`TauCeti.ExactStructure.boundedProjective`): morphisms out of such a complex are computed in the
homotopy category, since it is left orthogonal to the acyclic complexes (Bühler, Corollary 12.5),
and the mapping cone of a map of such complexes is again one. The **singularity category** of
`E` is the Verdier quotient

`D_sg(E) = Dᵇ(E) / Kᵇ(proj E)`,

with its localized triangulated structure (Buchweitz). For a Frobenius exact structure, the
projective objects are the projective-injective ones, and Keller–Vossieck identify `D_sg(E)` with
the stable category of `E`.

## Main definitions

* `TauCeti.ExactStructure.boundedProjective`: the classes of bounded complexes of projectives in
  `Dᵇ(E)`, a triangulated subcategory.
* `TauCeti.ExactStructure.SingularityCategory`: the Verdier quotient `Dᵇ(E) / Kᵇ(proj E)`, with
  its quotient functor `TauCeti.ExactStructure.SingularityCategory.Q`.

## Main results

* `TauCeti.ExactStructure.acyclicBounded_leftOrthogonal_quotient_obj`: a bounded complex of
  projectives is left orthogonal to the acyclic complexes in `Kᵇ(C)`.
* `TauCeti.ExactStructure.boundedProjective_Q_obj_singleFunctor_obj`: a projective object in
  any degree lies in `Kᵇ(proj E)`.
* `TauCeti.ExactStructure.boundedProjective_trW_Q_map_ιTop`: splitting off the top term of a
  bounded complex whose lower terms are projective is inverted in the singularity category.

## References

* Ragnar-Olaf Buchweitz, *Maximal Cohen–Macaulay Modules and Tate Cohomology*, Section 1.2.
* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1--69,
  <https://arxiv.org/abs/0811.1480>, Corollary 12.5.
* Bernhard Keller, Dieter Vossieck, *Sous les catégories dérivées*, C. R. Acad. Sci. Paris
  **305** (1987), 225--228, Example 2.3.
-/

public section

namespace TauCeti.ExactStructure

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated ZeroObject

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  (E : ExactStructure C)

/-- The objects of `Dᵇ(E)` isomorphic to the class of a bounded complex of `E`-projective objects,
the image of `Kᵇ(proj E)`. -/
def boundedProjective : ObjectProperty E.BoundedDerivedCategory := fun X ↦
  ∃ K : CochainComplex.Bounded C, (∀ n, E.isProjective (K.obj.X n)) ∧
    Nonempty (X ≅ (BoundedDerivedCategory.Q E).obj ((HomotopyCategory.Bounded.quotient C).obj K))

/-- The objects of `E.boundedProjective` are the classes of bounded complexes of projectives, up
to isomorphism. -/
lemma boundedProjective_iff (X : E.BoundedDerivedCategory) :
    E.boundedProjective X ↔ ∃ K : CochainComplex.Bounded C, (∀ n, E.isProjective (K.obj.X n)) ∧
      Nonempty (X ≅ (BoundedDerivedCategory.Q E).obj
        ((HomotopyCategory.Bounded.quotient C).obj K)) :=
  Iff.rfl

/-- The class of a bounded complex of projectives is in `E.boundedProjective`. -/
lemma boundedProjective_Q_obj_quotient_obj (K : CochainComplex.Bounded C)
    (hK : ∀ n, E.isProjective (K.obj.X n)) :
    E.boundedProjective ((BoundedDerivedCategory.Q E).obj
      ((HomotopyCategory.Bounded.quotient C).obj K)) :=
  ⟨K, hK, ⟨Iso.refl _⟩⟩

instance : E.boundedProjective.IsClosedUnderIsomorphisms where
  of_iso e := fun ⟨K, hK, ⟨e'⟩⟩ ↦ ⟨K, hK, ⟨e.symm ≪≫ e'⟩⟩

/-- **The class of a bounded complex of projectives is left orthogonal to the acyclic complexes**
in `Kᵇ(C)` (Bühler, Corollary 12.5). -/
theorem acyclicBounded_leftOrthogonal_quotient_obj (K : CochainComplex.Bounded C)
    (hK : ∀ n, E.isProjective (K.obj.X n)) :
    E.acyclicBounded.leftOrthogonal ((HomotopyCategory.Bounded.quotient C).obj K) := by
  intro Y f hY
  obtain ⟨L, _, hL, ⟨e⟩⟩ := (E.boundedAcyclic_iff _).1 ((E.acyclicBounded_iff Y).1 hY)
  obtain ⟨hL⟩ := (E.acyclic_iff L).1 hL
  obtain ⟨_, b, _, _⟩ := (CochainComplex.bounded_iff C K.obj).1 K.property
  obtain ⟨g, hg⟩ := (_root_.HomotopyCategory.quotient C (.up ℤ)).map_surjective
    (eqToHom (HomotopyCategory.Bounded.quotient_obj_obj C K).symm ≫ f.hom ≫ e.hom)
  have h0 := hL.quotient_map_eq_zero_of_projective g hK b
  apply ObjectProperty.hom_ext
  rw [← cancel_epi (eqToHom (HomotopyCategory.Bounded.quotient_obj_obj C K).symm),
    ← cancel_mono e.hom]
  simpa [hg] using h0

/-- A projective object placed in any degree is in `E.boundedProjective`. -/
theorem boundedProjective_Q_obj_singleFunctor_obj (n : ℤ) {P : C} (hP : E.isProjective P) :
    E.boundedProjective ((BoundedDerivedCategory.Q E).obj
      ((HomotopyCategory.Bounded.singleFunctor C n).obj P)) := by
  let K : CochainComplex.Bounded C := ⟨(CochainComplex.singleFunctor C n).obj P,
    (CochainComplex.bounded_iff C _).2 ⟨n, n, inferInstance, inferInstance⟩⟩
  refine ⟨K, fun k ↦ ?_, ⟨(BoundedDerivedCategory.Q E).mapIso
    ((HomotopyCategory.Bounded.fullyFaithfulι C).preimageIso
      ((HomotopyCategory.Bounded.singleFunctorCompιIso C n).app P ≪≫
        eqToIso (HomotopyCategory.quotient_obj_singleFunctors_obj C n P).symm ≪≫
        eqToIso (HomotopyCategory.Bounded.quotient_obj_obj C K).symm))⟩⟩
  by_cases hk : k = n
  · subst hk
    exact E.isProjective.prop_of_iso (HomologicalComplex.singleObjXSelf _ k P).symm hP
  · exact E.isProjective.prop_of_isZero (HomologicalComplex.isZero_single_obj_X _ n P k hk)

instance : E.boundedProjective.ContainsZero where
  exists_zero := ⟨_, Functor.map_isZero _ (Functor.map_isZero _
      (IsZero.of_full_of_faithful_of_isZero (CochainComplex.Bounded.ι C)
        (⟨0, (CochainComplex.bounded_iff C 0).2 ⟨0, 0, inferInstance, inferInstance⟩⟩ :
          CochainComplex.Bounded C) (isZero_zero _))),
    E.boundedProjective_Q_obj_quotient_obj _ fun n ↦
      E.isProjective.prop_of_isZero ((HomologicalComplex.eval C _ n).map_isZero (isZero_zero _))⟩

instance : E.boundedProjective.IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨fun _ ⟨K, hK, ⟨e⟩⟩ ↦ ⟨K⟦n⟧, fun k ↦
    E.isProjective.prop_of_iso ((HomologicalComplex.eval C _ k).mapIso
      (((CochainComplex.Bounded.ι C).commShiftIso n).app K).symm) (hK (k + n)),
    ⟨(shiftFunctor _ n).mapIso e ≪≫
      ((BoundedDerivedCategory.Q E).commShiftIso n).symm.app _ ≪≫
      (BoundedDerivedCategory.Q E).mapIso
        (((HomotopyCategory.Bounded.quotient C).commShiftIso n).symm.app K)⟩⟩⟩

instance : E.boundedProjective.IsTriangulatedClosed₃ where
  ext₃' T hT := fun ⟨K₁, hK₁, ⟨e₁⟩⟩ ⟨K₂, hK₂, ⟨e₂⟩⟩ ↦ by
    obtain ⟨g, hg⟩ := ((E.acyclicBounded_leftOrthogonal_quotient_obj K₁
      hK₁).map_bijective_of_isTriangulated (BoundedDerivedCategory.Q E) _).2
        (e₁.inv ≫ T.mor₁ ≫ e₂.hom)
    obtain ⟨φ, rfl⟩ := (HomotopyCategory.Bounded.quotient C).map_surjective g
    refine ObjectProperty.le_isoClosure _ _ ⟨CochainComplex.Bounded.mappingCone φ,
      fun _ ↦ E.isProjective_mappingCone_X φ.hom (hK₁ _) (hK₂ _),
      ⟨Triangle.π₃.mapIso (isoTriangleOfIso₁₂ T _ hT ((BoundedDerivedCategory.Q E).map_distinguished
        _ (HomotopyCategory.Bounded.quotient_mapTriangle_mappingConeTriangle_mem_distTriang φ))
        e₁ e₂ ?_)⟩⟩
    -- The first square of `isoTriangleOfIso₁₂`, with the triangle of the mapping cone unfolded to
    -- its first morphism, the image of `φ`.
    change T.mor₁ ≫ e₂.hom = e₁.hom ≫ (BoundedDerivedCategory.Q E).map
      ((HomotopyCategory.Bounded.quotient C).map φ)
    rw [hg]
    simp

instance : E.boundedProjective.IsTriangulated where
  toIsTriangulatedClosed₂ := .of_isTriangulatedClosed₃

variable {E} in
/-- **Splitting off the top term is inverted in the singularity category**: for a bounded complex
`K` vanishing above degree `n` whose terms below `n` are projective, the inclusion of the top term
`Kⁿ[-n] ⟶ K` lies in `E.boundedProjective.trW`. -/
theorem boundedProjective_trW_Q_map_ιTop (K : CochainComplex C ℤ) (n : ℤ) [K.IsStrictlyLE n]
    (hK : CochainComplex.bounded C K) (hP : ∀ k < n, E.isProjective (K.X k)) :
    E.boundedProjective.trW
      ((BoundedDerivedCategory.Q E).map (HomotopyCategory.Bounded.ιTop K n hK)) := by
  obtain ⟨b, rfl⟩ : ∃ b, n = b + 1 := ⟨n - 1, by lia⟩
  rw [← ObjectProperty.inverseImage_trW_iff]
  obtain ⟨Z, g, h, hT⟩ :=
    distinguished_cocone_triangle (HomotopyCategory.Bounded.ιTop K (b + 1) hK)
  refine ((E.boundedProjective.inverseImage (BoundedDerivedCategory.Q E)).trW_iff_of_distinguished _
    hT).2 ?_
  have e := isoTriangleOfIso₁₂ _ _ ((HomotopyCategory.Bounded.ι C).map_distinguished _ hT)
    (_root_.HomotopyCategory.mappingCone_triangleh_distinguished (K.ιTop (b + 1)))
    ((HomotopyCategory.Bounded.singleFunctorCompιIso C (b + 1)).app (K.X (b + 1)) ≪≫
      eqToIso (_root_.HomotopyCategory.quotient_obj_singleFunctors_obj C _ _).symm)
    (eqToIso (HomotopyCategory.Bounded.quotient_obj_obj C ⟨K, hK⟩)) (by
      dsimp
      rw [HomotopyCategory.Bounded.ιTop_hom]
      simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id])
  obtain ⟨e'⟩ := K.nonempty_iso_quotient_obj_mappingCone_ιTop b
  let L : CochainComplex.Bounded C :=
    ⟨_, CochainComplex.bounded_stupidTrunc_embeddingUpIntLE hK b⟩
  refine ⟨L, fun k ↦ ?_, ⟨(BoundedDerivedCategory.Q E).mapIso
    ((HomotopyCategory.Bounded.fullyFaithfulι C).preimageIso (Triangle.π₃.mapIso e ≪≫ e' ≪≫
      eqToIso (HomotopyCategory.Bounded.quotient_obj_obj C L).symm))⟩⟩
  by_cases hk : k ≤ b
  · have : IsIso ((K.πStupidTrunc (ComplexShape.embeddingUpIntLE b)).f k) :=
      K.isIso_πStupidTrunc_f (ComplexShape.embeddingUpIntLE b) (i := (b - k).natAbs) (i' := k)
        (by simp [Int.natAbs_of_nonneg (sub_nonneg.mpr hk)])
    exact E.isProjective.prop_of_iso
      (asIso ((K.πStupidTrunc (ComplexShape.embeddingUpIntLE b)).f k)) (hP k (by lia))
  · exact E.isProjective.prop_of_isZero
      (K.isZero_stupidTrunc_embeddingUpIntLE_X b (by lia))

/-- The **singularity category** `Dᵇ(E) / Kᵇ(proj E)` of an exact category: the Verdier quotient of
the bounded derived category by the bounded complexes of projectives. -/
abbrev SingularityCategory :=
  E.boundedProjective.trW.Localization

namespace SingularityCategory

/-- The Verdier quotient functor `Dᵇ(E) ⥤ D_sg(E)`. -/
noncomputable def Q : E.BoundedDerivedCategory ⥤ E.SingularityCategory :=
  E.boundedProjective.trW.Q

instance : (Q E).IsLocalization E.boundedProjective.trW := by
  dsimp only [Q]
  infer_instance

noncomputable instance : Preadditive E.SingularityCategory :=
  Localization.preadditive (Q E) E.boundedProjective.trW

instance : (Q E).Additive :=
  Localization.functor_additive (Q E) E.boundedProjective.trW

noncomputable instance : HasZeroObject E.SingularityCategory :=
  (Q E).hasZeroObject_of_additive

noncomputable instance : HasShift E.SingularityCategory ℤ :=
  HasShift.localized (Q E) E.boundedProjective.trW ℤ

noncomputable instance : (Q E).CommShift ℤ :=
  Functor.CommShift.localized (Q E) E.boundedProjective.trW ℤ

instance (n : ℤ) : (shiftFunctor E.SingularityCategory n).Additive := by
  rw [Localization.functor_additive_iff (Q E) E.boundedProjective.trW]
  exact Functor.additive_of_iso ((Q E).commShiftIso n)

noncomputable instance : Pretriangulated E.SingularityCategory :=
  Triangulated.Localization.pretriangulated (Q E) E.boundedProjective.trW

instance : (Q E).IsTriangulated :=
  Triangulated.Localization.isTriangulated_functor (Q E) E.boundedProjective.trW

instance : IsTriangulated E.SingularityCategory :=
  Triangulated.Localization.isTriangulated (Q E) E.boundedProjective.trW

end SingularityCategory

end TauCeti.ExactStructure
