/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Product
public import TauCeti.CategoryTheory.Exact.Stable.Functor.Basic

/-!
# Stable categories of products

The projective stable category of a product of exact categories is additively equivalent to
the product of their projective stable categories. The comparison sends a pair to the pair of
its stable classes and acts componentwise on morphisms. No Frobenius hypothesis is needed for
this additive equivalence: a pair of maps factors through a relative projective exactly when
both maps do.

For Frobenius exact categories the product exact structure is Frobenius, and the two projections
preserve projective-injectives. Their stable functors therefore admit the suspension comparisons
and triangle-functor structures of `StableConflationExact.stableFunctorIsTriangulated`. The
comparison here concerns the additive categories; it does not identify their triangulations.

## References

* Dieter Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, Chapter I, Section 2 (stable quotients of Frobenius categories).
-/

public section

namespace TauCeti.ExactStructure

open CategoryTheory CategoryTheory.Limits

universe v v' u u'

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  [HasBinaryBiproducts D]

variable (E : ExactStructure C) (E' : ExactStructure D)

/-- A map in the product is projectively trivial precisely when both components are
projectively trivial. Two component factorizations combine through the pair of projectives. -/
@[simp]
theorem mem_prod_projectiveStableIdeal_iff {X Y : C × D} (f : X ⟶ Y) :
    f ∈ (E.prod E').projectiveStableIdeal.hom X Y ↔
      f.1 ∈ E.projectiveStableIdeal.hom X.1 Y.1 ∧
        f.2 ∈ E'.projectiveStableIdeal.hom X.2 Y.2 := by
  simp only [mem_projectiveStableIdeal_iff, ObjectProperty.factorsThrough_iff]
  constructor
  · rintro ⟨Q, hQ, i, p, hp⟩
    obtain ⟨h₁, h₂⟩ := (prod_isProjective_iff E E' Q).mp hQ
    exact ⟨⟨Q.1, h₁, i.1, p.1, congrArg Prod.fst hp⟩,
      ⟨Q.2, h₂, i.2, p.2, congrArg Prod.snd hp⟩⟩
  · rintro ⟨⟨P, hP, i₁, p₁, hp₁⟩, ⟨Q, hQ, i₂, p₂, hp₂⟩⟩
    exact ⟨(P, Q), (prod_isProjective_iff E E' _).mpr ⟨hP, hQ⟩,
      (i₁, i₂), (p₁, p₂), Prod.hom_ext hp₁ hp₂⟩

private theorem projectiveStableIdeal_prod_le_ker :
    (E.prod E').projectiveStableIdeal ≤
      (E.projectiveStableFunctor.prod E'.projectiveStableFunctor).kerIdeal := by
  intro X Y f hf
  rw [Functor.mem_kerIdeal_hom]
  obtain ⟨h₁, h₂⟩ := (mem_prod_projectiveStableIdeal_iff E E' f).mp hf
  exact Prod.hom_ext
    (E.projectiveStableIdeal.quotientFunctor_map_eq_zero_iff.mpr h₁)
    (E'.projectiveStableIdeal.quotientFunctor_map_eq_zero_iff.mpr h₂)

/-- The componentwise comparison from the stable category of a product to the product of
stable categories. -/
noncomputable def projectiveStableProdFunctor :
    (E.prod E').ProjectiveStableCategory ⥤
      E.ProjectiveStableCategory × E'.ProjectiveStableCategory :=
  (E.prod E').projectiveStableIdeal.lift
    (E.projectiveStableFunctor.prod E'.projectiveStableFunctor)
    (projectiveStableIdeal_prod_le_ker E E')

/-- The product comparison sends the class of a pair to the pair of its classes. -/
@[simp]
theorem projectiveStableProdFunctor_obj (X : C × D) :
    (projectiveStableProdFunctor E E').obj ((E.prod E').projectiveStableFunctor.obj X) =
      (E.projectiveStableFunctor.obj X.1, E'.projectiveStableFunctor.obj X.2) :=
  (rfl)

/-- The product comparison acts componentwise on representatives of stable morphisms. -/
@[simp]
theorem projectiveStableProdFunctor_map {X Y : C × D} (f : X ⟶ Y) :
    (projectiveStableProdFunctor E E').map ((E.prod E').projectiveStableFunctor.map f) =
      eqToHom (projectiveStableProdFunctor_obj E E' X) ≫
        (E.projectiveStableFunctor.map f.1, E'.projectiveStableFunctor.map f.2) ≫
          eqToHom (projectiveStableProdFunctor_obj E E' Y).symm := by
  apply (conj_eqToHom_iff_heq _ _ (projectiveStableProdFunctor_obj E E' X)
    (projectiveStableProdFunctor_obj E E' Y)).mpr
  rw [projectiveStableProdFunctor, CategoryTheory.Quotient.lift_map_functor_map]
  rfl

/-- The product comparison commutes with the quotient functors. -/
@[simp]
theorem projectiveStableFunctor_prod_comp_projectiveStableProdFunctor :
    (E.prod E').projectiveStableFunctor ⋙ projectiveStableProdFunctor E E' =
      E.projectiveStableFunctor.prod E'.projectiveStableFunctor := by
  rw [projectiveStableProdFunctor]
  exact CategoryTheory.Quotient.lift_spec _ _ _

instance : (projectiveStableProdFunctor E E').Additive := by
  rw [projectiveStableProdFunctor]
  infer_instance

instance : (projectiveStableProdFunctor E E').Faithful := by
  rw [projectiveStableProdFunctor]
  constructor
  intro X Y f g h
  obtain ⟨f, rfl⟩ := (E.prod E').projectiveStableFunctor.map_surjective f
  obtain ⟨g, rfl⟩ := (E.prod E').projectiveStableFunctor.map_surjective g
  simp only [CategoryTheory.Quotient.lift_map_functor_map, Functor.prod_map] at h
  rw [MorphismIdeal.quotientFunctor_map_eq_iff, mem_prod_projectiveStableIdeal_iff]
  exact ⟨E.projectiveStableIdeal.quotientFunctor_map_eq_iff.mp (congrArg Prod.fst h),
    E'.projectiveStableIdeal.quotientFunctor_map_eq_iff.mp (congrArg Prod.snd h)⟩

instance : (projectiveStableProdFunctor E E').Full := by
  rw [projectiveStableProdFunctor]
  constructor
  intro X Y f
  obtain ⟨f₁, hf₁⟩ := E.projectiveStableFunctor.map_surjective f.1
  obtain ⟨f₂, hf₂⟩ := E'.projectiveStableFunctor.map_surjective f.2
  refine ⟨(E.prod E').projectiveStableFunctor.map (f₁, f₂), ?_⟩
  rw [CategoryTheory.Quotient.lift_map_functor_map]
  exact Prod.hom_ext hf₁ hf₂

instance : (projectiveStableProdFunctor E E').EssSurj := by
  rw [projectiveStableProdFunctor]
  constructor
  rintro ⟨⟨X⟩, ⟨Y⟩⟩
  exact ⟨(E.prod E').projectiveStableFunctor.obj (X, Y), ⟨Iso.refl _⟩⟩

noncomputable instance : (projectiveStableProdFunctor E E').IsEquivalence :=
  Functor.IsEquivalence.mk

/-- The projective stable category of a product is additively equivalent to the product of the
projective stable categories, without an enough-projectives or Frobenius hypothesis. -/
noncomputable def projectiveStableProdEquivalence :
    (E.prod E').ProjectiveStableCategory ≌
      E.ProjectiveStableCategory × E'.ProjectiveStableCategory :=
  (projectiveStableProdFunctor E E').asEquivalence

/-- The forward functor of the product equivalence is the componentwise comparison. -/
@[simp]
theorem projectiveStableProdEquivalence_functor :
    (projectiveStableProdEquivalence E E').functor = projectiveStableProdFunctor E E' :=
  (rfl)

instance : (projectiveStableProdEquivalence E E').functor.Additive := by
  rw [projectiveStableProdEquivalence_functor]
  infer_instance

/-- The first projection of exact categories preserves projective-injectives, and hence
induces a stable triangle functor when the exact structures are Frobenius. -/
theorem stableConflationExact_fst_prod :
    StableConflationExact (E.prod E') E (CategoryTheory.Prod.fst C D) where
  isConflationExact := isConflationExact_fst_prod E E'
  map_projectiveInjective {X} hX := by
    rw [projectiveInjective_iff] at hX ⊢
    exact ⟨((prod_isProjective_iff E E' X).mp hX.1).1,
      ((prod_isInjective_iff E E' X).mp hX.2).1⟩

/-- The second projection of exact categories preserves projective-injectives, and hence
induces a stable triangle functor when the exact structures are Frobenius. -/
theorem stableConflationExact_snd_prod :
    StableConflationExact (E.prod E') E' (CategoryTheory.Prod.snd C D) where
  isConflationExact := isConflationExact_snd_prod E E'
  map_projectiveInjective {X} hX := by
    rw [projectiveInjective_iff] at hX ⊢
    exact ⟨((prod_isProjective_iff E E' X).mp hX.1).2,
      ((prod_isInjective_iff E E' X).mp hX.2).2⟩

/-- The first component of the product comparison is the stable functor induced by the
first projection. Thus its suspension comparison and triangle-functor structure are those
already constructed for stable conflation-exact functors. -/
@[simp]
theorem projectiveStableProdFunctor_comp_fst (hE : E.IsFrobenius) (hE' : E'.IsFrobenius) :
    projectiveStableProdFunctor E E' ⋙
        CategoryTheory.Prod.fst E.ProjectiveStableCategory E'.ProjectiveStableCategory =
      (stableConflationExact_fst_prod E E').stableFunctor (hE.prod hE') := by
  apply CategoryTheory.Quotient.lift_unique' (E.prod E').projectiveStableIdeal.rel
  rw [← Functor.assoc, projectiveStableFunctor_prod_comp_projectiveStableProdFunctor,
    StableConflationExact.stableFunctor_eq_map, MorphismIdeal.quotientFunctor_comp_map]
  rfl

/-- The second component of the product comparison is the stable functor induced by the
second projection, with its existing suspension and triangle-functor structures. -/
@[simp]
theorem projectiveStableProdFunctor_comp_snd (hE : E.IsFrobenius) (hE' : E'.IsFrobenius) :
    projectiveStableProdFunctor E E' ⋙
        CategoryTheory.Prod.snd E.ProjectiveStableCategory E'.ProjectiveStableCategory =
      (stableConflationExact_snd_prod E E').stableFunctor (hE.prod hE') := by
  apply CategoryTheory.Quotient.lift_unique' (E.prod E').projectiveStableIdeal.rel
  rw [← Functor.assoc, projectiveStableFunctor_prod_comp_projectiveStableProdFunctor,
    StableConflationExact.stableFunctor_eq_map, MorphismIdeal.quotientFunctor_comp_map]
  rfl

end TauCeti.ExactStructure
