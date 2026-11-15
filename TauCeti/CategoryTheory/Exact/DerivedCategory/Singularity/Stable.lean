/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.DerivedCategory.Singularity.Basic
public import TauCeti.CategoryTheory.Exact.Stable.Basic

/-!
# From the stable category to the singularity category

Let `E` be an exact structure. Placing an object in degree zero gives a functor
`C ⥤ D_sg(E)` to the singularity category `Dᵇ(E) / Kᵇ(proj E)`. Projective objects vanish in
`D_sg(E)`, and every morphism factoring through a projective object becomes zero. Hence the
functor factors through the projective stable category:

```text
stable(E) ⥤ D_sg(E).
```

For a Frobenius exact structure this is the Keller–Vossieck comparison functor.

## Main definitions

* `TauCeti.ExactStructure.singleToSingularity`: the functor `C ⥤ D_sg(E)` placing an object in
  degree zero, with its defining equation `singleToSingularity_eq`.
  `TauCeti.ExactStructure.exists_Q_map_eq_comp_of_singleToSingularity_map_eq_zero` describes its
  kernel: such morphisms factor in `Dᵇ(E)` through a bounded complex of projectives.
* `TauCeti.ExactStructure.stableToSingularity`: the induced functor `stable(E) ⥤ D_sg(E)`, with
  its defining equation `stableToSingularity_eq` and the factorization
  `projectiveStableFunctor_comp_stableToSingularity`.
* `TauCeti.ExactStructure.stableToSingularityObjIso`: the identification of its values with
  objects placed in degree zero, natural by
  `stableToSingularity_map_comp_stableToSingularityObjIso_hom`.

## References

* Bernhard Keller, Dieter Vossieck, *Sous les catégories dérivées*, C. R. Acad. Sci. Paris
  **305** (1987), 225--228, Example 2.3.
-/

public section

namespace TauCeti.ExactStructure

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated ZeroObject

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  (E : ExactStructure C)

/-- The functor `C ⥤ D_sg(E)` placing an object in degree zero. -/
noncomputable def singleToSingularity : C ⥤ E.SingularityCategory :=
  HomotopyCategory.Bounded.singleFunctor C 0 ⋙ BoundedDerivedCategory.Q E ⋙
    SingularityCategory.Q E

/-- The functor `C ⥤ D_sg(E)` places an object in degree zero of `Kᵇ(C)` and passes to the
quotients `Dᵇ(E)` and `D_sg(E)`. -/
theorem singleToSingularity_eq : E.singleToSingularity =
    HomotopyCategory.Bounded.singleFunctor C 0 ⋙ BoundedDerivedCategory.Q E ⋙
      SingularityCategory.Q E :=
  (rfl)

theorem singleToSingularity_obj (X : C) :
    E.singleToSingularity.obj X = (SingularityCategory.Q E).obj
      ((BoundedDerivedCategory.Q E).obj ((HomotopyCategory.Bounded.singleFunctor C 0).obj X)) :=
  (rfl)

theorem singleToSingularity_map {X Y : C} (f : X ⟶ Y) :
    E.singleToSingularity.map f = eqToHom (E.singleToSingularity_obj X) ≫
      (SingularityCategory.Q E).map
        ((BoundedDerivedCategory.Q E).map ((HomotopyCategory.Bounded.singleFunctor C 0).map f)) ≫
          eqToHom (E.singleToSingularity_obj Y).symm := by
  simp [Functor.congr_hom E.singleToSingularity_eq f]

instance : E.singleToSingularity.Additive := by
  dsimp only [singleToSingularity]
  infer_instance

/-- A projective object vanishes in the singularity category. -/
theorem isZero_singleToSingularity_obj {P : C} (hP : E.isProjective P) :
    IsZero (E.singleToSingularity.obj P) :=
  ObjectProperty.TrWLocalization.isZero_obj E.boundedProjective (SingularityCategory.Q E)
    (E.boundedProjective_Q_obj_singleFunctor_obj 0 hP)

/-- A morphism factoring through a projective object vanishes in the singularity category. -/
theorem singleToSingularity_map_eq_zero {X Y : C} {f : X ⟶ Y}
    (hf : f ∈ E.projectiveStableIdeal.hom X Y) : E.singleToSingularity.map f = 0 := by
  obtain ⟨P, hP, p, q, rfl⟩ :=
    (ObjectProperty.factorsThrough_iff _ _).1 ((E.mem_projectiveStableIdeal_iff).1 hf)
  rw [Functor.map_comp,
    (E.isZero_singleToSingularity_obj hP).eq_of_src (E.singleToSingularity.map q) 0, comp_zero]

/-- **The kernel of `C ⥤ D_sg(E)`**: a morphism of `C` vanishing in the singularity category
factors in `Dᵇ(E)` through the class of a bounded complex of projectives. -/
theorem exists_Q_map_eq_comp_of_singleToSingularity_map_eq_zero {M N : C} (f : M ⟶ N)
    (hf : E.singleToSingularity.map f = 0) :
    ∃ (K : CochainComplex.Bounded C) (_ : ∀ n, E.isProjective (K.obj.X n))
      (a : (BoundedDerivedCategory.Q E).obj ((HomotopyCategory.Bounded.singleFunctor C 0).obj M) ⟶
        (BoundedDerivedCategory.Q E).obj ((HomotopyCategory.Bounded.quotient C).obj K))
      (g : (BoundedDerivedCategory.Q E).obj ((HomotopyCategory.Bounded.quotient C).obj K) ⟶
        (BoundedDerivedCategory.Q E).obj ((HomotopyCategory.Bounded.singleFunctor C 0).obj N)),
      a ≫ g =
        (BoundedDerivedCategory.Q E).map ((HomotopyCategory.Bounded.singleFunctor C 0).map f) := by
  rw [singleToSingularity_eq] at hf
  obtain ⟨Z, s, ⟨W, a, b, hT, hW⟩, hs⟩ := (MorphismProperty.map_eq_iff_precomp
    (SingularityCategory.Q E) E.boundedProjective.trW
      ((BoundedDerivedCategory.Q E).map ((HomotopyCategory.Bounded.singleFunctor C 0).map f))
        0).1 (by
      rw [Functor.map_zero]
      exact hf)
  rw [comp_zero] at hs
  obtain ⟨g, hg⟩ := Triangle.yoneda_exact₂ _ hT _ hs
  obtain ⟨K, hK, ⟨e⟩⟩ := (E.boundedProjective_iff W).1 hW
  exact ⟨K, hK, a ≫ e.hom, e.inv ≫ g, by simpa using hg.symm⟩

/-- Morphisms factoring through a projective object lie in the kernel of `C ⥤ D_sg(E)`. -/
theorem projectiveStableIdeal_le_kerIdeal_singleToSingularity :
    E.projectiveStableIdeal ≤ E.singleToSingularity.kerIdeal := fun _ _ _ hf ↦
  (Functor.mem_kerIdeal_hom _).2 (E.singleToSingularity_map_eq_zero hf)

/-- The functor `stable(E) ⥤ D_sg(E)` induced by placing objects in degree zero. -/
noncomputable def stableToSingularity :
    E.ProjectiveStableCategory ⥤ E.SingularityCategory :=
  E.projectiveStableIdeal.lift E.singleToSingularity
    E.projectiveStableIdeal_le_kerIdeal_singleToSingularity

/-- The functor `stable(E) ⥤ D_sg(E)` is the functor induced by `singleToSingularity` on the
quotient by the projective stable ideal. -/
theorem stableToSingularity_eq : E.stableToSingularity =
    E.projectiveStableIdeal.lift E.singleToSingularity
      E.projectiveStableIdeal_le_kerIdeal_singleToSingularity :=
  (rfl)

instance : E.stableToSingularity.Additive := by
  dsimp only [stableToSingularity]
  infer_instance

/-- The functor `stable(E) ⥤ D_sg(E)` restricts to `singleToSingularity` along the quotient. -/
theorem projectiveStableFunctor_comp_stableToSingularity :
    E.projectiveStableFunctor ⋙ E.stableToSingularity = E.singleToSingularity := by
  dsimp only [stableToSingularity]
  exact CategoryTheory.Quotient.lift_spec _ _ _

@[simp]
theorem stableToSingularity_obj_projectiveStableFunctor_obj (X : C) :
    E.stableToSingularity.obj (E.projectiveStableFunctor.obj X) = E.singleToSingularity.obj X :=
  (rfl)

/-- On the image of a morphism of `C`, `stableToSingularity` is `singleToSingularity`. -/
@[simp]
theorem stableToSingularity_map_projectiveStableFunctor_map {X Y : C} (f : X ⟶ Y) :
    E.stableToSingularity.map (E.projectiveStableFunctor.map f) =
      eqToHom (E.stableToSingularity_obj_projectiveStableFunctor_obj X) ≫
        E.singleToSingularity.map f ≫
          eqToHom (E.stableToSingularity_obj_projectiveStableFunctor_obj Y).symm :=
  Functor.congr_hom E.projectiveStableFunctor_comp_stableToSingularity f

/-- The image of an object of the stable category in the singularity category is the object
placed in degree zero. -/
noncomputable def stableToSingularityObjIso (X : C) :
    E.stableToSingularity.obj (E.projectiveStableFunctor.obj X) ≅
      (SingularityCategory.Q E).obj ((BoundedDerivedCategory.Q E).obj
        ((HomotopyCategory.Bounded.singleFunctor C 0).obj X)) :=
  Iso.refl _

@[simp]
theorem stableToSingularityObjIso_hom (X : C) :
    (E.stableToSingularityObjIso X).hom = eqToHom (by
      rw [stableToSingularity_obj_projectiveStableFunctor_obj, singleToSingularity_eq]
      rfl) :=
  (rfl)

@[simp]
theorem stableToSingularityObjIso_inv (X : C) :
    (E.stableToSingularityObjIso X).inv = eqToHom (by
      rw [stableToSingularity_obj_projectiveStableFunctor_obj, singleToSingularity_eq]
      rfl) :=
  (rfl)

/-- The identification `stableToSingularityObjIso` is natural. -/
@[reassoc]
theorem stableToSingularity_map_comp_stableToSingularityObjIso_hom {X Y : C} (f : X ⟶ Y) :
    E.stableToSingularity.map (E.projectiveStableFunctor.map f) ≫
        (E.stableToSingularityObjIso Y).hom =
      (E.stableToSingularityObjIso X).hom ≫ (SingularityCategory.Q E).map
        ((BoundedDerivedCategory.Q E).map
          ((HomotopyCategory.Bounded.singleFunctor C 0).map f)) := by
  simp [Functor.congr_hom E.singleToSingularity_eq f]

end TauCeti.ExactStructure
