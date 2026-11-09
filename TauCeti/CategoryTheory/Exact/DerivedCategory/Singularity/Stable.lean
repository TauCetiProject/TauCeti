/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.DerivedCategory.Singularity
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
  degree zero.
* `TauCeti.ExactStructure.stableToSingularity`: the induced functor `stable(E) ⥤ D_sg(E)`.

## References

* Bernhard Keller, Dieter Vossieck, *Sous les catégories dérivées*, C. R. Acad. Sci. Paris
  **305** (1987), 225--228, Example 2.3.
-/

public section

namespace TauCeti.ExactStructure

open CategoryTheory CategoryTheory.Limits ZeroObject

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  (E : ExactStructure C)

/-- The functor `C ⥤ D_sg(E)` placing an object in degree zero. -/
-- Exposed so that the induced functor on the stable category can be compared with it.
@[expose] noncomputable def singleToSingularity : C ⥤ E.SingularityCategory :=
  HomotopyCategory.Bounded.singleFunctor C 0 ⋙ BoundedDerivedCategory.Q E ⋙
    SingularityCategory.Q E

instance : E.singleToSingularity.Additive := by
  dsimp only [singleToSingularity]
  infer_instance

/-- A projective object vanishes in the singularity category. -/
theorem isZero_singleToSingularity_obj {P : C} (hP : E.isProjective P) :
    IsZero (E.singleToSingularity.obj P) :=
  SingularityCategory.isZero_Q_obj_of_boundedProjective
    (E.boundedProjective_Q_obj_singleFunctor_obj hP)

/-- A morphism factoring through a projective object vanishes in the singularity category. -/
theorem singleToSingularity_map_eq_zero {X Y : C} {f : X ⟶ Y}
    (hf : f ∈ E.projectiveStableIdeal.hom X Y) : E.singleToSingularity.map f = 0 := by
  obtain ⟨P, hP, p, q, rfl⟩ :=
    (ObjectProperty.factorsThrough_iff _ _).1 ((E.mem_projectiveStableIdeal_iff).1 hf)
  rw [Functor.map_comp,
    (E.isZero_singleToSingularity_obj hP).eq_of_src (E.singleToSingularity.map q) 0, comp_zero]

/-- The functor `stable(E) ⥤ D_sg(E)` induced by placing objects in degree zero. -/
-- Exposed so that its value on the image of a morphism of `C` can be stated.
@[expose] noncomputable def stableToSingularity :
    E.ProjectiveStableCategory ⥤ E.SingularityCategory :=
  CategoryTheory.Quotient.lift _ E.singleToSingularity fun _ _ f g h ↦ by
    rw [← sub_eq_zero, ← Functor.map_sub]
    exact E.singleToSingularity_map_eq_zero ((MorphismIdeal.rel_iff _).1 h)

/-- The functor `stable(E) ⥤ D_sg(E)` restricts to `singleToSingularity` along the quotient. -/
noncomputable def projectiveStableFunctorCompStableToSingularityIso :
    E.projectiveStableFunctor ⋙ E.stableToSingularity ≅ E.singleToSingularity :=
  CategoryTheory.Quotient.lift.isLift _ _ _

@[simp]
theorem stableToSingularity_map_projectiveStableFunctor_map {X Y : C} (f : X ⟶ Y) :
    E.stableToSingularity.map (E.projectiveStableFunctor.map f) =
      E.singleToSingularity.map f :=
  CategoryTheory.Quotient.lift_map_functor_map _ _ _ f

instance : E.stableToSingularity.Additive where
  map_add {X Y f g} := by
    obtain ⟨f, rfl⟩ := E.projectiveStableFunctor.map_surjective f
    obtain ⟨g, rfl⟩ := E.projectiveStableFunctor.map_surjective g
    rw [← E.projectiveStableFunctor.map_add, stableToSingularity_map_projectiveStableFunctor_map,
      stableToSingularity_map_projectiveStableFunctor_map,
      stableToSingularity_map_projectiveStableFunctor_map]
    exact E.singleToSingularity.map_add

end TauCeti.ExactStructure
