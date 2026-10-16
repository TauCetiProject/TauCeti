/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CommutativeAlgebra.MatrixFactorization.Triangulated
public import TauCeti.Algebra.Homology.Curved.Triangulated

/-!
# Finite matrix factorizations in the curved homotopy category

The inclusion of finite-projective matrix factorizations among curved duplexes descends to
homotopy categories. It is fully faithful: an odd homotopy between finite-projective
factorizations is exactly an odd homotopy between their underlying curved duplexes. Thus
the finite-projective homotopy category has precisely the same morphisms between its
objects as the ambient curved homotopy category.

The embedding is moreover a triangle functor for the triangulations of both homotopy categories
obtained from their componentwise split Frobenius structures. It commutes with the parity
shifts, hence with the shifts by `ℤ` they generate, and it sends the distinguished triangle of
a componentwise split short complex of finite-projective factorizations to the distinguished
triangle of the same short complex of curved duplexes. Being full, it then has a triangulated
essential image by Mathlib's general instance for full triangle functors.

This comparison uses the full-subcategory presentation of matrix factorizations and the
quotient-by-ideal construction. It is the homotopy-level form of the finite-projective
inclusion used in Orlov, *Triangulated categories of singularities and D-branes in
Landau–Ginzburg models*, Sections 1.2 and 3.

## Main results

* `TauCeti.MatrixFactorization.homotopyInclusion`: the fully faithful embedding of `HMF(S,w)`
  in the homotopy category of curved duplexes of finitely generated modules.
* `TauCeti.MatrixFactorization.parityShiftEquivalence_functor_comp_homotopyInclusion`: the
  embedding commutes with the parity shifts.
* `TauCeti.MatrixFactorization.homotopyInclusion_commShiftIso_one`: its compatibility with the
  shifts by `ℤ` is, in degree one, this commutation.
* The `Functor.IsTriangulated` instance for `homotopyInclusion`: the embedding is a triangle
  functor.
-/

public section

universe u

namespace TauCeti.MatrixFactorization

open CategoryTheory CategoryTheory.Limits

variable {S : Type u} [CommRing S] {w : S}

attribute [local instance] HasBinaryBiproducts.of_hasBinaryCoproducts

private theorem nullHomotopic_le_comap :
    nullHomotopic (S := S) (w := w) ≤
      (CurvedDuplex.nullHomotopic (FGModuleCat.{u} S) w).comap inclusion := by
  intro X Y f hf
  rw [MorphismIdeal.mem_comap_hom, CurvedDuplex.mem_nullHomotopic_iff]
  exact (mem_nullHomotopic_iff f).1 hf

/-- The finite-projective matrix-factorization homotopy category embeds in the homotopy
category of all curved duplexes of finitely generated modules. -/
noncomputable def homotopyInclusion :
    HomotopyCategory (S := S) (w := w) ⥤
      CurvedDuplex.HomotopyCategory (FGModuleCat.{u} S) w :=
  (nullHomotopic (S := S) (w := w)).map
    (CurvedDuplex.nullHomotopic (FGModuleCat.{u} S) w) inclusion nullHomotopic_le_comap

/-- The embedding of homotopy categories agrees on objects with the inclusion of
matrix factorizations followed by the curved-duplex quotient. -/
@[simp]
theorem homotopyInclusion_obj (X : MatrixFactorization S w) :
    homotopyInclusion.obj
        ((nullHomotopic (S := S) (w := w)).quotientFunctor.obj X) =
      (CurvedDuplex.nullHomotopic (FGModuleCat.{u} S) w).quotientFunctor.obj X.obj := by
  unfold homotopyInclusion
  exact MorphismIdeal.map_obj_quotientFunctor_obj
      (nullHomotopic (S := S) (w := w))
      (CurvedDuplex.nullHomotopic (FGModuleCat.{u} S) w) inclusion nullHomotopic_le_comap X

/-- On morphisms, the homotopy embedding sends a class to the class of the same
closed even map, viewed as a map of curved duplexes. -/
theorem homotopyInclusion_map (f : X ⟶ Y) :
    homotopyInclusion.map
        ((nullHomotopic (S := S) (w := w)).quotientFunctor.map f) ≫
          eqToHom (homotopyInclusion_obj Y) =
      eqToHom (homotopyInclusion_obj X) ≫
        (CurvedDuplex.nullHomotopic (FGModuleCat.{u} S) w).quotientFunctor.map f.hom := by
  unfold homotopyInclusion
  exact MorphismIdeal.map_map_quotientFunctor_map
      (nullHomotopic (S := S) (w := w))
      (CurvedDuplex.nullHomotopic (FGModuleCat.{u} S) w) inclusion nullHomotopic_le_comap f

/-- A homotopy class of finite-projective factorizations is zero in the curved-duplex
homotopy category only if it was already zero in the matrix-factorization homotopy category. -/
instance : homotopyInclusion (S := S) (w := w) |>.Faithful := by
  unfold homotopyInclusion
  exact (MorphismIdeal.faithful_map_iff
    (nullHomotopic (S := S) (w := w))
    (CurvedDuplex.nullHomotopic (FGModuleCat.{u} S) w) inclusion nullHomotopic_le_comap).2
      (by
        intro X Y f hf
        rw [MorphismIdeal.mem_comap_hom, CurvedDuplex.mem_nullHomotopic_iff] at hf
        exact (mem_nullHomotopic_iff f).2 hf)

/-- Every homotopy class between two finite-projective factorizations in the ambient curved
homotopy category is represented by a map of finite-projective factorizations. -/
instance : homotopyInclusion (S := S) (w := w) |>.Full := by
  unfold homotopyInclusion
  infer_instance

/-- The homotopy embedding restricts the curved-duplex quotient functor along the inclusion of
finite-projective factorizations. -/
theorem quotientFunctor_comp_homotopyInclusion :
    (nullHomotopic (S := S) (w := w)).quotientFunctor ⋙ homotopyInclusion =
      inclusion ⋙ (CurvedDuplex.nullHomotopic (FGModuleCat.{u} S) w).quotientFunctor :=
  MorphismIdeal.quotientFunctor_comp_map ..

/-- The homotopy embedding commutes with the parity shifts of the two homotopy categories. -/
theorem parityShiftEquivalence_functor_comp_homotopyInclusion :
    (HomotopyCategory.parityShiftEquivalence (S := S) (w := w)).functor ⋙ homotopyInclusion =
      homotopyInclusion ⋙
        (CurvedDuplex.HomotopyCategory.parityShiftEquivalence (FGModuleCat.{u} S) w).functor := by
  apply CategoryTheory.Quotient.lift_unique' (nullHomotopic (S := S) (w := w)).rel
  rw [← Functor.assoc, HomotopyCategory.quotientFunctor_comp_parityShiftEquivalence_functor,
    Functor.assoc, quotientFunctor_comp_homotopyInclusion, ← Functor.assoc,
    parityShift_comp_inclusion, Functor.assoc,
    ← CurvedDuplex.HomotopyCategory.quotientFunctor_comp_parityShiftEquivalence_functor,
    ← Functor.assoc, ← quotientFunctor_comp_homotopyInclusion, Functor.assoc]

/-- The homotopy embedding commutes with the shifts by `ℤ` generated by the parity shifts. -/
noncomputable instance : homotopyInclusion (S := S) (w := w) |>.CommShift ℤ :=
  Functor.commShiftOfIntertwining homotopyInclusion _ _
    (eqToIso parityShiftEquivalence_functor_comp_homotopyInclusion)

/-- In degree one, the shift compatibility of the homotopy embedding identifies the parity
shifts of the two homotopy categories. -/
theorem homotopyInclusion_commShiftIso_one :
    (homotopyInclusion (S := S) (w := w)).commShiftIso (1 : ℤ) =
      Functor.isoWhiskerRight (HomotopyCategory.shiftFunctorOneIso S w) _ ≪≫
        eqToIso parityShiftEquivalence_functor_comp_homotopyInclusion ≪≫
          Functor.isoWhiskerLeft _
            (CurvedDuplex.HomotopyCategory.shiftFunctorOneIso (FGModuleCat.{u} S) w).symm := by
  rw [HomotopyCategory.shiftFunctorOneIso_def,
    CurvedDuplex.HomotopyCategory.shiftFunctorOneIso_def]
  exact Functor.commShiftOfIntertwining_iso_one _ _ _ _

/-- On the image of a factorization `X`, the degree-one shift compatibility of the homotopy
embedding is induced by the identity of the parity shift of `X`. -/
@[reassoc]
private theorem map_parityShiftCompQuotientFunctorIso_hom_app_comp_commShiftIso_hom_app
    (X : MatrixFactorization S w) :
    homotopyInclusion.map ((HomotopyCategory.parityShiftCompQuotientFunctorIso S w).hom.app X) ≫
        (homotopyInclusion.commShiftIso (1 : ℤ)).hom.app
          ((nullHomotopic (S := S) (w := w)).quotientFunctor.obj X) =
      eqToHom (homotopyInclusion_obj _) ≫
        (CurvedDuplex.HomotopyCategory.parityShiftCompQuotientFunctorIso
          (FGModuleCat.{u} S) w).hom.app X.obj ≫
          eqToHom (by simp) := by
  rw [homotopyInclusion_commShiftIso_one]
  simp [eqToHom_map, eqToHom_app]

/-- **The homotopy embedding of matrix factorizations is a triangle functor.** The image of the
distinguished triangle of a componentwise split short complex of finite-projective factorizations
is the distinguished triangle of the same short complex of curved duplexes. -/
instance : homotopyInclusion (S := S) (w := w) |>.IsTriangulated where
  map_distinguished D hD := by
    obtain ⟨T, hT, a, δ, ha, hδ, ⟨e⟩⟩ := (HomotopyCategory.mem_distTriang_iff S w D).1 hD
    refine Pretriangulated.isomorphic_distinguished _
      (CurvedDuplex.HomotopyCategory.mk_distinguished_of_conflation
        (isConflationExact_inclusion.map_conflation hT) a.hom δ.hom
        (by simpa using congrArg InducedCategory.Hom.hom ha)
        (by simpa using congrArg InducedCategory.Hom.hom hδ)) _
      (homotopyInclusion.mapTriangle.mapIso e ≪≫ ?_)
    refine Pretriangulated.Triangle.isoMk _ _ (eqToIso (homotopyInclusion_obj _))
      (eqToIso (homotopyInclusion_obj _)) (eqToIso (homotopyInclusion_obj _)) ?_ ?_ ?_
    · exact homotopyInclusion_map T.f
    · exact homotopyInclusion_map T.g
    · simp only [Functor.mapTriangle_obj, Pretriangulated.Triangle.mk_obj₁,
        Pretriangulated.Triangle.mk_mor₃, ShortComplex.map_X₁, ObjectProperty.ι_obj, eqToIso.hom,
        Functor.map_comp, Category.assoc,
        map_parityShiftCompQuotientFunctorIso_hom_app_comp_commShiftIso_hom_app_assoc,
        eqToHom_map, eqToHom_trans, eqToHom_refl, Category.comp_id]
      rw [← Category.assoc, homotopyInclusion_map, Category.assoc]

end TauCeti.MatrixFactorization
