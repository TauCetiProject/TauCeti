/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.DerivedCategory.Singularity.KellerVossieck
public import TauCeti.CategoryTheory.Exact.DerivedCategory.Conflation
public import TauCeti.CategoryTheory.Exact.Stable.Triangulated

/-!
# The Keller–Vossieck equivalence is a triangle equivalence

Let `E` be a Frobenius exact structure. The functor `F : stable(E) ⥤ D_sg(E)` placing an object in
degree zero commutes with the shifts and sends Happel's standard triangles to distinguished
triangles, so the Keller–Vossieck equivalence is an equivalence of triangulated categories.

For an object `A` with suspension presentation `A ↣ I(A) ↠ ΣA`, the connecting morphism
`ΣA ⟶ A⟦1⟧` of the triangle of this conflation in `Dᵇ(E)` becomes invertible in `D_sg(E)`, since
`I(A)` is projective. These isomorphisms `F(ΣA) ≅ F(A)⟦1⟧` are natural by naturality of connecting
morphisms, and they make `F` commute with the shifts. The image of the standard triangle of a
conflation `S` is then the image in `D_sg(E)` of the triangle of `S` in `Dᵇ(E)`: the connecting
map `Z ⟶ ΣX` of `S` is a morphism from `S` to the suspension presentation of `X`.

The construction and the proofs adapt the abelian case of Gorenstein-projective objects, Chen's
functor in `TauCeti/Algebra/Homology/TotallyAcyclic/Abelian/Triangulated.lean`
(`CategoryTheory.GorensteinProjective.stableSuspensionCompToSingularityCategoryIso`,
`CategoryTheory.GorensteinProjective.toSingularityCategoryCommShift` and
`CategoryTheory.GorensteinProjective.toSingularityCategory_isTriangulated`), to a Frobenius exact
structure.

## Main definitions

* `TauCeti.ExactStructure.IsFrobenius.stableToSingularitySuspensionMap`: the comparison
  `F(ΣA) ⟶ F(A)⟦1⟧`, an isomorphism natural in `A`.
* `TauCeti.ExactStructure.IsFrobenius.stableSuspensionCompStableToSingularityIso`: the comparison
  `F ∘ Σ ≅ ⟦1⟧ ∘ F`.
* `TauCeti.ExactStructure.IsFrobenius.stableToSingularityCommShift`: the induced commutation of
  `F` with the shifts.

## Main results

* `TauCeti.ExactStructure.IsFrobenius.stableToSingularity_commShiftIso_one_hom_app`: the
  commutation with the shift in degree one.
* `TauCeti.ExactStructure.IsFrobenius.stableToSingularity_isTriangulated`: `F` is a triangle
  functor.

## References

* Bernhard Keller, Dieter Vossieck, *Sous les catégories dérivées*, C. R. Acad. Sci. Paris
  **305** (1987), 225--228, Example 2.3.
* Dieter Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, Chapter I, Section 2.
-/

public section

namespace TauCeti.ExactStructure.IsFrobenius

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  {E : ExactStructure C} (hF : E.IsFrobenius)

/-- The suspension presentation `A ↣ I(A) ↠ ΣA`, as a short complex. -/
private noncomputable abbrev suspensionShortComplex (A : C) : ShortComplex C :=
  ShortComplex.mk (hF.suspensionInflation A) (hF.suspensionDeflation A)
    (hF.suspensionPresentation A).zero

private theorem conflation_suspensionShortComplex (A : C) :
    E.Conflation (hF.suspensionShortComplex A) :=
  (hF.suspensionPresentation A).conflation

/-- `F` on the image of a morphism of `C`, through `stableToSingularityObjIso`. -/
private theorem stableToSingularity_map_eq {X Y : C} (f : X ⟶ Y) :
    E.stableToSingularity.map (E.projectiveStableFunctor.map f) =
      (E.stableToSingularityObjIso X).hom ≫ (SingularityCategory.Q E).map
        ((BoundedDerivedCategory.Q E).map ((HomotopyCategory.Bounded.singleFunctor C 0).map f)) ≫
          (E.stableToSingularityObjIso Y).inv := by
  rw [← E.stableToSingularity_map_comp_stableToSingularityObjIso_hom_assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- The comparison `F(ΣA) ⟶ F(A)⟦1⟧` for `F : stable(E) ⥤ D_sg(E)`: the connecting morphism of
the suspension presentation `A ↣ I(A) ↠ ΣA` in `Dᵇ(E)`, mapped to the singularity category. -/
noncomputable def stableToSingularitySuspensionMap (A : C) :
    E.stableToSingularity.obj (E.projectiveStableFunctor.obj (hF.suspensionObj A)) ⟶
      (E.stableToSingularity.obj (E.projectiveStableFunctor.obj A))⟦(1 : ℤ)⟧ :=
  (E.stableToSingularityObjIso _).hom ≫ ((SingularityCategory.Q E).map
    (BoundedDerivedCategory.conflationδ (hF.conflation_suspensionShortComplex A)) ≫
      ((SingularityCategory.Q E).commShiftIso (1 : ℤ)).hom.app _) ≫
        (E.stableToSingularityObjIso A).inv⟦(1 : ℤ)⟧'

/-- The comparison `F(ΣA) ⟶ F(A)⟦1⟧` is the connecting morphism of the suspension presentation
of `A` in `Dᵇ(E)`, mapped to the singularity category. -/
theorem stableToSingularitySuspensionMap_eq (A : C) :
    hF.stableToSingularitySuspensionMap A =
      (E.stableToSingularityObjIso _).hom ≫ ((SingularityCategory.Q E).map
        (BoundedDerivedCategory.conflationδ (hF.suspensionPresentation A).conflation) ≫
          ((SingularityCategory.Q E).commShiftIso (1 : ℤ)).hom.app _) ≫
            (E.stableToSingularityObjIso A).inv⟦(1 : ℤ)⟧' :=
  (rfl)

instance isIso_stableToSingularitySuspensionMap (A : C) :
    IsIso (hF.stableToSingularitySuspensionMap A) := by
  -- The middle term `I(A)` of the triangle of the presentation vanishes in `D_sg(E)`.
  have h := (Triangle.isZero₂_iff_isIso₃ _ ((SingularityCategory.Q E).map_distinguished _
    (BoundedDerivedCategory.conflationTriangle_distinguished
      (hF.conflation_suspensionShortComplex A)))).1
    (ObjectProperty.TrWLocalization.isZero_obj E.boundedProjective (SingularityCategory.Q E)
      (E.boundedProjective_Q_obj_singleFunctor_obj 0
        (hF.isProjective_I (hF.suspensionPresentation A))))
  have : IsIso ((SingularityCategory.Q E).map
      (BoundedDerivedCategory.conflationδ (hF.conflation_suspensionShortComplex A)) ≫
        ((SingularityCategory.Q E).commShiftIso (1 : ℤ)).hom.app _) := h
  dsimp only [stableToSingularitySuspensionMap]
  infer_instance

/-- The comparison `F(ΣA) ⟶ F(A)⟦1⟧` is natural in `A`. -/
theorem stableToSingularitySuspensionMap_naturality {A B : C} (f : A ⟶ B) :
    E.stableToSingularity.map (E.projectiveStableFunctor.map
        ((hF.suspensionPresentation A).cokernelMap (hF.suspensionPresentation B) f)) ≫
      hF.stableToSingularitySuspensionMap B =
        hF.stableToSingularitySuspensionMap A ≫
          (E.stableToSingularity.map (E.projectiveStableFunctor.map f))⟦(1 : ℤ)⟧' := by
  let φ : hF.suspensionShortComplex A ⟶ hF.suspensionShortComplex B :=
    { τ₁ := f
      τ₂ := (hF.suspensionPresentation A).middleMap (hF.suspensionPresentation B) f
      τ₃ := (hF.suspensionPresentation A).cokernelMap (hF.suspensionPresentation B) f
      comm₁₂ := ((hF.suspensionPresentation A).i_comp_middleMap _ f).symm
      comm₂₃ := ((hF.suspensionPresentation A).p_comp_cokernelMap _ f).symm }
  have h := BoundedDerivedCategory.conflationδ_naturality φ
    (hF.conflation_suspensionShortComplex A) (hF.conflation_suspensionShortComplex B)
  simp only [φ] at h
  have key := congrArg (SingularityCategory.Q E).map h
  simp only [Functor.map_comp] at key
  rw [stableToSingularity_map_eq,
    stableToSingularity_map_eq]
  dsimp only [stableToSingularitySuspensionMap]
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id_map_assoc]
  rw [← reassoc_of% key, Functor.commShiftIso_hom_naturality_assoc]

/-- **`F` intertwines stable suspension with the shift**: `F(ΣX) ≅ F(X)⟦1⟧`, naturally. -/
noncomputable def stableSuspensionCompStableToSingularityIso :
    hF.stableSuspension ⋙ E.stableToSingularity ≅
      E.stableToSingularity ⋙ shiftFunctor E.SingularityCategory (1 : ℤ) :=
  CategoryTheory.Quotient.natIsoLift _ (NatIso.ofComponents
    (fun A ↦ eqToIso (congrArg E.stableToSingularity.obj
        (hF.stableSuspension_obj_projectiveStableFunctor_obj A)) ≪≫
      asIso (hF.stableToSingularitySuspensionMap A))
    (fun {A B} f ↦ by
      simp only [Functor.comp_map, hF.stableSuspension_map_projectiveStableFunctor_map,
        Functor.map_comp, eqToHom_map, Iso.trans_hom, eqToIso.hom, asIso_hom, Category.assoc,
        eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
        stableToSingularitySuspensionMap_naturality]))

/-- On the class of an object `A`, the comparison is the connecting morphism `F(ΣA) ⟶ F(A)⟦1⟧` of
its suspension presentation. -/
@[simp]
theorem stableSuspensionCompStableToSingularityIso_hom_app (A : C) :
    hF.stableSuspensionCompStableToSingularityIso.hom.app (E.projectiveStableFunctor.obj A) =
      eqToHom (congrArg E.stableToSingularity.obj
        (hF.stableSuspension_obj_projectiveStableFunctor_obj A)) ≫
        hF.stableToSingularitySuspensionMap A :=
  (rfl)

/-- The commutation of `F : stable(E) ⥤ D_sg(E)` with the shifts. -/
@[instance_reducible]
noncomputable def stableToSingularityCommShift :
    letI := hF.stableHasShift
    E.stableToSingularity.CommShift ℤ :=
  hF.commShiftOfIntertwiningStableSuspensionShift _ hF.stableSuspensionCompStableToSingularityIso

/-- In degree one, the commutation of `F` with the shifts is the identification `Σ ≅ ⟦1⟧` of the
stable category followed by the comparison `F ∘ Σ ≅ ⟦1⟧ ∘ F`. -/
theorem stableToSingularity_commShiftIso_one_hom_app (X : E.ProjectiveStableCategory) :
    letI := hF.stableHasShift
    letI := hF.stableToSingularityCommShift
    (E.stableToSingularity.commShiftIso (1 : ℤ)).hom.app X =
      E.stableToSingularity.map (hF.stableShiftFunctorOneIso.hom.app X) ≫
        hF.stableSuspensionCompStableToSingularityIso.hom.app X := by
  let := hF.stableHasShift
  let := hF.stableToSingularityCommShift
  rw [hF.commShiftOfIntertwiningStableSuspensionShift_iso_one E.stableToSingularity
    hF.stableSuspensionCompStableToSingularityIso]
  rfl

/-- The image of the connecting map `Z ⟶ ΣX` of a conflation `X ↣ Y ↠ Z`, followed by the
comparison `F(ΣX) ⟶ F(X)⟦1⟧`, is the connecting morphism of the conflation in `D_sg(E)`. -/
theorem stableToSingularity_map_connectingMap_comp {S : ShortComplex C} (hS : E.Conflation S) :
    E.stableToSingularity.map (E.projectiveStableFunctor.map (hF.connectingMap hS)) ≫
        hF.stableToSingularitySuspensionMap S.X₁ =
      (E.stableToSingularityObjIso S.X₃).hom ≫ ((SingularityCategory.Q E).map
        (BoundedDerivedCategory.conflationδ hS) ≫
          ((SingularityCategory.Q E).commShiftIso (1 : ℤ)).hom.app _) ≫
            (E.stableToSingularityObjIso S.X₁).inv⟦(1 : ℤ)⟧' := by
  let φ : S ⟶ hF.suspensionShortComplex S.X₁ :=
    { τ₁ := 𝟙 _
      τ₂ := hF.connectingMiddleMap hS
      τ₃ := hF.connectingMap hS
      comm₁₂ := by simp
      comm₂₃ := (hF.g_comp_connectingMap hS).symm }
  have h := BoundedDerivedCategory.conflationδ_naturality φ hS
    (hF.conflation_suspensionShortComplex S.X₁)
  simp only [φ, CategoryTheory.Functor.map_id, Category.comp_id] at h
  simp only [stableToSingularity_map_eq,
    stableToSingularitySuspensionMap, Category.assoc, Iso.inv_hom_id_assoc, h, Functor.map_comp]

/-- **The Keller–Vossieck functor is a triangle functor**: `F : stable(E) ⥤ D_sg(E)` sends Happel's
distinguished triangles to distinguished triangles. -/
theorem stableToSingularity_isTriangulated :
    let := hF.stableHasShift
    let : ∀ n : ℤ, (shiftFunctor E.ProjectiveStableCategory n).Additive :=
      hF.stableShiftFunctor_additive
    let := hF.stablePretriangulated
    let := hF.stableToSingularityCommShift
    E.stableToSingularity.IsTriangulated := by
  let := hF.stableHasShift
  let : ∀ n : ℤ, (shiftFunctor E.ProjectiveStableCategory n).Additive :=
    hF.stableShiftFunctor_additive
  let := hF.stablePretriangulated
  let := hF.stableToSingularityCommShift
  constructor
  intro T hT
  rw [hF.stablePretriangulated_distinguishedTriangles] at hT
  obtain ⟨S, hS, ⟨e⟩⟩ := (hF.mem_stableDistinguishedTriangles_iff T).1 hT
  refine isomorphic_distinguished _ ((SingularityCategory.Q E).map_distinguished _
    (BoundedDerivedCategory.conflationTriangle_distinguished hS)) _
    (E.stableToSingularity.mapTriangle.mapIso e ≪≫ ?_)
  rw [hF.stableConflationTriangle_eq_mk]
  refine Triangle.isoMk _ _ (E.stableToSingularityObjIso _) (E.stableToSingularityObjIso _)
    (E.stableToSingularityObjIso _) ?_ ?_ ?_
  · dsimp
    rw [stableToSingularity_map_eq, Category.assoc, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  · dsimp
    rw [stableToSingularity_map_eq, Category.assoc, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  · -- The comparison of shifts in degree one is `stableToSingularitySuspensionMap`.
    have h₄ := hF.stableToSingularity_map_connectingMap_comp hS
    dsimp
    rw [stableToSingularity_commShiftIso_one_hom_app,
      stableSuspensionCompStableToSingularityIso_hom_app]
    simp only [Functor.map_comp, Category.assoc, ← Functor.map_comp_assoc E.stableToSingularity,
      Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp, eqToHom_map,
      eqToHom_trans_assoc, eqToHom_refl, reassoc_of% h₄, Iso.inv_hom_id_map, Category.comp_id]

end TauCeti.ExactStructure.IsFrobenius
