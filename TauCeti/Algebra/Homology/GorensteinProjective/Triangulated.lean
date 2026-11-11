/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.TotallyAcyclic.Abelian.Singularity
public import TauCeti.CategoryTheory.Exact.Stable.Triangulated

/-!
# Chen's functor is a triangle functor

Let `C` be an abelian category. Chen's functor `F : stable(Gproj C) ⥤ D_sg(C)` from the stable
category of Gorenstein-projective objects, triangulated by Happel's theorem, to the singularity
category `D_sg(C) = Dᵇ(C) / Perf(C)` places an object in degree zero. It commutes with the shifts
and sends Happel's standard triangles to distinguished triangles. Over an Iwanaga–Gorenstein ring it
is an equivalence (`TauCeti.IsIwanagaGorenstein.isEquivalence_toSingularityCategory`), hence a
triangle equivalence: this is Buchweitz's theorem.

For a Gorenstein-projective object `A` with suspension presentation `A ↣ I(A) ↠ ΣA`, the connecting
morphism `ΣA ⟶ A⟦1⟧` of the triangle of this short exact sequence in `Dᵇ(C)` becomes invertible in
`D_sg(C)`, since `I(A)` is projective. These isomorphisms `F(ΣA) ≅ F(A)⟦1⟧` are natural, by the
naturality of connecting morphisms, and make `F` commute with the shifts. The image of the standard
triangle of a conflation `S` is then the image in `D_sg(C)` of the triangle of `S` in `Dᵇ(C)`: the
connecting map `Z ⟶ ΣX` of `S` is a morphism from `S` to the suspension presentation of `X`.
This is the comparison of Keller–Vossieck's Example 2.3, specialized to an abelian category.

## Main definitions

* `CategoryTheory.GorensteinProjective.stableSuspensionCompToSingularityCategoryIso`: the comparison
  `F ∘ Σ ≅ ⟦1⟧ ∘ F`.
* `CategoryTheory.GorensteinProjective.toSingularityCategoryCommShift`: the induced commutation of
  `F` with the shifts.

## Main results

* `CategoryTheory.GorensteinProjective.toSingularityCategoryCommShift_hom_app_one` and
  `CategoryTheory.GorensteinProjective.toSingularityCategory_map_stableConflationTriangle_mor₃`: the
  commutation with the shift in degree one, and the image of the third morphism of a stable
  conflation triangle.
* `CategoryTheory.GorensteinProjective.toSingularityCategory_isTriangulated`: Chen's functor is a
  triangle functor.

## References

* Ragnar-Olaf Buchweitz, *Maximal Cohen–Macaulay Modules and Tate Cohomology*, Mathematical
  Surveys and Monographs **262**, American Mathematical Society (2021), Theorem 4.4.1.
* Xiao-Wu Chen, *Relative singularity categories and Gorenstein-projective modules*, Math. Nachr.
  **284** (2011), 199–212.
* Dieter Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, Chapter I, Section 2.
* Bernhard Keller, Dieter Vossieck, *Sous les catégories dérivées*, C. R. Acad. Sci. Paris Sér. I
  Math. **305** (1987), 225–228, Example 2.3.
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TauCeti

universe w v u

namespace CategoryTheory.GorensteinProjective

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

local notation "hF" => (exactStructure_isFrobenius (C := C))

/-- The suspension presentation `A ↣ I(A) ↠ ΣA` of a Gorenstein-projective object, as a short
complex of `C`. -/
private noncomputable abbrev suspensionShortComplex (A : GorensteinProjective C) : ShortComplex C :=
  (ShortComplex.mk ((hF).suspensionInflation A) ((hF).suspensionDeflation A)
    ((hF).suspensionPresentation A).zero).map (isGorensteinProjective C).ι

omit [HasDerivedCategory C] in
private theorem shortExact_suspensionShortComplex (A : GorensteinProjective C) :
    (suspensionShortComplex A).ShortExact :=
  (exactStructure_conflation_iff _).1 ((hF).suspensionPresentation A).conflation

variable (C) in
/-- The comparison `F(ΣA) ⟶ F(A)⟦1⟧`: the connecting morphism of the suspension presentation of
`A`, in the singularity category. -/
noncomputable def toSingularityCategoryFunctorSuspensionMap (A : GorensteinProjective C) :
    (toSingularityCategoryFunctor C).obj ((hF).suspensionObj A) ⟶
      ((toSingularityCategoryFunctor C).obj A)⟦(1 : ℤ)⟧ :=
  (SingularityCategory.Q C).map (shortExact_suspensionShortComplex A).boundedSingleTriangle.mor₃ ≫
    ((SingularityCategory.Q C).commShiftIso (1 : ℤ)).hom.app _

theorem isIso_toSingularityCategoryFunctorSuspensionMap (A : GorensteinProjective C) :
    IsIso (toSingularityCategoryFunctorSuspensionMap C A) := by
  have hT := (SingularityCategory.Q C).map_distinguished _
    (shortExact_suspensionShortComplex A).boundedSingleTriangle_distinguished
  have hI : Projective ((hF).suspensionPresentation A).I.obj :=
    (exactStructure_isProjective_iff _).1 ((hF).isProjective_I ((hF).suspensionPresentation A))
  exact (Triangle.isZero₂_iff_isIso₃ _ hT).1 (SingularityCategory.isZero_Q_obj_singleFunctor_obj hI)

/-- The comparison `F(ΣA) ⟶ F(A)⟦1⟧` is natural. -/
theorem toSingularityCategoryFunctorSuspensionMap_naturality {A B : GorensteinProjective C}
    (f : A ⟶ B) :
    (toSingularityCategoryFunctor C).map
        (((hF).suspensionPresentation A).cokernelMap ((hF).suspensionPresentation B) f) ≫
      toSingularityCategoryFunctorSuspensionMap C B =
        toSingularityCategoryFunctorSuspensionMap C A ≫
          ((toSingularityCategoryFunctor C).map f)⟦(1 : ℤ)⟧' := by
  let φ : suspensionShortComplex A ⟶ suspensionShortComplex B :=
    { τ₁ := f.hom
      τ₂ := (((hF).suspensionPresentation A).middleMap ((hF).suspensionPresentation B) f).hom
      τ₃ := (((hF).suspensionPresentation A).cokernelMap ((hF).suspensionPresentation B) f).hom
      comm₁₂ := congrArg (·.hom)
        (((hF).suspensionPresentation A).i_comp_middleMap ((hF).suspensionPresentation B) f).symm
      comm₂₃ := congrArg (·.hom)
        (((hF).suspensionPresentation A).p_comp_cokernelMap
          ((hF).suspensionPresentation B) f).symm }
  have h := (SingularityCategory.Q C).congr_map
    (ShortComplex.ShortExact.boundedSingleTriangle_mor₃_naturality φ
      (shortExact_suspensionShortComplex A) (shortExact_suspensionShortComplex B))
  simp only [Functor.map_comp] at h
  -- Chen's functor on `C` is, by definition, `Q` applied to the bounded single functor.
  calc _ = (SingularityCategory.Q C).map ((DerivedCategory.Bounded.singleFunctor C 0).map φ.τ₃) ≫
        (SingularityCategory.Q C).map
          (shortExact_suspensionShortComplex B).boundedSingleTriangle.mor₃ ≫
        ((SingularityCategory.Q C).commShiftIso (1 : ℤ)).hom.app _ := rfl
    _ = (SingularityCategory.Q C).map
          (shortExact_suspensionShortComplex A).boundedSingleTriangle.mor₃ ≫
        (SingularityCategory.Q C).map
          (((DerivedCategory.Bounded.singleFunctor C 0).map φ.τ₁)⟦(1 : ℤ)⟧') ≫
        ((SingularityCategory.Q C).commShiftIso (1 : ℤ)).hom.app _ := (reassoc_of% h) _
    _ = _ := by rw [Functor.commShiftIso_hom_naturality, ← Category.assoc]; rfl

/-- The comparison `F(ΣA) ⟶ F(A)⟦1⟧`, between objects of the stable category. -/
private noncomputable def suspensionIsoAux (A : GorensteinProjective C) :
    (toSingularityCategory C).obj ((exactStructure C).projectiveStableFunctor.obj
        ((hF).suspensionObj A)) ≅
      ((toSingularityCategory C).obj ((exactStructure C).projectiveStableFunctor.obj A))⟦(1 : ℤ)⟧ :=
  @asIso _ _ _ _ (toSingularityCategoryFunctorSuspensionMap C A)
    (isIso_toSingularityCategoryFunctorSuspensionMap A)

private theorem suspensionIsoAux_hom_naturality {A B : GorensteinProjective C} (f : A ⟶ B) :
    (toSingularityCategory C).map ((exactStructure C).projectiveStableFunctor.map
        (((hF).suspensionPresentation A).cokernelMap ((hF).suspensionPresentation B) f)) ≫
      (suspensionIsoAux B).hom = (suspensionIsoAux A).hom ≫
        ((toSingularityCategory C).map
          ((exactStructure C).projectiveStableFunctor.map f))⟦(1 : ℤ)⟧' :=
  toSingularityCategoryFunctorSuspensionMap_naturality f

variable (C) in
/-- **Chen's functor intertwines the stable suspension with the shift**: `F(ΣX) ≅ F(X)⟦1⟧`,
naturally. -/
noncomputable def stableSuspensionCompToSingularityCategoryIso :
    (hF).stableSuspension ⋙ toSingularityCategory C ≅
      toSingularityCategory C ⋙ shiftFunctor (SingularityCategory C) (1 : ℤ) :=
  CategoryTheory.Quotient.natIsoLift _ (NatIso.ofComponents
    (fun A ↦ eqToIso (congrArg (toSingularityCategory C).obj
        ((hF).stableSuspension_obj_projectiveStableFunctor_obj A)) ≪≫ suspensionIsoAux A)
    (fun {A B} f ↦ by
      -- The quotient functor followed by the stable suspension is the map on cokernels.
      change (toSingularityCategory C).map ((hF).stableSuspension.map
          ((exactStructure C).projectiveStableFunctor.map f)) ≫ _ =
        _ ≫ ((toSingularityCategory C).map
          ((exactStructure C).projectiveStableFunctor.map f))⟦(1 : ℤ)⟧'
      rw [(hF).stableSuspension_map_projectiveStableFunctor_map, Functor.map_comp,
        Functor.map_comp, eqToHom_map, eqToHom_map]
      simp only [Iso.trans_hom, eqToIso.hom, Category.assoc, eqToHom_trans_assoc,
        eqToHom_refl, Category.id_comp, suspensionIsoAux_hom_naturality]))

/-- On the image of a Gorenstein-projective object `A`, the comparison is the connecting morphism
`F(ΣA) ⟶ F(A)⟦1⟧` of its suspension presentation. -/
@[simp]
theorem stableSuspensionCompToSingularityCategoryIso_hom_app (A : GorensteinProjective C) :
    (stableSuspensionCompToSingularityCategoryIso C).hom.app
      ((exactStructure C).projectiveStableFunctor.obj A) =
        eqToHom (congrArg (toSingularityCategory C).obj
          ((hF).stableSuspension_obj_projectiveStableFunctor_obj A)) ≫
        toSingularityCategoryFunctorSuspensionMap C A :=
  (rfl)

variable (C) in
/-- The commutation of Chen's functor with the shifts. -/
@[instance_reducible]
noncomputable def toSingularityCategoryCommShift :
    letI := (hF).stableHasShift
    (toSingularityCategory C).CommShift ℤ :=
  (hF).commShiftOfIntertwiningStableSuspensionShift _
    (stableSuspensionCompToSingularityCategoryIso C)

/-- In degree one, the commutation of Chen's functor with the shifts is the identification
`Σ ≅ ⟦1⟧` of the stable category followed by the comparison `F ∘ Σ ≅ ⟦1⟧ ∘ F`. -/
theorem toSingularityCategoryCommShift_hom_app_one
    (X : (exactStructure C).ProjectiveStableCategory) :
    letI := (hF).stableHasShift
    letI := toSingularityCategoryCommShift C
    ((toSingularityCategory C).commShiftIso (1 : ℤ)).hom.app X =
      (toSingularityCategory C).map ((hF).stableShiftFunctorOneIso.hom.app X) ≫
        (stableSuspensionCompToSingularityCategoryIso C).hom.app X := by
  let := (hF).stableHasShift
  let := toSingularityCategoryCommShift C
  rw [(hF).commShiftOfIntertwiningStableSuspensionShift_iso_one (toSingularityCategory C)
    (stableSuspensionCompToSingularityCategoryIso C)]
  rfl

/-- In the singularity category, the connecting morphism of a short exact sequence
`X ↣ Y ↠ Z` of Gorenstein-projective objects is its connecting map `Z ⟶ ΣX` followed by the
comparison `F(ΣX) ≅ F(X)⟦1⟧`. -/
theorem Q_map_boundedSingleTriangle_mor₃ {S : ShortComplex (GorensteinProjective C)}
    (hS : (exactStructure C).Conflation S) :
    (SingularityCategory.Q C).map
        ((exactStructure_conflation_iff S).1 hS).boundedSingleTriangle.mor₃ ≫
      ((SingularityCategory.Q C).commShiftIso (1 : ℤ)).hom.app _ =
        (toSingularityCategoryFunctor C).map ((hF).connectingMap hS) ≫
          toSingularityCategoryFunctorSuspensionMap C S.X₁ := by
  let φ : S.map (isGorensteinProjective C).ι ⟶ suspensionShortComplex S.X₁ :=
    { τ₁ := 𝟙 _
      τ₂ := ((hF).connectingMiddleMap hS).hom
      τ₃ := ((hF).connectingMap hS).hom
      comm₁₂ := by
        rw [Category.id_comp]
        exact (congrArg (·.hom) ((hF).f_comp_connectingMiddleMap hS)).symm
      comm₂₃ := congrArg (·.hom) ((hF).g_comp_connectingMap hS).symm }
  have h := ShortComplex.ShortExact.boundedSingleTriangle_mor₃_naturality φ
    ((exactStructure_conflation_iff S).1 hS) (shortExact_suspensionShortComplex S.X₁)
  -- Chen's functor on `C` is, by definition, `Q` applied to the bounded single functor.
  calc _ = (SingularityCategory.Q C).map
        (((exactStructure_conflation_iff S).1 hS).boundedSingleTriangle.mor₃ ≫
          ((DerivedCategory.Bounded.singleFunctor C 0).map φ.τ₁)⟦(1 : ℤ)⟧') ≫
        ((SingularityCategory.Q C).commShiftIso (1 : ℤ)).hom.app _ := by simp [φ]
    _ = (SingularityCategory.Q C).map ((DerivedCategory.Bounded.singleFunctor C 0).map φ.τ₃ ≫
        (shortExact_suspensionShortComplex S.X₁).boundedSingleTriangle.mor₃) ≫
        ((SingularityCategory.Q C).commShiftIso (1 : ℤ)).hom.app _ := by rw [h]; rfl
    _ = _ := by rw [Functor.map_comp, Category.assoc]; rfl

/-- **The third morphism of a stable conflation triangle.** For a conflation `S` of
Gorenstein-projective objects, the third morphism of its stable conflation triangle
(`ExactStructure.IsFrobenius.stableConflationTriangle_eq_mk`), followed by the commutation of
Chen's functor with the shift, is sent to the connecting morphism of the triangle of `S` in
`Dᵇ(C)`. -/
theorem toSingularityCategory_map_stableConflationTriangle_mor₃
    {S : ShortComplex (GorensteinProjective C)} (hS : (exactStructure C).Conflation S) :
    letI := (hF).stableHasShift
    letI := toSingularityCategoryCommShift C
    (toSingularityCategory C).map ((exactStructure C).projectiveStableFunctor.map
        ((hF).connectingMap hS) ≫
          eqToHom ((hF).stableSuspension_obj_projectiveStableFunctor_obj S.X₁).symm ≫
          (hF).stableShiftFunctorOneIso.inv.app
            ((exactStructure C).projectiveStableFunctor.obj S.X₁)) ≫
        ((toSingularityCategory C).commShiftIso (1 : ℤ)).hom.app
          ((exactStructure C).projectiveStableFunctor.obj S.X₁) =
      (SingularityCategory.Q C).map
          ((exactStructure_conflation_iff S).1 hS).boundedSingleTriangle.mor₃ ≫
        ((SingularityCategory.Q C).commShiftIso (1 : ℤ)).hom.app _ := by
  let := (hF).stableHasShift
  let := toSingularityCategoryCommShift C
  -- The shift identification `Σ ≅ ⟦1⟧` cancels, and the comparison on `ΣX₁` is the connecting
  -- morphism of the suspension presentation of `X₁`.
  have k₁ : (toSingularityCategory C).map
      ((hF).stableShiftFunctorOneIso.inv.app
        ((exactStructure C).projectiveStableFunctor.obj S.X₁)) ≫
        (toSingularityCategory C).map ((hF).stableShiftFunctorOneIso.hom.app
          ((exactStructure C).projectiveStableFunctor.obj S.X₁)) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  have k₂ : (toSingularityCategory C).map
      (eqToHom ((hF).stableSuspension_obj_projectiveStableFunctor_obj S.X₁).symm) ≫
        (stableSuspensionCompToSingularityCategoryIso C).hom.app
          ((exactStructure C).projectiveStableFunctor.obj S.X₁) =
      toSingularityCategoryFunctorSuspensionMap C S.X₁ := by
    rw [stableSuspensionCompToSingularityCategoryIso_hom_app, eqToHom_map]
    exact eqToHom_trans_assoc _ _ _ |>.trans
      (by simp only [eqToHom_refl]; exact Category.id_comp _)
  rw [toSingularityCategoryCommShift_hom_app_one, Functor.map_comp, Functor.map_comp,
    Category.assoc, Category.assoc, reassoc_of% k₁, k₂,
    toSingularityCategory_map_projectiveStableFunctor_map]
  exact (Q_map_boundedSingleTriangle_mor₃ hS).symm

/-- **Chen's functor is a triangle functor**: `F : stable(Gproj C) ⥤ D_sg(C)` sends Happel's
distinguished triangles to distinguished triangles. -/
theorem toSingularityCategory_isTriangulated :
    let := (hF).stableHasShift
    let : ∀ n : ℤ, (shiftFunctor (exactStructure C).ProjectiveStableCategory n).Additive :=
      (hF).stableShiftFunctor_additive
    let := (hF).stablePretriangulated
    let := toSingularityCategoryCommShift C
    (toSingularityCategory C).IsTriangulated := by
  let := (hF).stableHasShift
  let : ∀ n : ℤ, (shiftFunctor (exactStructure C).ProjectiveStableCategory n).Additive :=
    (hF).stableShiftFunctor_additive
  let := (hF).stablePretriangulated
  let := toSingularityCategoryCommShift C
  constructor
  intro T hT
  rw [(hF).stablePretriangulated_distinguishedTriangles] at hT
  obtain ⟨S, hS, ⟨e⟩⟩ := ((hF).mem_stableDistinguishedTriangles_iff T).1 hT
  refine isomorphic_distinguished _ ((SingularityCategory.Q C).map_distinguished _
    ((exactStructure_conflation_iff S).1 hS).boundedSingleTriangle_distinguished) _
    ((toSingularityCategory C).mapTriangle.mapIso e ≪≫ ?_)
  rw [(hF).stableConflationTriangle_eq_mk]
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · exact (Category.comp_id _).trans ((toSingularityCategory_map_projectiveStableFunctor_map
      S.f).trans (Category.id_comp _).symm)
  · exact (Category.comp_id _).trans ((toSingularityCategory_map_projectiveStableFunctor_map
      S.g).trans (Category.id_comp _).symm)
  · exact (congrArg (fun x ↦ _ ≫ x) (CategoryTheory.Functor.map_id
      (shiftFunctor (SingularityCategory C) (1 : ℤ)) _)).trans
        ((Category.comp_id _).trans ((toSingularityCategory_map_stableConflationTriangle_mor₃
          hS).trans (Category.id_comp _).symm))

end CategoryTheory.GorensteinProjective
