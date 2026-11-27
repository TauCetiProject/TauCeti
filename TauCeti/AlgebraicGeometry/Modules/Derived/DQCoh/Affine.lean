/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Derived.Affine.GlobalSections
public import TauCeti.AlgebraicGeometry.Modules.Derived.Affine.Sections
public import TauCeti.AlgebraicGeometry.Modules.Derived.DQCoh.Basic

/-!
# The derived category of an affine scheme

For a commutative ring `A`, this file proves that `M ↦ M~` induces an equivalence
`DQCoh.affineEquiv A : D(A) ≌ D_QCoh(𝒪_{Spec A})`
([Stacks, Lemma 36.3.5](https://stacks.math.columbia.edu/tag/06Z0)), whose quasi-inverse is
derived global sections `derivedModuleSpecΓFunctor A`, the right derived functor of global sections
on unbounded complexes.

* `isIso_tildeDerivedAdjunction_unit`: the unit of the derived adjunction
  `tildeDerivedAdjunction A : (M ↦ M~) ⊣ RΓ(Spec A, -)` is an isomorphism, so that
  `D(A) ⥤ D(𝒪_{Spec A})` is fully faithful (`fullyFaithfulMapDerivedCategoryTildeFunctor`).
* `isIso_tildeDerivedAdjunction_counit_app`: its counit is an isomorphism on `D_QCoh(𝒪_{Spec A})`,
  and the essential image of `D(A) ⥤ D(𝒪_{Spec A})` is `D_QCoh(𝒪_{Spec A})`
  (`DQCoh.mem_essImage_mapDerivedCategory_tildeFunctor_iff`).
* `DQCoh.affineEquiv`: the derived adjunction restricted to `D_QCoh(𝒪_{Spec A})` is an equivalence.
  On complexes, its functor is `M ↦ M~` applied termwise (`DQCoh.affineEquivFunctorFactors`).

The input is the computation of global sections of K-injective complexes with quasi-coherent
cohomology in `TauCeti.AlgebraicGeometry.Modules.Derived.Affine.Sections`, which rests on the
vanishing of the cohomology of quasi-coherent sheaves on affine schemes.

## References

* [Stacks: Lemma 36.3.5](https://stacks.math.columbia.edu/tag/06Z0), the derived category of an
  affine scheme.
-/

public section

open CategoryTheory Limits DerivedCategory

namespace TauCeti.AlgebraicGeometry.Coherent

open _root_.AlgebraicGeometry

universe w w' u

section AffineEquiv

open CochainComplex HomologicalComplex ZeroObject

variable {A : CommRingCat.{u}}

/-- On complexes, the global-section functors with values in `A`-modules and in modules over the
ring of global functions agree on quasi-isomorphisms: they have the same underlying abelian groups
and maps. -/
private lemma quasiIso_map_moduleSpecΓFunctor_iff {K L : CochainComplex (Spec A).Modules ℤ}
    (f : K ⟶ L) :
    QuasiIso (((moduleSpecΓFunctor (R := A)).mapHomologicalComplex _).map f) ↔
      QuasiIso (((Scheme.Modules.sectionsFunctor (⊤ : (Spec A).Opens)).mapHomologicalComplex
        _).map f) := by
  rw [← quasiIso_map_iff_of_preservesHomology _ (forget₂ (ModuleCat.{u} A) AddCommGrpCat),
    ← quasiIso_map_iff_of_preservesHomology _ (forget₂ (ModuleCat.{u} Γ(Spec A, ⊤)) AddCommGrpCat)]
  -- after forgetting the scalars, both functors take the sections over `⊤`, by definition
  rfl

/-- On complexes, exactness of global sections does not depend on the ring over which they are
viewed as modules. -/
private lemma exactAt_map_moduleSpecΓFunctor_iff (K : CochainComplex (Spec A).Modules ℤ) (m : ℤ) :
    (((moduleSpecΓFunctor (R := A)).mapHomologicalComplex _).obj K).ExactAt m ↔
      (((Scheme.Modules.sectionsFunctor (⊤ : (Spec A).Opens)).mapHomologicalComplex _).obj
        K).ExactAt m := by
  rw [HomologicalComplex.exactAt_iff, HomologicalComplex.exactAt_iff,
    ← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (ModuleCat.{u} A) AddCommGrpCat),
    ← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (ModuleCat.{u} Γ(Spec A, ⊤)) AddCommGrpCat)]
  -- after forgetting the scalars, both functors take the sections over `⊤`, by definition
  rfl

/-- **Global sections compute derived global sections on `M~`.** For a complex `P` of `A`-modules
and a quasi-isomorphism `P~ ⟶ I` into a K-injective complex, the map `P = Γ(P~) ⟶ Γ(I)` is a
quasi-isomorphism. -/
private lemma quasiIso_map_moduleSpecΓFunctor_of_tilde (P : CochainComplex (ModuleCat.{u} A) ℤ)
    {I : CochainComplex (Spec A).Modules ℤ} [I.IsKInjective]
    (f : ((tilde.functor A).mapHomologicalComplex _).obj P ⟶ I) [QuasiIso f] :
    QuasiIso (((moduleSpecΓFunctor (R := A)).mapHomologicalComplex _).map f) := by
  rw [quasiIso_map_moduleSpecΓFunctor_iff]
  refine TauCeti.AlgebraicGeometry.Scheme.Modules.quasiIso_map_sectionsFunctor_of_isKInjective
    (fun i ↦ ?_) (fun j ↦ ?_) f
  · exact (Scheme.Modules.isQuasicoherent _).prop_of_iso
      ((P.sc i).mapHomologyIso (tilde.functor A)).symm
      (inferInstanceAs ((tilde.functor A).obj _).IsQuasicoherent)
  · have h (i : ℤ) : ((((tilde.functor A).mapHomologicalComplex _).obj P).X i).IsQuasicoherent :=
      inferInstanceAs ((tilde.functor A).obj _).IsQuasicoherent
    exact @Scheme.Modules.preservesLeftHomologyOf_sectionsFunctor_of_isQuasicoherent _ _ _
      (h _) (h _)

variable [HasDerivedCategory.{w} (Spec A).Modules] [HasDerivedCategory.{w'} (ModuleCat.{u} A)]


/-- **The unit of the derived adjunction is an isomorphism**: for every complex `M` of `A`-modules,
`M ⟶ RΓ(Spec A, M~)` is an isomorphism in `D(A)`. -/
instance isIso_tildeDerivedAdjunction_unit_app (M : DerivedCategory (ModuleCat.{u} A)) :
    IsIso ((tildeDerivedAdjunction A).unit.app M) := by
  suffices h : ∀ K : HomotopyCategory (ModuleCat.{u} A) (.up ℤ),
      IsIso ((tildeDerivedAdjunction A).unit.app (Qh.obj K)) from
    (NatTrans.isIso_app_iff_of_iso _ (Qh.objObjPreimageIso M)).1 (h _)
  intro K
  -- the unit of `M ↦ M~ ⊣ Γ` is an isomorphism, also on complexes
  have h₁ : IsIso (Qh.map ((tilde.adjunction.mapHomotopyCategory (.up ℤ)).unit.app K)) := by
    -- every object of the homotopy category is the class of its underlying complex
    rw [show K = (HomotopyCategory.quotient _ _).obj K.as from rfl,
      Adjunction.mapHomotopyCategory_unit_app]
    have (i : ℤ) :
        IsIso (((tilde.adjunction.mapHomologicalComplex (.up ℤ)).unit.app K.as).f i) := by
      rw [Adjunction.mapHomologicalComplex_unit_app_f]
      infer_instance
    have := HomologicalComplex.Hom.isIso_of_components
      ((tilde.adjunction.mapHomologicalComplex (.up ℤ)).unit.app K.as)
    infer_instance
  -- global sections of `M~` compute derived global sections
  have h₂ : IsIso ((moduleSpecΓFunctor (R := A)).rightDerivedFunctorUnith.app
      ((tilde.functor A).mapHomotopyCategory (.up ℤ) |>.obj K)) := by
    rw [Functor.rightDerivedFunctorUnith_app]
    let X := ((tilde.functor A).mapHomotopyCategory (.up ℤ)).obj K
    have : IsIso (Qh.map (((moduleSpecΓFunctor (R := A)).mapHomotopyCategory _).map
        ((kInjectiveReplacementAdjunction _).unit.app X))) := by
      obtain ⟨f, hf⟩ := (HomotopyCategory.quotient _ _).map_surjective
        ((kInjectiveReplacementAdjunction _).unit.app X)
      have := quasiIso_of_quotient_map_eq_kInjectiveReplacementAdjunction_unit_app f hf
      rw [isIso_Qh_map_iff, ← hf, Functor.mapHomotopyCategory_map,
        HomotopyCategory.quotient_map_mem_quasiIso_iff, HomologicalComplex.mem_quasiIso_iff]
      exact quasiIso_map_moduleSpecΓFunctor_of_tilde K.as f
    infer_instance
  have : IsIso ((tildeDerivedAdjunction A).unit.app (Qh.obj K) ≫ (derivedModuleSpecΓFunctor A).map
      ((tilde.functor A).mapDerivedCategoryFactorsh.hom.app K)) := by
    rw [tildeDerivedAdjunction_unit_app]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((derivedModuleSpecΓFunctor A).map
    ((tilde.functor A).mapDerivedCategoryFactorsh.hom.app K))

/-- **Derived global sections are conservative on `D_QCoh(𝒪_{Spec A})`**: an object of
`D_QCoh(𝒪_{Spec A})` whose derived global sections vanish is zero. -/
private lemma isZero_of_isZero_derivedModuleSpecΓFunctor_obj {K : DerivedCategory (Spec A).Modules}
    (hK : DQCoh (Spec A) K) (h : IsZero ((derivedModuleSpecΓFunctor A).obj K)) : IsZero K := by
  -- `K` is represented by its K-injective replacement `J`
  let J := ((kInjectiveReplacement _).obj K).as
  let eK : Q.obj J ≅ K := ((quotientCompQhIso _).app J).symm ≪≫
    (asIso (kInjectiveReplacementAdjunction _).counit).app K
  have hJ (i : ℤ) : (J.homology i).IsQuasicoherent :=
    (Scheme.Modules.isQuasicoherent _).prop_of_iso
      ((homologyFunctor _ i).mapIso eK.symm ≪≫ (homologyFunctorFactors _ i).app J)
      (DQCoh.mem_iff.1 hK i)
  -- the global sections of `J` are acyclic, hence so is `J`
  have hΓ : IsZero (Q.obj (((moduleSpecΓFunctor (R := A)).mapHomologicalComplex _).obj J)) :=
    h.of_iso ((Functor.rightDerivedFunctorObjIso _ J).symm ≪≫
      (derivedModuleSpecΓFunctor A).mapIso eK)
  have hJ' (m : ℤ) : J.ExactAt m := by
    refine TauCeti.AlgebraicGeometry.Scheme.Modules.exactAt_of_exactAt_map_sectionsFunctor hJ m ?_
    rw [← exactAt_map_moduleSpecΓFunctor_iff, HomologicalComplex.exactAt_iff_isZero_homology]
    exact ((homologyFunctor _ m).map_isZero hΓ).of_iso ((homologyFunctorFactors _ m).app _).symm
  -- an acyclic complex is zero in the derived category
  have : QuasiIso (0 : J ⟶ 0) := (quasiIso_iff _).2 fun m ↦
    (quasiIsoAt_iff_exactAt' _ m
      (ExactAt.of_isZero ((HomologicalComplex.eval _ _ m).map_isZero (isZero_zero _)))).2 (hJ' m)
  exact (Q.map_isZero (isZero_zero _)).of_iso (asIso (Q.map (0 : J ⟶ 0))) |>.of_iso eK.symm

/-- **The counit of the derived adjunction is an isomorphism on `D_QCoh`**: for `K` in
`D_QCoh(𝒪_{Spec A})`, the map `RΓ(Spec A, K)~ ⟶ K` is an isomorphism. -/
theorem isIso_tildeDerivedAdjunction_counit_app {K : DerivedCategory (Spec A).Modules}
    (hK : DQCoh (Spec A) K) : IsIso ((tildeDerivedAdjunction A).counit.app K) := by
  -- derived global sections invert the counit, by the triangle identity
  have : IsIso ((derivedModuleSpecΓFunctor A).map ((tildeDerivedAdjunction A).counit.app K)) :=
    isIso_of_hom_comp_eq_id _ ((tildeDerivedAdjunction A).right_triangle_components K)
  -- the cone of the counit lies in `D_QCoh` and has vanishing derived global sections
  obtain ⟨Z, g, h, hT⟩ :=
    Pretriangulated.distinguished_cocone_triangle ((tildeDerivedAdjunction A).counit.app K)
  have hZ : DQCoh (Spec A) Z := (DQCoh (Spec A)).ext_of_isTriangulatedClosed₃ _ hT
    (DQCoh.mapDerivedCategory_tildeFunctor_obj A _) hK
  have hRZ : IsZero ((derivedModuleSpecΓFunctor A).obj Z) :=
    (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _
      ((derivedModuleSpecΓFunctor A).map_distinguished _ hT)).2 this
  exact (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _ hT).1
    (isZero_of_isZero_derivedModuleSpecΓFunctor_obj hZ hRZ)

/-- The unit `𝟭 ⟶ RΓ(Spec A, (-)~)` of the derived adjunction is an isomorphism. -/
instance isIso_tildeDerivedAdjunction_unit : IsIso (tildeDerivedAdjunction A).unit :=
  NatIso.isIso_of_isIso_app _

variable (A) in
/-- **`D(A)` embeds into `D(𝒪_{Spec A})`**: the functor `D(A) ⥤ D(𝒪_{Spec A})` induced by
`M ↦ M~` is fully faithful. -/
noncomputable def fullyFaithfulMapDerivedCategoryTildeFunctor :
    (tilde.functor A).mapDerivedCategory.FullyFaithful :=
  (tildeDerivedAdjunction A).fullyFaithfulLOfIsIsoUnit

instance : (tilde.functor A).mapDerivedCategory.Full :=
  (fullyFaithfulMapDerivedCategoryTildeFunctor A).full

instance : (tilde.functor A).mapDerivedCategory.Faithful :=
  (fullyFaithfulMapDerivedCategoryTildeFunctor A).faithful

/-- The essential image of `D(A) ⥤ D(𝒪_{Spec A})`, induced by `M ↦ M~`, is `D_QCoh(𝒪_{Spec A})`. -/
theorem DQCoh.mem_essImage_mapDerivedCategory_tildeFunctor_iff
    (K : DerivedCategory (Spec A).Modules) :
    (tilde.functor A).mapDerivedCategory.essImage K ↔ DQCoh (Spec A) K :=
  ⟨fun ⟨_, ⟨e⟩⟩ ↦ (DQCoh (Spec A)).prop_of_iso e (DQCoh.mapDerivedCategory_tildeFunctor_obj A _),
    fun hK ↦ ⟨_, ⟨@asIso _ _ _ _ _ (isIso_tildeDerivedAdjunction_counit_app hK)⟩⟩⟩

variable (A) in
/-- The derived adjunction `M ↦ M~ ⊣ RΓ(Spec A, -)`, restricted to `D_QCoh(𝒪_{Spec A})`, into which
`M ↦ M~` sends `D(A)`. -/
private noncomputable def tildeDerivedAdjunctionDQCoh :
    (DQCoh (Spec A)).lift (tilde.functor A).mapDerivedCategory
        (DQCoh.mapDerivedCategory_tildeFunctor_obj A) ⊣
      (DQCoh (Spec A)).ι ⋙ derivedModuleSpecΓFunctor A :=
  (tildeDerivedAdjunction A).restrictFullyFaithful (Functor.FullyFaithful.id _)
    (DQCoh (Spec A)).fullyFaithfulι
    (Functor.leftUnitor _ ≪≫ ((DQCoh (Spec A)).liftCompιIso _ _).symm) (Functor.rightUnitor _).symm

/-- The unit of the restricted derived adjunction is that of the derived adjunction, hence an
isomorphism. -/
private instance (M : DerivedCategory (ModuleCat.{u} A)) :
    IsIso ((tildeDerivedAdjunctionDQCoh A).unit.app M) := by
  have : IsIso ((𝟭 _).map ((tildeDerivedAdjunctionDQCoh A).unit.app M)) := by
    unfold tildeDerivedAdjunctionDQCoh
    rw [Adjunction.map_restrictFullyFaithful_unit_app]
    infer_instance
  exact this

/-- The counit of the restricted derived adjunction is that of the derived adjunction on
`D_QCoh(𝒪_{Spec A})`, hence an isomorphism. -/
private instance (K : (DQCoh (Spec A)).FullSubcategory) :
    IsIso ((tildeDerivedAdjunctionDQCoh A).counit.app K) := by
  have : IsIso ((tildeDerivedAdjunction A).counit.app ((DQCoh (Spec A)).ι.obj K)) :=
    isIso_tildeDerivedAdjunction_counit_app K.property
  have : IsIso ((DQCoh (Spec A)).ι.map ((tildeDerivedAdjunctionDQCoh A).counit.app K)) := by
    unfold tildeDerivedAdjunctionDQCoh
    rw [Adjunction.map_restrictFullyFaithful_counit_app]
    infer_instance
  exact (DQCoh (Spec A)).fullyFaithfulι.isIso_of_isIso_map _

variable (A) in
/-- **The derived category of an affine scheme**
([Stacks, Lemma 36.3.5](https://stacks.math.columbia.edu/tag/06Z0)). For a commutative ring `A`,
the functor induced by `M ↦ M~` is an equivalence `D(A) ≌ D_QCoh(𝒪_{Spec A})` between the
unbounded derived category of `A`-modules and the complexes of `𝒪_{Spec A}`-modules with
quasi-coherent cohomology. Its quasi-inverse is derived global sections `RΓ(Spec A, -)`; it is the
derived adjunction `tildeDerivedAdjunction A`, restricted to `D_QCoh(𝒪_{Spec A})`. -/
noncomputable def DQCoh.affineEquiv :
    DerivedCategory (ModuleCat.{u} A) ≌ (DQCoh (Spec A)).FullSubcategory :=
  (tildeDerivedAdjunctionDQCoh A).toEquivalence

/-- The functor of `DQCoh.affineEquiv` is `M ↦ M~` on derived categories. -/
@[simp]
lemma DQCoh.affineEquiv_functor_obj_obj (M : DerivedCategory (ModuleCat.{u} A)) :
    ((DQCoh.affineEquiv A).functor.obj M).obj = (tilde.functor A).mapDerivedCategory.obj M :=
  (rfl)

/-- The quasi-inverse of `DQCoh.affineEquiv` is derived global sections. -/
@[simp]
lemma DQCoh.affineEquiv_inverse_obj (K : (DQCoh (Spec A)).FullSubcategory) :
    (DQCoh.affineEquiv A).inverse.obj K = (derivedModuleSpecΓFunctor A).obj K.obj :=
  (rfl)

/-- The inverse of the affine equivalence is naturally derived global sections, restricted to
complexes with quasi-coherent cohomology. -/
noncomputable def DQCoh.affineEquivInverseIso :
    (DQCoh.affineEquiv A).inverse ≅ (DQCoh (Spec A)).ι ⋙ derivedModuleSpecΓFunctor A :=
  Iso.refl _

variable (A) in
/-- On complexes, the equivalence `DQCoh.affineEquiv A` followed by the inclusion of
`D_QCoh(𝒪_{Spec A})` into `D(𝒪_{Spec A})` is `M ↦ M~` applied termwise: the comparison
`Functor.mapDerivedCategoryFactors` of the derived functor of `M ↦ M~`. -/
noncomputable def DQCoh.affineEquivFunctorFactors :
    DerivedCategory.Q ⋙ (DQCoh.affineEquiv A).functor ⋙ (DQCoh (Spec A)).ι ≅
      (tilde.functor A).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.isoWhiskerLeft DerivedCategory.Q ((DQCoh (Spec A)).liftCompιIso _ _) ≪≫
    (tilde.functor A).mapDerivedCategoryFactors

end AffineEquiv

end TauCeti.AlgebraicGeometry.Coherent
