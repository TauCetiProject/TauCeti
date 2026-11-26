/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DerivedCategory.Coproduct
public import TauCeti.Algebra.Homology.DerivedCategory.HomologyIn
public import TauCeti.Algebra.Homology.ModelCategory.KInjective.Resolution
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.WeakSerre
public import TauCeti.Algebra.Homology.DerivedCategory.RightDerivedFunctor.Adjunction
public import TauCeti.AlgebraicGeometry.Modules.Derived.AffineSections

/-!
# The derived category of complexes with quasi-coherent cohomology

Let `X` be a scheme. This file defines `TauCeti.AlgebraicGeometry.Coherent.DQCoh X`, the full
subcategory `D_QCoh(𝒪_X)` of the derived category `D(𝒪_X)` of all `𝒪_X`-modules consisting of the
complexes all of whose cohomology sheaves are quasi-coherent. It is the property
`DerivedCategory.homologyIn` for quasi-coherence, and works for any model of the derived category
(`HasDerivedCategory`).

* `DQCoh.mem_iff`: membership is quasi-coherence of all cohomology sheaves.
* `DQCoh.isTriangulated`: `D_QCoh(𝒪_X)` is a triangulated subcategory, closed under shifts and
  cones. Quasi-coherent sheaves are closed under kernels, cokernels and extensions in all
  `𝒪_X`-modules.
* `DQCoh.isClosedUnderCoproducts` and `DQCoh.hasCoproducts`: `D(𝒪_X)` has coproducts indexed by
  `u`-small types, computed by degreewise direct sums of complexes, and `D_QCoh(𝒪_X)` is closed
  under them. Hence `D_QCoh(𝒪_X)` has these coproducts, computed in `D(𝒪_X)`.
* `DQCoh.singleFunctor_obj_mem_iff`: a module sheaf placed in one degree lies in `D_QCoh(𝒪_X)` if
  and only if it is quasi-coherent; for instance `𝒪_X[0] ∈ D_QCoh(𝒪_X)`.
* `DQCoh.restrict`: derived restriction along an open immersion preserves `D_QCoh`, and
  `DQCoh.mem_iff_of_iSup_eq_top`: membership in `D_QCoh(𝒪_X)` is local on `X`.
* `DQCoh.mapDerivedCategory_tildeFunctor_obj`: for a commutative ring `A`, the derived functor of
  `M ↦ M~` sends `D(A)` into `D_QCoh(𝒪_{Spec A})`.
* `DQCoh.affineEquiv`: **the derived category of an affine scheme**. For a commutative ring `A`,
  `M ↦ M~` induces an equivalence `D(A) ≌ D_QCoh(𝒪_{Spec A})`
  ([Stacks, Lemma 36.3.5](https://stacks.math.columbia.edu/tag/06Z0)), whose quasi-inverse is
  derived global sections `derivedModuleSpecΓFunctor A`, the right derived functor of global
  sections on unbounded complexes. The equivalence comes from the derived adjunction
  `tildeDerivedAdjunction A`, whose unit is an isomorphism
  (`isIso_tildeDerivedAdjunction_unit`), so that `D(A) ⥤ D(𝒪_{Spec A})` is fully faithful
  (`fullyFaithfulMapDerivedCategoryTildeFunctor`), and whose counit is an isomorphism on
  `D_QCoh(𝒪_{Spec A})` (`isIso_tildeDerivedAdjunction_counit_app`); the essential image is
  `D_QCoh(𝒪_{Spec A})` (`DQCoh.mem_essImage_mapDerivedCategory_tildeFunctor_iff`). The input is the
  computation of global sections of K-injective complexes with quasi-coherent cohomology in
  `TauCeti.AlgebraicGeometry.Modules.Derived.AffineSections`, which rests on the vanishing of the
  cohomology of quasi-coherent sheaves on affine schemes.

The category of `𝒪_X`-modules is a Grothendieck abelian category, so it has K-injective
resolutions and exact coproducts; these give the coproducts in `D(𝒪_X)` and their homology.

## References

* [Stacks: Section 36.3](https://stacks.math.columbia.edu/tag/06YZ), the definition of `D_QCoh`.
* [Stacks: Lemma 36.3.1](https://stacks.math.columbia.edu/tag/08DT), direct sums in `D_QCoh`.
* [Stacks: Lemma 36.3.5](https://stacks.math.columbia.edu/tag/06Z0), the derived category of an
  affine scheme.
-/

public section

open CategoryTheory Limits DerivedCategory

namespace TauCeti.AlgebraicGeometry.Coherent

open _root_.AlgebraicGeometry

universe w w' u

section

variable (X : Scheme.{u}) [HasDerivedCategory.{w} X.Modules]

/-- `D_QCoh(𝒪_X)`: the objects of the derived category of `𝒪_X`-modules all of whose cohomology
sheaves are quasi-coherent. -/
def DQCoh : ObjectProperty (DerivedCategory X.Modules) :=
  homologyIn (Scheme.Modules.isQuasicoherent X)

variable {X} in
/-- An object of `D(𝒪_X)` lies in `D_QCoh(𝒪_X)` if and only if all its cohomology sheaves are
quasi-coherent. -/
theorem DQCoh.mem_iff {K : DerivedCategory X.Modules} :
    DQCoh X K ↔ ∀ n : ℤ, ((homologyFunctor X.Modules n).obj K).IsQuasicoherent :=
  homologyIn_iff K

/-- Membership in `D_QCoh(𝒪_X)` is invariant under isomorphism in `D(𝒪_X)`. -/
instance : (DQCoh X).IsClosedUnderIsomorphisms :=
  inferInstanceAs (homologyIn (Scheme.Modules.isQuasicoherent X)).IsClosedUnderIsomorphisms

/-- `D_QCoh(𝒪_X)` is a triangulated subcategory of `D(𝒪_X)`: it contains zero and is closed under
shifts and extensions, hence under cones. -/
instance DQCoh.isTriangulated : (DQCoh X).IsTriangulated :=
  inferInstanceAs (homologyIn (Scheme.Modules.isQuasicoherent X)).IsTriangulated

/-- `D_QCoh(𝒪_X)` is closed under the coproducts of `D(𝒪_X)` indexed by `u`-small types. -/
instance DQCoh.isClosedUnderCoproducts (J : Type u) :
    (DQCoh X).IsClosedUnderColimitsOfShape (Discrete J) :=
  inferInstanceAs
    ((homologyIn (Scheme.Modules.isQuasicoherent X)).IsClosedUnderColimitsOfShape (Discrete J))

/-- `D_QCoh(𝒪_X)` has coproducts indexed by `u`-small types, computed in `D(𝒪_X)`. -/
instance DQCoh.hasCoproducts : HasCoproducts.{u} (DQCoh X).FullSubcategory :=
  ⟨fun _ ↦ hasColimitsOfShape_of_closedUnderColimits _ _⟩

variable {X} in
/-- A sheaf of modules placed in one degree lies in `D_QCoh(𝒪_X)` if and only if it is
quasi-coherent. -/
@[simp]
theorem DQCoh.singleFunctor_obj_mem_iff (F : X.Modules) (n : ℤ) :
    DQCoh X ((singleFunctor X.Modules n).obj F) ↔ F.IsQuasicoherent :=
  homologyIn_singleFunctor_obj_iff (P := Scheme.Modules.isQuasicoherent X) F n

end

section Restriction

variable {X U : Scheme.{u}} [HasDerivedCategory.{w} X.Modules] [HasDerivedCategory.{w'} U.Modules]

/-- Derived restriction along an open immersion `f : U ⟶ X`, the functor `D(𝒪_X) ⥤ D(𝒪_U)` induced
by the exact restriction functor, sends `D_QCoh(𝒪_X)` into `D_QCoh(𝒪_U)`. -/
theorem DQCoh.restrict (f : U ⟶ X) [IsOpenImmersion f] {K : DerivedCategory X.Modules}
    (hK : DQCoh X K) : DQCoh U ((Scheme.Modules.restrictFunctor f).mapDerivedCategory.obj K) :=
  homologyIn_mapDerivedCategory_obj (P := Scheme.Modules.isQuasicoherent X)
    (P' := Scheme.Modules.isQuasicoherent U) _
    (fun F (_ : F.IsQuasicoherent) ↦
      inferInstanceAs ((Scheme.Modules.restrictFunctor f).obj F).IsQuasicoherent) hK

end Restriction

/-- Membership in `D_QCoh(𝒪_X)` is local on `X`: for opens `U i` covering `X`, an object of
`D(𝒪_X)` lies in `D_QCoh(𝒪_X)` if and only if each of its restrictions to the `U i` lies in
`D_QCoh(𝒪_{U i})`. -/
theorem DQCoh.mem_iff_of_iSup_eq_top {X : Scheme.{u}} [HasDerivedCategory.{w} X.Modules]
    {ι : Type*} (U : ι → X.Opens) (hU : iSup U = ⊤)
    [∀ i, HasDerivedCategory.{w'} (U i).toScheme.Modules] (K : DerivedCategory X.Modules) :
    DQCoh X K ↔ ∀ i,
      DQCoh (U i) ((Scheme.Modules.restrictFunctor (U i).ι).mapDerivedCategory.obj K) := by
  refine ⟨fun hK i ↦ DQCoh.restrict _ hK, fun hK ↦ DQCoh.mem_iff.2 fun n ↦ ?_⟩
  refine (((homologyFunctor X.Modules n).obj K).isQuasicoherent_iff_of_iSup_eq_top U hU).2
    fun i ↦ ?_
  exact (Scheme.Modules.isQuasicoherent _).prop_of_iso
    (((Scheme.Modules.restrictFunctor (U i).ι).mapDerivedCategoryCompHomologyFunctorIso n).app K)
    (DQCoh.mem_iff.1 (hK i) n)

/-- For a commutative ring `A`, the functor `D(A) ⥤ D(𝒪_{Spec A})` induced by the exact functor
`M ↦ M~` takes values in `D_QCoh(𝒪_{Spec A})`: the cohomology sheaves of `M~` are the sheaves
associated with the cohomology modules of `M`. -/
theorem DQCoh.mapDerivedCategory_tildeFunctor_obj (A : CommRingCat.{u})
    [HasDerivedCategory.{w} (Spec A).Modules] [HasDerivedCategory.{w'} (ModuleCat.{u} A)]
    (M : DerivedCategory (ModuleCat.{u} A)) :
    DQCoh (Spec A) ((tilde.functor A).mapDerivedCategory.obj M) :=
  homologyIn_mapDerivedCategory_obj (P := ⊤) (P' := Scheme.Modules.isQuasicoherent (Spec A)) _
    (fun N _ ↦ inferInstanceAs ((tilde.functor A).obj N).IsQuasicoherent)
    ((homologyIn_iff M).2 fun _ ↦ trivial)

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
      (h _) (h _) (h _)

variable (A) [HasDerivedCategory.{w} (Spec A).Modules] [HasDerivedCategory.{w'} (ModuleCat.{u} A)]

/-- Derived global sections `RΓ(Spec A, -) : D(𝒪_{Spec A}) ⥤ D(A)` on unbounded complexes: the right
derived functor of the global-section functor, computed on K-injective replacements. -/
noncomputable abbrev derivedModuleSpecΓFunctor :
    DerivedCategory (Spec A).Modules ⥤ DerivedCategory (ModuleCat.{u} A) :=
  (moduleSpecΓFunctor (R := A)).rightDerivedFunctor

/-- The derived adjunction `M ↦ M~ ⊣ RΓ(Spec A, -)` between `D(A)` and `D(𝒪_{Spec A})`, derived from
the adjunction between `M ↦ M~` and global sections. -/
noncomputable def tildeDerivedAdjunction :
    (tilde.functor A).mapDerivedCategory ⊣ derivedModuleSpecΓFunctor A :=
  tilde.adjunction.mapDerivedCategoryRightDerivedFunctor

variable {A}


/-- **The unit of the derived adjunction is an isomorphism**: for every complex `M` of `A`-modules,
`M ⟶ RΓ(Spec A, M~)` is an isomorphism in `D(A)`. -/
instance isIso_tildeDerivedAdjunction_unit_app (M : DerivedCategory (ModuleCat.{u} A)) :
    IsIso ((tildeDerivedAdjunction A).unit.app M) := by
  suffices h : ∀ K : HomotopyCategory (ModuleCat.{u} A) (.up ℤ),
      IsIso ((tildeDerivedAdjunction A).unit.app (Qh.obj K)) from
    (NatTrans.isIso_app_iff_of_iso _ (Qh.objObjPreimageIso M)).1 (h _)
  intro K
  have hfac := tilde.adjunction.mapDerivedCategoryRightDerivedFunctor_unit_app K
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
    rw [tildeDerivedAdjunction, hfac]
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
/-- **The derived category of an affine scheme**
([Stacks, Lemma 36.3.5](https://stacks.math.columbia.edu/tag/06Z0)). For a commutative ring `A`,
the functor induced by `M ↦ M~` is an equivalence `D(A) ≌ D_QCoh(𝒪_{Spec A})` between the
unbounded derived category of `A`-modules and the complexes of `𝒪_{Spec A}`-modules with
quasi-coherent cohomology. Its quasi-inverse is derived global sections `RΓ(Spec A, -)`, and its
unit and counit are those of the derived adjunction `tildeDerivedAdjunction A`. -/
noncomputable def DQCoh.affineEquiv :
    DerivedCategory (ModuleCat.{u} A) ≌ (DQCoh (Spec A)).FullSubcategory where
  functor := (DQCoh (Spec A)).lift (tilde.functor A).mapDerivedCategory
    (DQCoh.mapDerivedCategory_tildeFunctor_obj A)
  inverse := (DQCoh (Spec A)).ι ⋙ derivedModuleSpecΓFunctor A
  unitIso := asIso (tildeDerivedAdjunction A).unit
  counitIso := NatIso.ofComponents (fun K ↦ (DQCoh (Spec A)).fullyFaithfulι.preimageIso
      (@asIso _ _ _ _ _ (isIso_tildeDerivedAdjunction_counit_app K.property)))
    fun f ↦ (DQCoh (Spec A)).fullyFaithfulι.map_injective <| by
      simp
  functor_unitIso_comp M := (DQCoh (Spec A)).fullyFaithfulι.map_injective <| by
    simp

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

end AffineEquiv

end TauCeti.AlgebraicGeometry.Coherent
