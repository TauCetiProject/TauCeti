/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import TauCeti.Algebra.Homology.CochainComplex.Plus.InjectiveResolution
public import TauCeti.Algebra.Homology.DerivedCategory.Plus.Basic

/-!
# Bounded-below right derived functors from adapted resolutions

Let `F : C ⥤ D` be an additive functor between abelian categories, where `C` has enough
injectives, and let `F.rightDerivedFunctorPlus : DerivedCategory.Plus C ⥤ DerivedCategory.Plus D`
be Mathlib's bounded-below right derived functor. This file develops the resolution-computation
and left t-exactness API for `F.rightDerivedFunctorPlus` (complementing the adapted-complex
derived-unit invertibility theorem `CategoryTheory.Functor.isIso_rightDerivedFunctorPlusUnit_app` in
`TauCeti/Algebra/Homology/DerivedCategory/RightDerivedFunctor/Plus.lean`):

* **Derived-unit invertibility on injective complexes:** `F.rightDerivedFunctorPlusUnit.app K` is an
  isomorphism for every bounded-below complex `K` of injective objects
  (`CategoryTheory.Functor.isIso_rightDerivedFunctorPlusUnit_app_of_injective`).
* **Computation from resolutions:** for any quasi-isomorphism `ι : K ⟶ L` in
  `CochainComplex.Plus C` with `[IsIso (F.rightDerivedFunctorPlusUnit.app L)]`,
  `F.rightDerivedFunctorPlus.obj (Q.obj K) ≅ Q.obj (F(L))`
  (`CategoryTheory.Functor.rightDerivedFunctorPlusObjIsoOfResolution`), with naturality,
  cohomology computation
  (`CategoryTheory.Functor.rightDerivedFunctorPlusHomologyObjIsoOfResolution`), and a functorial
  version (`CategoryTheory.Functor.rightDerivedFunctorPlusIsoOfResolution`).
* **Left t-exactness and truncation:** `F.rightDerivedFunctorPlus` preserves
  `DerivedCategory.Plus.IsGE b` for every `b : ℤ`
  (`CategoryTheory.Functor.isGE_rightDerivedFunctorPlus_obj`), and applying
  `F.rightDerivedFunctorPlus` to `τ≤n X ⟶ X` induces an isomorphism on `Hᵐ` for `m ≤ n`
  (`CategoryTheory.Functor.isIso_homology_rightDerivedFunctorPlus_map_truncLEι_app`).

Exact-functor comparison and degree-zero recovery of classical right derived functors `RⁿF` are
proved in `TauCeti/Algebra/Homology/DerivedCategory/Plus/Comparison.lean`.

## References

* `TauCeti/CategoryTheory/Abelian/AcyclicResolution.lean`, the formal source whose
  resolution-isomorphism API is adapted here to `CochainComplex.Plus` and `DerivedCategory.Plus`.
* `TauCeti/Algebra/Homology/DerivedCategory/RightDerivedFunctor/Plus.lean`, which proves
  `CategoryTheory.Functor.isIso_rightDerivedFunctorPlusUnit_app` for adapted complexes.
* The Stacks Project, Derived Categories, §13.15–§13.16 (tags 05T8, 015E).
* M. Kashiwara, P. Schapira, *Categories and Sheaves*, Grundlehren 332, Springer, 2006, §13.3.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor HomologicalComplex

universe w₁ w₂ v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

section UnitNaturality

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
  [EnoughInjectives C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
  (F : C ⥤ D) [F.Additive]

/-- Component naturality equation for `F.rightDerivedFunctorPlusUnit`. -/
@[reassoc]
lemma rightDerivedFunctorPlusUnit_naturality
    {K L : CochainComplex.Plus C} (f : K ⟶ L) :
    DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map f) ≫
        F.rightDerivedFunctorPlusUnit.app L =
      F.rightDerivedFunctorPlusUnit.app K ≫
        F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f) := by
  simpa only [Functor.comp_obj, Functor.comp_map] using
    F.rightDerivedFunctorPlusUnit.naturality f

end UnitNaturality

/-! ### Computation from acyclic resolutions and left t-exactness -/

section Resolution

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
  [EnoughInjectives C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
  (F : C ⥤ D) [F.Additive]

/-- The derived unit `F.rightDerivedFunctorPlusUnit` is an isomorphism on any bounded-below
cochain complex of injective objects. -/
instance isIso_rightDerivedFunctorPlusUnit_app_of_injective
    (K : CochainComplex.Plus C) [∀ n, Injective (K.obj.X n)] :
    IsIso (F.rightDerivedFunctorPlusUnit.app K) := by
  let e := CochainComplex.Plus.liftInjectiveIso K inferInstance
  have : IsIso (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map e.hom) ≫
      F.rightDerivedFunctorPlusUnit.app K) := by
    rw [F.rightDerivedFunctorPlusUnit_naturality e.hom]
    infer_instance
  exact IsIso.of_isIso_comp_left (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map e.hom)) _

/-- **Bounded-below right derived functors from acyclic resolutions.** Given a quasi-isomorphism
`ι : K ⟶ L` in `CochainComplex.Plus C` such that `F.rightDerivedFunctorPlusUnit.app L` is an
isomorphism (for instance when `L` is termwise injective or lies in an `F`-adapted class),
`RF⁺(Q(K)) ≅ Q(F(L))`. -/
def rightDerivedFunctorPlusObjIsoOfResolution
    {K L : CochainComplex.Plus C} (ι : K ⟶ L) [QuasiIso ι.hom]
    [IsIso (F.rightDerivedFunctorPlusUnit.app L)] :
    F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K) ≅
      DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj L) :=
  F.rightDerivedFunctorPlus.mapIso (asIso (DerivedCategory.Plus.Q.map ι)) ≪≫
    (asIso (F.rightDerivedFunctorPlusUnit.app L)).symm

/-- For any morphism `φ : L ⟶ M` in `CochainComplex.Plus C`, composing
`(F.rightDerivedFunctorPlusObjIsoOfResolution ι).hom` with `Q.map (F(φ))` and
`F.rightDerivedFunctorPlusUnit.app M` equals `RF⁺(Q(ι ≫ φ))`. -/
@[reassoc]
lemma rightDerivedFunctorPlusObjIsoOfResolution_hom_comp
    {K L M : CochainComplex.Plus C} (ι : K ⟶ L) [QuasiIso ι.hom]
    [IsIso (F.rightDerivedFunctorPlusUnit.app L)] (φ : L ⟶ M) :
    (F.rightDerivedFunctorPlusObjIsoOfResolution ι).hom ≫
        DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map φ) ≫
        F.rightDerivedFunctorPlusUnit.app M =
      F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map (ι ≫ φ)) := by
  dsimp [rightDerivedFunctorPlusObjIsoOfResolution]
  rw [Category.assoc, F.rightDerivedFunctorPlusUnit_naturality φ, IsIso.inv_hom_id_assoc,
    ← Functor.map_comp, ← Functor.map_comp]

/-- Composing `(F.rightDerivedFunctorPlusObjIsoOfResolution ι).hom` with
`F.rightDerivedFunctorPlusUnit.app L` recovers `RF⁺(Q(ι))`. -/
@[reassoc (attr := simp)]
lemma rightDerivedFunctorPlusObjIsoOfResolution_hom_comp_unit
    {K L : CochainComplex.Plus C} (ι : K ⟶ L) [QuasiIso ι.hom]
    [IsIso (F.rightDerivedFunctorPlusUnit.app L)] :
    (F.rightDerivedFunctorPlusObjIsoOfResolution ι).hom ≫
        F.rightDerivedFunctorPlusUnit.app L =
      F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map ι) := by
  dsimp [rightDerivedFunctorPlusObjIsoOfResolution]
  simp

/-- Naturality of `rightDerivedFunctorPlusObjIsoOfResolution` in morphisms of resolved complexes
whose comparison square commutes in `DerivedCategory.Plus C`. -/
@[reassoc]
lemma rightDerivedFunctorPlusObjIsoOfResolution_hom_naturality
    {K K' L L' : CochainComplex.Plus C}
    (ι : K ⟶ L) [QuasiIso ι.hom] [IsIso (F.rightDerivedFunctorPlusUnit.app L)]
    (κ : K' ⟶ L') [QuasiIso κ.hom] [IsIso (F.rightDerivedFunctorPlusUnit.app L')]
    (f : K ⟶ K') (φ : L ⟶ L')
    (hφ : DerivedCategory.Plus.Q.map (ι ≫ φ) = DerivedCategory.Plus.Q.map (f ≫ κ)) :
    F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f) ≫
        (F.rightDerivedFunctorPlusObjIsoOfResolution κ).hom =
      (F.rightDerivedFunctorPlusObjIsoOfResolution ι).hom ≫
        DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map φ) := by
  rw [← cancel_mono (F.rightDerivedFunctorPlusUnit.app L'), Category.assoc, Category.assoc,
    F.rightDerivedFunctorPlusObjIsoOfResolution_hom_comp ι φ, hφ,
    Functor.map_comp, Functor.map_comp,
    F.rightDerivedFunctorPlusObjIsoOfResolution_hom_comp_unit]

/-- Cohomology of `RF⁺(Q(K))` computed by a resolution `ι : K ⟶ L` on which the derived unit is
an isomorphism. -/
def rightDerivedFunctorPlusHomologyObjIsoOfResolution
    {K L : CochainComplex.Plus C} (ι : K ⟶ L) [QuasiIso ι.hom]
    [IsIso (F.rightDerivedFunctorPlusUnit.app L)] (m : ℤ) :
    (DerivedCategory.Plus.homologyFunctor D m).obj
        (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)) ≅
      ((F.mapHomologicalComplex _).obj L.obj).homology m :=
  (DerivedCategory.Plus.homologyFunctor D m).mapIso
      (F.rightDerivedFunctorPlusObjIsoOfResolution ι) ≪≫
    (TauCeti.DerivedCategory.Plus.homologyFunctorFactors D m).app
      (F.mapCochainComplexPlus.obj L)

/-- Characterizing formula for `(F.rightDerivedFunctorPlusHomologyObjIsoOfResolution ι m).hom`. -/
@[reassoc]
lemma rightDerivedFunctorPlusHomologyObjIsoOfResolution_hom
    {K L : CochainComplex.Plus C} (ι : K ⟶ L) [QuasiIso ι.hom]
    [IsIso (F.rightDerivedFunctorPlusUnit.app L)] (m : ℤ) :
    (F.rightDerivedFunctorPlusHomologyObjIsoOfResolution ι m).hom =
      (DerivedCategory.Plus.homologyFunctor D m).map
          (F.rightDerivedFunctorPlusObjIsoOfResolution ι).hom ≫
        (TauCeti.DerivedCategory.Plus.homologyFunctorFactors D m).hom.app
          (F.mapCochainComplexPlus.obj L) :=
  (rfl)

/-- Naturality of `rightDerivedFunctorPlusHomologyObjIsoOfResolution` in morphisms of resolved
complexes whose comparison square commutes in `DerivedCategory.Plus C`. -/
@[reassoc]
lemma rightDerivedFunctorPlusHomologyObjIsoOfResolution_hom_naturality
    {K K' L L' : CochainComplex.Plus C}
    (ι : K ⟶ L) [QuasiIso ι.hom] [IsIso (F.rightDerivedFunctorPlusUnit.app L)]
    (κ : K' ⟶ L') [QuasiIso κ.hom] [IsIso (F.rightDerivedFunctorPlusUnit.app L')]
    (f : K ⟶ K') (φ : L ⟶ L')
    (hφ : DerivedCategory.Plus.Q.map (ι ≫ φ) = DerivedCategory.Plus.Q.map (f ≫ κ)) (m : ℤ) :
    (DerivedCategory.Plus.homologyFunctor D m).map
          (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f)) ≫
        (F.rightDerivedFunctorPlusHomologyObjIsoOfResolution κ m).hom =
      (F.rightDerivedFunctorPlusHomologyObjIsoOfResolution ι m).hom ≫
        HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map φ.hom) m := by
  calc (DerivedCategory.Plus.homologyFunctor D m).map
        (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f)) ≫
      (F.rightDerivedFunctorPlusHomologyObjIsoOfResolution κ m).hom
    _ = ((DerivedCategory.Plus.homologyFunctor D m).map
          (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f)) ≫
        (DerivedCategory.Plus.homologyFunctor D m).map
          (F.rightDerivedFunctorPlusObjIsoOfResolution κ).hom) ≫
        (TauCeti.DerivedCategory.Plus.homologyFunctorFactors D m).hom.app
          (F.mapCochainComplexPlus.obj L') := by
      rw [rightDerivedFunctorPlusHomologyObjIsoOfResolution_hom, Category.assoc]
    _ = (DerivedCategory.Plus.homologyFunctor D m).map
          (F.rightDerivedFunctorPlusObjIsoOfResolution ι).hom ≫
        ((DerivedCategory.Plus.homologyFunctor D m).map
          (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map φ)) ≫
        (TauCeti.DerivedCategory.Plus.homologyFunctorFactors D m).hom.app
          (F.mapCochainComplexPlus.obj L')) := by
      rw [← Functor.map_comp,
        F.rightDerivedFunctorPlusObjIsoOfResolution_hom_naturality ι κ f φ hφ,
        Functor.map_comp, Category.assoc]
    _ = (F.rightDerivedFunctorPlusHomologyObjIsoOfResolution ι m).hom ≫
        HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map φ.hom) m := by
      rw [TauCeti.DerivedCategory.Plus.homologyFunctorFactors_hom_naturality
        (F.mapCochainComplexPlus.map φ) m,
        ← Category.assoc, ← rightDerivedFunctorPlusHomologyObjIsoOfResolution_hom,
        Functor.mapCochainComplexPlus_map_hom]

/-- A functorial resolution `ι : 𝟭 _ ⟶ R` on `CochainComplex.Plus C` on whose values the derived
unit is an isomorphism computes `Q ⋙ F.rightDerivedFunctorPlus` naturally. -/
def rightDerivedFunctorPlusIsoOfResolution
    (R : CochainComplex.Plus C ⥤ CochainComplex.Plus C)
    (ι : 𝟭 (CochainComplex.Plus C) ⟶ R) [∀ K, QuasiIso (ι.app K).hom]
    [∀ K, IsIso (F.rightDerivedFunctorPlusUnit.app (R.obj K))] :
    DerivedCategory.Plus.Q ⋙ F.rightDerivedFunctorPlus ≅
      R ⋙ F.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q :=
  NatIso.ofComponents
    (fun K ↦ F.rightDerivedFunctorPlusObjIsoOfResolution (ι.app K))
    (fun f ↦ F.rightDerivedFunctorPlusObjIsoOfResolution_hom_naturality
      (ι.app _) (ι.app _) f (R.map f) (congrArg DerivedCategory.Plus.Q.map (ι.naturality f).symm))

/-- Each component of `rightDerivedFunctorPlusIsoOfResolution` is the objectwise resolution
isomorphism. -/
@[simp]
lemma rightDerivedFunctorPlusIsoOfResolution_app
    (R : CochainComplex.Plus C ⥤ CochainComplex.Plus C)
    (ι : 𝟭 (CochainComplex.Plus C) ⟶ R) [∀ K, QuasiIso (ι.app K).hom]
    [∀ K, IsIso (F.rightDerivedFunctorPlusUnit.app (R.obj K))] (K : CochainComplex.Plus C) :
    (F.rightDerivedFunctorPlusIsoOfResolution R ι).app K =
      F.rightDerivedFunctorPlusObjIsoOfResolution (ι.app K) := by
  simp [rightDerivedFunctorPlusIsoOfResolution]

@[simp]
lemma rightDerivedFunctorPlusIsoOfResolution_hom_app
    (R : CochainComplex.Plus C ⥤ CochainComplex.Plus C)
    (ι : 𝟭 (CochainComplex.Plus C) ⟶ R) [∀ K, QuasiIso (ι.app K).hom]
    [∀ K, IsIso (F.rightDerivedFunctorPlusUnit.app (R.obj K))] (K : CochainComplex.Plus C) :
    (F.rightDerivedFunctorPlusIsoOfResolution R ι).hom.app K =
      (F.rightDerivedFunctorPlusObjIsoOfResolution (ι.app K)).hom :=
  (rfl)

@[simp]
lemma rightDerivedFunctorPlusIsoOfResolution_inv_app
    (R : CochainComplex.Plus C ⥤ CochainComplex.Plus C)
    (ι : 𝟭 (CochainComplex.Plus C) ⟶ R) [∀ K, QuasiIso (ι.app K).hom]
    [∀ K, IsIso (F.rightDerivedFunctorPlusUnit.app (R.obj K))] (K : CochainComplex.Plus C) :
    (F.rightDerivedFunctorPlusIsoOfResolution R ι).inv.app K =
      (F.rightDerivedFunctorPlusObjIsoOfResolution (ι.app K)).inv :=
  (rfl)

/-- `F.rightDerivedFunctorPlus` is left t-exact: if `X` is cohomologically concentrated in degrees
`≥ b`, then so is `F.rightDerivedFunctorPlus.obj X`. -/
instance isGE_rightDerivedFunctorPlus_obj (X : DerivedCategory.Plus C) (b : ℤ) [X.IsGE b] :
    (F.rightDerivedFunctorPlus.obj X).IsGE b := by
  obtain ⟨I, _, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso X b
  let K := (InjectiveObject.ι C).mapCochainComplexPlus.obj I
  have : K.obj.IsStrictlyGE b := by
    dsimp [K]
    infer_instance
  have : (F.mapCochainComplexPlus.obj K).obj.IsStrictlyGE b := by
    dsimp
    infer_instance
  have : DerivedCategory.TStructure.t.IsGE
      ((CochainComplex.Plus.ι D ⋙ DerivedCategory.Q).obj (F.mapCochainComplexPlus.obj K)) b := by
    dsimp
    infer_instance
  have hQ : ((F.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q).obj K).IsGE b := by
    rw [← DerivedCategory.Plus.isGE_ι_obj_iff]
    exact DerivedCategory.TStructure.t.isGE_of_iso
      ((DerivedCategory.Plus.QCompιIso D).app (F.mapCochainComplexPlus.obj K)).symm b
  exact DerivedCategory.Plus.TStructure.t.isGE_of_iso
    (asIso (F.rightDerivedFunctorPlusUnit.app K) ≪≫ F.rightDerivedFunctorPlus.mapIso e) b

/-- For every `m ≤ n`, applying `F.rightDerivedFunctorPlus` to the truncation map `τ≤n X ⟶ X`
induces an isomorphism on cohomology in degree `m`. -/
theorem isIso_homology_rightDerivedFunctorPlus_map_truncLEι_app
    (X : DerivedCategory.Plus C) (n m : ℤ) (hm : m ≤ n) :
    IsIso ((DerivedCategory.Plus.homologyFunctor D m).map
      (F.rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.TStructure.t.truncLEι n).app X))) := by
  let T := F.rightDerivedFunctorPlus.mapTriangle.obj
    ((DerivedCategory.Plus.TStructure.t.triangleLEGT n).obj X)
  have hT := F.rightDerivedFunctorPlus.map_distinguished _
    (DerivedCategory.Plus.TStructure.t.triangleLEGT_distinguished n X)
  have : ((DerivedCategory.Plus.TStructure.t.triangleLEGT n).obj X).obj₃.IsGE (n + 1) :=
    inferInstanceAs (((DerivedCategory.Plus.TStructure.t.truncGT n).obj X).IsGE (n + 1))
  have : T.obj₃.IsGE (n + 1) := F.isGE_rightDerivedFunctorPlus_obj _ (n + 1)
  have hZero_m : IsZero ((DerivedCategory.Plus.homologyFunctor D m).obj T.obj₃) :=
    DerivedCategory.Plus.isZero_homology_of_isGE _ (n + 1) m (by lia)
  have hZero_m1 : IsZero ((DerivedCategory.Plus.homologyFunctor D (m - 1)).obj T.obj₃) :=
    DerivedCategory.Plus.isZero_homology_of_isGE _ (n + 1) (m - 1) (by lia)
  have : Epi ((DerivedCategory.Plus.homologyFunctor D m).map
      (F.rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.TStructure.t.truncLEι n).app X))) :=
    ((DerivedCategory.Plus.homologyFunctor D 0).homologySequence_epi_shift_map_mor₁_iff
      T hT m).2 (hZero_m.eq_of_tgt _ _)
  have : Mono ((DerivedCategory.Plus.homologyFunctor D m).map
      (F.rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.TStructure.t.truncLEι n).app X))) :=
    ((DerivedCategory.Plus.homologyFunctor D 0).homologySequence_mono_shift_map_mor₁_iff
      T hT (m - 1) m (by lia)).2 (hZero_m1.eq_of_src _ _)
  exact isIso_of_mono_of_epi _

end Resolution

end CategoryTheory.Functor
