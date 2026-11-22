/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import TauCeti.Algebra.Homology.CochainComplex.Plus.Acyclic
public import TauCeti.Algebra.Homology.DerivedCategory.Plus.Basic

/-!
# Bounded-below right derived functors from adapted resolutions

Let `F : C ⥤ D` be an additive functor between abelian categories, where `C` has enough
injectives, and let `F.rightDerivedFunctorPlus : DerivedCategory.Plus C ⥤ DerivedCategory.Plus D`
be Mathlib's bounded-below right derived functor. This file develops the adapted-resolution,
resolution-computation, and left t-exactness API for `F.rightDerivedFunctorPlus`:

* **Derived-unit invertibility:** `F.rightDerivedFunctorPlusUnit.app K` is an isomorphism for
  every bounded-below complex `K` of injective objects
  (`CategoryTheory.Functor.isIso_rightDerivedFunctorPlusUnit_app_of_injective`) and every
  bounded-below `P`-complex
  (`CategoryTheory.Functor.isIso_rightDerivedFunctorPlusUnit_app_of_adapted`), using
  `CategoryTheory.Functor.quasiIso_map_of_adapted_to_injective`.
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
* The Stacks Project, Derived Categories, §13.15–§13.16 (tags 05T8, 015E).
* M. Kashiwara, P. Schapira, *Categories and Sheaves*, Grundlehren 332, Springer, 2006, §13.3.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor HomologicalComplex

universe w₁ w₂ v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

/-! ### Derived-unit invertibility on adapted complexes -/

section Adapted

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [EnoughInjectives C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]
  (F : C ⥤ D) [F.Additive]
  (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
  (hinj : ∀ (Y : C), Injective Y → P Y)
  (hP : ∀ S : ShortComplex C, S.ShortExact → P S.X₁ → P S.X₂ → P S.X₃)
  (hF : ∀ S : ShortComplex C, S.ShortExact → P S.X₁ → P S.X₂ → (S.map F).ShortExact)

variable [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]

include hinj hP hF in
/-- **The derived unit is an isomorphism on bounded-below complexes in an adapted class.** -/
theorem isIso_rightDerivedFunctorPlusUnit_app_of_adapted
    (K : CochainComplex.Plus C) (hK : ∀ n, P (K.obj.X n)) :
    IsIso (F.rightDerivedFunctorPlusUnit.app K) := by
  obtain ⟨b, _⟩ := K.property
  obtain ⟨I, _, i, hi⟩ := CochainComplex.Plus.exists_quasiIso_injective K b
  have : QuasiIso i.hom := (CochainComplex.Plus.quasiIso_iff C i).1 hi
  have : QuasiIso (F.mapCochainComplexPlus.map i).hom :=
    F.quasiIso_map_of_adapted_to_injective P hinj hP hF hK i
  have hnat := F.rightDerivedFunctorPlusUnit.naturality i
  dsimp at hnat
  have : IsIso (F.rightDerivedFunctorPlusUnit.app K ≫
      F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map i)) := by
    rw [← hnat]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map i))

end Adapted

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
  let L₀ : CochainComplex (InjectiveObject C) ℤ :=
    HomologicalComplex.liftObjectProperty _ K.obj inferInstance
  obtain ⟨b, _⟩ := K.property
  have hL₀ : L₀.IsStrictlyGE b := by
    rwa [← CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff _ (InjectiveObject.ι C)]
  let L : CochainComplex.Plus (InjectiveObject C) := ⟨L₀, b, hL₀⟩
  let e : (InjectiveObject.ι C).mapCochainComplexPlus.obj L ≅ K :=
    ObjectProperty.isoMk _
      (HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) (by dsimp [L, L₀]; simp))
  have hnat := F.rightDerivedFunctorPlusUnit.naturality e.hom
  dsimp at hnat
  have : IsIso (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map e.hom) ≫
      F.rightDerivedFunctorPlusUnit.app K) := by
    rw [hnat]
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
  have hnat := F.rightDerivedFunctorPlusUnit.naturality φ
  dsimp at hnat
  rw [hnat, Category.assoc, IsIso.inv_hom_id_assoc, ← Functor.map_comp, ← Functor.map_comp]

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

/-- Naturality of `rightDerivedFunctorPlusObjIsoOfResolution` in morphisms of resolved complexes. -/
@[reassoc]
lemma rightDerivedFunctorPlusObjIsoOfResolution_hom_naturality
    {K K' L L' : CochainComplex.Plus C}
    (ι : K ⟶ L) [QuasiIso ι.hom] [IsIso (F.rightDerivedFunctorPlusUnit.app L)]
    (κ : K' ⟶ L') [QuasiIso κ.hom] [IsIso (F.rightDerivedFunctorPlusUnit.app L')]
    (f : K ⟶ K') (φ : L ⟶ L') (hφ : ι ≫ φ = f ≫ κ) :
    F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f) ≫
        (F.rightDerivedFunctorPlusObjIsoOfResolution κ).hom =
      (F.rightDerivedFunctorPlusObjIsoOfResolution ι).hom ≫
        DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map φ) := by
  rw [← cancel_mono (F.rightDerivedFunctorPlusUnit.app L'), Category.assoc, Category.assoc,
    F.rightDerivedFunctorPlusObjIsoOfResolution_hom_comp ι φ, hφ,
    F.rightDerivedFunctorPlusObjIsoOfResolution_hom_comp_unit,
    Functor.map_comp, Functor.map_comp]

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
complexes. -/
@[reassoc]
lemma rightDerivedFunctorPlusHomologyObjIsoOfResolution_hom_naturality
    {K K' L L' : CochainComplex.Plus C}
    (ι : K ⟶ L) [QuasiIso ι.hom] [IsIso (F.rightDerivedFunctorPlusUnit.app L)]
    (κ : K' ⟶ L') [QuasiIso κ.hom] [IsIso (F.rightDerivedFunctorPlusUnit.app L')]
    (f : K ⟶ K') (φ : L ⟶ L') (hφ : ι ≫ φ = f ≫ κ) (m : ℤ) :
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
        ← Category.assoc, ← rightDerivedFunctorPlusHomologyObjIsoOfResolution_hom]
      rfl

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
      (ι.app _) (ι.app _) f (R.map f) (ι.naturality f).symm)

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
