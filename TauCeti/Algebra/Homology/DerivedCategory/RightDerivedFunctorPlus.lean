/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.Algebra.Homology.Factorizations.CM5a
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import TauCeti.Algebra.Homology.DerivedCategory.Plus
public import TauCeti.Algebra.Homology.HomologicalComplex.Acyclic
public import TauCeti.CategoryTheory.Abelian.AcyclicResolution
import TauCeti.Algebra.Homology.Embedding.CochainComplex

/-!
# Computing bounded-below right derived functors from adapted resolutions

Let `F : C ⥤ D` be an additive functor between abelian categories, where `C` has enough injectives.
Mathlib constructs `F.rightDerivedFunctorPlus : DerivedCategory.Plus C ⥤ DerivedCategory.Plus D` via
injective resolutions of complexes. This file computes `F.rightDerivedFunctorPlus` from resolutions
in any `F`-adapted class `P` (closed under isomorphisms, containing injectives, and closed under
third terms of short exact sequences on which `F` remains exact). Boundedness below is essential:
over `R = k[x]/(x²)`, free modules are `Hom_R(k, -)`-acyclic, yet the unbounded acyclic complex
`⋯ ⟶ R --x--> R --x--> R ⟶ ⋯` maps under `Hom_R(k, -)` to a complex with nonzero cohomology in all
degrees.

## Main definitions and results

* `CategoryTheory.Functor.isIso_rightDerivedFunctorPlusUnit_app` and
  `CategoryTheory.Functor.quasiIso_map_of_isStrictlyGE`: on bounded-below `P`-adapted complexes,
  `F.rightDerivedFunctorPlusUnit` is an isomorphism and `F` preserves quasi-isomorphisms (Stacks,
  tags 015D and 015E).
* `CategoryTheory.Functor.rightDerivedFunctorPlusObjIsoOfResolution` and
  `CategoryTheory.Functor.rightDerivedFunctorPlusHomologyIsoOfResolution`: computation of
  `R⁺F(Q(K))` and `Hᵐ(R⁺F(Q(K)))` from adapted resolutions, natural up to chain homotopy and
  compatible with shifts, additive natural transformations, and short exact sequences.
* `CategoryTheory.Functor.isGE_rightDerivedFunctorPlus_obj`: `F.rightDerivedFunctorPlus` preserves
  `IsGE b`, giving cohomology comparisons for `τ_{≤ n}` (`m ≤ n`) and `σ_{≤ n}` (iso for `m < n`,
  mono at `m = n`).
* `CategoryTheory.Functor.singleCompRightDerivedFunctorPlusHomologyIso`: degree-`0` comparison
  `Hⁿ(R⁺F(X[0])) ≅ F.rightDerived n`, compatible with adapted resolutions and
  `NatTrans.rightDerived`.

## References

* The Stacks Project, Derived Categories, Lemmas 13.16.6 and 13.16.7 (tags 015D and 015E).
* M. Kashiwara, P. Schapira, *Categories and Sheaves*, Grundlehren 332, Springer, 2006,
  Theorem 13.3.7 and Corollary 13.3.8.
-/

public section

noncomputable section

open CategoryTheory Category Limits Pretriangulated Triangulated HomologicalComplex

namespace CategoryTheory

section PropOfIsStrictlyGE

variable {C : Type*} [Category* C]

/-- If `P` contains every injective object and `K : CochainComplex C ℤ` is strictly supported in
degrees `≥ b`, then `P (K.X q)` holds in all degrees `q : ℤ` as soon as it holds for `q ≥ b`,
because zero objects are injective. -/
lemma ObjectProperty.prop_X_of_isStrictlyGE [HasZeroMorphisms C] (P : ObjectProperty C)
    (hinj : ∀ Y : C, Injective Y → P Y) {K : CochainComplex C ℤ} (b : ℤ) [K.IsStrictlyGE b]
    (hK : ∀ q : ℤ, b ≤ q → P (K.X q)) (q : ℤ) : P (K.X q) := by
  by_cases hbq : b ≤ q
  · exact hK q hbq
  · exact hinj _ (K.isZero_of_isStrictlyGE b q (by lia)).injective

/-- If `P` is closed under isomorphisms and contains every injective object, then extending a
`ℕ`-indexed complex with terms in `P` to `CochainComplex.Plus C` yields a complex with terms in `P`
in all integer degrees. -/
lemma ObjectProperty.prop_extendNat_X [HasZeroMorphisms C] [HasZeroObject C] (P : ObjectProperty C)
    [P.IsClosedUnderIsomorphisms] (hinj : ∀ Y : C, Injective Y → P Y)
    {K : CochainComplex C ℕ} (hK : ∀ n : ℕ, P (K.X n)) (q : ℤ) :
    P (((CochainComplex.Plus.extendNat C).obj K).obj.X q) := by
  refine P.prop_X_of_isStrictlyGE hinj 0 (fun q hq ↦ ?_) q
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hq
  exact P.prop_of_iso (K.extendXIso ComplexShape.embeddingUpNat (i := n) (by simp)).symm (hK n)

/-- If `P` is closed under isomorphisms, shifting a bounded-below complex with terms in `P` keeps
its terms in `P`. -/
lemma ObjectProperty.prop_shift_X [Preadditive C] (P : ObjectProperty C)
    [P.IsClosedUnderIsomorphisms] {R : CochainComplex.Plus C} (hR : ∀ q : ℤ, P (R.obj.X q))
    (k q : ℤ) : P ((R⟦k⟧).obj.X q) :=
  P.prop_of_iso (((HomologicalComplex.eval C (.up ℤ) q).mapIso
    (((CochainComplex.Plus.ι C).commShiftIso k).app R)).symm) (hR _)

end PropOfIsStrictlyGE

namespace Functor

section QuasiIsoWithoutDerivedCategory

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D] [EnoughInjectives C]
  (F : C ⥤ D) [F.Additive]

section Derived

variable [HasDerivedCategory C] [HasDerivedCategory D]

/-- The complex-level unit `F.rightDerivedFunctorPlusUnit` is an isomorphism on any bounded-below
complex of injective objects. -/
instance isIso_rightDerivedFunctorPlusUnit_app_of_injective
    (L : CochainComplex.Plus C) [∀ q : ℤ, Injective (L.obj.X q)] :
    IsIso (F.rightDerivedFunctorPlusUnit.app L) := by
  obtain ⟨b, _⟩ := L.property
  let L' : CochainComplex (InjectiveObject C) ℤ :=
    HomologicalComplex.liftObjectProperty _ L.obj inferInstance
  have hL' : L'.IsStrictlyGE b := by
    rwa [← L'.isStrictlyGE_mapHomologicalComplex_obj_iff (InjectiveObject.ι C)]
  let e : (InjectiveObject.ι C).mapCochainComplexPlus.obj ⟨L', b, hL'⟩ ≅ L :=
    (CochainComplex.Plus.ι C).preimageIso (HomologicalComplex.Hom.isoOfComponents
      (fun _ ↦ Iso.refl _) fun i j _ ↦ (id_comp (L.obj.d i j)).trans (comp_id (L.obj.d i j)).symm)
  have hnat := F.rightDerivedFunctorPlusUnit.naturality e.hom
  have : IsIso (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map e.hom) ≫
      F.rightDerivedFunctorPlusUnit.app L) := by dsimp at hnat; rw [hnat]; infer_instance
  exact IsIso.of_isIso_comp_left (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map e.hom)) _

section Adapted

variable (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
  (hinj : ∀ Y : C, Injective Y → P Y)
  (hP : ∀ S : ShortComplex C, S.ShortExact → P S.X₁ → P S.X₂ → P S.X₃)
  (hF : ∀ S : ShortComplex C, S.ShortExact → P S.X₁ → P S.X₂ → (S.map F).ShortExact)

include hinj hP hF in
/-- **Adapted complexes compute `F.rightDerivedFunctorPlus` (Stacks, tag 015E).** If `P` is a class
of objects adapted to `F`, then the derived functor unit `F.rightDerivedFunctorPlusUnit.app K` is
an isomorphism on every `K : CochainComplex.Plus C` whose terms lie in `P`. -/
theorem isIso_rightDerivedFunctorPlusUnit_app (K : CochainComplex.Plus C)
    (hK : ∀ q : ℤ, P (K.obj.X q)) : IsIso (F.rightDerivedFunctorPlusUnit.app K) := by
  obtain ⟨b, _⟩ := K.property
  obtain ⟨L, i, _, _, _, _⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_mono_quasiIso_injective K.obj (b - 1) b (by lia)
  let iplus : K ⟶ CochainComplex.Plus.ofIsStrictlyGE L (b - 1) := ObjectProperty.homMk i
  have : QuasiIso iplus.hom := inferInstanceAs (QuasiIso i)
  let S : ShortComplex (CochainComplex C ℤ) :=
    ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
  have hS : S.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel i)) inferInstance inferInstance
  have hSq := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS
  have hFS : (S.map (F.mapHomologicalComplex (.up ℤ))).ShortExact :=
    HomologicalComplex.shortExact_of_degreewise_shortExact _ fun q ↦
      hF _ (hSq q) (hK q) (hinj _ (by dsimp [S]; infer_instance))
  have : S.X₃.IsStrictlyGE (b - 1) := hS.isStrictlyGE_X₃ (b - 1)
  have : QuasiIso (F.mapCochainComplexPlus.map iplus).hom :=
    hFS.quasiIso_f_iff.2 (HomologicalComplex.Acyclic.map_of_shortExact_of_isStrictlyGE
      F P hP hF (b - 1) (hS.quasiIso_f_iff.1 inferInstance) fun q _ ↦
        hP _ (hSq q) (hK q) (hinj _ (by dsimp [S]; infer_instance)))
  have hnat := F.rightDerivedFunctorPlusUnit.naturality iplus
  have : IsIso (F.rightDerivedFunctorPlusUnit.app K ≫
      F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map iplus)) := by
    dsimp at hnat; rw [← hnat]; infer_instance
  exact IsIso.of_isIso_comp_right (F.rightDerivedFunctorPlusUnit.app K)
    (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map iplus))

include hinj hP hF in
/-- Variant of `isIso_rightDerivedFunctorPlusUnit_app` requiring `P (K.obj.X q)` only in the
supported range `q ≥ b` when `[K.obj.IsStrictlyGE b]`. -/
theorem isIso_rightDerivedFunctorPlusUnit_app_of_isStrictlyGE (K : CochainComplex.Plus C)
    (b : ℤ) [K.obj.IsStrictlyGE b] (hK : ∀ q : ℤ, b ≤ q → P (K.obj.X q)) :
    IsIso (F.rightDerivedFunctorPlusUnit.app K) :=
  F.isIso_rightDerivedFunctorPlusUnit_app P hinj hP hF K (P.prop_X_of_isStrictlyGE hinj b hK)

end Adapted

end Derived

/-- **An additive functor preserves quasi-isomorphisms between bounded-below adapted complexes.**
No ambient `HasDerivedCategory` assumption is required on `C` or `D`. -/
theorem quasiIso_map_of_isStrictlyGE (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
    (hinj : ∀ Y : C, Injective Y → P Y)
    (hP : ∀ S : ShortComplex C, S.ShortExact → P S.X₁ → P S.X₂ → P S.X₃)
    (hF : ∀ S : ShortComplex C, S.ShortExact → P S.X₁ → P S.X₂ → (S.map F).ShortExact)
    {K₁ K₂ : CochainComplex C ℤ} (b : ℤ) [K₁.IsStrictlyGE b] [K₂.IsStrictlyGE b]
    (φ : K₁ ⟶ K₂) [QuasiIso φ]
    (hK₁ : ∀ q : ℤ, b ≤ q → P (K₁.X q)) (hK₂ : ∀ q : ℤ, b ≤ q → P (K₂.X q)) :
    QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map φ) := by
  let := HasDerivedCategory.standard C
  let := HasDerivedCategory.standard D
  let K₁plus : CochainComplex.Plus C := CochainComplex.Plus.ofIsStrictlyGE K₁ b
  let K₂plus : CochainComplex.Plus C := CochainComplex.Plus.ofIsStrictlyGE K₂ b
  let φplus : K₁plus ⟶ K₂plus := ObjectProperty.homMk φ
  have : QuasiIso φplus.hom := inferInstanceAs (QuasiIso φ)
  have := F.isIso_rightDerivedFunctorPlusUnit_app_of_isStrictlyGE P hinj hP hF K₁plus b hK₁
  have := F.isIso_rightDerivedFunctorPlusUnit_app_of_isStrictlyGE P hinj hP hF K₂plus b hK₂
  have hnat := F.rightDerivedFunctorPlusUnit.naturality φplus
  have : IsIso (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map φplus) ≫
      F.rightDerivedFunctorPlusUnit.app K₂plus) := by dsimp at hnat; rw [hnat]; infer_instance
  exact (DerivedCategory.Plus.isIso_Q_map_iff_quasiIso (F.mapCochainComplexPlus.map φplus)).1
    (IsIso.of_isIso_comp_right _ (F.rightDerivedFunctorPlusUnit.app K₂plus))

end QuasiIsoWithoutDerivedCategory

section ResolutionAPI

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
  (F : C ⥤ D) [F.Additive]

/-- `F.rightDerivedFunctorPlus` sends the triangle of any short exact sequence in
`CochainComplex.Plus C` to a distinguished triangle in `DerivedCategory.Plus D`. -/
lemma rightDerivedFunctorPlus_triangleOfSES_distinguished
    {S : ShortComplex (CochainComplex.Plus C)}
    (hS : (S.map (CochainComplex.Plus.ι C)).ShortExact) :
    F.rightDerivedFunctorPlus.mapTriangle.obj (DerivedCategory.Plus.triangleOfSES hS) ∈
      distTriang (DerivedCategory.Plus D) :=
  F.rightDerivedFunctorPlus.map_distinguished _
    (DerivedCategory.Plus.triangleOfSES_distinguished hS)

section AdaptedResolution

variable (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
  (hinj : ∀ Y : C, Injective Y → P Y)
  (hP : ∀ S : ShortComplex C, S.ShortExact → P S.X₁ → P S.X₂ → P S.X₃)
  (hF : ∀ S : ShortComplex C, S.ShortExact → P S.X₁ → P S.X₂ → (S.map F).ShortExact)

/-- **Bounded-below right derived functor from an adapted resolution.** Given a quasi-isomorphism
`ι : K ⟶ R` in `CochainComplex.Plus C` into a complex `R` whose terms lie in an `F`-adapted class
`P`, `R⁺F(Q(K))` is canonically isomorphic to `Q(F(R))`. -/
def rightDerivedFunctorPlusObjIsoOfResolution {K R : CochainComplex.Plus C}
    (ι : K ⟶ R) [QuasiIso ι.hom] (hR : ∀ q : ℤ, P (R.obj.X q)) :
    F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K) ≅
      DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj R) :=
  have := F.isIso_rightDerivedFunctorPlusUnit_app P hinj hP hF R hR
  F.rightDerivedFunctorPlus.mapIso (asIso (DerivedCategory.Plus.Q.map ι)) ≪≫
    (asIso (F.rightDerivedFunctorPlusUnit.app R)).symm

@[reassoc (attr := simp)]
lemma rightDerivedFunctorPlusObjIsoOfResolution_hom_unit {K R : CochainComplex.Plus C}
    (ι : K ⟶ R) [QuasiIso ι.hom] (hR : ∀ q : ℤ, P (R.obj.X q)) :
    (F.rightDerivedFunctorPlusObjIsoOfResolution P hinj hP hF ι hR).hom ≫
      F.rightDerivedFunctorPlusUnit.app R =
        F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map ι) := by
  have := F.isIso_rightDerivedFunctorPlusUnit_app P hinj hP hF R hR
  simp [rightDerivedFunctorPlusObjIsoOfResolution]

@[reassoc (attr := simp)]
lemma rightDerivedFunctorPlusObjIsoOfResolution_inv_map {K R : CochainComplex.Plus C}
    (ι : K ⟶ R) [QuasiIso ι.hom] (hR : ∀ q : ℤ, P (R.obj.X q)) :
    (F.rightDerivedFunctorPlusObjIsoOfResolution P hinj hP hF ι hR).inv ≫
      F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map ι) =
        F.rightDerivedFunctorPlusUnit.app R := by
  have := F.isIso_rightDerivedFunctorPlusUnit_app P hinj hP hF R hR
  simp [rightDerivedFunctorPlusObjIsoOfResolution]

/-- **Cohomology of `R⁺F(Q(K))` from an adapted resolution.** For a quasi-isomorphism `ι : K ⟶ R`
in `CochainComplex.Plus C` with `R` degreewise in `P`, `Hᵐ(R⁺F(Q(K))) ≅ Hᵐ(F(R))`. -/
def rightDerivedFunctorPlusHomologyIsoOfResolution {K R : CochainComplex.Plus C}
    (ι : K ⟶ R) [QuasiIso ι.hom] (hR : ∀ q : ℤ, P (R.obj.X q)) (m : ℤ) :
    (DerivedCategory.Plus.homologyFunctor D m).obj
      (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)) ≅
        (HomologicalComplex.homologyFunctor D (.up ℤ) m).obj
          ((F.mapHomologicalComplex (.up ℤ)).obj R.obj) :=
  (DerivedCategory.Plus.homologyFunctor D m).mapIso
    (F.rightDerivedFunctorPlusObjIsoOfResolution P hinj hP hF ι hR) ≪≫
    (DerivedCategory.Plus.homologyFunctorFactors D m).app (F.mapCochainComplexPlus.obj R)

/-- Naturality of `rightDerivedFunctorPlusObjIsoOfResolution` for morphisms of bounded-below
resolutions commuting up to chain homotopy. -/
@[reassoc]
lemma rightDerivedFunctorPlusObjIsoOfResolution_hom_naturality_of_homotopy
    {K₁ R₁ K₂ R₂ : CochainComplex.Plus C}
    (ι₁ : K₁ ⟶ R₁) [QuasiIso ι₁.hom] (hR₁ : ∀ q : ℤ, P (R₁.obj.X q))
    (ι₂ : K₂ ⟶ R₂) [QuasiIso ι₂.hom] (hR₂ : ∀ q : ℤ, P (R₂.obj.X q))
    (f : K₁ ⟶ K₂) (φ : R₁ ⟶ R₂) (h : Homotopy (ι₁.hom ≫ φ.hom) (f.hom ≫ ι₂.hom)) :
    F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f) ≫
      (F.rightDerivedFunctorPlusObjIsoOfResolution P hinj hP hF ι₂ hR₂).hom =
    (F.rightDerivedFunctorPlusObjIsoOfResolution P hinj hP hF ι₁ hR₁).hom ≫
      DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map φ) := by
  have := F.isIso_rightDerivedFunctorPlusUnit_app P hinj hP hF R₂ hR₂
  rw [← cancel_mono (F.rightDerivedFunctorPlusUnit.app R₂), assoc, assoc,
    rightDerivedFunctorPlusObjIsoOfResolution_hom_unit]
  have hnat := F.rightDerivedFunctorPlusUnit.naturality φ
  dsimp at hnat
  rw [hnat, rightDerivedFunctorPlusObjIsoOfResolution_hom_unit_assoc]
  simp only [← Functor.map_comp]
  rw [DerivedCategory.Plus.Q_map_eq_of_homotopy (f := ι₁ ≫ φ) (g := f ≫ ι₂) h]

/-- Naturality of `rightDerivedFunctorPlusObjIsoOfResolution` for strictly commuting squares of
bounded-below resolutions. -/
@[reassoc]
lemma rightDerivedFunctorPlusObjIsoOfResolution_hom_naturality
    {K₁ R₁ K₂ R₂ : CochainComplex.Plus C}
    (ι₁ : K₁ ⟶ R₁) [QuasiIso ι₁.hom] (hR₁ : ∀ q : ℤ, P (R₁.obj.X q))
    (ι₂ : K₂ ⟶ R₂) [QuasiIso ι₂.hom] (hR₂ : ∀ q : ℤ, P (R₂.obj.X q))
    (f : K₁ ⟶ K₂) (φ : R₁ ⟶ R₂) (h : ι₁ ≫ φ = f ≫ ι₂) :
    F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f) ≫
      (F.rightDerivedFunctorPlusObjIsoOfResolution P hinj hP hF ι₂ hR₂).hom =
    (F.rightDerivedFunctorPlusObjIsoOfResolution P hinj hP hF ι₁ hR₁).hom ≫
      DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map φ) :=
  F.rightDerivedFunctorPlusObjIsoOfResolution_hom_naturality_of_homotopy P hinj hP hF
    ι₁ hR₁ ι₂ hR₂ f φ (Homotopy.ofEq (congrArg (CochainComplex.Plus.ι C).map h))

/-- Naturality in cohomology of `rightDerivedFunctorPlusHomologyIsoOfResolution` for morphisms of
bounded-below resolutions commuting up to chain homotopy. -/
@[reassoc]
lemma rightDerivedFunctorPlusHomologyIsoOfResolution_hom_naturality_of_homotopy
    {K₁ R₁ K₂ R₂ : CochainComplex.Plus C}
    (ι₁ : K₁ ⟶ R₁) [QuasiIso ι₁.hom] (hR₁ : ∀ q : ℤ, P (R₁.obj.X q))
    (ι₂ : K₂ ⟶ R₂) [QuasiIso ι₂.hom] (hR₂ : ∀ q : ℤ, P (R₂.obj.X q))
    (f : K₁ ⟶ K₂) (φ : R₁ ⟶ R₂) (h : Homotopy (ι₁.hom ≫ φ.hom) (f.hom ≫ ι₂.hom)) (m : ℤ) :
    (DerivedCategory.Plus.homologyFunctor D m).map
        (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f)) ≫
      (F.rightDerivedFunctorPlusHomologyIsoOfResolution P hinj hP hF ι₂ hR₂ m).hom =
    (F.rightDerivedFunctorPlusHomologyIsoOfResolution P hinj hP hF ι₁ hR₁ m).hom ≫
      (F.mapHomologicalComplex (.up ℤ) ⋙ HomologicalComplex.homologyFunctor D (.up ℤ) m).map
        φ.hom := by
  have hnat := (DerivedCategory.Plus.homologyFunctorFactors D m).hom.naturality
    (F.mapCochainComplexPlus.map φ)
  simp only [Functor.comp_obj, Functor.comp_map, ObjectProperty.ι_map,
    Functor.mapCochainComplexPlus_map_hom] at hnat
  dsimp [rightDerivedFunctorPlusHomologyIsoOfResolution]
  rw [← Functor.map_comp_assoc,
    F.rightDerivedFunctorPlusObjIsoOfResolution_hom_naturality_of_homotopy P hinj hP hF
      ι₁ hR₁ ι₂ hR₂ f φ h,
    Functor.map_comp_assoc, hnat, assoc]

/-- Naturality in cohomology of `rightDerivedFunctorPlusHomologyIsoOfResolution` for strictly
commuting squares of bounded-below resolutions. -/
@[reassoc]
lemma rightDerivedFunctorPlusHomologyIsoOfResolution_hom_naturality
    {K₁ R₁ K₂ R₂ : CochainComplex.Plus C}
    (ι₁ : K₁ ⟶ R₁) [QuasiIso ι₁.hom] (hR₁ : ∀ q : ℤ, P (R₁.obj.X q))
    (ι₂ : K₂ ⟶ R₂) [QuasiIso ι₂.hom] (hR₂ : ∀ q : ℤ, P (R₂.obj.X q))
    (f : K₁ ⟶ K₂) (φ : R₁ ⟶ R₂) (h : ι₁ ≫ φ = f ≫ ι₂) (m : ℤ) :
    (DerivedCategory.Plus.homologyFunctor D m).map
        (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f)) ≫
      (F.rightDerivedFunctorPlusHomologyIsoOfResolution P hinj hP hF ι₂ hR₂ m).hom =
    (F.rightDerivedFunctorPlusHomologyIsoOfResolution P hinj hP hF ι₁ hR₁ m).hom ≫
      (F.mapHomologicalComplex (.up ℤ) ⋙ HomologicalComplex.homologyFunctor D (.up ℤ) m).map
        φ.hom :=
  F.rightDerivedFunctorPlusHomologyIsoOfResolution_hom_naturality_of_homotopy P hinj hP hF
    ι₁ hR₁ ι₂ hR₂ f φ (Homotopy.ofEq (congrArg (CochainComplex.Plus.ι C).map h)) m

/-- Any comparison morphism `φ : R₁ ⟶ R₂` commuting up to homotopy with two adapted resolutions of
the same bounded-below complex `K` intertwines their cohomology identifications (in particular, the
identification is independent of the choice of adapted or injective resolution). -/
@[reassoc]
lemma rightDerivedFunctorPlusHomologyIsoOfResolution_hom_comp_homologyMap
    {K R₁ R₂ : CochainComplex.Plus C}
    (ι₁ : K ⟶ R₁) [QuasiIso ι₁.hom] (hR₁ : ∀ q : ℤ, P (R₁.obj.X q))
    (ι₂ : K ⟶ R₂) [QuasiIso ι₂.hom] (hR₂ : ∀ q : ℤ, P (R₂.obj.X q))
    (φ : R₁ ⟶ R₂) (h : Homotopy (ι₁.hom ≫ φ.hom) ι₂.hom) (m : ℤ) :
    (F.rightDerivedFunctorPlusHomologyIsoOfResolution P hinj hP hF ι₁ hR₁ m).hom ≫
      (F.mapHomologicalComplex (.up ℤ) ⋙ HomologicalComplex.homologyFunctor D (.up ℤ) m).map
        φ.hom =
    (F.rightDerivedFunctorPlusHomologyIsoOfResolution P hinj hP hF ι₂ hR₂ m).hom := by
  simpa using (F.rightDerivedFunctorPlusHomologyIsoOfResolution_hom_naturality_of_homotopy
    P hinj hP hF ι₁ hR₁ ι₂ hR₂ (𝟙 K) φ (h.trans (Homotopy.ofEq (id_comp ι₂.hom).symm)) m).symm

/-- Shift compatibility of `rightDerivedFunctorPlusObjIsoOfResolution`. -/
@[reassoc]
lemma rightDerivedFunctorPlusObjIsoOfResolution_shift
    {K R : CochainComplex.Plus C} (ι : K ⟶ R) [QuasiIso ι.hom]
    (hR : ∀ q : ℤ, P (R.obj.X q)) (k : ℤ) :
    (F.rightDerivedFunctorPlus.commShiftIso k).hom.app (DerivedCategory.Plus.Q.obj K) ≫
      ((F.rightDerivedFunctorPlusObjIsoOfResolution P hinj hP hF ι hR).hom)⟦k⟧' =
    F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.Q.commShiftIso k).inv.app K) ≫
      (F.rightDerivedFunctorPlusObjIsoOfResolution P hinj hP hF (ι⟦k⟧')
        (P.prop_shift_X hR k)).hom ≫
      DerivedCategory.Plus.Q.map ((F.mapCochainComplexPlus.commShiftIso k).hom.app R) ≫
      (DerivedCategory.Plus.Q.commShiftIso k).hom.app (F.mapCochainComplexPlus.obj R) := by
  have := F.isIso_rightDerivedFunctorPlusUnit_app P hinj hP hF R hR
  have := F.isIso_rightDerivedFunctorPlusUnit_app P hinj hP hF (R⟦k⟧) (P.prop_shift_X hR k)
  have hshift := NatTrans.shift_app_comm F.rightDerivedFunctorPlusUnit k R
  simp only [Functor.comp_obj, Functor.commShiftIso_comp_hom_app, assoc] at hshift
  rw [← cancel_mono ((F.rightDerivedFunctorPlusUnit.app R)⟦k⟧'), assoc, assoc, assoc, assoc,
    ← Functor.map_comp, rightDerivedFunctorPlusObjIsoOfResolution_hom_unit,
    hshift, rightDerivedFunctorPlusObjIsoOfResolution_hom_unit_assoc]
  have hRF :=
    (F.rightDerivedFunctorPlus.commShiftIso k).hom.naturality (DerivedCategory.Plus.Q.map ι)
  have hQ := (DerivedCategory.Plus.Q.commShiftIso k).hom.naturality ι
  dsimp only [Functor.comp_obj, Functor.comp_map] at hRF hQ
  rw [← hRF, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  simp only [assoc, hQ, Iso.inv_hom_id_app_assoc]

end AdaptedResolution

section NatTransCompatibility

variable {F} {G : C ⥤ D} [G.Additive] (τ : F ⟶ G)
  (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
  (hinj : ∀ Y : C, Injective Y → P Y)
  (hP : ∀ S : ShortComplex C, S.ShortExact → P S.X₁ → P S.X₂ → P S.X₃)
  (hF : ∀ S : ShortComplex C, S.ShortExact → P S.X₁ → P S.X₂ → (S.map F).ShortExact)
  (hG : ∀ S : ShortComplex C, S.ShortExact → P S.X₁ → P S.X₂ → (S.map G).ShortExact)

/-- `rightDerivedFunctorPlusObjIsoOfResolution` is compatible with
`NatTrans.rightDerivedFunctorPlus` for any additive natural transformation `τ : F ⟶ G`. -/
@[reassoc]
lemma rightDerivedFunctorPlusObjIsoOfResolution_hom_naturality_natTrans
    {K R : CochainComplex.Plus C} (ι : K ⟶ R) [QuasiIso ι.hom] (hR : ∀ q : ℤ, P (R.obj.X q)) :
    τ.rightDerivedFunctorPlus.app (DerivedCategory.Plus.Q.obj K) ≫
      (G.rightDerivedFunctorPlusObjIsoOfResolution P hinj hP hG ι hR).hom =
    (F.rightDerivedFunctorPlusObjIsoOfResolution P hinj hP hF ι hR).hom ≫
      DerivedCategory.Plus.Q.map (τ.mapCochainComplexPlus.app R) := by
  have := G.isIso_rightDerivedFunctorPlusUnit_app P hinj hP hG R hR
  rw [← cancel_mono (G.rightDerivedFunctorPlusUnit.app R), assoc, assoc,
    rightDerivedFunctorPlusObjIsoOfResolution_hom_unit, ← τ.rightDerivedFunctorPlus_fac_app,
    rightDerivedFunctorPlusObjIsoOfResolution_hom_unit_assoc]
  exact (τ.rightDerivedFunctorPlus.naturality (DerivedCategory.Plus.Q.map ι)).symm

/-- Cohomology-level compatibility of `rightDerivedFunctorPlusHomologyIsoOfResolution` with
`NatTrans.rightDerivedFunctorPlus`. -/
@[reassoc]
lemma rightDerivedFunctorPlusHomologyIsoOfResolution_hom_naturality_natTrans
    {K R : CochainComplex.Plus C} (ι : K ⟶ R) [QuasiIso ι.hom] (hR : ∀ q : ℤ, P (R.obj.X q))
    (m : ℤ) :
    (DerivedCategory.Plus.homologyFunctor D m).map
        (τ.rightDerivedFunctorPlus.app (DerivedCategory.Plus.Q.obj K)) ≫
      (G.rightDerivedFunctorPlusHomologyIsoOfResolution P hinj hP hG ι hR m).hom =
    (F.rightDerivedFunctorPlusHomologyIsoOfResolution P hinj hP hF ι hR m).hom ≫
      (HomologicalComplex.homologyFunctor D (.up ℤ) m).map
        ((τ.mapHomologicalComplex (.up ℤ)).app R.obj) := by
  have hnat := (DerivedCategory.Plus.homologyFunctorFactors D m).hom.naturality
    (τ.mapCochainComplexPlus.app R)
  simp only [Functor.comp_obj, Functor.comp_map, ObjectProperty.ι_map,
    NatTrans.mapCochainComplexPlus_app_hom] at hnat
  dsimp [rightDerivedFunctorPlusHomologyIsoOfResolution]
  rw [← Functor.map_comp_assoc,
    rightDerivedFunctorPlusObjIsoOfResolution_hom_naturality_natTrans τ P hinj hP hF hG ι hR,
    Functor.map_comp_assoc, hnat, assoc]

end NatTransCompatibility

section LowerBoundsAndTruncations

/-- `F.rightDerivedFunctorPlus` is left `t`-exact: it preserves `IsGE b` for all `b : ℤ`. -/
instance isGE_rightDerivedFunctorPlus_obj (X : DerivedCategory.Plus C) (b : ℤ) [X.IsGE b] :
    (F.rightDerivedFunctorPlus.obj X).IsGE b := by
  obtain ⟨⟨Y₀, hY₀⟩, ⟨e₁⟩⟩ :
      ∃ Y : HomotopyCategory.Plus C, Nonempty (DerivedCategory.Plus.Qh.obj Y ≅ X) :=
    ⟨DerivedCategory.Plus.Qh.objPreimage X, ⟨DerivedCategory.Plus.Qh.objObjPreimageIso X⟩⟩
  obtain ⟨K₀, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y₀
  let K : CochainComplex.Plus C := ⟨K₀, (HomotopyCategory.plus_quotient_obj_iff K₀).1 hY₀⟩
  let eK : DerivedCategory.Plus.Q.obj K ≅ X :=
    ((DerivedCategory.Plus.quotientCompQhIso C).app K).symm ≪≫ e₁
  have : (DerivedCategory.Plus.Q.obj K).IsGE b :=
    DerivedCategory.Plus.TStructure.t.isGE_of_iso eK.symm b
  have : QuasiIso (K.obj.πTruncGE b) :=
    (K.obj.quasiIso_πTruncGE_iff_isSupported (ComplexShape.embeddingUpIntGE b)).2
      ((DerivedCategory.Plus.isGE_Q_obj_iff K b).1 this)
  let Kt : CochainComplex.Plus C := CochainComplex.Plus.ofIsStrictlyGE (K.obj.truncGE b) b
  let π : K ⟶ Kt := ObjectProperty.homMk (K.obj.πTruncGE b)
  have : QuasiIso π.hom := inferInstanceAs (QuasiIso (K.obj.πTruncGE b))
  obtain ⟨L, _, i, hi⟩ := CochainComplex.Plus.exists_quasiIso_injective Kt b
  have : QuasiIso i.hom := hi
  let Lplus := (InjectiveObject.ι C).mapCochainComplexPlus.obj L
  let eL : DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj Lplus) ≅
      F.rightDerivedFunctorPlus.obj X :=
    asIso (F.rightDerivedFunctorPlusUnit.app Lplus) ≪≫ F.rightDerivedFunctorPlus.mapIso
      ((asIso (DerivedCategory.Plus.Q.map i)).symm ≪≫
        (asIso (DerivedCategory.Plus.Q.map π)).symm ≪≫ eK)
  have : Lplus.obj.IsStrictlyGE b := by dsimp [Lplus]; infer_instance
  have : (F.mapCochainComplexPlus.obj Lplus).obj.IsStrictlyGE b := by dsimp; infer_instance
  exact DerivedCategory.Plus.TStructure.t.isGE_of_iso eL b

/-- If `X : DerivedCategory.Plus C` is cohomologically concentrated in degrees `≥ b`, then
`Hᵐ(R⁺F(X))` vanishes for `m < b`. -/
lemma isZero_homology_rightDerivedFunctorPlus_of_isGE
    (X : DerivedCategory.Plus C) (b m : ℤ) [X.IsGE b] (hm : m < b) :
    IsZero ((DerivedCategory.Plus.homologyFunctor D m).obj (F.rightDerivedFunctorPlus.obj X)) :=
  DerivedCategory.Plus.isZero_homology_of_isGE (F.rightDerivedFunctorPlus.obj X) b m hm

/-- If `K : CochainComplex.Plus C` is strictly supported in degrees `≥ b`, then `Hᵐ(R⁺F(Q(K)))`
vanishes for `m < b`. -/
lemma isZero_homology_rightDerivedFunctorPlus_Q_of_isStrictlyGE
    (K : CochainComplex.Plus C) (b m : ℤ) [K.obj.IsStrictlyGE b] (hm : m < b) :
    IsZero ((DerivedCategory.Plus.homologyFunctor D m).obj
      (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K))) :=
  F.isZero_homology_rightDerivedFunctorPlus_of_isGE (DerivedCategory.Plus.Q.obj K) b m hm

/-- **Canonical truncation comparison for `F.rightDerivedFunctorPlus`.** In degrees `m ≤ n`,
`K.ιTruncLE n : K.truncLE n ⟶ K` induces an isomorphism `Hᵐ(R⁺F(Q(τ_{≤ n} K))) ≅ Hᵐ(R⁺F(Q(K)))`. -/
theorem isIso_homologyMap_rightDerivedFunctorPlus_ιTruncLE
    (K : CochainComplex.Plus C) (n m : ℤ) (hm : m ≤ n) :
    IsIso ((DerivedCategory.Plus.homologyFunctor D m).map
      (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map (K.ιTruncLE n)))) := by
  obtain ⟨a, _⟩ := K.property
  let S₀ := K.obj.shortComplexTruncLE n
  have hS₀ : S₀.ShortExact := K.obj.shortComplexTruncLE_shortExact n
  have : S₀.X₂.IsStrictlyGE a := inferInstanceAs (K.obj.IsStrictlyGE a)
  have : S₀.X₃.IsStrictlyGE a := hS₀.isStrictlyGE_X₃ a
  let C₃ : CochainComplex.Plus C := CochainComplex.Plus.ofIsStrictlyGE S₀.X₃ a
  let S : ShortComplex (CochainComplex.Plus C) :=
    ShortComplex.mk (K.ιTruncLE n) (ObjectProperty.homMk (Y := C₃) S₀.g) (by ext : 1; exact S₀.zero)
  have hS : (S.map (CochainComplex.Plus.ι C)).ShortExact := hS₀
  let q : C₃ ⟶ CochainComplex.Plus.ofIsStrictlyGE (K.obj.truncGE (n + 1)) (n + 1) :=
    ObjectProperty.homMk (K.obj.shortComplexTruncLEX₃ToTruncGE n (n + 1) rfl)
  have : QuasiIso q.hom :=
    inferInstanceAs (QuasiIso (K.obj.shortComplexTruncLEX₃ToTruncGE n (n + 1) rfl))
  have : (DerivedCategory.Plus.Q.obj C₃).IsGE (n + 1) :=
    DerivedCategory.Plus.TStructure.t.isGE_of_iso (asIso (DerivedCategory.Plus.Q.map q)).symm
      (n + 1)
  let T := DerivedCategory.Plus.ι.mapTriangle.obj
    (F.rightDerivedFunctorPlus.mapTriangle.obj (DerivedCategory.Plus.triangleOfSES hS))
  have hT : T ∈ distTriang (DerivedCategory D) :=
    DerivedCategory.Plus.ι.map_distinguished _
      (F.rightDerivedFunctorPlus_triangleOfSES_distinguished hS)
  have hZ₁ := F.isZero_homology_rightDerivedFunctorPlus_of_isGE
    (DerivedCategory.Plus.Q.obj C₃) (n + 1) m (by lia)
  have hZ₀ := F.isZero_homology_rightDerivedFunctorPlus_of_isGE
    (DerivedCategory.Plus.Q.obj C₃) (n + 1) (m - 1) (by lia)
  have : Epi ((DerivedCategory.homologyFunctor D m).map T.mor₁) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT m).2 (hZ₁.eq_of_tgt _ _)
  have : Mono ((DerivedCategory.homologyFunctor D m).map T.mor₁) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hT (m - 1) m (by lia)).2
      (hZ₀.eq_of_src _ _)
  exact isIso_of_mono_of_epi ((DerivedCategory.homologyFunctor D m).map T.mor₁)

/-- **Stupid truncation comparison for `F.rightDerivedFunctorPlus` (monomorphism up to `n`).** In
degrees `m ≤ n`, `K.πStupidTruncLE n : K ⟶ K.stupidTruncLE n` induces a monomorphism
`Hᵐ(R⁺F(Q(K))) ⟶ Hᵐ(R⁺F(Q(σ_{≤ n} K)))`. -/
theorem mono_homologyMap_rightDerivedFunctorPlus_πStupidTruncLE
    (K : CochainComplex.Plus C) (n m : ℤ) (hm : m ≤ n) :
    Mono ((DerivedCategory.Plus.homologyFunctor D m).map
      (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map (K.πStupidTruncLE n)))) := by
  have hS := CochainComplex.Plus.shortComplexStupidTruncLE_shortExact K n
  let T := DerivedCategory.Plus.ι.mapTriangle.obj
    (F.rightDerivedFunctorPlus.mapTriangle.obj (DerivedCategory.Plus.triangleOfSES hS))
  have hT : T ∈ distTriang (DerivedCategory D) :=
    DerivedCategory.Plus.ι.map_distinguished _
      (F.rightDerivedFunctorPlus_triangleOfSES_distinguished hS)
  have hZ := F.isZero_homology_rightDerivedFunctorPlus_of_isGE
    (DerivedCategory.Plus.Q.obj (CochainComplex.Plus.shortComplexStupidTruncLE K n).X₁)
    (n + 1) m (by lia)
  exact (DerivedCategory.HomologySequence.mono_homologyMap_mor₂_iff T hT m).2 (hZ.eq_of_src _ _)

/-- **Stupid truncation comparison for `F.rightDerivedFunctorPlus` (isomorphism strictly below
`n`).** In degrees `m < n`, `K.πStupidTruncLE n : K ⟶ K.stupidTruncLE n` induces an isomorphism
`Hᵐ(R⁺F(Q(K))) ≅ Hᵐ(R⁺F(Q(σ_{≤ n} K)))`. -/
theorem isIso_homologyMap_rightDerivedFunctorPlus_πStupidTruncLE
    (K : CochainComplex.Plus C) (n m : ℤ) (hm : m < n) :
    IsIso ((DerivedCategory.Plus.homologyFunctor D m).map
      (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map (K.πStupidTruncLE n)))) := by
  have hS := CochainComplex.Plus.shortComplexStupidTruncLE_shortExact K n
  let T := DerivedCategory.Plus.ι.mapTriangle.obj
    (F.rightDerivedFunctorPlus.mapTriangle.obj (DerivedCategory.Plus.triangleOfSES hS))
  have hT : T ∈ distTriang (DerivedCategory D) :=
    DerivedCategory.Plus.ι.map_distinguished _
      (F.rightDerivedFunctorPlus_triangleOfSES_distinguished hS)
  have hZ₁ := F.isZero_homology_rightDerivedFunctorPlus_of_isGE
    (DerivedCategory.Plus.Q.obj (CochainComplex.Plus.shortComplexStupidTruncLE K n).X₁)
    (n + 1) (m + 1) (by lia)
  have : Epi ((DerivedCategory.homologyFunctor D m).map T.mor₂) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T hT m (m + 1) rfl).2
      (hZ₁.eq_of_tgt _ _)
  have : Mono ((DerivedCategory.homologyFunctor D m).map T.mor₂) :=
    F.mono_homologyMap_rightDerivedFunctorPlus_πStupidTruncLE K n m (by lia)
  exact isIso_of_mono_of_epi ((DerivedCategory.homologyFunctor D m).map T.mor₂)

end LowerBoundsAndTruncations

end ResolutionAPI

end Functor

section SingleDegreeZero

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]

namespace InjectiveResolution

/-- Extending `I.ι : (single₀ C).obj X ⟶ I.cocomplex` along `ℕ ↪ ℤ` gives a quasi-isomorphism
`(CochainComplex.Plus.singleFunctor C 0).obj X ⟶ (CochainComplex.Plus.extendNat C).obj I.cocomplex`
into a bounded-below complex of injectives. -/
def ιPlus {X : C} (I : InjectiveResolution X) :
    (CochainComplex.Plus.singleFunctor C 0).obj X ⟶
      (CochainComplex.Plus.extendNat C).obj I.cocomplex :=
  (CochainComplex.Plus.extendNatSingle₀Iso C).inv.app X ≫ (CochainComplex.Plus.extendNat C).map I.ι

instance {X : C} (I : InjectiveResolution X) : QuasiIso I.ιPlus.hom := by
  unfold ιPlus; infer_instance

instance {X : C} (I : InjectiveResolution X) (q : ℤ) :
    Injective (((CochainComplex.Plus.extendNat C).obj I.cocomplex).obj.X q) :=
  inferInstanceAs (Injective ((I.cocomplex.extend ComplexShape.embeddingUpNat).X q))

@[reassoc]
lemma ιPlus_naturality {X Y : C} (f : X ⟶ Y) (I : InjectiveResolution X)
    (J : InjectiveResolution Y) (φ : I.cocomplex ⟶ J.cocomplex)
    (comm : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) :
    I.ιPlus ≫ (CochainComplex.Plus.extendNat C).map φ =
      (CochainComplex.Plus.singleFunctor C 0).map f ≫ J.ιPlus := by
  have hφ : I.ι ≫ φ = (CochainComplex.single₀ C).map f ≫ J.ι :=
    HomologicalComplex.from_single_hom_ext (by simpa using comm)
  unfold ιPlus
  rw [assoc, ← Functor.map_comp, hφ, Functor.map_comp,
    ← NatIso.naturality_1_assoc (CochainComplex.Plus.extendNatSingle₀Iso C) f]
  simp

variable [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]

/-- Given an injective resolution `I` of `X : C`, this isomorphism identifies `Hⁿ(R⁺F(X[0]))` with
`(F.rightDerived n).obj X`. -/
def isoSingleCompRightDerivedFunctorPlusHomology {X : C} (I : InjectiveResolution X)
    (F : C ⥤ D) [F.Additive] (n : ℕ) :
    (DerivedCategory.Plus.singleFunctor C 0 ⋙ F.rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor D (n : ℤ)).obj X ≅ (F.rightDerived n).obj X :=
  (DerivedCategory.Plus.homologyFunctor D (n : ℤ)).mapIso
    (F.rightDerivedFunctorPlus.mapIso
      ((DerivedCategory.Plus.singleFunctorIsoCompQ C 0).app X ≪≫
        asIso (DerivedCategory.Plus.Q.map I.ιPlus)) ≪≫
      (asIso (F.rightDerivedFunctorPlusUnit.app
        ((CochainComplex.Plus.extendNat C).obj I.cocomplex))).symm) ≪≫
    (DerivedCategory.Plus.homologyFunctorFactors D (n : ℤ)).app
      (F.mapCochainComplexPlus.obj ((CochainComplex.Plus.extendNat C).obj I.cocomplex)) ≪≫
    (F.extendNatMapCochainComplexPlusHomologyIso n).app I.cocomplex ≪≫
    (I.isoRightDerivedObj F n).symm

@[reassoc]
lemma isoSingleCompRightDerivedFunctorPlusHomology_hom_naturality
    {X Y : C} (f : X ⟶ Y) (I : InjectiveResolution X) (J : InjectiveResolution Y)
    (φ : I.cocomplex ⟶ J.cocomplex) (comm : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0)
    (F : C ⥤ D) [F.Additive] (n : ℕ) :
    (DerivedCategory.Plus.singleFunctor C 0 ⋙ F.rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor D (n : ℤ)).map f ≫
      (J.isoSingleCompRightDerivedFunctorPlusHomology F n).hom =
    (I.isoSingleCompRightDerivedFunctorPlusHomology F n).hom ≫ (F.rightDerived n).map f := by
  simp only [isoSingleCompRightDerivedFunctorPlusHomology, Functor.comp_map, Iso.trans_hom,
    Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom, asIso_hom, asIso_inv, assoc]
  rw [InjectiveResolution.isoRightDerivedObj_inv_naturality f I J φ comm F n]
  simp only [Functor.comp_map]
  rw [← F.extendNatMapCochainComplexPlusHomologyIso_hom_naturality_assoc n φ]
  have hFact := (DerivedCategory.Plus.homologyFunctorFactors D (n : ℤ)).hom.naturality
    (F.mapCochainComplexPlus.map ((CochainComplex.Plus.extendNat C).map φ))
  dsimp only [Functor.comp_obj, Functor.comp_map] at hFact
  rw [reassoc_of% hFact.symm, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc,
    ← Functor.map_comp_assoc]
  congr 2
  rw [← cancel_mono (F.rightDerivedFunctorPlusUnit.app
    ((CochainComplex.Plus.extendNat C).obj J.cocomplex))]
  simp only [assoc, IsIso.inv_hom_id, comp_id]
  have hUnit := F.rightDerivedFunctorPlusUnit.naturality ((CochainComplex.Plus.extendNat C).map φ)
  have hSingle := (DerivedCategory.Plus.singleFunctorIsoCompQ C 0).hom.naturality f
  dsimp only [Functor.comp_obj, Functor.comp_map] at hUnit hSingle
  rw [hUnit, IsIso.inv_hom_id_assoc]
  simp only [← Functor.map_comp]
  congr 1
  rw [assoc, ← Functor.map_comp, ιPlus_naturality f I J φ comm, Functor.map_comp,
    reassoc_of% hSingle]

end InjectiveResolution

variable [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]

namespace Functor

variable (F : C ⥤ D) [F.Additive]

/-- **Degree-zero single complexes recover `F.rightDerived n`.** On `C`, placing an object in
degree `0` in `DerivedCategory.Plus C`, applying `F.rightDerivedFunctorPlus`, and taking `n`-th
cohomology is naturally isomorphic to `F.rightDerived n`. -/
def singleCompRightDerivedFunctorPlusHomologyIso (n : ℕ) :
    DerivedCategory.Plus.singleFunctor C 0 ⋙ F.rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor D (n : ℤ) ≅ F.rightDerived n :=
  NatIso.ofComponents
    (fun X ↦ (injectiveResolution X).isoSingleCompRightDerivedFunctorPlusHomology F n)
    fun {X Y} f ↦ InjectiveResolution.isoSingleCompRightDerivedFunctorPlusHomology_hom_naturality
      f (injectiveResolution X) (injectiveResolution Y)
      (InjectiveResolution.desc f (injectiveResolution Y) (injectiveResolution X))
      (InjectiveResolution.desc_commutes_zero f _ _) F n

/-- On any injective resolution `I` of `X`,
`(F.singleCompRightDerivedFunctorPlusHomologyIso n).app X` agrees with
`I.isoSingleCompRightDerivedFunctorPlusHomology F n`. -/
lemma singleCompRightDerivedFunctorPlusHomologyIso_app_eq_of_injectiveResolution
    {X : C} (I : InjectiveResolution X) (n : ℕ) :
    (F.singleCompRightDerivedFunctorPlusHomologyIso n).app X =
      I.isoSingleCompRightDerivedFunctorPlusHomology F n := by
  ext : 1
  simpa [singleCompRightDerivedFunctorPlusHomologyIso] using
    (InjectiveResolution.isoSingleCompRightDerivedFunctorPlusHomology_hom_naturality (𝟙 X)
      (injectiveResolution X) I (InjectiveResolution.desc (𝟙 X) I (injectiveResolution X))
      (InjectiveResolution.desc_commutes_zero (𝟙 X) I (injectiveResolution X)) F n).symm

/-- For `m < 0`, `Hᵐ(R⁺F(X[0]))` vanishes. -/
lemma isZero_singleCompRightDerivedFunctorPlusHomology_of_neg (X : C) (m : ℤ) (hm : m < 0) :
    IsZero ((DerivedCategory.Plus.singleFunctor C 0 ⋙ F.rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor D m).obj X) :=
  F.isZero_homology_rightDerivedFunctorPlus_of_isGE
    ((DerivedCategory.Plus.singleFunctor C 0).obj X) 0 m hm

/-- **Compatibility of `singleCompRightDerivedFunctorPlusHomologyIso` with `ℕ`-indexed adapted
resolutions.** For any quasi-isomorphism `ι : X[0] ⟶ K` in `CochainComplex C ℕ` with terms in an
`F`-adapted class `P`, the composite identification `Hⁿ(R⁺F(X[0])) ≅ RⁿF(X) ≅ Hⁿ(F(K))` via
`F.rightDerivedObjIsoOfResolution` agrees with `F.rightDerivedFunctorPlusHomologyIsoOfResolution`
applied to the extended resolution in `CochainComplex.Plus C`. -/
@[reassoc]
lemma singleCompRightDerivedFunctorPlusHomologyIso_hom_comp_rightDerivedObjIsoOfResolution
    (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
    (hinj : ∀ Y : C, Injective Y → P Y)
    (hP : ∀ S : ShortComplex C, S.ShortExact → P S.X₁ → P S.X₂ → P S.X₃)
    (hF : ∀ S : ShortComplex C, S.ShortExact → P S.X₁ → P S.X₂ → (S.map F).ShortExact)
    {X : C} {K : CochainComplex C ℕ} (ι : (CochainComplex.single₀ C).obj X ⟶ K) [QuasiIso ι]
    (hK : ∀ n : ℕ, P (K.X n)) (n : ℕ) :
    (F.singleCompRightDerivedFunctorPlusHomologyIso n).hom.app X ≫
      (F.rightDerivedObjIsoOfResolution P hinj hP hF ι hK n).hom =
    (DerivedCategory.Plus.homologyFunctor D (n : ℤ)).map
        (F.rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctorIsoCompQ C 0).hom.app X)) ≫
      (F.rightDerivedFunctorPlusHomologyIsoOfResolution P hinj hP hF
        ((CochainComplex.Plus.extendNatSingle₀Iso C).inv.app X ≫
          (CochainComplex.Plus.extendNat C).map ι)
        (P.prop_extendNat_X hinj hK) (n : ℤ)).hom ≫
      (F.extendNatMapCochainComplexPlusHomologyIso n).hom.app K := by
  let I := injectiveResolution X
  let φ : K ⟶ I.cocomplex := InjectiveResolution.descOfQuasiIso (𝟙 X) I ι
  have hφ : ι ≫ φ = I.ι := by simp [φ]
  have : QuasiIso ((F.mapHomologicalComplex (.up ℕ)).map φ) :=
    InjectiveResolution.quasiIso_map_of_comp_eq F P hinj hP hF ι hK I φ hφ
  have : IsIso ((F.mapHomologicalComplex (.up ℕ) ⋙
      HomologicalComplex.homologyFunctor D (.up ℕ) n).map φ) :=
    inferInstanceAs (IsIso (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (.up ℕ)).map φ) n))
  rw [← cancel_mono ((F.mapHomologicalComplex (.up ℕ) ⋙
      HomologicalComplex.homologyFunctor D (.up ℕ) n).map φ)]
  simp only [assoc]
  have hComp : (((CochainComplex.Plus.extendNatSingle₀Iso C).inv.app X ≫
      (CochainComplex.Plus.extendNat C).map ι) ≫ (CochainComplex.Plus.extendNat C).map φ) =
    I.ιPlus := by unfold InjectiveResolution.ιPlus; rw [assoc, ← Functor.map_comp, hφ]
  rw [F.rightDerivedObjIsoOfResolution_hom_comp_homologyMap P hinj hP hF ι hK n I φ hφ]
  dsimp only [Functor.comp_map]
  rw [← F.extendNatMapCochainComplexPlusHomologyIso_hom_naturality n φ]
  dsimp only [ObjectProperty.ι_map, Functor.mapCochainComplexPlus_map_hom]
  rw [F.rightDerivedFunctorPlusHomologyIsoOfResolution_hom_comp_homologyMap_assoc P hinj hP hF
      ((CochainComplex.Plus.extendNatSingle₀Iso C).inv.app X ≫
        (CochainComplex.Plus.extendNat C).map ι)
      (P.prop_extendNat_X hinj hK) I.ιPlus (fun _ ↦ hinj _ inferInstance)
      ((CochainComplex.Plus.extendNat C).map φ)
      (Homotopy.ofEq (congrArg (CochainComplex.Plus.ι C).map hComp)) (n : ℤ),
    ← Iso.app_hom, F.singleCompRightDerivedFunctorPlusHomologyIso_app_eq_of_injectiveResolution I n]
  dsimp [InjectiveResolution.isoSingleCompRightDerivedFunctorPlusHomology,
    rightDerivedFunctorPlusHomologyIsoOfResolution, rightDerivedFunctorPlusObjIsoOfResolution]
  simp only [Functor.map_comp, assoc, Iso.inv_hom_id, comp_id]

end Functor

namespace NatTrans

variable {F₁ F₂ : C ⥤ D} [F₁.Additive] [F₂.Additive] (τ : F₁ ⟶ F₂)

/-- `Functor.singleCompRightDerivedFunctorPlusHomologyIso` intertwines
`NatTrans.rightDerivedFunctorPlus τ` with `NatTrans.rightDerived τ n`. -/
@[reassoc]
lemma singleCompRightDerivedFunctorPlusHomologyIso_hom_naturality_natTrans (n : ℕ) (X : C) :
    (DerivedCategory.Plus.homologyFunctor D (n : ℤ)).map
        (τ.rightDerivedFunctorPlus.app ((DerivedCategory.Plus.singleFunctor C 0).obj X)) ≫
      (F₂.singleCompRightDerivedFunctorPlusHomologyIso n).hom.app X =
    (F₁.singleCompRightDerivedFunctorPlusHomologyIso n).hom.app X ≫
      (NatTrans.rightDerived τ n).app X := by
  let I := injectiveResolution X
  rw [← Iso.app_hom, ← Iso.app_hom,
    F₁.singleCompRightDerivedFunctorPlusHomologyIso_app_eq_of_injectiveResolution I n,
    F₂.singleCompRightDerivedFunctorPlusHomologyIso_app_eq_of_injectiveResolution I n,
    I.rightDerived_app_eq τ n]
  simp only [InjectiveResolution.isoSingleCompRightDerivedFunctorPlusHomology, Iso.trans_hom,
    Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom, asIso_hom, asIso_inv, assoc]
  rw [← cancel_mono (I.isoRightDerivedObj F₂ n).hom]
  simp only [assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, comp_id]
  have hFact := (DerivedCategory.Plus.homologyFunctorFactors D (n : ℤ)).hom.naturality
    (τ.mapCochainComplexPlus.app ((CochainComplex.Plus.extendNat C).obj I.cocomplex))
  dsimp only [Functor.comp_obj, Functor.comp_map] at hFact
  rw [← τ.extendNatMapCochainComplexPlusHomologyIso_hom_naturality n I.cocomplex,
    ← reassoc_of% hFact, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  congr 2
  rw [← cancel_mono (F₂.rightDerivedFunctorPlusUnit.app
    ((CochainComplex.Plus.extendNat C).obj I.cocomplex))]
  simp only [assoc, IsIso.inv_hom_id, comp_id]
  rw [← τ.rightDerivedFunctorPlus_fac_app, IsIso.inv_hom_id_assoc]
  exact (τ.rightDerivedFunctorPlus.naturality _).symm

end NatTrans

end SingleDegreeZero

end CategoryTheory
