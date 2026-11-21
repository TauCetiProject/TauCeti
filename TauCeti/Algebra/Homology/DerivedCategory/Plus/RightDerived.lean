/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.Algebra.Homology.Factorizations.CM5b
public import TauCeti.Algebra.Homology.DerivedCategory.Plus.Basic
public import TauCeti.Algebra.Homology.HomologicalComplex.Acyclic
public import TauCeti.Algebra.Homology.HomologySequenceLemmas
public import TauCeti.Algebra.Homology.ShortComplex.ShortExact

/-!
# Bounded-below right derived functors from adapted resolutions

Let `F : C ⥤ D` be an additive functor between abelian categories, where `C` has enough
injectives, and let `F.rightDerivedFunctorPlus : DerivedCategory.Plus C ⥤ DerivedCategory.Plus D`
be Mathlib's bounded-below right derived functor. This file develops the adapted-resolution,
resolution-computation, and left t-exactness API for `F.rightDerivedFunctorPlus`:

* **Adapted quasi-isomorphisms:** for a class `P : ObjectProperty C` closed under isomorphisms,
  containing injectives, closed under cokernels of monomorphisms, and on whose short exact
  sequences `F` is exact, `F` preserves quasi-isomorphisms from bounded-below `P`-complexes into
  injective complexes (`CategoryTheory.Functor.quasiIso_map_of_adapted_injective`) and between any
  two bounded-below `P`-complexes (`CategoryTheory.Functor.quasiIso_map_of_adapted`), without
  assuming `HasDerivedCategory`.
* **Derived-unit invertibility:** `F.rightDerivedFunctorPlusUnit.app K` is an isomorphism for
  every bounded-below complex `K` of injective objects
  (`CategoryTheory.Functor.isIso_rightDerivedFunctorPlusUnit_app_of_injective`) and every
  bounded-below `P`-complex
  (`CategoryTheory.Functor.isIso_rightDerivedFunctorPlusUnit_app_of_adapted`).
* **Computation from resolutions:** for any quasi-isomorphism `ι : K ⟶ L` in
  `CochainComplex.Plus C` with `[IsIso (F.rightDerivedFunctorPlusUnit.app L)]`,
  `F.rightDerivedFunctorPlus.obj (Q.obj K) ≅ Q.obj (F(L))`
  (`CategoryTheory.Functor.rightDerivedFunctorPlusObjIsoOfResolution`), with naturality,
  cohomology computation
  (`CategoryTheory.Functor.rightDerivedFunctorPlusHomologyObjIsoOfResolution`), and a functorial
  version (`CategoryTheory.Functor.rightDerivedFunctorPlusIsoOfResolution`).
* **Left t-exactness:** `F.rightDerivedFunctorPlus` preserves `DerivedCategory.Plus.IsGE b` for
  every `b : ℤ` (`CategoryTheory.Functor.isGE_rightDerivedFunctorPlus_obj`).

Exact-functor comparison and degree-zero recovery of classical right derived functors `RⁿF` are
proved in `TauCeti/Algebra/Homology/DerivedCategory/Plus/Comparison.lean`.

## References

* `TauCeti/CategoryTheory/Abelian/AcyclicResolution.lean`, the formal source whose adapted
  quasi-isomorphism proof pattern and resolution-isomorphism API are adapted here to
  `CochainComplex.Plus` and `DerivedCategory.Plus`.
* Mathlib's `Mathlib/Algebra/Homology/Factorizations/CM5b.lean`, whose bounded-below injective
  monomorphism factorization `CochainComplex.cm5b` is used in `quasiIso_map_of_adapted_injective`.
* The Stacks Project, Derived Categories, §13.15–§13.16 (tags 05T8, 015E).
* M. Kashiwara, P. Schapira, *Categories and Sheaves*, Grundlehren 332, Springer, 2006, §13.3.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor HomologicalComplex

universe w₁ w₂ v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

/-! ### Adapted quasi-isomorphisms and unit invertibility -/

section Adapted

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [EnoughInjectives C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]
  (F : C ⥤ D) [F.Additive]
  (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
  (hinj : ∀ (Y : C), Injective Y → P Y)
  (hP : ∀ S : ShortComplex C, S.ShortExact → P S.X₁ → P S.X₂ → P S.X₃)
  (hF : ∀ S : ShortComplex C, S.ShortExact → P S.X₁ → P S.X₂ → (S.map F).ShortExact)

include hinj hP hF in
/-- **Adapted bounded-below complexes preserve quasi-isomorphisms into injective complexes.**
For a quasi-isomorphism `i : K ⟶ ι(I)` from a bounded-below `P`-complex `K` to a bounded-below
complex `I` of injective objects, `F(i)` is a quasi-isomorphism. -/
theorem quasiIso_map_of_adapted_injective
    {K : CochainComplex.Plus C} (hK : ∀ n, P (K.obj.X n))
    {I : CochainComplex.Plus (InjectiveObject C)}
    (i : K ⟶ (InjectiveObject.ι C).mapCochainComplexPlus.obj I) [QuasiIso i.hom] :
    QuasiIso ((F.mapHomologicalComplex _).map i.hom) := by
  obtain ⟨b₁, _⟩ := K.property
  obtain ⟨b₂, _⟩ := I.property
  let b := min (b₁ - 1) b₂
  have : K.obj.IsStrictlyGE (b + 1) := K.obj.isStrictlyGE_of_ge (b + 1) b₁ (by omega)
  let L := ((InjectiveObject.ι C).mapCochainComplexPlus.obj I).obj
  have : I.obj.IsStrictlyGE b := I.obj.isStrictlyGE_of_ge b b₂ (min_le_right _ _)
  have : L.IsStrictlyGE b := by
    dsimp [L]
    infer_instance
  -- Factor `i.hom` via `cm5b` as a monomorphism `ψ` followed by the homotopy equivalence `p`.
  let ψ := CochainComplex.cm5b.i i.hom
  have : QuasiIso ψ := by
    have : QuasiIso (ψ ≫ CochainComplex.cm5b.p K.obj L) := by
      rw [CochainComplex.cm5b.fac]
      infer_instance
    exact quasiIso_of_comp_right ψ (CochainComplex.cm5b.p K.obj L)
  -- Apply `F` to the short exact cokernel sequence `0 ⟶ K ⟶ cone(𝟙 (I K)) ⊞ L ⟶ coker(ψ) ⟶ 0`.
  let S := ShortComplex.cokernelSequence ψ
  have hS : S.ShortExact := TauCeti.cokernelSequence_shortExact ψ
  have hSn := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS
  have hX₂ (n : ℤ) : P (S.X₂.X n) := by
    have : Injective ((HomologicalComplex.eval C (.up ℤ) n).obj
        (CochainComplex.mappingCone (𝟙 (CochainComplex.cm5b.I K.obj)))) := by
      dsimp
      infer_instance
    have : Injective ((HomologicalComplex.eval C (.up ℤ) n).obj L) := (I.obj.X n).property
    have : Injective (S.X₂.X n) := Injective.of_iso
      ((HomologicalComplex.eval C (.up ℤ) n).mapBiprod _ _).symm inferInstance
    exact hinj _ inferInstance
  have hQge : S.X₃.IsStrictlyGE b := by
    have : S.X₂.IsStrictlyGE b :=
      inferInstanceAs
        ((CochainComplex.mappingCone (𝟙 (CochainComplex.cm5b.I K.obj)) ⊞ L).IsStrictlyGE b)
    rw [CochainComplex.isStrictlyGE_iff]
    intro n hn
    have := (hSn n).epi_g
    exact IsZero.of_epi (S.g.f n) (S.X₂.isZero_of_isStrictlyGE b n hn)
  have hFS : (S.map (F.mapHomologicalComplex _)).ShortExact :=
    HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦
      hF _ (hSn n) (hK n) (hX₂ n)
  have : QuasiIso S.f := by
    dsimp [S, ShortComplex.cokernelSequence]
    infer_instance
  have : QuasiIso ((F.mapHomologicalComplex _).map ψ) :=
    hFS.quasiIso_f_iff.2 (HomologicalComplex.Acyclic.map_of_shortExact_of_isStrictlyGE F P hP hF
      b (hS.quasiIso_f_iff.1 inferInstance) fun n ↦ hP _ (hSn n) (hK n) (hX₂ n))
  have : QuasiIso ((F.mapHomologicalComplex _).map (CochainComplex.cm5b.p K.obj L)) :=
    (F.mapHomotopyEquiv (CochainComplex.cm5b.homotopyEquiv K.obj L)).quasiIso_hom
  rw [← CochainComplex.cm5b.fac i.hom, Functor.map_comp]
  infer_instance

include hinj hP hF in
/-- A quasi-isomorphism between bounded-below complexes in an adapted class remains a
quasi-isomorphism after applying `F`. -/
theorem quasiIso_map_of_adapted
    {K L : CochainComplex.Plus C} (f : K ⟶ L) [QuasiIso f.hom]
    (hK : ∀ n, P (K.obj.X n)) (hL : ∀ n, P (L.obj.X n)) :
    QuasiIso ((F.mapHomologicalComplex _).map f.hom) := by
  obtain ⟨b, _⟩ := L.property
  obtain ⟨I, _, j, hj⟩ := CochainComplex.Plus.exists_quasiIso_injective L b
  have : QuasiIso j.hom := (CochainComplex.Plus.quasiIso_iff C j).1 hj
  have : QuasiIso (f ≫ j).hom := inferInstanceAs (QuasiIso (f.hom ≫ j.hom))
  have : QuasiIso ((F.mapHomologicalComplex _).map j.hom) :=
    F.quasiIso_map_of_adapted_injective P hinj hP hF hL j
  have : QuasiIso ((F.mapHomologicalComplex _).map f.hom ≫
      (F.mapHomologicalComplex _).map j.hom) := by
    rw [← Functor.map_comp]
    exact F.quasiIso_map_of_adapted_injective P hinj hP hF hK (f ≫ j)
  exact quasiIso_of_comp_right ((F.mapHomologicalComplex _).map f.hom)
    ((F.mapHomologicalComplex _).map j.hom)

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
    F.quasiIso_map_of_adapted_injective P hinj hP hF hK i
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
  exact inferInstanceAs
    (IsIso (F.rightDerivedFunctorPlusUnit.app ((InjectiveObject.ι C).mapCochainComplexPlus.obj L)))

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
  have h1 : (DerivedCategory.Plus.homologyFunctor D m).map
        (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f)) ≫
      (DerivedCategory.Plus.homologyFunctor D m).map
        (F.rightDerivedFunctorPlusObjIsoOfResolution κ).hom =
      (DerivedCategory.Plus.homologyFunctor D m).map
        (F.rightDerivedFunctorPlusObjIsoOfResolution ι).hom ≫
      (DerivedCategory.Plus.homologyFunctor D m).map
        (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map φ)) := by
    rw [← Functor.map_comp, ← Functor.map_comp,
      F.rightDerivedFunctorPlusObjIsoOfResolution_hom_naturality ι κ f φ hφ]
  have h2 := TauCeti.DerivedCategory.Plus.homologyFunctorFactors_hom_naturality
    (F.mapCochainComplexPlus.map φ) m
  rw [rightDerivedFunctorPlusHomologyObjIsoOfResolution_hom,
    rightDerivedFunctorPlusHomologyObjIsoOfResolution_hom]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) h1).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) h2).trans (Category.assoc _ _ _).symm)))

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

end Resolution

end CategoryTheory.Functor
