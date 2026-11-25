/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DerivedCategory.RightDerivedFunctor.Plus
public import TauCeti.Topology.Sheaves.Cohomology.Forget
public import TauCeti.Topology.Sheaves.Flasque.Resolution

/-!
# Bounded-below derived global sections of sheaves of modules

Let `R` be a commutative ring and `X` an arbitrary topological space (no separation, compactness,
or paracompactness hypothesis). Flasque sheaves of `R`-modules on `X` form a class adapted to
global sections `Γ(X, -)` (`CategoryTheory.Sheaf.isFlasque_of_injective`,
`CategoryTheory.Sheaf.isFlasque_X₃`, `CategoryTheory.Sheaf.shortExact_map_Γ_of_isFlasque`), and
`CategoryTheory.Sheaf.isIso_rightDerivedFunctorPlusUnit_app_Γ_of_isFlasque` shows that bounded-below
flasque complexes compute `R⁺Γ(X, -)`.

Specializing `TauCeti/Algebra/Homology/DerivedCategory/RightDerivedFunctor/Plus.lean` to `Γ(X, -)`
gives the bounded-below hypercohomology and degree-`0` comparison API of Stacks §20.3 (tags 015D,
015E, and 09SY):
* `CategoryTheory.Sheaf.quasiIso_map_Γ_of_isFlasque_of_isStrictlyGE` and
  `CategoryTheory.Sheaf.isIso_rightDerivedFunctorPlusUnit_app_Γ_of_isStrictlyGE_of_isFlasque`:
  `Γ(X, -)` preserves quasi-isomorphisms between complexes supported in degrees `≥ b` whose terms
  in degrees `≥ b` are flasque, and the derived unit is an isomorphism under that weaker range
  condition;
* `CategoryTheory.Sheaf.rightDerivedFunctorPlusΓObjIsoOfIsFlasque` and
  `CategoryTheory.Sheaf.rightDerivedFunctorPlusΓHomologyIsoOfIsFlasque`: computation of
  `R⁺Γ(X, Q(K))` and `Hᵐ(R⁺Γ(X, Q(K)))` from bounded-below flasque resolutions, natural up to
  chain homotopy and compatible with shifts;
* `TauCeti.Topology.singleCompRightDerivedFunctorPlusΓHomologyIsoGodement` and
  `TauCeti.Topology.singleCompRightDerivedFunctorPlusΓForgetComparison`: degree-`0` comparison of
  `Hⁿ(R⁺Γ(X, F[0]))` with Godement cohomology and with Mathlib's `Ext`-based sheaf cohomology
  `Hⁿ(X, U F)` of the underlying abelian sheaf.

## References

* The Stacks Project, Cohomology of Sheaves, §20.3 and Lemma 20.12.3 (tag 09SY); Derived
  Categories, Lemmas 13.16.6 and 13.16.7 (tags 015D and 015E).
* R. Hartshorne, *Residues and Duality*, Lecture Notes in Mathematics 20, Chapter I, §5.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u

namespace CategoryTheory.Sheaf

variable {X : TopCat.{u}} {R : Type u} [CommRing R]
  [(Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).Additive]

/-- **Global sections preserve quasi-isomorphisms between bounded-below complexes of flasque
sheaves of `R`-modules.** No ambient `HasDerivedCategory` assumption is required. -/
theorem quasiIso_map_Γ_of_isFlasque_of_isStrictlyGE
    {K₁ K₂ : CochainComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) ℤ}
    (b : ℤ) [K₁.IsStrictlyGE b] [K₂.IsStrictlyGE b] (φ : K₁ ⟶ K₂) [QuasiIso φ]
    (hK₁ : ∀ q : ℤ, b ≤ q → TopCat.Presheaf.IsFlasque (K₁.X q).obj)
    (hK₂ : ∀ q : ℤ, b ≤ q → TopCat.Presheaf.IsFlasque (K₂.X q).obj) :
    QuasiIso
      (((Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapHomologicalComplex (.up ℤ)).map
        φ) :=
  (Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).quasiIso_map_of_isStrictlyGE
    (isFlasque X _) isFlasque_X₃ (fun S hS h₁ _ ↦ shortExact_map_Γ_of_isFlasque S hS h₁)
    isFlasque_of_injective b φ
    (fun q hq ↦ isFlasque_iff.mpr (hK₁ q hq)) (fun q hq ↦ isFlasque_iff.mpr (hK₂ q hq))

section Derived

variable [HasDerivedCategory (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))]
  [HasDerivedCategory (ModuleCat.{u} R)]

/-- Variant of `isIso_rightDerivedFunctorPlusUnit_app_Γ_of_isFlasque` assuming flasqueness only in
the supported range `q ≥ b` when `[F.obj.IsStrictlyGE b]`. -/
theorem isIso_rightDerivedFunctorPlusUnit_app_Γ_of_isStrictlyGE_of_isFlasque
    (F : CochainComplex.Plus (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)))
    (b : ℤ) [F.obj.IsStrictlyGE b]
    (hF : ∀ q : ℤ, b ≤ q → TopCat.Presheaf.IsFlasque (F.obj.X q).obj) :
    IsIso ((Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).rightDerivedFunctorPlusUnit.app
      F) :=
  (Γ (Opens.grothendieckTopology X)
    (ModuleCat.{u} R)).isIso_rightDerivedFunctorPlusUnit_app_of_isStrictlyGE
    (isFlasque X _) isFlasque_X₃ (fun S hS h₁ _ ↦ shortExact_map_Γ_of_isFlasque S hS h₁)
    isFlasque_of_injective F b (fun q hq ↦ isFlasque_iff.mpr (hF q hq))

/-- **Derived global sections via a bounded-below flasque resolution (Stacks, §20.3, eq.
(20.3.0.2)).** Given a quasi-isomorphism `ι : K ⟶ F` in `CochainComplex.Plus` into a complex of
flasque sheaves of `R`-modules, `R⁺Γ(Q(K))` is canonically isomorphic to `Q(Γ(F))`. -/
def rightDerivedFunctorPlusΓObjIsoOfIsFlasque
    {K F : CochainComplex.Plus (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))}
    (ι : K ⟶ F) [QuasiIso ι.hom] (hF : ∀ q : ℤ, TopCat.Presheaf.IsFlasque (F.obj.X q).obj) :
    (Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).rightDerivedFunctorPlus.obj
      (DerivedCategory.Plus.Q.obj K) ≅
    DerivedCategory.Plus.Q.obj
      ((Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapCochainComplexPlus.obj F) :=
  (Γ (Opens.grothendieckTopology X)
    (ModuleCat.{u} R)).rightDerivedFunctorPlusObjIsoOfResolution
    (isFlasque X _) isFlasque_X₃ (fun S hS h₁ _ ↦ shortExact_map_Γ_of_isFlasque S hS h₁)
    isFlasque_of_injective ι (fun q ↦ isFlasque_iff.mpr (hF q))

/-- Unfolding equation expressing `rightDerivedFunctorPlusΓObjIsoOfIsFlasque` in terms of
`Functor.rightDerivedFunctorPlusObjIsoOfResolution`. -/
lemma rightDerivedFunctorPlusΓObjIsoOfIsFlasque_eq
    {K F : CochainComplex.Plus (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))}
    (ι : K ⟶ F) [QuasiIso ι.hom] (hF : ∀ q : ℤ, TopCat.Presheaf.IsFlasque (F.obj.X q).obj) :
    rightDerivedFunctorPlusΓObjIsoOfIsFlasque ι hF =
      (Γ (Opens.grothendieckTopology X)
        (ModuleCat.{u} R)).rightDerivedFunctorPlusObjIsoOfResolution
        (isFlasque X _) isFlasque_X₃ (fun S hS h₁ _ ↦ shortExact_map_Γ_of_isFlasque S hS h₁)
        isFlasque_of_injective ι (fun q ↦ isFlasque_iff.mpr (hF q)) :=
  (rfl)

@[reassoc (attr := simp)]
lemma rightDerivedFunctorPlusΓObjIsoOfIsFlasque_hom_unit
    {K F : CochainComplex.Plus (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))}
    (ι : K ⟶ F) [QuasiIso ι.hom] (hF : ∀ q : ℤ, TopCat.Presheaf.IsFlasque (F.obj.X q).obj) :
    (rightDerivedFunctorPlusΓObjIsoOfIsFlasque ι hF).hom ≫
      (Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).rightDerivedFunctorPlusUnit.app F =
    (Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).rightDerivedFunctorPlus.map
      (DerivedCategory.Plus.Q.map ι) :=
  Functor.rightDerivedFunctorPlusObjIsoOfResolution_hom_unit _ _ _ _ _ ι _

@[reassoc (attr := simp)]
lemma rightDerivedFunctorPlusΓObjIsoOfIsFlasque_inv_map
    {K F : CochainComplex.Plus (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))}
    (ι : K ⟶ F) [QuasiIso ι.hom] (hF : ∀ q : ℤ, TopCat.Presheaf.IsFlasque (F.obj.X q).obj) :
    (rightDerivedFunctorPlusΓObjIsoOfIsFlasque ι hF).inv ≫
      (Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Q.map ι) =
    (Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).rightDerivedFunctorPlusUnit.app F :=
  Functor.rightDerivedFunctorPlusObjIsoOfResolution_inv_map _ _ _ _ _ ι _

/-- Naturality of `rightDerivedFunctorPlusΓObjIsoOfIsFlasque` for morphisms of bounded-below
flasque resolutions commuting up to chain homotopy. -/
@[reassoc]
lemma rightDerivedFunctorPlusΓObjIsoOfIsFlasque_hom_naturality_of_homotopy
    {K₁ F₁ K₂ F₂ : CochainComplex.Plus (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))}
    (ι₁ : K₁ ⟶ F₁) [QuasiIso ι₁.hom] (hF₁ : ∀ q : ℤ, TopCat.Presheaf.IsFlasque (F₁.obj.X q).obj)
    (ι₂ : K₂ ⟶ F₂) [QuasiIso ι₂.hom] (hF₂ : ∀ q : ℤ, TopCat.Presheaf.IsFlasque (F₂.obj.X q).obj)
    (f : K₁ ⟶ K₂) (φ : F₁ ⟶ F₂) (h : Homotopy (ι₁.hom ≫ φ.hom) (f.hom ≫ ι₂.hom)) :
    (Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Q.map f) ≫
      (rightDerivedFunctorPlusΓObjIsoOfIsFlasque ι₂ hF₂).hom =
    (rightDerivedFunctorPlusΓObjIsoOfIsFlasque ι₁ hF₁).hom ≫
      DerivedCategory.Plus.Q.map
        ((Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapCochainComplexPlus.map φ) :=
  Functor.rightDerivedFunctorPlusObjIsoOfResolution_hom_naturality_of_homotopy _ _ _ _ _
    ι₁ _ ι₂ _ f φ h

/-- Naturality of `rightDerivedFunctorPlusΓObjIsoOfIsFlasque` for strictly commuting squares of
bounded-below flasque resolutions. -/
@[reassoc]
lemma rightDerivedFunctorPlusΓObjIsoOfIsFlasque_hom_naturality
    {K₁ F₁ K₂ F₂ : CochainComplex.Plus (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))}
    (ι₁ : K₁ ⟶ F₁) [QuasiIso ι₁.hom] (hF₁ : ∀ q : ℤ, TopCat.Presheaf.IsFlasque (F₁.obj.X q).obj)
    (ι₂ : K₂ ⟶ F₂) [QuasiIso ι₂.hom] (hF₂ : ∀ q : ℤ, TopCat.Presheaf.IsFlasque (F₂.obj.X q).obj)
    (f : K₁ ⟶ K₂) (φ : F₁ ⟶ F₂) (h : ι₁ ≫ φ = f ≫ ι₂) :
    (Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Q.map f) ≫
      (rightDerivedFunctorPlusΓObjIsoOfIsFlasque ι₂ hF₂).hom =
    (rightDerivedFunctorPlusΓObjIsoOfIsFlasque ι₁ hF₁).hom ≫
      DerivedCategory.Plus.Q.map
        ((Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapCochainComplexPlus.map φ) :=
  Functor.rightDerivedFunctorPlusObjIsoOfResolution_hom_naturality _ _ _ _ _ ι₁ _ ι₂ _ f φ h

/-- Shift compatibility of `rightDerivedFunctorPlusΓObjIsoOfIsFlasque`. -/
@[reassoc]
lemma rightDerivedFunctorPlusΓObjIsoOfIsFlasque_shift
    {K F : CochainComplex.Plus (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))}
    (ι : K ⟶ F) [QuasiIso ι.hom] (hF : ∀ q : ℤ, TopCat.Presheaf.IsFlasque (F.obj.X q).obj) (k : ℤ) :
    ((Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).rightDerivedFunctorPlus.commShiftIso
        k).hom.app (DerivedCategory.Plus.Q.obj K) ≫
      ((rightDerivedFunctorPlusΓObjIsoOfIsFlasque ι hF).hom)⟦k⟧' =
    (Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.Q.commShiftIso k).inv.app K) ≫
      (rightDerivedFunctorPlusΓObjIsoOfIsFlasque (ι⟦k⟧')
        (fun q ↦ isFlasque_iff.mp ((isFlasque X _).prop_shift_X
          (fun i ↦ isFlasque_iff.mpr (hF i)) k q))).hom ≫
      DerivedCategory.Plus.Q.map
        (((Γ (Opens.grothendieckTopology X)
          (ModuleCat.{u} R)).mapCochainComplexPlus.commShiftIso k).hom.app F) ≫
      (DerivedCategory.Plus.Q.commShiftIso k).hom.app
        ((Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapCochainComplexPlus.obj F) :=
  Functor.rightDerivedFunctorPlusObjIsoOfResolution_shift _ _ _ _ _ ι _ k

/-- **Hypercohomology of bounded-below sheaf complexes via flasque resolutions (Stacks, §20.3, eq.
(20.3.0.3)).** Given a quasi-isomorphism `ι : K ⟶ F` in `CochainComplex.Plus` into a complex of
flasque sheaves of `R`-modules, `Hᵐ(R⁺Γ(Q(K)))` is canonically isomorphic as an `R`-module to
`Hᵐ(Γ(F))`. -/
def rightDerivedFunctorPlusΓHomologyIsoOfIsFlasque
    {K F : CochainComplex.Plus (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))}
    (ι : K ⟶ F) [QuasiIso ι.hom]
    (hF : ∀ q : ℤ, TopCat.Presheaf.IsFlasque (F.obj.X q).obj) (m : ℤ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) m).obj
      ((Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).rightDerivedFunctorPlus.obj
        (DerivedCategory.Plus.Q.obj K)) ≅
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℤ) m).obj
      (((Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapHomologicalComplex (.up ℤ)).obj
        F.obj) :=
  (Γ (Opens.grothendieckTopology X)
    (ModuleCat.{u} R)).rightDerivedFunctorPlusHomologyIsoOfResolution
    (isFlasque X _) isFlasque_X₃ (fun S hS h₁ _ ↦ shortExact_map_Γ_of_isFlasque S hS h₁)
    isFlasque_of_injective ι (fun q ↦ isFlasque_iff.mpr (hF q)) m

/-- Unfolding equation expressing `rightDerivedFunctorPlusΓHomologyIsoOfIsFlasque` in terms of
`Functor.rightDerivedFunctorPlusHomologyIsoOfResolution`. -/
lemma rightDerivedFunctorPlusΓHomologyIsoOfIsFlasque_eq
    {K F : CochainComplex.Plus (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))}
    (ι : K ⟶ F) [QuasiIso ι.hom]
    (hF : ∀ q : ℤ, TopCat.Presheaf.IsFlasque (F.obj.X q).obj) (m : ℤ) :
    rightDerivedFunctorPlusΓHomologyIsoOfIsFlasque ι hF m =
      (Γ (Opens.grothendieckTopology X)
        (ModuleCat.{u} R)).rightDerivedFunctorPlusHomologyIsoOfResolution
        (isFlasque X _) isFlasque_X₃ (fun S hS h₁ _ ↦ shortExact_map_Γ_of_isFlasque S hS h₁)
        isFlasque_of_injective ι (fun q ↦ isFlasque_iff.mpr (hF q)) m :=
  (rfl)

/-- Naturality in cohomology of `rightDerivedFunctorPlusΓHomologyIsoOfIsFlasque` for morphisms of
bounded-below flasque resolutions commuting up to chain homotopy. -/
@[reassoc]
lemma rightDerivedFunctorPlusΓHomologyIsoOfIsFlasque_hom_naturality_of_homotopy
    {K₁ F₁ K₂ F₂ : CochainComplex.Plus (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))}
    (ι₁ : K₁ ⟶ F₁) [QuasiIso ι₁.hom] (hF₁ : ∀ q : ℤ, TopCat.Presheaf.IsFlasque (F₁.obj.X q).obj)
    (ι₂ : K₂ ⟶ F₂) [QuasiIso ι₂.hom] (hF₂ : ∀ q : ℤ, TopCat.Presheaf.IsFlasque (F₂.obj.X q).obj)
    (f : K₁ ⟶ K₂) (φ : F₁ ⟶ F₂) (h : Homotopy (ι₁.hom ≫ φ.hom) (f.hom ≫ ι₂.hom)) (m : ℤ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) m).map
        ((Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map f)) ≫
      (rightDerivedFunctorPlusΓHomologyIsoOfIsFlasque ι₂ hF₂ m).hom =
    (rightDerivedFunctorPlusΓHomologyIsoOfIsFlasque ι₁ hF₁ m).hom ≫
      ((Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℤ) m).map φ.hom :=
  Functor.rightDerivedFunctorPlusHomologyIsoOfResolution_hom_naturality_of_homotopy _ _ _ _ _
    ι₁ _ ι₂ _ f φ h m

/-- Naturality in cohomology of `rightDerivedFunctorPlusΓHomologyIsoOfIsFlasque` for strictly
commuting squares of bounded-below flasque resolutions. -/
@[reassoc]
lemma rightDerivedFunctorPlusΓHomologyIsoOfIsFlasque_hom_naturality
    {K₁ F₁ K₂ F₂ : CochainComplex.Plus (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))}
    (ι₁ : K₁ ⟶ F₁) [QuasiIso ι₁.hom] (hF₁ : ∀ q : ℤ, TopCat.Presheaf.IsFlasque (F₁.obj.X q).obj)
    (ι₂ : K₂ ⟶ F₂) [QuasiIso ι₂.hom] (hF₂ : ∀ q : ℤ, TopCat.Presheaf.IsFlasque (F₂.obj.X q).obj)
    (f : K₁ ⟶ K₂) (φ : F₁ ⟶ F₂) (h : ι₁ ≫ φ = f ≫ ι₂) (m : ℤ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) m).map
        ((Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map f)) ≫
      (rightDerivedFunctorPlusΓHomologyIsoOfIsFlasque ι₂ hF₂ m).hom =
    (rightDerivedFunctorPlusΓHomologyIsoOfIsFlasque ι₁ hF₁ m).hom ≫
      ((Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℤ) m).map φ.hom :=
  Functor.rightDerivedFunctorPlusHomologyIsoOfResolution_hom_naturality _ _ _ _ _ ι₁ _ ι₂ _ f φ h m

/-- Any comparison morphism `φ : F₁ ⟶ F₂` commuting up to homotopy with two bounded-below flasque
resolutions of `K` intertwines their cohomology identifications; in particular, the identification
is independent of the choice of flasque or injective resolution. -/
@[reassoc]
lemma rightDerivedFunctorPlusΓHomologyIsoOfIsFlasque_hom_comp_homologyMap
    {K F₁ F₂ : CochainComplex.Plus (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))}
    (ι₁ : K ⟶ F₁) [QuasiIso ι₁.hom] (hF₁ : ∀ q : ℤ, TopCat.Presheaf.IsFlasque (F₁.obj.X q).obj)
    (ι₂ : K ⟶ F₂) [QuasiIso ι₂.hom] (hF₂ : ∀ q : ℤ, TopCat.Presheaf.IsFlasque (F₂.obj.X q).obj)
    (φ : F₁ ⟶ F₂) (h : Homotopy (ι₁.hom ≫ φ.hom) ι₂.hom) (m : ℤ) :
    (rightDerivedFunctorPlusΓHomologyIsoOfIsFlasque ι₁ hF₁ m).hom ≫
      ((Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℤ) m).map φ.hom =
    (rightDerivedFunctorPlusΓHomologyIsoOfIsFlasque ι₂ hF₂ m).hom :=
  Functor.rightDerivedFunctorPlusHomologyIsoOfResolution_hom_comp_homologyMap _ _ _ _ _
    ι₁ _ ι₂ _ φ h m

/-- Compatibility of `Functor.singleCompRightDerivedFunctorPlusHomologyIso` for `Γ` with any
`ℕ`-indexed flasque resolution `ι : F[0] ⟶ K` and its extension to `CochainComplex.Plus`. -/
@[reassoc]
lemma singleCompRightDerivedFunctorPlusHomologyIso_Γ_hom_comp_rightDerivedΓObjIsoOfIsFlasque
    {F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)}
    {K : CochainComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) ℕ}
    (ι : (CochainComplex.single₀ _).obj F ⟶ K) [QuasiIso ι]
    (hK : ∀ n : ℕ, TopCat.Presheaf.IsFlasque (K.X n).obj) (n : ℕ) :
    (((Γ (Opens.grothendieckTopology X)
        (ModuleCat.{u} R)).singleCompRightDerivedFunctorPlusHomologyIso n).hom.app F) ≫
      (rightDerivedΓObjIsoOfIsFlasque ι hK n).hom =
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).map
        ((Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctorIsoCompQ _ 0).hom.app F)) ≫
      (rightDerivedFunctorPlusΓHomologyIsoOfIsFlasque
        ((CochainComplex.Plus.extendNatSingle₀Iso _).inv.app F ≫
          (CochainComplex.Plus.extendNat _).map ι)
        (fun q ↦ isFlasque_iff.mp ((isFlasque X _).prop_extendNat_X
          isFlasque_of_injective (fun i ↦ isFlasque_iff.mpr (hK i)) q)) (n : ℤ)).hom ≫
      ((Γ (Opens.grothendieckTopology X)
        (ModuleCat.{u} R)).extendNatMapCochainComplexPlusHomologyIso n).hom.app K := by
  rw [rightDerivedΓObjIsoOfIsFlasque_eq, rightDerivedFunctorPlusΓHomologyIsoOfIsFlasque_eq]
  exact Functor.singleCompRightDerivedFunctorPlusHomologyIso_hom_comp_rightDerivedObjIsoOfResolution
    (Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R))
    (isFlasque X _) isFlasque_X₃ (fun S hS h₁ _ ↦ shortExact_map_Γ_of_isFlasque S hS h₁)
    isFlasque_of_injective ι (fun i ↦ isFlasque_iff.mpr (hK i)) n

end Derived

end CategoryTheory.Sheaf

namespace TauCeti.Topology

variable {X : TopCat.{u}} {R : Type u} [CommRing R]
  [(Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).Additive]
  [HasDerivedCategory (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))]
  [HasDerivedCategory (ModuleCat.{u} R)]

/-- **Single sheaves in degree `0` recover Godement cohomology.** Placing a sheaf of `R`-modules in
degree `0` in `DerivedCategory.Plus`, applying `R⁺Γ`, and taking `n`-th cohomology is naturally
isomorphic as an `R`-module to the `n`-th cohomology of global sections of the Godement
resolution. -/
def singleCompRightDerivedFunctorPlusΓHomologyIsoGodement (n : ℕ) :
    DerivedCategory.Plus.singleFunctor
        (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) 0 ⋙
      (Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) (n : ℤ) ≅
    godementResolution (ModuleCat.{u} R) X ⋙
      (Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapHomologicalComplex _ ⋙
      HomologicalComplex.homologyFunctor _ _ n :=
  (Sheaf.Γ (Opens.grothendieckTopology X)
      (ModuleCat.{u} R)).singleCompRightDerivedFunctorPlusHomologyIso n ≪≫
    rightDerivedΓIsoGodement n

/-- Unfolding equation expressing `singleCompRightDerivedFunctorPlusΓHomologyIsoGodement` as the
composite of `singleCompRightDerivedFunctorPlusHomologyIso` and `rightDerivedΓIsoGodement`. -/
lemma singleCompRightDerivedFunctorPlusΓHomologyIsoGodement_eq (n : ℕ) :
    singleCompRightDerivedFunctorPlusΓHomologyIsoGodement (X := X) (R := R) n =
      (Sheaf.Γ (Opens.grothendieckTopology X)
          (ModuleCat.{u} R)).singleCompRightDerivedFunctorPlusHomologyIso n ≪≫
        rightDerivedΓIsoGodement n :=
  (rfl)

/-- **Single sheaves in degree `0` recover `Ext`-cohomology of the underlying abelian sheaf.** On
any topological space `X`, the abelian group underlying `Hⁿ(R⁺Γ(F[0]))` is naturally isomorphic to
Mathlib's `Ext`-based sheaf cohomology `Hⁿ(X, U F)` (`CategoryTheory.Sheaf.functorH`) of the
underlying sheaf of abelian groups `U F`. -/
def singleCompRightDerivedFunctorPlusΓForgetComparison (n : ℕ) :
    (DerivedCategory.Plus.singleFunctor
        (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) 0 ⋙
      (Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) (n : ℤ)) ⋙
        forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u} ≅
    sheafCompose (Opens.grothendieckTopology X) (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) ⋙
      Sheaf.functorH (Opens.grothendieckTopology X) n :=
  Functor.isoWhiskerRight
      ((Sheaf.Γ (Opens.grothendieckTopology X)
        (ModuleCat.{u} R)).singleCompRightDerivedFunctorPlusHomologyIso n)
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) ≪≫
    moduleCohomologyForgetComparison X R n

/-- Unfolding equation expressing `singleCompRightDerivedFunctorPlusΓForgetComparison` in terms of
`singleCompRightDerivedFunctorPlusHomologyIso` and `moduleCohomologyForgetComparison`. -/
lemma singleCompRightDerivedFunctorPlusΓForgetComparison_eq (n : ℕ) :
    singleCompRightDerivedFunctorPlusΓForgetComparison (X := X) (R := R) n =
      Functor.isoWhiskerRight
          ((Sheaf.Γ (Opens.grothendieckTopology X)
            (ModuleCat.{u} R)).singleCompRightDerivedFunctorPlusHomologyIso n)
          (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) ≪≫
        moduleCohomologyForgetComparison X R n :=
  (rfl)

end TauCeti.Topology
