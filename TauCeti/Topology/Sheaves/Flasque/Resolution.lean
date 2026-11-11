/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Abelian.AcyclicResolution
public import TauCeti.Topology.Sheaves.Flasque.Locality
public import TauCeti.Topology.Sheaves.Flasque.Module

/-!
# Flasque resolutions compute the derived functors of global sections

Let `R` be a commutative ring and `X` a topological space. Flasque sheaves of `R`-modules form a
class adapted to the global sections functor `Γ`, in the sense of
`TauCeti/CategoryTheory/Abelian/AcyclicResolution.lean`: injective sheaves are flasque, the
cokernel of a monomorphism between flasque sheaves is flasque, and `Γ` keeps a short exact sequence
`0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` with `F₁` flasque exact
(`CategoryTheory.ShortComplex.ShortExact.map_Γ_of_isFlasque`). Hence a
flasque resolution `0 ⟶ F ⟶ K⁰ ⟶ K¹ ⟶ ⋯` computes the right derived functors of `Γ`:
`RⁿΓ(F) ≅ Hⁿ(Γ(K))`. No hypothesis is made on `X`.

The right derived functors of `Γ` are Mathlib's `CategoryTheory.Functor.rightDerived`, defined
through injective resolutions. Additivity of `Γ`, which they require, is kept as an instance
argument.

## Main definitions and results

* `CategoryTheory.Sheaf.quasiIso_map_Γ_of_isFlasque`: for a flasque resolution `K` and a
  comparison map `φ : K ⟶ I` to an injective resolution, `Γ(φ)` is a quasi-isomorphism.
* `CategoryTheory.Sheaf.rightDerivedΓObjIsoOfIsFlasque`: `RⁿΓ(F) ≅ Hⁿ(Γ(K))` for a flasque
  resolution `K` of `F`, characterized through any injective resolution and comparison map by
  `CategoryTheory.Sheaf.rightDerivedΓObjIsoOfIsFlasque_hom_comp_homologyMap`.
* `CategoryTheory.Sheaf.rightDerivedΓIsoOfIsFlasque`: the natural isomorphism for a functorial
  flasque resolution.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Proposition III.1.2A and
  Lemma III.2.4.
* The Stacks Project, Cohomology of Sheaves, Lemma 20.12.3 (tag 09SY), and Derived Categories,
  Lemma 13.15.6 (tag 05T8).
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace CochainComplex

universe u

namespace CategoryTheory.Sheaf

variable {X : TopCat.{u}} {R : Type u} [CommRing R]
  [(Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).Additive]

variable {F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)}
  {K : CochainComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) ℕ}
  (ι : (single₀ _).obj F ⟶ K) [QuasiIso ι] (hK : ∀ n, TopCat.Presheaf.IsFlasque (K.X n).obj)

omit [(Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).Additive] in
private lemma isFlasque_X₃
    (S : ShortComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))) (hS : S.ShortExact)
    (h₁ : isFlasque X _ S.X₁) (h₂ : isFlasque X _ S.X₂) : isFlasque X _ S.X₃ :=
  have : TopCat.Presheaf.IsFlasque S.X₁.obj := isFlasque_iff.mp h₁
  have : TopCat.Presheaf.IsFlasque S.X₂.obj := isFlasque_iff.mp h₂
  isFlasque_iff.mpr hS.isFlasque_X₃_of_isFlasque

private lemma shortExact_map_Γ_of_isFlasque
    (S : ShortComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))) (hS : S.ShortExact)
    (h₁ : isFlasque X _ S.X₁) (_ : isFlasque X _ S.X₂) :
    (S.map (Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R))).ShortExact :=
  have : TopCat.Presheaf.IsFlasque S.X₁.obj := isFlasque_iff.mp h₁
  hS.map_Γ_of_isFlasque

include hK in
/-- **Flasque resolutions compute the derived functors of global sections.** For a flasque
resolution `ι : F[0] ⟶ K` of a sheaf of `R`-modules `F` and a morphism `φ : K ⟶ I` compatible
with `ι` and an injective resolution `I` of `F`, the map of global sections `Γ(K) ⟶ Γ(I)` is a
quasi-isomorphism. -/
theorem quasiIso_map_Γ_of_isFlasque (I : InjectiveResolution F) (φ : K ⟶ I.cocomplex)
    (hφ : ι ≫ φ = I.ι) :
    QuasiIso (((Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapHomologicalComplex _).map
      φ) :=
  InjectiveResolution.quasiIso_map_of_comp_eq (Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R))
    (isFlasque X _) (fun _ _ ↦ isFlasque_iff.mpr (isFlasque_of_injective_moduleCat _)) isFlasque_X₃
    shortExact_map_Γ_of_isFlasque ι (fun n ↦ isFlasque_iff.mpr (hK n)) I φ hφ

include hK in
/-- **`RⁿΓ(F) ≅ Hⁿ(Γ(K))` for a flasque resolution `K` of `F`.** The isomorphism is induced by
global sections of any comparison map from `K` to an injective resolution of `F`
(`CategoryTheory.Sheaf.rightDerivedΓObjIsoOfIsFlasque_hom_comp_homologyMap`). -/
noncomputable def rightDerivedΓObjIsoOfIsFlasque (n : ℕ) :
    ((Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).rightDerived n).obj F ≅
      (HomologicalComplex.homologyFunctor _ _ n).obj
        (((Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapHomologicalComplex _).obj K) :=
  Functor.rightDerivedObjIsoOfResolution (Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R))
    (isFlasque X _) (fun _ _ ↦ isFlasque_iff.mpr (isFlasque_of_injective_moduleCat _)) isFlasque_X₃
    shortExact_map_Γ_of_isFlasque ι (fun n ↦ isFlasque_iff.mpr (hK n)) n

/-- The isomorphism `rightDerivedΓObjIsoOfIsFlasque` is compatible with the identification of
`RⁿΓ(F)` through any injective resolution `I` of `F` and any comparison map `φ : K ⟶ I`. -/
@[reassoc]
lemma rightDerivedΓObjIsoOfIsFlasque_hom_comp_homologyMap (n : ℕ) (I : InjectiveResolution F)
    (φ : K ⟶ I.cocomplex) (hφ : ι ≫ φ = I.ι) :
    (rightDerivedΓObjIsoOfIsFlasque ι hK n).hom ≫
      (((Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapHomologicalComplex _) ⋙
        HomologicalComplex.homologyFunctor _ _ n).map φ =
          (I.isoRightDerivedObj (Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)) n).hom :=
  Functor.rightDerivedObjIsoOfResolution_hom_comp_homologyMap _ _ _ _ _ ι
    (fun n ↦ isFlasque_iff.mpr (hK n)) n I φ hφ

/-- A functorial flasque resolution computes the native right derived functors of global
sections, naturally in the sheaf. No injectivity of the terms of the resolution is assumed. -/
noncomputable def rightDerivedΓIsoOfIsFlasque
    (K : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R) ⥤
      CochainComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) ℕ)
    (ι : single₀ _ ⟶ K) [∀ F, QuasiIso (ι.app F)]
    (hK : ∀ F n, TopCat.Presheaf.IsFlasque ((K.obj F).X n).obj) (n : ℕ) :
    (Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).rightDerived n ≅
      K ⋙ (Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapHomologicalComplex _ ⋙
        HomologicalComplex.homologyFunctor _ _ n :=
  Functor.rightDerivedIsoOfResolution (Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R))
    (isFlasque X _) (fun _ _ ↦ isFlasque_iff.mpr (isFlasque_of_injective_moduleCat _)) isFlasque_X₃
    shortExact_map_Γ_of_isFlasque K ι (fun F n ↦ isFlasque_iff.mpr (hK F n)) n

/-- Each component of the functorial flasque comparison is the comparison for that resolution.
-/
@[simp]
lemma rightDerivedΓIsoOfIsFlasque_app
    (K : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R) ⥤
      CochainComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) ℕ)
    (ι : single₀ _ ⟶ K) [∀ F, QuasiIso (ι.app F)]
    (hK : ∀ F n, TopCat.Presheaf.IsFlasque ((K.obj F).X n).obj) (n : ℕ)
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) :
    (rightDerivedΓIsoOfIsFlasque K ι hK n).app F =
      rightDerivedΓObjIsoOfIsFlasque (ι.app F) (hK F) n := by
  simp [rightDerivedΓIsoOfIsFlasque, rightDerivedΓObjIsoOfIsFlasque]

end CategoryTheory.Sheaf
