/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import TauCeti.Algebra.Homology.LinearYoneda
import TauCeti.Algebra.Homology.Ext.ProjectiveResolution

/-!
# Group cohomology from a projective resolution, through a comparison map

For a projective resolution `P` of the trivial representation `k` of `G`, Mathlib's
`groupCohomologyIso A n P : Hⁿ(G, A) ≅ Hⁿ(Hom(P, A))` is defined through `Ext`. This file makes its
inverse explicit: given a chain map `φ` from the bar resolution of `G` to `P` lying over the
identity of `k`, it is the map induced on cohomology by

`Hom(P, A) ⟶ Hom(bar, A) ≅ Fun(Gⁿ, A)`,

precomposition with `φ` followed by the identification of `Hom(bar, A)` with the inhomogeneous
cochains. This is how an explicit comparison map computes a cohomology isomorphism that Mathlib
constructs abstractly, such as Shapiro's isomorphism or the periodicity isomorphism of a finite
cyclic group.

The explicit form also shows that `groupCohomologyIso A n P` is natural in the coefficients `A`:
it carries Mathlib's map `groupCohomology.map (MonoidHom.id G) φ n` induced by `φ : A ⟶ B` to the
map on the cohomology of `Hom(P, -)` given by postcomposition with `φ`.

## Main results

* `TauCeti.Rep.groupCohomologyIso_inv_eq_homologyMap`: the inverse of `groupCohomologyIso A n P` is
  the map on cohomology induced by a comparison map from the bar resolution to `P`.
* `TauCeti.Rep.inhomogeneousCochainsIso_inv_naturality`: the identification of `Hom(bar, A)` with
  the inhomogeneous cochains is natural in `A`.
* `TauCeti.Rep.groupCohomologyIso_hom_naturality`, `TauCeti.Rep.groupCohomologyIso_inv_naturality`:
  `groupCohomologyIso A n P` is natural in `A`.

## References

* K. S. Brown, *Cohomology of Groups*, Graduate Texts in Mathematics 87, Springer (1982),
  Chapter I, §7 (comparison of projective resolutions).
-/

public section

open CategoryTheory

namespace TauCeti.Rep

universe u

variable {k G : Type u} [CommRing k] [Group G] (A : Rep.{u} k G)

/-- **Group cohomology from a projective resolution, through a comparison map.** For a projective
resolution `P` of the trivial representation `k` and a chain map `φ` from the bar resolution to `P`
lying over the identity of `k`, the inverse of `groupCohomologyIso A n P` is the map on cohomology
induced by precomposition with `φ`, followed by the identification of `Hom(bar, A)` with the
inhomogeneous cochains. -/
theorem groupCohomologyIso_inv_eq_homologyMap (P : ProjectiveResolution (Rep.trivial k G k))
    (φ : (Rep.barResolution k G).complex ⟶ P.complex)
    (comm : φ.f 0 ≫ P.π.f 0 = (Rep.barResolution k G).π.f 0) (n : ℕ) :
    (groupCohomologyIso A n P).inv = HomologicalComplex.homologyMap
      ((HomologicalComplex.unopFunctor _ _).map
        ((((linearYoneda k (Rep k G)).obj A).rightOp.mapHomologicalComplex _).map φ).op ≫
        (groupCohomology.inhomogeneousCochainsIso A).inv) n := by
  have hext := ProjectiveResolution.isoExt_hom_comp_homologyMap (R := k)
    (Rep.barResolution k G) P φ comm n A
  have hinhom : (isoOfQuasiIsoAt
      (HomotopyEquiv.ofIso (groupCohomology.inhomogeneousCochainsIso A)).hom n).inv =
      HomologicalComplex.homologyMap (groupCohomology.inhomogeneousCochainsIso A).inv n :=
    Iso.inv_ext ((HomologicalComplex.homologyMap_comp _ _ n).symm.trans
      ((congrArg (HomologicalComplex.homologyMap · n)
        (groupCohomology.inhomogeneousCochainsIso A).hom_inv_id).trans
        (HomologicalComplex.homologyMap_id _ n)))
  -- `groupCohomologyIso` is `groupCohomologyIsoExt` followed by the `Ext` computation from `P`,
  -- and `groupCohomologyIsoExt` is the `Ext` computation from the bar resolution followed by the
  -- inhomogeneous cochain isomorphism. The unfolding is taken from the `Iso.trans` lemmas, not
  -- restated and proved by `rfl`: restated, its `Ext` objects carry fresh instance terms and the
  -- kernel unfolds `Ext` to match.
  have h₁ : (groupCohomologyIso A n P).inv = _ := Iso.trans_inv _ _
  have h₂ : (groupCohomologyIsoExt A n).inv = _ := Iso.trans_inv _ _
  rw [h₁, h₂, Iso.symm_inv, hinhom]
  exact ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ _) ((Iso.inv_comp_eq _).2 hext.symm))).trans
      (HomologicalComplex.homologyMap_comp _ _ n).symm

variable {A} in
/-- The identification of the inhomogeneous cochains with `Hom(bar, -)` is natural in the
coefficients: postcomposing a cochain on the bar resolution with `φ : A ⟶ B` corresponds to
applying `φ` to the values of an inhomogeneous cochain, Mathlib's
`groupCohomology.cochainsMap (MonoidHom.id G) φ`. -/
@[reassoc]
theorem inhomogeneousCochainsIso_inv_naturality {B : Rep.{u} k G} (φ : A ⟶ B) :
    (groupCohomology.inhomogeneousCochainsIso A).inv ≫
        groupCohomology.cochainsMap (MonoidHom.id G) φ =
      (Rep.barComplex k G).linearYonedaObjMap k φ ≫
        (groupCohomology.inhomogeneousCochainsIso B).inv := by
  ext i (g : (Rep.barComplex k G).X i ⟶ A) x
  -- The inverse of `inhomogeneousCochainsIso` is `Rep.freeLiftLEquiv`, evaluation on basis
  -- elements, and Mathlib's `cochainsMap` applies `φ` to values, so both sides evaluate `g ≫ φ`
  -- on the basis element of `x`; the left side does so by definition. The isomorphism is built by
  -- `isoOfComponents` between complexes whose shapes `up ℕ` and `(down ℕ).symm` agree only by
  -- unfolding, so its simp lemmas do not fire on these components.
  exact congrArg (fun c ↦ ((groupCohomology.inhomogeneousCochainsIso B).inv.f i).hom c x)
    ((Rep.barComplex k G).linearYonedaObjMap_f_hom_apply k φ i g).symm

variable {A} in
/-- **Group cohomology from a projective resolution is natural in the coefficients**, inverse
form: for a morphism `φ : A ⟶ B` of representations and a projective resolution `P` of the trivial
representation `k`, the inverses of the identifications `groupCohomologyIso` carry the map on the
cohomology of `Hom(P, -)` given by postcomposition with `φ` to Mathlib's map
`groupCohomology.map (MonoidHom.id G) φ n`. -/
@[reassoc]
theorem groupCohomologyIso_inv_naturality {B : Rep.{u} k G} (φ : A ⟶ B)
    (P : ProjectiveResolution (Rep.trivial k G k)) (n : ℕ) :
    HomologicalComplex.homologyMap (P.complex.linearYonedaObjMap k φ) n ≫
        (groupCohomologyIso B n P).inv =
      (groupCohomologyIso A n P).inv ≫ groupCohomology.map (MonoidHom.id G) φ n := by
  have hβ := (ProjectiveResolution.lift_commutes_zero (𝟙 _) (Rep.barResolution k G) P).trans
    (Category.comp_id _)
  -- On cochains, postcomposition with `φ` commutes with precomposition with the comparison map
  -- from the bar resolution to `P`, and then with the identification of `Hom(bar, -)` with the
  -- inhomogeneous cochains.
  have key : P.complex.linearYonedaObjMap k φ ≫
      (TauCeti.ChainComplex.linearYonedaFunctor k B).map
        (ProjectiveResolution.lift (𝟙 _) (Rep.barResolution k G) P).op ≫
      (groupCohomology.inhomogeneousCochainsIso B).inv =
    ((TauCeti.ChainComplex.linearYonedaFunctor k A).map
        (ProjectiveResolution.lift (𝟙 _) (Rep.barResolution k G) P).op ≫
      (groupCohomology.inhomogeneousCochainsIso A).inv) ≫
      groupCohomology.cochainsMap (MonoidHom.id G) φ :=
    (ChainComplex.linearYonedaObjMap_comp_linearYonedaFunctor_map_assoc k
      (ProjectiveResolution.lift (𝟙 _) (Rep.barResolution k G) P) φ
      (groupCohomology.inhomogeneousCochainsIso B).inv).trans <|
    (congrArg (_ ≫ ·) (inhomogeneousCochainsIso_inv_naturality φ).symm).trans
      (Category.assoc _ _ _).symm
  rw [groupCohomologyIso_inv_eq_homologyMap A P _ hβ,
    groupCohomologyIso_inv_eq_homologyMap B P _ hβ]
  exact (HomologicalComplex.homologyMap_comp _ _ n).symm.trans
    ((congrArg (HomologicalComplex.homologyMap · n) key).trans
      (HomologicalComplex.homologyMap_comp _ _ n))

variable {A} in
/-- **Group cohomology from a projective resolution is natural in the coefficients**: for a
morphism `φ : A ⟶ B` of representations and a projective resolution `P` of the trivial
representation `k`, the identifications `groupCohomologyIso` carry Mathlib's map
`groupCohomology.map (MonoidHom.id G) φ n : Hⁿ(G, A) ⟶ Hⁿ(G, B)` to the map on the cohomology of
`Hom(P, -)` given by postcomposition with `φ`. -/
@[reassoc]
theorem groupCohomologyIso_hom_naturality {B : Rep.{u} k G} (φ : A ⟶ B)
    (P : ProjectiveResolution (Rep.trivial k G k)) (n : ℕ) :
    groupCohomology.map (MonoidHom.id G) φ n ≫ (groupCohomologyIso B n P).hom =
      (groupCohomologyIso A n P).hom ≫
        HomologicalComplex.homologyMap (P.complex.linearYonedaObjMap k φ) n := by
  rw [← Iso.inv_comp_eq, ← Category.assoc, ← Iso.eq_comp_inv,
    groupCohomologyIso_inv_naturality]

end TauCeti.Rep
