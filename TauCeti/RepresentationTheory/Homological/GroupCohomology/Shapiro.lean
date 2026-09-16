/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
public import TauCeti.Algebra.Homology.Ext.ProjectiveResolution
public import TauCeti.RepresentationTheory.Homological.Resolution

/-!
# Shapiro's isomorphism is restriction followed by evaluation

For a subgroup `S ≤ G` and an `S`-representation `A`, Mathlib's Shapiro isomorphism
`groupCohomology.coindIso A n : Hⁿ(G, Coind_S^G A) ≅ Hⁿ(S, A)` is constructed through `Ext`: it
compares the bar resolution of `S` with the restriction to `S` of the bar resolution of `G`. This
file identifies it with an explicit map. It is the change-of-group map

`Hⁿ(G, Coind_S^G A) ⟶ Hⁿ(S, Res_S Coind_S^G A) ⟶ Hⁿ(S, A)`,

restriction to `S` followed by the counit `Res_S Coind_S^G A ⟶ A` of restriction–coinduction,
which evaluates a function `G → A` at `1`. On inhomogeneous cochains it sends
`c : Gⁿ → Coind_S^G A` to `(s₁, …, sₙ) ↦ c (s₁, …, sₙ) 1`.

The explicit form is what makes Shapiro's isomorphism usable against the rest of Mathlib's
functoriality: it is a `groupCohomology.map`, so it composes with restriction and coefficient maps
by `groupCohomology.map_comp`. In particular it is what identifies restriction with the unit of the
adjunction under Shapiro's lemma, the step that turns the counit of the finite-index adjunction into
a corestriction satisfying `cor ∘ res = [G : S]`.

## Main results

* `TauCeti.groupCohomology.coindIso_hom`: `(coindIso A n).hom` is
  `groupCohomology.map S.subtype ((resCoindAdjunction k S.subtype).counit.app A) n`.
* `TauCeti.groupCohomology.coindIso_hom_naturality`: consequently, Shapiro's isomorphism is natural
  in the coefficients.
* `TauCeti.groupCohomology.map_unit_comp_coindIso_hom`: read through Shapiro's isomorphism,
  restriction to `S` is the map induced by the unit `B ⟶ Coind_S^G Res_S B`.

## References

* K. S. Brown, *Cohomology of Groups*, Graduate Texts in Mathematics 87, Springer (1982),
  Chapter III, §6 (Shapiro's lemma) and Chapter III, §8.
-/

public section

open CategoryTheory Finsupp Rep

namespace TauCeti.groupCohomology

open _root_.groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G] (S : Subgroup G) (A : Rep.{u} k S)

/-- The inhomogeneous-cochain map underlying Shapiro's isomorphism, evaluated on a cochain and a
tuple: going from `Gⁿ → Coind_S^G A` to `Hom_G(Gⁿ ⊗ k[G], Coind_S^G A)`, to
`Hom_S(Res_S (Gⁿ ⊗ k[G]), A)`, to `Hom_S(Sⁿ ⊗ k[S], A)` along the bar resolution of `S`, and back to
`Sⁿ → A` gives `c ↦ ((s₁, …, sₙ) ↦ c (s₁, …, sₙ) 1)`. -/
private theorem shapiroCochains_apply (i : ℕ) (c : (Fin i → G) → coind S.subtype A)
    (s : Fin i → S) :
    ((inhomogeneousCochainsIso A).inv.f i).hom
      ((((HomologicalComplex.unopFunctor _ _).map
        ((((linearYoneda k (Rep k S)).obj A).rightOp.mapHomologicalComplex _).map
          (TauCeti.Rep.barComplex.resChainMap (k := k) S.subtype)).op).f i).hom
      (((linearYonedaObjResProjectiveResolutionIso (barResolution k G) A).inv.f i).hom
      (((inhomogeneousCochainsIso (coind S.subtype A)).hom.f i).hom c))) s =
      (c (S.subtype ∘ s)).1 1 := by
  -- Unfolding the two cochain isomorphisms, the value is the Shapiro adjunct of `freeLift c`
  -- evaluated on the image of the basis element `s` under the bar resolution along `S ≤ G`.
  refine Eq.trans (b := ((resCoindHomEquiv.{u} S.subtype (free k G (Fin i → G)) A).symm
    (freeLift k G (coind S.subtype A) c)).hom
      (((TauCeti.Rep.barComplex.resChainMap (k := k) S.subtype).f i).hom
        (single s (MonoidAlgebra.single 1 1)))) rfl ?_
  rw [TauCeti.Rep.barComplex.resChainMap_f, TauCeti.Rep.barComplex.resHom_single]
  simp

/-- The chain-level form of `coindIso_hom`. -/
private theorem shapiroCochains :
    (inhomogeneousCochainsIso (coind S.subtype A)).hom ≫
      (linearYonedaObjResProjectiveResolutionIso (barResolution k G) A).inv ≫
      (HomologicalComplex.unopFunctor _ _).map
        ((((linearYoneda k (Rep k S)).obj A).rightOp.mapHomologicalComplex _).map
          (TauCeti.Rep.barComplex.resChainMap (k := k) S.subtype)).op ≫
      (inhomogeneousCochainsIso A).inv =
    cochainsMap S.subtype ((resCoindAdjunction k S.subtype).counit.app A) :=
  HomologicalComplex.hom_ext _ _ fun i => ModuleCat.hom_ext (LinearMap.ext fun c =>
    funext fun s => shapiroCochains_apply S A i c s)

/-- **Shapiro's isomorphism is restriction followed by evaluation at `1`.** The isomorphism
`Hⁿ(G, Coind_S^G A) ≅ Hⁿ(S, A)` of `groupCohomology.coindIso` is the change-of-group map along
`S ≤ G` induced by the counit `Res_S Coind_S^G A ⟶ A` of restriction–coinduction. -/
theorem coindIso_hom (n : ℕ) :
    (coindIso A n).hom = map S.subtype ((resCoindAdjunction k S.subtype).counit.app A) n := by
  have hext := ProjectiveResolution.isoExt_hom_comp_homologyMap (R := k) (barResolution k S)
    ((resFunctor S.subtype).mapProjectiveResolution (barResolution k G))
    (TauCeti.Rep.barComplex.resChainMap S.subtype)
    (TauCeti.Rep.barComplex.resChainMap_f_zero_comp_π S.subtype) n A
  have hinhom : (isoOfQuasiIsoAt (HomotopyEquiv.ofIso (inhomogeneousCochainsIso A)).hom n).inv =
      HomologicalComplex.homologyMap (inhomogeneousCochainsIso A).inv n :=
    Iso.inv_ext ((HomologicalComplex.homologyMap_comp _ _ n).symm.trans
      ((congrArg (HomologicalComplex.homologyMap · n) (inhomogeneousCochainsIso A).hom_inv_id).trans
        (HomologicalComplex.homologyMap_id _ n)))
  -- `coindIso` is by definition the homology of the Shapiro cochain isomorphism followed by the
  -- comparison, through `Ext`, of the restricted bar resolution of `G` with the bar resolution
  -- of `S`.
  have e : (coindIso A n).hom = HomologicalComplex.homologyMap
      ((inhomogeneousCochainsIso (coind S.subtype A)).hom ≫
        (linearYonedaObjResProjectiveResolutionIso (barResolution k G) A).inv) n ≫
      (((resFunctor S.subtype).mapProjectiveResolution (barResolution k G)).isoExt n A).inv ≫
      ((barResolution k S).isoExt n A).hom ≫
      (isoOfQuasiIsoAt (HomotopyEquiv.ofIso (inhomogeneousCochainsIso A)).hom n).inv := rfl
  rw [e, hinhom]
  exact (congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ _) ((Iso.inv_comp_eq _).2 hext.symm)))).trans
    ((congrArg (_ ≫ ·) (HomologicalComplex.homologyMap_comp _ _ n).symm).trans
    ((HomologicalComplex.homologyMap_comp _ _ n).symm.trans
    (congrArg (HomologicalComplex.homologyMap · n)
      ((Category.assoc _ _ _).trans (shapiroCochains S A)))))

/-- **Shapiro's isomorphism is natural in the coefficients**: for a morphism `φ : A ⟶ B` of
`S`-representations, it intertwines the maps induced by `Coind_S^G φ` and by `φ`. -/
@[reassoc]
theorem coindIso_hom_naturality {B : Rep.{u} k S} (φ : A ⟶ B) (n : ℕ) :
    map (MonoidHom.id G) ((coindFunctor k S.subtype).map φ) n ≫ (coindIso B n).hom =
      (coindIso A n).hom ≫ map (MonoidHom.id S) φ n := by
  rw [coindIso_hom, coindIso_hom, ← map_comp, ← map_comp]
  exact map_congr rfl (congrArg (fun f => f.hom.toLinearMap)
    ((resCoindAdjunction k S.subtype).counit.naturality φ)).symm n

/-- **Restriction through Shapiro's lemma.** For a `G`-representation `B`, the map induced by the
unit `B ⟶ Coind_S^G Res_S B` of restriction–coinduction, followed by Shapiro's isomorphism, is
restriction `Hⁿ(G, B) ⟶ Hⁿ(S, Res_S B)`. -/
theorem map_unit_comp_coindIso_hom (B : Rep.{u} k G) (n : ℕ) :
    map (MonoidHom.id G) ((resCoindAdjunction k S.subtype).unit.app B) n ≫
      (coindIso (res S.subtype B) n).hom = map S.subtype (𝟙 (res S.subtype B)) n := by
  rw [coindIso_hom, ← map_comp, (resCoindAdjunction k S.subtype).left_triangle_components B]
  -- `(MonoidHom.id G).comp S.subtype` is `S.subtype` by definition.
  rfl

end TauCeti.groupCohomology
