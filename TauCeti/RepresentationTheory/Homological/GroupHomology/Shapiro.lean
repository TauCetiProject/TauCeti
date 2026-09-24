/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Shapiro
public import TauCeti.RepresentationTheory.Homological.Resolution

/-!
# The inverse of Shapiro's isomorphism in homology is the corestriction of the unit

For a subgroup `S ≤ G` and an `S`-representation `A`, Mathlib's homological Shapiro isomorphism
`groupHomology.indIso A n : Hₙ(G, Ind_S^G A) ≅ Hₙ(S, A)` is constructed through `Tor`: it compares
the bar resolution of `S` with the restriction to `S` of the bar resolution of `G`. This file
identifies its inverse with an explicit map. It is the change-of-group map

`Hₙ(S, A) ⟶ Hₙ(G, Ind_S^G A)`

along `S ≤ G`, induced by the unit `A ⟶ Res_S Ind_S^G A`, `a ↦ 1 ⊗ a`, of induction–restriction.
On inhomogeneous chains it sends `a · (s₁, …, sₙ)` to `(1 ⊗ a) · (s₁, …, sₙ)`.

The explicit form is what makes Shapiro's isomorphism usable against the rest of Mathlib's
functoriality: its inverse is a `groupHomology.map`, so it composes with corestriction and
coefficient maps by `groupHomology.map_comp`. In particular, corestriction from `S` to `G` becomes
the map induced by the counit `Ind_S^G Res_S B ⟶ B`, which is what gives the homological transfer
the normalization `cor ∘ res = [G : S]`.

This is the homological counterpart of `TauCeti.groupCohomology.coindIso_hom`.

## Main results

* `TauCeti.groupHomology.indIso_inv`: `(indIso A n).inv` is
  `groupHomology.map S.subtype ((indResAdjunction k S.subtype).unit.app A) n`.
* `TauCeti.groupHomology.indIso_inv_comp_map_counit`: read through Shapiro's isomorphism,
  corestriction from `S` to `G` is the map induced by the counit `Ind_S^G Res_S B ⟶ B`.
* `TauCeti.groupHomology.indIso_inv_naturality`, `TauCeti.groupHomology.indIso_hom_naturality`:
  Shapiro's isomorphism is natural in the coefficients.

## References

* K. S. Brown, *Cohomology of Groups*, Graduate Texts in Mathematics 87, Springer (1982),
  Chapter III, §6 (Shapiro's lemma) and Chapter III, §8.
-/

public section

open CategoryTheory Finsupp Rep

namespace TauCeti.groupHomology

open _root_.groupHomology

universe u

variable {k G : Type u} [CommRing k] [Group G] [DecidableEq G]
  (S : Subgroup G) (A : Rep.{u} k S)

/-- The chain-level form of `indIso_inv`: going from inhomogeneous chains of `S` to the bar complex
of `S`, along the bar resolution to the restricted bar complex of `G`, across the
induction–coinvariants identification, and back to inhomogeneous chains of `G` sends
`a · (s₁, …, sₙ)` to `(1 ⊗ a) · (s₁, …, sₙ)`. -/
private theorem shapiroChains :
    (inhomogeneousChainsIso A).hom ≫
      (((coinvariantsTensor k S).obj A).mapHomologicalComplex _).map
        (TauCeti.Rep.barComplex.resChainMap (k := k) S.subtype) ≫
      (NatIso.mapHomologicalComplex (coinvariantsTensorIndNatIso S.subtype A).symm _).hom.app
        (barComplex k G) ≫
      (inhomogeneousChainsIso (ind S.subtype A)).inv =
    chainsMap S.subtype ((indResAdjunction k S.subtype).unit.app A) := by
  refine HomologicalComplex.hom_ext _ _ fun i => ModuleCat.hom_ext (lhom_ext fun x a => ?_)
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    inhomogeneousChainsIso, HomologicalComplex.Hom.isoOfComponents_hom_f,
    HomologicalComplex.Hom.isoOfComponents_inv_f, Iso.symm_hom, Iso.symm_inv,
    LinearEquiv.toModuleIso_inv, LinearEquiv.toModuleIso_hom, ModuleCat.hom_ofHom,
    LinearEquiv.coe_coe, coinvariantsTensorFreeLEquiv_symm_apply,
    finsuppToCoinvariantsTensorFree_single, Functor.mapHomologicalComplex_map_f,
    TauCeti.Rep.barComplex.resChainMap_f, NatIso.mapHomologicalComplex_hom_app_f,
    coinvariantsTensorIndNatIso_inv_app]
  simp only [Functor.mapHomologicalComplex_obj_X, Functor.postcompose₂_obj_obj_obj_obj,
    MonoidalCategory.curriedTensor_obj_obj, coinvariantsFunctor_obj_carrier, tensor_V, tensor_ρ,
    Functor.postcompose₂_obj_obj_obj_map, MonoidalCategory.curriedTensor_obj_map,
    coinvariantsFunctor_map_hom, hom_whiskerLeft, Representation.Coinvariants.map_mk,
    Representation.IntertwiningMap.lTensor_apply]
  rw [chainsMap_f_single, TauCeti.Rep.barComplex.resHom_single, map_one,
    coinvariantsTensorIndInv_mk_tmul_indMk, coinvariantsTensorMk_apply]
  refine (coinvariantsTensorFreeToFinsupp_mk_tmul_single _ _ _ _ _).trans ?_
  simp [indResAdjunction, indResHomEquiv]

/-- **The inverse of Shapiro's isomorphism in homology is corestriction of the unit.** The
inverse of the isomorphism `Hₙ(G, Ind_S^G A) ≅ Hₙ(S, A)` of `groupHomology.indIso` is the
change-of-group map along `S ≤ G` induced by the unit `A ⟶ Res_S Ind_S^G A`, `a ↦ 1 ⊗ a`,
of induction–restriction. The `DecidableEq G` instance is the one used by Mathlib's `indIso`;
keeping it caller-supplied ensures that this equality rewrites the caller's isomorphism. -/
theorem indIso_inv (n : ℕ) :
    (indIso S A n).inv = map S.subtype ((indResAdjunction k S.subtype).unit.app A) n := by
  -- The comparison, through `Tor`, of the bar resolution of `S` with the restricted bar resolution
  -- of `G` is the map induced on homology by the chain map between them.
  have hcomp : ((barResolution k S).isoLeftDerivedObj ((coinvariantsTensor k S).obj A) n).inv ≫
      (((resFunctor S.subtype).mapProjectiveResolution (barResolution k G)).isoLeftDerivedObj
        ((coinvariantsTensor k S).obj A) n).hom =
      HomologicalComplex.homologyMap ((((coinvariantsTensor k S).obj A).mapHomologicalComplex _).map
        (TauCeti.Rep.barComplex.resChainMap S.subtype)) n := by
    have hnat := ProjectiveResolution.isoLeftDerivedObj_hom_naturality (𝟙 _)
      (barResolution k S) ((resFunctor S.subtype).mapProjectiveResolution (barResolution k G))
      (TauCeti.Rep.barComplex.resChainMap S.subtype)
      ((TauCeti.Rep.barComplex.resChainMap_f_zero_comp_π S.subtype).trans
        (Category.comp_id _).symm) ((coinvariantsTensor k S).obj A) n
    rw [CategoryTheory.Functor.map_id, Category.id_comp] at hnat
    have hmap :
        (((coinvariantsTensor k S).obj A).mapHomologicalComplex _ ⋙
          HomologicalComplex.homologyFunctor _ _ n).map
            (TauCeti.Rep.barComplex.resChainMap S.subtype) =
          HomologicalComplex.homologyMap
            ((((coinvariantsTensor k S).obj A).mapHomologicalComplex _).map
              (TauCeti.Rep.barComplex.resChainMap S.subtype)) n := by
      rw [CategoryTheory.Functor.comp_map, HomologicalComplex.homologyFunctor_map]
    exact (Iso.inv_comp_eq _).2 (hnat.trans (congrArg (_ ≫ ·) hmap))
  -- `indIso` is by definition the homology of the Shapiro chain isomorphism preceded by that
  -- comparison and by the identification of inhomogeneous chains with the bar complex. Mathlib's
  -- definition resolves the trivial representation of `S` both by `barResolution k S` and by the
  -- restriction of `barResolution k G`, so its intermediate objects have two syntactic forms and
  -- rewriting inside it is not type-correct; the steps below are applied as terms instead. The
  -- explicit universes on `ind` avoid a slow universe unification (as in Mathlib's `indIso`).
  have e : (indIso S A n).inv =
      HomologicalComplex.homologyMap (inhomogeneousChainsIso A).hom n ≫
      (((barResolution k S).isoLeftDerivedObj ((coinvariantsTensor k S).obj A) n).inv ≫
      (((resFunctor S.subtype).mapProjectiveResolution (barResolution k G)).isoLeftDerivedObj
        ((coinvariantsTensor k S).obj A) n).hom) ≫
      HomologicalComplex.homologyMap
        ((NatIso.mapHomologicalComplex (coinvariantsTensorIndNatIso S.subtype A).symm _).hom.app
          (barComplex k G) ≫ (inhomogeneousChainsIso (ind.{u, u, u, u} S.subtype A)).inv) n := rfl
  refine e.trans ((congrArg (fun t => HomologicalComplex.homologyMap
    (inhomogeneousChainsIso A).hom n ≫ t ≫ HomologicalComplex.homologyMap
      ((NatIso.mapHomologicalComplex (coinvariantsTensorIndNatIso S.subtype A).symm _).hom.app
        (barComplex k G) ≫ (inhomogeneousChainsIso (ind.{u, u, u, u} S.subtype A)).inv) n)
    hcomp).trans ?_)
  exact ((congrArg (_ ≫ ·) (HomologicalComplex.homologyMap_comp _ _ n).symm).trans
    (HomologicalComplex.homologyMap_comp _ _ n).symm).trans
    (congrArg (HomologicalComplex.homologyMap · n) (shapiroChains S A))

/-- **Corestriction through Shapiro's lemma.** For a `G`-representation `B`, the inverse of
Shapiro's isomorphism `Hₙ(G, Ind_S^G Res_S B) ≅ Hₙ(S, Res_S B)` followed by the map induced by the
counit `Ind_S^G Res_S B ⟶ B` of induction–restriction is corestriction
`Hₙ(S, Res_S B) ⟶ Hₙ(G, B)`. -/
@[reassoc]
theorem indIso_inv_comp_map_counit (B : Rep.{u} k G) (n : ℕ) :
    (indIso S (res S.subtype B) n).inv ≫
        map (MonoidHom.id G) ((indResAdjunction k S.subtype).counit.app B) n =
      map S.subtype (𝟙 (res S.subtype B)) n := by
  rw [indIso_inv, ← map_comp, (indResAdjunction k S.subtype).right_triangle_components B]
  -- `(MonoidHom.id G).comp S.subtype` is `S.subtype` by definition.
  rfl

/-- **The inverse of Shapiro's isomorphism is natural in the coefficients**: for a morphism
`φ : A ⟶ B` of `S`-representations, it intertwines the maps induced by `φ` and by `Ind_S^G φ`. -/
@[reassoc]
theorem indIso_inv_naturality {B : Rep.{u} k S} (φ : A ⟶ B) (n : ℕ) :
    map (MonoidHom.id S) φ n ≫ (indIso S B n).inv =
      (indIso S A n).inv ≫ map (MonoidHom.id G) ((indFunctor k S.subtype).map φ) n := by
  rw [indIso_inv, indIso_inv, ← map_comp, ← map_comp]
  -- Comparing the underlying linear maps through `map_congr` avoids unifying the free universe
  -- of `indResAdjunction` against `map`'s arguments, which costs seconds.
  refine map_congr rfl ?_ n
  exact congrArg (·.hom.toLinearMap) ((indResAdjunction k S.subtype).unit.naturality φ)

/-- **Shapiro's isomorphism is natural in the coefficients**: `indIso_inv_naturality` for
`(indIso S A n).hom`. -/
@[reassoc]
theorem indIso_hom_naturality {B : Rep.{u} k S} (φ : A ⟶ B) (n : ℕ) :
    map (MonoidHom.id G) ((indFunctor k S.subtype).map φ) n ≫ (indIso S B n).hom =
      (indIso S A n).hom ≫ map (MonoidHom.id S) φ n := by
  rw [← Iso.inv_comp_eq, ← indIso_inv_naturality_assoc, Iso.inv_hom_id, Category.comp_id]

end TauCeti.groupHomology
