/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.Addition
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.BaseChange.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.Neg
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Addition.Pointed

/-!
# The group law of an elliptic curve commutes with base change

Let `E` be an elliptic curve over a scheme `S` and `E'` an elliptic curve over a scheme `S'`. A
morphism `g : E' ⟶ E` lying over `f : S' ⟶ S` such that the square formed by `g`, `f` and the two
structure morphisms is a pullback square, and carrying the zero section of `E'` to that of `E`,
exhibits `E'` as the base change of `E` along `f`. This file shows that such a morphism carries
the addition morphism of `E'` to that of `E`
(`EllipticCurveGeom.addition_comp_of_isPullback`) and the negation morphism of `E'` to that of `E`
(`EllipticCurveGeom.neg_comp_of_isPullback`). In particular the group law of the base change
`E.baseChange f` is the base change of the group law of `E`, for every morphism `f : S' ⟶ S`
(`EllipticCurveGeom.addition_baseChangeIso_hom_fst` and
`EllipticCurveGeom.neg_baseChangeIso_hom_fst`).

The addition morphism of `E'` is characterised by its restrictions to the charts of any pointed
Weierstrass atlas (`EllipticCurveGeom.eq_addition_of_atlas`). The charts of `E'` whose bases
map over `f` into bases of charts of `E` form an atlas of `E'`
(`EllipticCurveGeom.exists_chart_comp_baseMap`). On such a chart `k`, lying over a chart `c` of
`E`, the morphism `g` restricts to a morphism from the restriction of `E'` to the base of `k` to
the restriction of `E` to the base of `c` (`PointedWeierstrassChart.carrierMap`). Through the
isomorphisms with the projective models of the equations of `k` and `c`, it is a base change
square of projective models carrying the zero section to the zero section
(`PointedWeierstrassChart.modelMap`), and the Bosma–Lenstra addition morphism and the negation
morphism commute with such squares
(`WeierstrassCurve.additionMorphism_comp_of_isPullback` and
`WeierstrassCurve.projModelNeg_comp_of_isPullback`).

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.addition_comp_of_isPullback` and
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.neg_comp_of_isPullback`: a pointed morphism of
  elliptic curves forming a pullback square over a morphism of bases carries the addition and
  negation morphisms of its source to those of its target.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.addition_baseChangeIso_hom_fst` and
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.neg_baseChangeIso_hom_fst`: the projection from the
  base change `E.baseChange f` to `E` carries the addition morphism and the negation morphism of
  `E.baseChange f` to those of `E`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.1–2.2.
* P. Deligne and M. Rapoport, *Les schémas de modules de courbes elliptiques*, II.1.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

/-! ### The group law on charts over a base change square -/

namespace PointedWeierstrassChart

variable {S X S' X' : Scheme.{u}} {π : X ⟶ S} {zero : S ⟶ X} {π' : X' ⟶ S'} {zero' : S' ⟶ X'}
  {g : X' ⟶ X} {f : S' ⟶ S} (hg : IsPullback g π' π f)
  {k : PointedWeierstrassChart π' zero'} {c : PointedWeierstrassChart π zero} {h : k.base ⟶ c.base}
  (hh : h ≫ c.baseMap = k.baseMap ≫ f)

-- The morphism `carrierMap hg hh` carries the addition of `k` to the addition of `c`.
@[reassoc]
private theorem addition_carrierMap (h0 : zero' ≫ g = f ≫ zero) :
    k.addition ≫ carrierMap hg hh =
      pullback.map _ _ _ _ (carrierMap hg hh) (carrierMap hg hh) h
        (carrierMap_toBase hg hh).symm (carrierMap_toBase hg hh).symm ≫ c.addition := by
  have hk : k.addition ≫ carrierMap hg hh ≫ c.modelIso.hom =
      pullback.map _ _ _ _ k.modelIso.hom k.modelIso.hom k.baseIso.hom k.modelIso_over.symm
        k.modelIso_over.symm ≫ k.equation.additionMorphism ≫ modelMap hg hh := by
    rw [← modelIso_hom_modelMap, addition_modelIso_hom_assoc]
  rw [← cancel_mono c.modelIso.hom, Category.assoc, Category.assoc, addition_modelIso_hom, hk,
    WeierstrassCurve.additionMorphism_comp_of_isPullback (isPullback_modelMap hg hh)
      (projModelZero_modelMap hg hh h0)]
  simp only [← Category.assoc]
  congr 1
  apply pullback.hom_ext <;> simp [modelIso_hom_modelMap]

-- The morphism `carrierMap hg hh` carries the negation of `k` to the negation of `c`.
@[reassoc]
private theorem neg_carrierMap (h0 : zero' ≫ g = f ≫ zero) :
    k.neg ≫ carrierMap hg hh = carrierMap hg hh ≫ c.neg := by
  rw [← cancel_mono c.modelIso.hom, Category.assoc, Category.assoc, neg_modelIso_hom,
    ← modelIso_hom_modelMap, ← modelIso_hom_modelMap_assoc, neg_modelIso_hom_assoc,
    WeierstrassCurve.projModelNeg_comp_of_isPullback (isPullback_modelMap hg hh)
      (projModelZero_modelMap hg hh h0)]

end PointedWeierstrassChart

/-! ### Pointed pullback squares of elliptic curves -/

namespace EllipticCurveGeom

open PointedWeierstrassChart

variable {S S' : Scheme.{u}} {E : EllipticCurveGeom S} {E' : EllipticCurveGeom S'} {f : S' ⟶ S}

variable {g : E'.carrier ⟶ E.carrier} (hg : IsPullback g E'.structureMap E.structureMap f)
  (h0 : E'.zero ≫ g = f ≫ E.zero)

include h0 in
-- On the restriction of `E' ×_{S'} E'` to the base of a chart `k` of `E'` lying over a chart `c`
-- of `E`, the composite of `g × g` with the addition morphism of `E` is the addition of `k`
-- followed by `g`.
private theorem pullbackMap_comp_addition {k : PointedWeierstrassChart E'.structureMap E'.zero}
    {c : PointedWeierstrassChart E.structureMap E.zero} {h : k.base ⟶ c.base}
    (hh : h ≫ c.baseMap = k.baseMap ≫ f) :
    pullback.map _ _ _ _ k.toTotal k.toTotal k.baseMap k.isPullback.w.symm k.isPullback.w.symm ≫
        pullback.map _ _ _ _ g g f hg.w.symm hg.w.symm ≫ E.addition =
      k.addition ≫ k.toTotal ≫ g := by
  -- `g × g` restricts to the morphism induced by `g` between the restrictions to the chart bases
  have hm : pullback.map _ _ _ _ k.toTotal k.toTotal k.baseMap k.isPullback.w.symm
      k.isPullback.w.symm ≫ pullback.map _ _ _ _ g g f hg.w.symm hg.w.symm =
      pullback.map _ _ _ _ (carrierMap hg hh) (carrierMap hg hh) h (carrierMap_toBase _ _).symm
        (carrierMap_toBase _ _).symm ≫
      pullback.map _ _ _ _ c.toTotal c.toTotal c.baseMap c.isPullback.w.symm
        c.isPullback.w.symm := by
    apply pullback.hom_ext <;> simp [carrierMap_toTotal]
  rw [reassoc_of% hm, pullbackMap_addition, ← addition_carrierMap_assoc hg hh h0,
    carrierMap_toTotal]

include hg h0 in
-- On the restriction of `E'` to the base of a chart `k` of `E'` lying over a chart `c` of `E`, the
-- composite of `g` with the negation morphism of `E` is the negation of `k` followed by `g`.
private theorem toTotal_comp_neg {k : PointedWeierstrassChart E'.structureMap E'.zero}
    {c : PointedWeierstrassChart E.structureMap E.zero} {h : k.base ⟶ c.base}
    (hh : h ≫ c.baseMap = k.baseMap ≫ f) :
    k.toTotal ≫ g ≫ E.neg = k.neg ≫ k.toTotal ≫ g := by
  rw [← carrierMap_toTotal_assoc hg hh, toTotal_neg, ← neg_carrierMap_assoc hg hh h0,
    carrierMap_toTotal]

include h0 in
/-- **The addition morphism commutes with base change.** Let `g : E' ⟶ E` be a morphism of
elliptic curves lying over `f : S' ⟶ S`, such that the square formed by `g`, `f` and the structure
morphisms is a pullback square, and carrying the zero section of `E'` to that of `E`. Then `g`
carries the addition morphism of `E'` to that of `E`. -/
@[reassoc]
theorem addition_comp_of_isPullback :
    E'.addition ≫ g = pullback.map _ _ _ _ g g f hg.w.symm hg.w.symm ≫ E.addition := by
  -- charts `k s` of `E'` around each point `s`, with bases mapping over `f` into charts of `E`
  choose k c h hh hk using E.exists_chart_comp_baseMap E' f
  -- the morphism `E' ×_{S'} E' ⟶ E'` whose composite with `g` is the right-hand side
  let μ := hg.lift (pullback.map _ _ _ _ g g f hg.w.symm hg.w.symm ≫ E.addition)
    (pullback.fst _ _ ≫ E'.structureMap) (by simp [hg.w])
  suffices hμ : μ = E'.addition by rw [← hμ, hg.lift_fst]
  refine E'.eq_addition_of_atlas ⟨S', k, fun s ↦ ⟨s, hk s⟩⟩ fun x ↦ hg.hom_ext ?_ ?_
  · simpa only [μ, Category.assoc, IsPullback.lift_fst] using pullbackMap_comp_addition hg h0 (hh x)
  · simp [μ, (k x).isPullback.w]

include hg h0 in
/-- **The negation morphism commutes with base change.** Let `g : E' ⟶ E` be a morphism of
elliptic curves lying over `f : S' ⟶ S`, such that the square formed by `g`, `f` and the structure
morphisms is a pullback square, and carrying the zero section of `E'` to that of `E`. Then `g`
carries the negation morphism of `E'` to that of `E`. -/
@[reassoc]
theorem neg_comp_of_isPullback : E'.neg ≫ g = g ≫ E.neg := by
  -- charts `k s` of `E'` around each point `s`, with bases mapping over `f` into charts of `E`
  choose k c h hh hk using E.exists_chart_comp_baseMap E' f
  -- the morphism `E' ⟶ E'` whose composite with `g` is the right-hand side
  let ν := hg.lift (g ≫ E.neg) E'.structureMap (by simp [hg.w])
  suffices hν : ν = E'.neg by rw [← hν, hg.lift_fst]
  refine E'.eq_neg_of_atlas ⟨S', k, fun s ↦ ⟨s, hk s⟩⟩ fun x ↦ hg.hom_ext ?_ ?_
  · simpa only [ν, Category.assoc, IsPullback.lift_fst] using toTotal_comp_neg hg h0 (hh x)
  · simp [ν, (k x).isPullback.w]

/-! ### The base change of an elliptic curve -/

variable (E) (f : S' ⟶ S)

/-- **The addition morphism of a base change.** The projection from the base change
`E.baseChange f` to `E` carries the addition morphism of `E.baseChange f` to that of `E`. -/
@[reassoc (attr := simp)]
theorem addition_baseChangeIso_hom_fst :
    (E.baseChange f).addition ≫ (E.baseChangeIso f).hom ≫ pullback.fst E.structureMap f =
      pullback.map _ _ _ _ ((E.baseChangeIso f).hom ≫ pullback.fst E.structureMap f)
        ((E.baseChangeIso f).hom ≫ pullback.fst E.structureMap f) f
        (E.isPullback_baseChange f).w.symm (E.isPullback_baseChange f).w.symm ≫ E.addition :=
  addition_comp_of_isPullback (E.isPullback_baseChange f) (by simp)

/-- **The negation morphism of a base change.** The projection from the base change
`E.baseChange f` to `E` carries the negation morphism of `E.baseChange f` to that of `E`. -/
@[reassoc (attr := simp)]
theorem neg_baseChangeIso_hom_fst :
    (E.baseChange f).neg ≫ (E.baseChangeIso f).hom ≫ pullback.fst E.structureMap f =
      (E.baseChangeIso f).hom ≫ pullback.fst E.structureMap f ≫ E.neg := by
  rw [neg_comp_of_isPullback (E.isPullback_baseChange f) (by simp), Category.assoc]

end EllipticCurveGeom

end TauCeti.AlgebraicGeometry
