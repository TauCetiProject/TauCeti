/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.Glue
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Neg

/-!
# The negation morphism of an elliptic curve over a scheme

Let `E` be an elliptic curve over a scheme `S`, with structure morphism `π : E ⟶ S` and zero
section `0`. Zariski-locally on `S`, `E` is the projective model of an elliptic Weierstrass curve,
through a pointed Weierstrass chart; the projective model carries the negation morphism
`WeierstrassCurve.projModelNeg`, `[X : Y : Z] ↦ [X : -Y - a₁X - a₃Z : Z]`. This file glues these
local negation morphisms to the negation morphism `E ⟶ E` over `S`.

A pointed Weierstrass chart `c`, over an open `U = base ⟶ S`, presents the restriction `E_U` of
`E` as the projective model of its equation. Transporting the negation morphism of the equation
along this presentation gives the **negation of the chart** `E_U ⟶ E_U`
(`PointedWeierstrassChart.neg`). If the base of a chart `k` maps to the base of a chart `c` over
`S`, the comparison of the two projective models carries the zero section to the zero section and
is a base change square, so it commutes with negation
(`WeierstrassCurve.projModelNeg_comp_of_isPullback`). The negations of the charts therefore glue
along the cover of `E` by the restrictions `E_U` (`EllipticCurveGeom.glueMorphisms`) to
`EllipticCurveGeom.neg`. Its restriction to every chart is the negation of the chart
(`EllipticCurveGeom.toTotal_neg`), and this characterises it among all morphisms `E ⟶ E`, already
on the charts of any one atlas (`EllipticCurveGeom.eq_neg_of_atlas`). In particular the negation
morphism does not depend on the choice of local Weierstrass equations. Like its local models, it
is an involution over `S` that fixes the zero section.

## Main definitions

* `TauCeti.AlgebraicGeometry.PointedWeierstrassChart.neg c`: the negation of a pointed Weierstrass
  chart, the negation morphism of its equation transported to the restriction of the curve to the
  base of the chart.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.neg E`: the negation morphism `E ⟶ E` of an
  elliptic curve over a scheme.

## Main results

* `TauCeti.AlgebraicGeometry.PointedWeierstrassChart.neg_pullbackCarrierMap`: the negation of a
  chart restricts, over a chart whose base maps into its base, to the negation of that chart.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.toTotal_neg`: on the restriction of `E` to the base
  of any pointed Weierstrass chart, the negation morphism is the negation of the chart.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.eq_neg_of_atlas`: a morphism `E ⟶ E` that restricts
  to the negation of every chart of a pointed Weierstrass atlas is the negation morphism.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.neg_structureMap`,
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.zero_neg` and
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.neg_neg`: the negation morphism lies over `S`, fixes
  the zero section and is an involution; in particular it is an isomorphism, its own inverse.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.1–2.2.
* P. Deligne and M. Rapoport, *Les schémas de modules de courbes elliptiques*, II.1.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

namespace PointedWeierstrassChart

variable {S X : Scheme.{u}} {π : X ⟶ S} {zero : S ⟶ X}

/-! ### The negation of a chart -/

section Neg

variable (c : PointedWeierstrassChart π zero)

/-- The **negation of a pointed Weierstrass chart** `c` of `π : X ⟶ S`: the morphism
`X_U ⟶ X_U`, for `X_U` the restriction of `X` to the base `U` of the chart, obtained by
transporting the negation morphism of the projective model of the equation of `c` along the
isomorphism of `X_U` with that model (`neg_modelIso_hom`). -/
noncomputable def neg : c.pullbackCarrier ⟶ c.pullbackCarrier :=
  c.modelIso.hom ≫ c.equation.projModelNeg ≫ c.modelIso.inv

/-- Through the isomorphism of the restriction of the curve to the base of a chart with the
projective model of its equation, the negation of the chart is the negation morphism of the
projective model. -/
@[reassoc (attr := simp)]
theorem neg_modelIso_hom : c.neg ≫ c.modelIso.hom = c.modelIso.hom ≫ c.equation.projModelNeg := by
  simp [neg]

/-- The negation of a chart lies over the base of the chart. -/
@[reassoc (attr := simp)]
theorem neg_toBase : c.neg ≫ c.toBase = c.toBase := by
  rw [← cancel_mono c.baseIso.hom, Category.assoc, ← c.modelIso_over, neg_modelIso_hom_assoc,
    WeierstrassCurve.projModelNeg_projModelOver, c.modelIso_over]

/-- The negation of a chart fixes the section induced by the zero section. -/
@[reassoc (attr := simp)]
theorem pulledZero_neg : c.pulledZero ≫ c.neg = c.pulledZero := by
  rw [← cancel_mono c.modelIso.hom, Category.assoc, neg_modelIso_hom, c.modelIso_zero_assoc,
    WeierstrassCurve.projModelZero_projModelNeg, c.modelIso_zero]

/-- The negation of a chart is an involution. -/
@[reassoc (attr := simp)]
theorem neg_neg : c.neg ≫ c.neg = 𝟙 _ := by
  simp [neg]

end Neg

/-! ### Restriction of the negation of a chart -/

section Lift

variable {k c : PointedWeierstrassChart π zero} {h : k.base ⟶ c.base}
  (hh : h ≫ c.baseMap = k.baseMap)

/-- **Restriction of the negation of a chart.** If the base of a chart `k` maps to the base of a
chart `c` over `S`, the negation of `c` restricts to the negation of `k`. Both are the negation
morphisms of the projective models of their equations; the comparison of the two models is a base
change square carrying the zero section to the zero section, and negation commutes with it
(`WeierstrassCurve.projModelNeg_comp_of_isPullback`). -/
@[reassoc]
theorem neg_pullbackCarrierMap : k.neg ≫ pullbackCarrierMap hh = pullbackCarrierMap hh ≫ c.neg := by
  -- the comparison `projModelMap hh` of the projective models of the two equations
  rw [← cancel_mono c.modelIso.hom, Category.assoc, Category.assoc, neg_modelIso_hom,
    ← modelIso_hom_projModelMap, ← modelIso_hom_projModelMap_assoc, neg_modelIso_hom_assoc,
    WeierstrassCurve.projModelNeg_comp_of_isPullback (isPullback_projModelMap hh)
      (projModelZero_projModelMap hh)]

end Lift

end PointedWeierstrassChart

/-! ### Gluing the negations of the charts -/

namespace EllipticCurveGeom

open PointedWeierstrassChart

variable {S : Scheme.{u}} (E : EllipticCurveGeom S)

-- The negation of a chart, on the part of `E` over its base.
private noncomputable def pieceNeg (c : PointedWeierstrassChart E.structureMap E.zero) :
    pullback E.structureMap c.baseMap ⟶ E.carrier :=
  c.isPullback.isoPullback.inv ≫ c.neg ≫ c.toTotal

-- The negations of the charts are compatible with restriction along morphisms of bases.
private theorem map_pieceNeg {k c : PointedWeierstrassChart E.structureMap E.zero}
    {h : k.base ⟶ c.base} (hh : h ≫ c.baseMap = k.baseMap) :
    pullback.map E.structureMap k.baseMap E.structureMap c.baseMap (𝟙 _) h (𝟙 _) (by simp)
      (by simp [hh]) ≫ pieceNeg E c = pieceNeg E k := by
  have : pullback.map E.structureMap k.baseMap E.structureMap c.baseMap (𝟙 _) h (𝟙 _) (by simp)
      (by simp [hh]) ≫ c.isPullback.isoPullback.inv =
      k.isPullback.isoPullback.inv ≫ pullbackCarrierMap hh := by
    apply c.isPullback.hom_ext <;> simp
  simp only [pieceNeg, reassoc_of% this, ← neg_pullbackCarrierMap_assoc,
    pullbackCarrierMap_toTotal]

/-- The **negation morphism** `E ⟶ E` of an elliptic curve `E` over a scheme `S`: the morphism
whose restriction to the base `U` of every pointed Weierstrass chart is the negation morphism
`[X : Y : Z] ↦ [X : -Y - a₁X - a₃Z : Z]` of the projective model of the equation of the chart
(`toTotal_neg`). It is glued from these local negation morphisms, which agree where they overlap. -/
noncomputable def neg : E.carrier ⟶ E.carrier :=
  glueMorphisms (pieceNeg E) (map_pieceNeg E)

/-- **The negation morphism on a chart.** On the restriction of `E` to the base of a pointed
Weierstrass chart `c`, the negation morphism of `E` is the negation of the chart, the negation
morphism of the projective model of the equation of `c`. -/
@[reassoc (attr := simp)]
theorem toTotal_neg (c : PointedWeierstrassChart E.structureMap E.zero) :
    c.toTotal ≫ E.neg = c.neg ≫ c.toTotal := by
  rw [← cancel_epi c.isPullback.isoPullback.inv, ← Category.assoc,
    c.isPullback.isoPullback_inv_fst, neg, fst_glueMorphisms, pieceNeg]

/-- **Uniqueness of the negation morphism.** A morphism `ν : E ⟶ E` whose restriction to the base
of every chart of a pointed Weierstrass atlas is the negation of the chart is the negation
morphism of `E`. -/
theorem eq_neg_of_atlas (A : PointedWeierstrassAtlas E.structureMap E.zero)
    {ν : E.carrier ⟶ E.carrier}
    (hν : ∀ i, (A.chart i).toTotal ≫ ν = (A.chart i).neg ≫ (A.chart i).toTotal) :
    ν = E.neg :=
  A.hom_ext_of_toTotal _ _ fun i ↦ by rw [hν, toTotal_neg]

/-- The negation morphism of an elliptic curve over `S` lies over `S`. -/
@[reassoc (attr := simp)]
theorem neg_structureMap : E.neg ≫ E.structureMap = E.structureMap := by
  obtain ⟨A⟩ := E.localModel
  refine A.hom_ext_of_toTotal _ _ fun i ↦ ?_
  simp [(A.chart i).isPullback.w]

/-- The negation morphism of an elliptic curve fixes the zero section. -/
@[reassoc (attr := simp)]
theorem zero_neg : E.zero ≫ E.neg = E.zero := by
  obtain ⟨A⟩ := E.localModel
  refine A.hom_ext (𝟙 S) _ _ fun i ↦ ?_
  -- over the base of a chart, the zero section is the section induced by it on the chart
  have h : pullback.fst (𝟙 S) (A.chart i).baseMap ≫ E.zero =
      pullback.snd _ _ ≫ (A.chart i).pulledZero ≫ (A.chart i).toTotal := by
    rw [pulledZero_toTotal, ← Category.assoc, ← pullback.condition, Category.comp_id]
  rw [reassoc_of% h, h, toTotal_neg, pulledZero_neg_assoc]

/-- The negation morphism of an elliptic curve is an involution. -/
@[reassoc (attr := simp)]
theorem neg_neg : E.neg ≫ E.neg = 𝟙 E.carrier := by
  obtain ⟨A⟩ := E.localModel
  refine A.hom_ext_of_toTotal _ _ fun i ↦ ?_
  simp

/-- The negation morphism of an elliptic curve is an isomorphism, being an involution. -/
instance isIso_neg : IsIso E.neg :=
  ⟨E.neg, E.neg_neg, E.neg_neg⟩

/-- The negation morphism of an elliptic curve is its own inverse. -/
@[simp]
theorem inv_neg : inv E.neg = E.neg :=
  IsIso.inv_eq_of_hom_inv_id E.neg_neg

end EllipticCurveGeom

end TauCeti.AlgebraicGeometry
