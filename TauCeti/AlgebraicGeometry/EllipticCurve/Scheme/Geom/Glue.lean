/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.Basic

/-!
# Gluing morphisms along the pointed Weierstrass charts of an elliptic curve

Let `E` be an elliptic curve over a scheme `S` and `q : Y ⟶ S` a morphism of schemes. The bases of
the pointed Weierstrass charts of `E` are affine opens of `S` covering `S`, so their preimages
`Y ×_S U` cover `Y`. This file glues morphisms out of `Y` along this cover: a family of morphisms
`Y ×_S U ⟶ Z`, one for each chart, glues to a morphism `Y ⟶ Z` as soon as it is compatible with
the morphisms of chart bases over `S`.

Compatibility is only required along morphisms of bases, not on the overlaps of the cover. Two
charts `c` and `d` agree near every point of `U_c ∩ U_d` because, around each such point, the
restriction of `c` to an affine open of its base mapping into `U_d` is again a chart, whose base
maps both to `U_c` and to `U_d`.

This is how the morphisms of the group law of `E`, defined on each chart through its Weierstrass
equation, become morphisms over the whole of `S`: for the addition `E ×_S E ⟶ E`, `Y = E ×_S E`;
for the negation `E ⟶ E`, `Y = E`.

## Main definitions

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.glueMorphisms E q g hg`: the morphism `Y ⟶ Z`
  glued from a family `g` of morphisms `Y ×_S U ⟶ Z` over the bases `U` of the pointed Weierstrass
  charts of `E`, compatible along morphisms of chart bases.

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.fst_glueMorphisms`: the glued morphism restricts to
  the given morphism over the base of every chart.
* `TauCeti.AlgebraicGeometry.PointedWeierstrassAtlas.hom_ext`: two morphisms out of `Y` that
  agree over the bases of the charts of one pointed Weierstrass atlas of any `π : X ⟶ S` are
  equal; `TauCeti.AlgebraicGeometry.PointedWeierstrassAtlas.hom_ext_of_toTotal` is the case
  `Y = X`, stated on the restrictions of `X` to the chart bases.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

variable {S : Scheme.{u}} {Y Z : Scheme.{u}} (q : Y ⟶ S)

-- The preimages in `Y` of the bases of a family of charts covering `S` cover `Y`: the pullback
-- along `q` of the open cover of `S` by the bases of the charts.
private noncomputable def pieceCover {X : Scheme.{u}} {π : X ⟶ S} {zero : S ⟶ X} {ι : Type*}
    (c : ι → PointedWeierstrassChart π zero)
    (hc : ∀ s : S, ∃ i, ∃ b : (c i).base, (c i).baseMap b = s) : Y.OpenCover :=
  (Scheme.Cover.mkOfCovers ι (fun i ↦ (c i).base) (fun i ↦ (c i).baseMap) hc).pullback₁ q

namespace PointedWeierstrassAtlas

variable {X : Scheme.{u}} {π : X ⟶ S} {zero : S ⟶ X}

/-- **Morphisms are determined on the charts of an atlas.** Two morphisms out of `Y` that agree on
the preimages `Y ×_S U` of the bases `U` of the charts of a pointed Weierstrass atlas of `π` are
equal. -/
theorem hom_ext (A : PointedWeierstrassAtlas π zero) (f g : Y ⟶ Z)
    (h : ∀ i, pullback.fst q (A.chart i).baseMap ≫ f = pullback.fst q (A.chart i).baseMap ≫ g) :
    f = g :=
  (pieceCover q A.chart A.covers).hom_ext f g h

/-- **Morphisms out of `X` are determined on the charts of an atlas.** Two morphisms out of `X`
that agree on the restrictions of `X` to the bases of the charts of a pointed Weierstrass atlas of
`π` are equal. -/
theorem hom_ext_of_toTotal (A : PointedWeierstrassAtlas π zero) (f g : X ⟶ Z)
    (h : ∀ i, (A.chart i).toTotal ≫ f = (A.chart i).toTotal ≫ g) : f = g :=
  A.hom_ext π f g fun i ↦ by
    rw [← (A.chart i).isPullback.isoPullback_inv_fst, Category.assoc, Category.assoc, h]

end PointedWeierstrassAtlas

namespace EllipticCurveGeom

open PointedWeierstrassChart

variable (E : EllipticCurveGeom S)

-- The preimages in `Y` of the bases of all pointed Weierstrass charts of `E` cover `Y`.
private noncomputable def chartCover : Y.OpenCover :=
  pieceCover q (id : PointedWeierstrassChart E.structureMap E.zero → _) fun s ↦ by
    obtain ⟨A⟩ := E.localModel
    obtain ⟨i, b, hb⟩ := A.covers s
    exact ⟨A.chart i, b, hb⟩

variable {E q} (g : ∀ c : PointedWeierstrassChart E.structureMap E.zero, pullback q c.baseMap ⟶ Z)
  (hg : ∀ {k c : PointedWeierstrassChart E.structureMap E.zero} {h : k.base ⟶ c.base}
    (hh : h ≫ c.baseMap = k.baseMap),
    pullback.map q k.baseMap q c.baseMap (𝟙 _) h (𝟙 _) (by simp) (by simp [hh]) ≫ g c = g k)

include hg in
-- A compatible family agrees on the overlaps of the preimages of two chart bases: near every
-- point, both restrict to the morphism given on a restriction of the first chart to an affine open
-- whose image lies in the base of the second chart.
private theorem agree (c d : PointedWeierstrassChart E.structureMap E.zero) :
    pullback.fst (pullback.fst q c.baseMap) (pullback.fst q d.baseMap) ≫ g c =
      pullback.snd _ _ ≫ g d := by
  refine Scheme.hom_ext_of_forall _ _ fun x ↦ ?_
  -- the part of the intersection over the base of `c`
  let r := pullback.fst (pullback.fst q c.baseMap) (pullback.fst q d.baseMap) ≫ pullback.snd _ _
  have hr : r ≫ c.baseMap =
      (pullback.snd (pullback.fst q c.baseMap) (pullback.fst q d.baseMap) ≫ pullback.snd _ _) ≫
        d.baseMap := by
    simp only [r, Category.assoc, ← pullback.condition, pullback.condition_assoc]
  -- an affine open `V` of the base of `c`, around the image of `x`, mapping into the base of `d`
  have hx : r x ∈ c.baseMap ⁻¹ᵁ d.baseMap.opensRange :=
    ⟨_, by rw [← Scheme.Hom.comp_apply, ← hr, Scheme.Hom.comp_apply]⟩
  obtain ⟨V, hV, hxV, hVd⟩ := exists_isAffineOpen_mem_and_subset hx
  let V' : c.base.affineOpens := ⟨V, hV⟩
  have hV' (y : (c.restrict V').base) : c.restrictι V' y ∈ V :=
    (c.range_restrictι V').subset ⟨y, rfl⟩
  have hkd : Set.range (c.restrict V').baseMap ⊆ Set.range d.baseMap := by
    rintro _ ⟨y, rfl⟩
    rw [← restrictι_baseMap, Scheme.Hom.comp_apply]
    exact hVd (hV' y)
  -- the part `U` of the intersection over `V` maps to the preimage of the base of the restriction
  -- of `c` to `V`
  refine ⟨r ⁻¹ᵁ V, hxV, ?_⟩
  have hU : Set.range ((r ⁻¹ᵁ V).ι ≫ r) ⊆ Set.range (c.restrictι V') := by
    rintro _ ⟨y, rfl⟩
    rw [range_restrictι, Scheme.Hom.comp_apply]
    exact y.2
  have hℓ : ((r ⁻¹ᵁ V).ι ≫ pullback.fst _ _ ≫ pullback.fst _ _) ≫ q =
      IsOpenImmersion.lift (c.restrictι V') _ hU ≫ (c.restrict V').baseMap := by
    rw [← restrictι_baseMap, IsOpenImmersion.lift_fac_assoc]
    simp only [r, Category.assoc, ← pullback.condition]
  let ℓ := pullback.lift _ _ hℓ
  have hc : (r ⁻¹ᵁ V).ι ≫ pullback.fst _ _ = ℓ ≫ pullback.map q (c.restrict V').baseMap q
      c.baseMap (𝟙 _) (c.restrictι V') (𝟙 _) (by simp) (by simp) := by
    apply pullback.hom_ext
    · simp [ℓ]
    · simp [ℓ, r]
  have hd : (r ⁻¹ᵁ V).ι ≫ pullback.snd _ _ = ℓ ≫ pullback.map q (c.restrict V').baseMap q
      d.baseMap (𝟙 _) (IsOpenImmersion.lift d.baseMap _ hkd) (𝟙 _) (by simp) (by simp) := by
    apply pullback.hom_ext
    · simp [ℓ, pullback.condition]
    · rw [← cancel_mono d.baseMap]
      have h' := (r ⁻¹ᵁ V).ι ≫= hr
      simp only [Category.assoc] at h'
      simp [ℓ, ← restrictι_baseMap, ← h']
  rw [reassoc_of% hc, reassoc_of% hd, hg (restrictι_baseMap c V'),
    hg (IsOpenImmersion.lift_fac _ _ hkd)]

/-- **Gluing along the charts of an elliptic curve.** The morphism `Y ⟶ Z` glued from a family `g`
of morphisms `Y ×_S U ⟶ Z`, one over the base `U` of each pointed Weierstrass chart of `E`, that is
compatible with the morphisms of chart bases over `S`: if the base of a chart `k` maps to the base
of a chart `c`, then `g c` restricts to `g k`. Its restriction to every chart is the given morphism
(`fst_glueMorphisms`). -/
noncomputable def glueMorphisms : Y ⟶ Z :=
  (chartCover q E).glueMorphisms g (agree g hg)

/-- On the preimage of the base of a chart `c`, the morphism glued from a compatible family `g` is
`g c`. -/
@[reassoc (attr := simp)]
theorem fst_glueMorphisms (c : PointedWeierstrassChart E.structureMap E.zero) :
    pullback.fst q c.baseMap ≫ glueMorphisms g hg = g c :=
  (chartCover q E).ι_glueMorphisms g (agree g hg) c

end EllipticCurveGeom

end TauCeti.AlgebraicGeometry
