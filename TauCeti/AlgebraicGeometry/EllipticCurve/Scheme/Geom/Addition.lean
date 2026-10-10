/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Addition.Morphism
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Addition.Pointed

/-!
# The addition morphism of an elliptic curve over a scheme

Let `E` be an elliptic curve over a scheme `S`, with structure morphism `π : E ⟶ S` and zero
section `0`. Zariski-locally on `S`, `E` is the projective model of an elliptic Weierstrass curve,
through a pointed Weierstrass chart; the projective model carries the Bosma–Lenstra addition
morphism `WeierstrassCurve.additionMorphism`. This file glues these local addition morphisms to the
addition morphism `E ×_S E ⟶ E` over `S`.

A pointed Weierstrass chart `c`, over an open `U = base ⟶ S`, presents the restriction `E_U` of
`E` as the projective model of its equation. Transporting the addition morphism of the equation
along this presentation gives the **addition of the chart** `E_U ×_U E_U ⟶ E_U`
(`PointedWeierstrassChart.addition`). The additions of two charts agree where both are defined.
Over an affine open `V` of the base of a chart `c`, the restriction `c.restrict V` is again a
chart, and the comparison of the two charts over `V` is a morphism of projective models which
carries the zero section to the zero section and is a base change square. The Bosma–Lenstra
addition morphism commutes with such morphisms
(`WeierstrassCurve.additionMorphism_comp_of_isPullback`), because a pointed isomorphism of
projective models over an affine base is induced by a change of variables. So the addition of
every chart restricts to the addition of each of its restrictions to affine opens, and two charts
`c` and `d` agree near every point of `U_c ∩ U_d`, through a restriction of `c` to an affine open
mapping into `U_d`.

The parts `E_U ×_U E_U` of `E ×_S E` over the bases of all pointed Weierstrass charts form an open
cover, and the additions of the charts glue along it to `EllipticCurveGeom.addition`. Its
restriction to every chart is the addition of the chart (`EllipticCurveGeom.pullbackMap_addition`),
and this characterises it among all morphisms `E ×_S E ⟶ E`, already on the charts of any one atlas
(`EllipticCurveGeom.eq_addition_of_atlas`). In particular the addition morphism does not depend on
the choice of local Weierstrass equations.

## Main definitions

* `TauCeti.AlgebraicGeometry.PointedWeierstrassChart.addition c`: the addition of a pointed
  Weierstrass chart, the Bosma–Lenstra addition morphism of its equation transported to the
  restriction of the curve to the base of the chart.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.addition E`: the addition morphism `E ×_S E ⟶ E` of
  an elliptic curve over a scheme.

## Main results

* `TauCeti.AlgebraicGeometry.PointedWeierstrassChart.addition_pullbackCarrierMap`: the addition of
  a chart restricts, over a chart whose base maps into its base, to the addition of that chart.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.pullbackMap_addition`: on the restriction of
  `E ×_S E` to the base of any pointed Weierstrass chart, the addition morphism is the addition of
  the chart.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.addition_structureMap`: the addition morphism lies
  over `S`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.eq_addition_of_atlas`: a morphism `E ×_S E ⟶ E`
  that restricts to the addition of every chart of a pointed Weierstrass atlas is the addition
  morphism.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.1–2.2.
* P. Deligne and M. Rapoport, *Les schémas de modules de courbes elliptiques*, II.1.
* W. Bosma and H. W. Lenstra, Jr., *Complete systems of two addition laws for elliptic curves*,
  J. Number Theory 53 (1995), 229–240.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

namespace PointedWeierstrassChart

variable {S X : Scheme.{u}} {π : X ⟶ S} {zero : S ⟶ X}

/-! ### The addition of a chart -/

section Addition

variable (c : PointedWeierstrassChart π zero)

/-- The **addition of a pointed Weierstrass chart** `c` of `π : X ⟶ S`: the morphism
`X_U ×_U X_U ⟶ X_U`, for `X_U` the restriction of `X` to the base `U` of the chart, obtained by
transporting the Bosma–Lenstra addition morphism of the equation of `c` along the isomorphism of
`X_U` with its projective model (`addition_modelIso_hom`). -/
noncomputable def addition : pullback c.toBase c.toBase ⟶ c.pullbackCarrier :=
  pullback.map _ _ _ _ c.modelIso.hom c.modelIso.hom c.baseIso.hom c.modelIso_over.symm
    c.modelIso_over.symm ≫ c.equation.additionMorphism ≫ c.modelIso.inv

/-- Through the isomorphism of the restriction of the curve to the base of a chart with the
projective model of its equation, the addition of the chart is the Bosma–Lenstra addition
morphism of the equation. -/
@[reassoc (attr := simp)]
theorem addition_modelIso_hom : c.addition ≫ c.modelIso.hom =
    pullback.map _ _ _ _ c.modelIso.hom c.modelIso.hom c.baseIso.hom c.modelIso_over.symm
      c.modelIso_over.symm ≫ c.equation.additionMorphism := by
  simp [addition]

/-- The addition of a chart lies over the base of the chart. -/
@[reassoc (attr := simp)]
theorem addition_toBase : c.addition ≫ c.toBase = pullback.fst c.toBase c.toBase ≫ c.toBase := by
  rw [← cancel_mono c.baseIso.hom, Category.assoc, Category.assoc, ← c.modelIso_over,
    addition_modelIso_hom_assoc, WeierstrassCurve.additionMorphism_projModelOver,
    pullback.lift_fst_assoc, Category.assoc, c.modelIso_over]

end Addition

/-! ### Restriction of the addition of a chart -/

section Lift

variable {k c : PointedWeierstrassChart π zero} {h : k.base ⟶ c.base}
  (hh : h ≫ c.baseMap = k.baseMap)

/-- **Restriction of the addition of a chart.** If the base of a chart `k` maps to the base of a
chart `c` over `S`, the addition of `c` restricts to the addition of `k`. Both are the
Bosma–Lenstra addition morphisms of their equations; the comparison of the projective models of
the two equations is a base change square carrying the zero section to the zero section, and the
addition morphism commutes with it (`WeierstrassCurve.additionMorphism_comp_of_isPullback`). -/
@[reassoc]
theorem addition_pullbackCarrierMap : k.addition ≫ pullbackCarrierMap hh =
    pullback.map _ _ _ _ (pullbackCarrierMap hh) (pullbackCarrierMap hh) h (by simp) (by simp) ≫
      c.addition := by
  -- the comparison `F` of the projective models of the two equations, over `ψ`
  let F := k.modelIso.inv ≫ pullbackCarrierMap hh ≫ c.modelIso.hom
  let ψ := k.baseIso.inv ≫ h ≫ c.baseIso.hom
  have hF : IsPullback F k.equation.projModelOver c.equation.projModelOver ψ :=
    (isPullback_pullbackCarrierMap hh).of_iso k.modelIso c.modelIso k.baseIso c.baseIso
      (by simp [F]) k.modelIso_over.symm c.modelIso_over.symm (by simp [ψ])
  have h0 : k.equation.projModelZero ≫ F = ψ ≫ c.equation.projModelZero := by
    rw [← cancel_epi k.baseIso.hom, ← k.modelIso_zero_assoc]
    simp [F, ψ]
  have hk : k.addition ≫ pullbackCarrierMap hh ≫ c.modelIso.hom =
      pullback.map _ _ _ _ k.modelIso.hom k.modelIso.hom k.baseIso.hom k.modelIso_over.symm
        k.modelIso_over.symm ≫ k.equation.additionMorphism ≫ F := by
    simp [addition, F]
  rw [← cancel_mono c.modelIso.hom, Category.assoc, Category.assoc, addition_modelIso_hom, hk,
    WeierstrassCurve.additionMorphism_comp_of_isPullback hF h0]
  simp only [← Category.assoc]
  congr 1
  apply pullback.hom_ext <;> simp [F]

end Lift

end PointedWeierstrassChart

/-! ### Gluing the additions of the charts -/

namespace EllipticCurveGeom

open PointedWeierstrassChart

variable {S : Scheme.{u}} (E : EllipticCurveGeom S)

-- The morphism `E ×_S E ⟶ S`.
local notation "p" => pullback.fst E.structureMap E.structureMap ≫ E.structureMap

-- The parts of `E ×_S E` over the bases of a family of charts covering `S` cover `E ×_S E`: the
-- pullback along `E ×_S E ⟶ S` of the open cover of `S` by the bases of the charts.
private noncomputable def pieceCover {ι : Type*}
    (c : ι → PointedWeierstrassChart E.structureMap E.zero)
    (hc : ∀ s : S, ∃ i, ∃ b : (c i).base, (c i).baseMap b = s) :
    (pullback E.structureMap E.structureMap).OpenCover :=
  (Scheme.Cover.mkOfCovers ι (fun i ↦ (c i).base) (fun i ↦ (c i).baseMap) hc).pullback₁ p

-- The parts of `E ×_S E` over the bases of all pointed Weierstrass charts cover `E ×_S E`.
private noncomputable def chartCover : (pullback E.structureMap E.structureMap).OpenCover :=
  pieceCover E id fun s ↦ by
    obtain ⟨A⟩ := E.localModel
    obtain ⟨i, b, hb⟩ := A.covers s
    exact ⟨A.chart i, b, hb⟩

-- Morphisms out of `E ×_S E` agreeing on the parts over the bases of a family of charts covering
-- `S` are equal.
private theorem hom_ext_of_covers {ι : Type*}
    (c : ι → PointedWeierstrassChart E.structureMap E.zero)
    (hc : ∀ s : S, ∃ i, ∃ b : (c i).base, (c i).baseMap b = s) {Y : Scheme.{u}}
    (f g : pullback E.structureMap E.structureMap ⟶ Y)
    (h : ∀ i, pullback.fst p (c i).baseMap ≫ f = pullback.fst p (c i).baseMap ≫ g) : f = g :=
  (pieceCover E c hc).hom_ext f g h

-- A point of the part of `E ×_S E` over the base of a chart is a pair of points of the
-- restriction of `E` to that base.
private noncomputable def toPair (c : PointedWeierstrassChart E.structureMap E.zero) :
    pullback p c.baseMap ⟶ pullback c.toBase c.toBase :=
  pullback.lift
    (c.isPullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _)
      (by rw [Category.assoc]; exact pullback.condition))
    (c.isPullback.lift (pullback.fst _ _ ≫ pullback.snd _ _) (pullback.snd _ _)
      (by rw [Category.assoc, ← pullback.condition]; exact pullback.condition))
    (by simp)

-- The addition of a chart, on the part of `E ×_S E` over its base.
private noncomputable def pieceAddition (c : PointedWeierstrassChart E.structureMap E.zero) :
    pullback p c.baseMap ⟶ E.carrier :=
  toPair E c ≫ c.addition ≫ c.toTotal

-- On the part of `E ×_S E` over the base of a chart, the inclusion into `E ×_S E` is the pair of
-- the inclusions of the restriction of `E` into `E`.
private theorem toPair_map (c : PointedWeierstrassChart E.structureMap E.zero) :
    toPair E c ≫ pullback.map _ _ _ _ c.toTotal c.toTotal c.baseMap c.isPullback.w.symm
      c.isPullback.w.symm = pullback.fst p c.baseMap := by
  apply pullback.hom_ext <;> simp [toPair]

-- The additions of the charts are compatible with restriction along morphisms of bases.
private theorem map_pieceAddition {k c : PointedWeierstrassChart E.structureMap E.zero}
    {h : k.base ⟶ c.base} (hh : h ≫ c.baseMap = k.baseMap) :
    pullback.map p k.baseMap p c.baseMap (𝟙 _) h (𝟙 _) (by simp) (by simp [hh]) ≫
      pieceAddition E c = pieceAddition E k := by
  have : pullback.map p k.baseMap p c.baseMap (𝟙 _) h (𝟙 _) (by simp) (by simp [hh]) ≫
      toPair E c =
      toPair E k ≫ pullback.map _ _ _ _ (pullbackCarrierMap hh) (pullbackCarrierMap hh) h (by simp)
        (by simp) := by
    apply pullback.hom_ext <;> apply c.isPullback.hom_ext <;> simp [toPair]
  simp only [pieceAddition, reassoc_of% this, ← addition_pullbackCarrierMap_assoc,
    pullbackCarrierMap_toTotal]

-- The additions of two charts agree on the part of `E ×_S E` over the intersection of their
-- bases: near every point, both restrict to the addition of a restriction of the first chart to an
-- affine open whose image lies in the base of the second chart.
private theorem pieceAddition_agree (c d : PointedWeierstrassChart E.structureMap E.zero) :
    pullback.fst (pullback.fst p c.baseMap) (pullback.fst p d.baseMap) ≫ pieceAddition E c =
      pullback.snd _ _ ≫ pieceAddition E d := by
  refine Scheme.hom_ext_of_forall _ _ fun x ↦ ?_
  -- the part of the intersection over the base of `c`
  let q := pullback.fst (pullback.fst p c.baseMap) (pullback.fst p d.baseMap) ≫ pullback.snd _ _
  have hq : q ≫ c.baseMap =
      (pullback.snd (pullback.fst p c.baseMap) (pullback.fst p d.baseMap) ≫ pullback.snd _ _) ≫
        d.baseMap := by
    simp only [q, Category.assoc, ← pullback.condition, pullback.condition_assoc]
  -- an affine open `V` of the base of `c`, around the image of `x`, mapping into the base of `d`
  have hx : q x ∈ c.baseMap ⁻¹ᵁ d.baseMap.opensRange :=
    ⟨_, by rw [← Scheme.Hom.comp_apply, ← hq, Scheme.Hom.comp_apply]⟩
  obtain ⟨V, hV, hxV, hVd⟩ := exists_isAffineOpen_mem_and_subset hx
  let V' : c.base.affineOpens := ⟨V, hV⟩
  have hr (y : (c.restrict V').base) : c.restrictι V' y ∈ V :=
    (c.range_restrictι V').subset ⟨y, rfl⟩
  have hkd : Set.range (c.restrict V').baseMap ⊆ Set.range d.baseMap := by
    rintro _ ⟨y, rfl⟩
    rw [← restrictι_baseMap, Scheme.Hom.comp_apply]
    exact hVd (hr y)
  -- the part `U` of the intersection over `V` maps to the part of `E ×_S E` over the base of the
  -- restriction of `c` to `V`
  refine ⟨q ⁻¹ᵁ V, hxV, ?_⟩
  have hU : Set.range ((q ⁻¹ᵁ V).ι ≫ q) ⊆ Set.range (c.restrictι V') := by
    rintro _ ⟨y, rfl⟩
    rw [range_restrictι, Scheme.Hom.comp_apply]
    exact y.2
  have hℓ : ((q ⁻¹ᵁ V).ι ≫ pullback.fst _ _ ≫ pullback.fst _ _) ≫ p =
      IsOpenImmersion.lift (c.restrictι V') _ hU ≫ (c.restrict V').baseMap := by
    rw [← restrictι_baseMap, IsOpenImmersion.lift_fac_assoc]
    simp only [q, Category.assoc, ← pullback.condition]
  let ℓ := pullback.lift _ _ hℓ
  have hc : (q ⁻¹ᵁ V).ι ≫ pullback.fst _ _ = ℓ ≫ pullback.map p (c.restrict V').baseMap p
      c.baseMap (𝟙 _) (c.restrictι V') (𝟙 _) (by simp) (by simp) := by
    apply pullback.hom_ext
    · simp [ℓ]
    · simp [ℓ, q]
  have hd : (q ⁻¹ᵁ V).ι ≫ pullback.snd _ _ = ℓ ≫ pullback.map p (c.restrict V').baseMap p
      d.baseMap (𝟙 _) (IsOpenImmersion.lift d.baseMap _ hkd) (𝟙 _) (by simp) (by simp) := by
    apply pullback.hom_ext
    · simp [ℓ, pullback.condition]
    · rw [← cancel_mono d.baseMap]
      have h' := (q ⁻¹ᵁ V).ι ≫= hq
      simp only [Category.assoc] at h'
      simp [ℓ, ← restrictι_baseMap, ← h']
  rw [reassoc_of% hc, reassoc_of% hd, map_pieceAddition E (restrictι_baseMap c V'),
    map_pieceAddition E (IsOpenImmersion.lift_fac _ _ hkd)]

/-- The **addition morphism** `E ×_S E ⟶ E` of an elliptic curve `E` over a scheme `S`: the
morphism whose restriction to the base `U` of every pointed Weierstrass chart is the Bosma–Lenstra
addition morphism of the equation of the chart (`pullbackMap_addition`). It is glued from these
local addition morphisms, which agree where they overlap, and it lies over `S`
(`addition_structureMap`). -/
noncomputable def addition : pullback E.structureMap E.structureMap ⟶ E.carrier :=
  (chartCover E).glueMorphisms (pieceAddition E) (pieceAddition_agree E)

-- On the part of `E ×_S E` over the base of a chart, the addition morphism is the addition of the
-- chart.
private theorem fst_addition (c : PointedWeierstrassChart E.structureMap E.zero) :
    pullback.fst p c.baseMap ≫ E.addition = pieceAddition E c :=
  (chartCover E).ι_glueMorphisms (pieceAddition E) (pieceAddition_agree E) c

/-- **The addition morphism on a chart.** On the restriction of `E ×_S E` to the base of a pointed
Weierstrass chart `c`, the addition morphism of `E` is the addition of the chart, the Bosma–Lenstra
addition morphism of the equation of `c`. -/
@[reassoc (attr := simp)]
theorem pullbackMap_addition (c : PointedWeierstrassChart E.structureMap E.zero) :
    pullback.map _ _ _ _ c.toTotal c.toTotal c.baseMap c.isPullback.w.symm c.isPullback.w.symm ≫
      E.addition = c.addition ≫ c.toTotal := by
  -- the restriction of `E ×_S E` to the base of `c` is the part of the open cover indexed by `c`
  obtain ⟨ℓ, hℓ, hℓ'⟩ : ∃ ℓ : pullback c.toBase c.toBase ⟶ pullback p c.baseMap,
      ℓ ≫ pullback.fst _ _ = pullback.map _ _ _ _ c.toTotal c.toTotal c.baseMap
        c.isPullback.w.symm c.isPullback.w.symm ∧ ℓ ≫ toPair E c = 𝟙 _ :=
    ⟨pullback.lift _ (pullback.fst _ _ ≫ c.toBase) (by simp [c.isPullback.w]),
      pullback.lift_fst _ _ _, by
        apply pullback.hom_ext <;> apply c.isPullback.hom_ext <;>
          simp [toPair, pullback.condition]⟩
  rw [← hℓ, Category.assoc, fst_addition, pieceAddition, reassoc_of% hℓ']

/-- The addition morphism of an elliptic curve over `S` lies over `S`. -/
@[reassoc (attr := simp)]
theorem addition_structureMap : E.addition ≫ E.structureMap =
    pullback.fst E.structureMap E.structureMap ≫ E.structureMap := by
  obtain ⟨A⟩ := E.localModel
  refine hom_ext_of_covers E A.chart A.covers _ _ fun i ↦ ?_
  rw [← toPair_map]
  simp [(A.chart i).isPullback.w]

/-- **Uniqueness of the addition morphism.** A morphism `μ : E ×_S E ⟶ E` whose restriction to the
base of every chart of a pointed Weierstrass atlas is the addition of the chart is the addition
morphism of `E`. -/
theorem eq_addition_of_atlas (A : PointedWeierstrassAtlas E.structureMap E.zero)
    {μ : pullback E.structureMap E.structureMap ⟶ E.carrier}
    (hμ : ∀ i, pullback.map _ _ _ _ (A.chart i).toTotal (A.chart i).toTotal (A.chart i).baseMap
      (A.chart i).isPullback.w.symm (A.chart i).isPullback.w.symm ≫ μ =
        (A.chart i).addition ≫ (A.chart i).toTotal) :
    μ = E.addition :=
  hom_ext_of_covers E A.chart A.covers _ _ fun i ↦ by
    rw [← toPair_map, Category.assoc, Category.assoc, hμ, pullbackMap_addition]

end EllipticCurveGeom

end TauCeti.AlgebraicGeometry
