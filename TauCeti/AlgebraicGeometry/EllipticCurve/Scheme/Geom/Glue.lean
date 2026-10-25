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

The same gluing turns a universal property over affine bases into one over arbitrary bases. Let
`p : U ⟶ B` be a family of curves with sections, such as a universal Weierstrass normal form. If
the projective model of every chart of `E`, with the sections induced by given sections of `E`, is
the base change of `p` along a unique morphism, compatibly with the sections, then so is `E`
(`TauCeti.AlgebraicGeometry.EllipticCurveGeom.existsUnique_isPullback_of_forall_chart`).

## Main definitions

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.glueMorphisms E q g hg`: the morphism `Y ⟶ Z`
  glued from a family `g` of morphisms `Y ×_S U ⟶ Z` over the bases `U` of the pointed Weierstrass
  charts of `E`, compatible along morphisms of chart bases.

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.fst_glueMorphisms`: the glued morphism restricts to
  the given morphism over the base of every chart.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.existsUnique_isPullback_of_forall_chart`: a pointed
  family which is the base change of a fixed family along a unique morphism over the base of every
  chart is the base change of that family along a unique morphism.
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

/-! ### Classifying pairs -/

section Classifying

variable {B U : Scheme.{u}} {p : U ⟶ B} {t₀ : B ⟶ U} {ι : Type*} {t : ι → (B ⟶ U)}

-- `(f, g)` classifies `(π, zero, τ)`: `g` exhibits `X` as the base change of `p` along `f`,
-- carrying `zero` to `t₀` and each section `τ i` to `t i`.
private def IsClassifying (p : U ⟶ B) (t₀ : B ⟶ U) (t : ι → (B ⟶ U)) {X T : Scheme.{u}}
    (π : X ⟶ T) (zero : T ⟶ X) (τ : ι → (T ⟶ X)) (f : T ⟶ B) (g : X ⟶ U) : Prop :=
  IsPullback g π p f ∧ zero ≫ g = f ≫ t₀ ∧ ∀ i, τ i ≫ g = f ≫ t i

-- Classifying pairs pull back along cartesian squares.
private theorem IsClassifying.comp {X T X' T' : Scheme.{u}} {π : X ⟶ T} {zero : T ⟶ X}
    {τ : ι → (T ⟶ X)} {f : T ⟶ B} {g : X ⟶ U} (h : IsClassifying p t₀ t π zero τ f g)
    {π' : X' ⟶ T'} {zero' : T' ⟶ X'} {τ' : ι → (T' ⟶ X')} {a : X' ⟶ X} {b : T' ⟶ T}
    (hab : IsPullback a π' π b) (h₀ : zero' ≫ a = b ≫ zero) (hτ : ∀ i, τ' i ≫ a = b ≫ τ i) :
    IsClassifying p t₀ t π' zero' τ' (b ≫ f) (a ≫ g) :=
  ⟨hab.paste_horiz h.1, by simp [reassoc_of% h₀, h.2.1],
    fun i ↦ by simp [reassoc_of% (hτ i), h.2.2 i]⟩

-- Morphisms out of `S` are determined on the bases of the charts of an atlas.
private theorem hom_ext_baseMap (A : PointedWeierstrassAtlas E.structureMap E.zero)
    {Z : Scheme.{u}} {x y : S ⟶ Z} (h : ∀ i, (A.chart i).baseMap ≫ x = (A.chart i).baseMap ≫ y) :
    x = y :=
  A.hom_ext (𝟙 S) x y fun i ↦ by
    have hc : pullback.fst (𝟙 S) (A.chart i).baseMap = pullback.snd _ _ ≫ (A.chart i).baseMap := by
      simpa using pullback.condition (f := 𝟙 S) (g := (A.chart i).baseMap)
    rw [hc, Category.assoc, Category.assoc, h]

variable {σ : ι → (S ⟶ E.carrier)} (hσ : ∀ i, σ i ≫ E.structureMap = 𝟙 S)

-- A classifying pair of `E` restricts to a classifying pair of the model of every chart.
private theorem IsClassifying.chart (c : PointedWeierstrassChart E.structureMap E.zero)
    {f : S ⟶ B} {g : E.carrier ⟶ U} (hg : IsClassifying p t₀ t E.structureMap E.zero σ f g) :
    IsClassifying p t₀ t c.equation.projModelOver c.equation.projModelZero
      (fun i ↦ c.modelPoint (hσ i)) ((c.baseIso.inv ≫ c.baseMap) ≫ f)
      ((c.modelIso.inv ≫ c.toTotal) ≫ g) :=
  hg.comp c.isPullback_modelIso_inv_toTotal c.projModelZero_modelIso_inv_toTotal
    fun i ↦ c.modelPoint_modelIso_inv_toTotal (hσ i)

variable (hc : ∀ c : PointedWeierstrassChart E.structureMap E.zero,
  ∃! fg : (Spec c.ring ⟶ B) × (c.equation.projModel ⟶ U),
    IsPullback fg.2 c.equation.projModelOver p fg.1 ∧ c.equation.projModelZero ≫ fg.2 = fg.1 ≫ t₀ ∧
      ∀ i, c.modelPoint (hσ i) ≫ fg.2 = fg.1 ≫ t i)

include hσ hc

-- Two classifying pairs of the model of a chart agree.
private theorem IsClassifying.eq_of_chart (c : PointedWeierstrassChart E.structureMap E.zero)
    {f f' : Spec c.ring ⟶ B} {g g' : c.equation.projModel ⟶ U}
    (hg : IsClassifying p t₀ t c.equation.projModelOver c.equation.projModelZero
      (fun i ↦ c.modelPoint (hσ i)) f g)
    (hg' : IsClassifying p t₀ t c.equation.projModelOver c.equation.projModelZero
      (fun i ↦ c.modelPoint (hσ i)) f' g') : f = f' ∧ g = g' :=
  Prod.ext_iff.mp ((hc c).unique (y₁ := (f, g)) (y₂ := (f', g')) hg hg')

-- A classifying pair of `E` is unique, being unique on the charts of an atlas.
private theorem IsClassifying.unique {f f' : S ⟶ B} {g g' : E.carrier ⟶ U}
    (hg : IsClassifying p t₀ t E.structureMap E.zero σ f g)
    (hg' : IsClassifying p t₀ t E.structureMap E.zero σ f' g') : f = f' ∧ g = g' := by
  obtain ⟨A⟩ := E.localModel
  have key (i) := IsClassifying.eq_of_chart hσ hc (A.chart i) (hg.chart hσ (A.chart i))
    (hg'.chart hσ (A.chart i))
  refine ⟨hom_ext_baseMap A fun i ↦ ?_, A.hom_ext_of_toTotal g g' fun i ↦ ?_⟩
  · rw [← cancel_epi (A.chart i).baseIso.inv]
    simpa using (key i).1
  · rw [← cancel_epi (A.chart i).modelIso.inv]
    simpa using (key i).2

section Glue

variable (c : PointedWeierstrassChart E.structureMap E.zero)

-- The base of the classifying pair of the model of `c`.
private noncomputable def chartBase : Spec c.ring ⟶ B :=
  (hc c).exists.choose.1

-- The total morphism of the classifying pair of the model of `c`.
private noncomputable def chartTotal : c.equation.projModel ⟶ U :=
  (hc c).exists.choose.2

private theorem isClassifying_chartBase :
    IsClassifying p t₀ t c.equation.projModelOver c.equation.projModelZero
      (fun i ↦ c.modelPoint (hσ i)) (chartBase hσ hc c) (chartTotal hσ hc c) :=
  (hc c).exists.choose_spec

variable {c} {k : PointedWeierstrassChart E.structureMap E.zero} {h : k.base ⟶ c.base}
  (hh : h ≫ c.baseMap = k.baseMap)

-- The classifying pair of `c` restricts along a morphism of chart bases to that of `k`, by
-- uniqueness on `k`.
private theorem chartBase_comp_and_chartTotal_comp :
    (k.baseIso.inv ≫ h ≫ c.baseIso.hom) ≫ chartBase hσ hc c = chartBase hσ hc k ∧
      projModelMap hh ≫ chartTotal hσ hc c = chartTotal hσ hc k :=
  IsClassifying.eq_of_chart hσ hc k
    ((isClassifying_chartBase hσ hc c).comp (isPullback_projModelMap hh)
      (projModelZero_projModelMap hh) fun i ↦ modelPoint_projModelMap (hσ i) hh)
    (isClassifying_chartBase hσ hc k)

variable (c) in
-- The classifying morphism of `c`, on the part of `S` over its base.
private noncomputable def pieceBase : pullback (𝟙 S) c.baseMap ⟶ B :=
  pullback.snd (𝟙 S) c.baseMap ≫ c.baseIso.hom ≫ chartBase hσ hc c

private theorem map_pieceBase :
    pullback.map (𝟙 S) k.baseMap (𝟙 S) c.baseMap (𝟙 _) h (𝟙 _) (by simp) (by simp [hh]) ≫
      pieceBase hσ hc c = pieceBase hσ hc k := by
  simp [pieceBase, ← (chartBase_comp_and_chartTotal_comp hσ hc hh).1]

variable (c) in
-- The total morphism of the classifying pair of `c`, on the part of `E` over its base.
private noncomputable def pieceTotal : pullback E.structureMap c.baseMap ⟶ U :=
  c.isPullback.isoPullback.inv ≫ c.modelIso.hom ≫ chartTotal hσ hc c

private theorem map_pieceTotal :
    pullback.map E.structureMap k.baseMap E.structureMap c.baseMap (𝟙 _) h (𝟙 _) (by simp)
      (by simp [hh]) ≫ pieceTotal hσ hc c = pieceTotal hσ hc k := by
  have key : pullback.map E.structureMap k.baseMap E.structureMap c.baseMap (𝟙 _) h (𝟙 _)
      (by simp) (by simp [hh]) ≫ c.isPullback.isoPullback.inv =
      k.isPullback.isoPullback.inv ≫ pullbackCarrierMap hh :=
    c.isPullback.hom_ext (by simp) (by simp)
  rw [pieceTotal, pieceTotal, reassoc_of% key, ← (chartBase_comp_and_chartTotal_comp hσ hc hh).2]
  simp

-- The classifying morphism of `E`, glued from the classifying pairs of the charts.
private noncomputable def glueBase : S ⟶ B :=
  glueMorphisms (pieceBase hσ hc) (map_pieceBase hσ hc)

-- The total morphism of the classifying pair of `E`, glued from those of the charts.
private noncomputable def glueTotal : E.carrier ⟶ U :=
  glueMorphisms (pieceTotal hσ hc) (map_pieceTotal hσ hc)

variable (c) in
@[reassoc]
private theorem baseMap_glueBase :
    c.baseMap ≫ glueBase hσ hc = c.baseIso.hom ≫ chartBase hσ hc c := by
  simpa [glueBase, pieceBase, -fst_glueMorphisms, -fst_glueMorphisms_assoc] using
    pullback.lift c.baseMap (𝟙 c.base) (by simp) ≫=
      fst_glueMorphisms (pieceBase hσ hc) (map_pieceBase hσ hc) c

variable (c) in
private theorem toTotal_glueTotal :
    c.toTotal ≫ glueTotal hσ hc = c.modelIso.hom ≫ chartTotal hσ hc c := by
  simpa [glueTotal, pieceTotal, -fst_glueMorphisms, -fst_glueMorphisms_assoc] using
    c.isPullback.isoPullback.hom ≫=
      fst_glueMorphisms (pieceTotal hσ hc) (map_pieceTotal hσ hc) c

-- The glued pair classifies `E`: this is checked over the charts of an atlas.
private theorem isClassifying_glue :
    IsClassifying p t₀ t E.structureMap E.zero σ (glueBase hσ hc) (glueTotal hσ hc) := by
  obtain ⟨A⟩ := E.localModel
  refine ⟨?_, hom_ext_baseMap A fun i ↦ ?_, fun j ↦ hom_ext_baseMap A fun i ↦ ?_⟩
  · -- cartesian, checked over the cover of `S` by the chart bases of `A`
    let 𝒰 : S.OpenCover := Scheme.Cover.mkOfCovers A.index (fun i ↦ (A.chart i).base)
      (fun i ↦ (A.chart i).baseMap) A.covers
    refine (Scheme.isPullback_of_openCover _ _ _ _ 𝒰 fun i ↦ ?_).flip
    -- the maps of `𝒰` are the chart base maps, and those of its pullback along `E.structureMap`
    -- are the projections; `simp` does not see through `Scheme.Cover.mkOfCovers` here
    change IsPullback (pullback.snd E.structureMap (A.chart i).baseMap)
      (pullback.fst E.structureMap (A.chart i).baseMap ≫ glueTotal hσ hc)
      ((A.chart i).baseMap ≫ glueBase hσ hc) p
    -- over the base of a chart, this is the cartesian square of the classifying pair of the chart
    rw [baseMap_glueBase, ← (A.chart i).isPullback.isoPullback_inv_fst, Category.assoc,
      toTotal_glueTotal]
    exact (isClassifying_chartBase hσ hc (A.chart i)).1.flip.of_iso
      ((A.chart i).modelIso.symm ≪≫ (A.chart i).isPullback.isoPullback) (A.chart i).baseIso.symm
      (.refl _) (.refl _) (by simp [Iso.eq_inv_comp]) (by simp) (by simp) (by simp)
  · rw [← (A.chart i).pulledZero_toTotal_assoc, toTotal_glueTotal,
      (A.chart i).modelIso_zero_assoc, (isClassifying_chartBase hσ hc _).2.1,
      baseMap_glueBase_assoc]
  · rw [← chartPoint_toTotal_assoc _ (hσ j), toTotal_glueTotal,
      reassoc_of% chartPoint_modelIso_hom _ (hσ j), (isClassifying_chartBase hσ hc _).2.2 j,
      baseMap_glueBase_assoc]

end Glue

/-- **Classifying pairs glue along the charts.** Let `p : U ⟶ B` be a morphism of schemes with
sections `t₀` and `t i`, and let `E` be an elliptic curve over `S` with sections `σ i`. Suppose
that over the base of every pointed Weierstrass chart `c` of `E` there is a unique pair of a
morphism `f : Spec c.ring ⟶ B` and a morphism `g` from the projective model of the equation of `c`
to `U` such that `g` exhibits the model as the base change of `p` along `f`, carrying the zero
section to `t₀` and the model point of each `σ i` to `t i`. Then there is a unique such pair for
`E` itself.

This is how a universal family over `B`, such as a universal Weierstrass normal form, becomes a
fine moduli space over arbitrary bases once its universal property is known over affine bases. -/
theorem existsUnique_isPullback_of_forall_chart :
    ∃! fg : (S ⟶ B) × (E.carrier ⟶ U),
      IsPullback fg.2 E.structureMap p fg.1 ∧ E.zero ≫ fg.2 = fg.1 ≫ t₀ ∧
        ∀ i, σ i ≫ fg.2 = fg.1 ≫ t i :=
  ⟨(glueBase hσ hc, glueTotal hσ hc), isClassifying_glue hσ hc, fun _ hfg ↦
    have h := IsClassifying.unique hσ hc hfg (isClassifying_glue hσ hc)
    Prod.ext h.1 h.2⟩

end Classifying

end EllipticCurveGeom

end TauCeti.AlgebraicGeometry
