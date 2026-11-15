/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.BaseChange.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.Glue
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.JInvariant

/-!
# The `j`-invariant of an elliptic curve over a scheme

Let `E` be an elliptic curve over a scheme `S`. Zariski-locally on `S`, `E` is the projective
model of an elliptic Weierstrass curve, through a pointed Weierstrass chart, and the `j`-invariant
`WeierstrassCurve.j` of that equation is a function on the base of the chart. Two charts give the
same function where both are defined, because a pointed isomorphism of projective Weierstrass models
is a change of variables and the `j`-invariant is invariant under changes of variables
(`WeierstrassCurve.j_eq_of_isPullback`). These local functions therefore glue to a global function
`EllipticCurveGeom.j E : Γ(S, ⊤)`, the **`j`-invariant** of `E`. Equivalently it is a morphism
`EllipticCurveGeom.jMap E : S ⟶ Spec ℤ[j]` to the `j`-line, where `ℤ[j]` is the polynomial ring
`MvPolynomial PUnit (ULift ℤ)` in one variable, the integral model of the affine line in
`Mathlib.AlgebraicGeometry.AffineSpace`.

The `j`-invariant is compatible with every cartesian morphism of elliptic curves: if `g : E' ⟶ E`
exhibits `E'` over `S'` as the base change of `E` along `f : S' ⟶ S`, compatibly with the zero
sections, then `f` pulls back the `j`-invariant of `E` to that of `E'`
(`EllipticCurveGeom.appTop_j_of_isPullback`). Thus `E ↦ jMap E` is a morphism from the moduli
problem of elliptic curves to the affine line, constant on isomorphism classes
(`EllipticCurveGeom.j_eq_of_iso`) and compatible with base change
(`EllipticCurveGeom.jMap_baseChange`). On the projective model of an elliptic Weierstrass curve
`W` over `R` it is `W.j` (`WeierstrassCurve.j_toEllipticCurveGeom`, in
`TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.OfWeierstrass`).

## Main definitions

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.jMap E`: the `j`-invariant of `E` as a morphism
  `S ⟶ Spec ℤ[j]`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.j E`: the `j`-invariant of `E` as a global function
  on `S`.

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.baseMap_appTop_j`: on the base of any pointed
  Weierstrass chart, the `j`-invariant is that of the equation of the chart.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.eq_j_of_atlas`: this characterises it, already on
  the charts of any one atlas.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.appTop_j_of_isPullback` and
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.comp_jMap_of_isPullback`: compatibility with
  cartesian morphisms of elliptic curves, in particular with base change
  (`TauCeti.AlgebraicGeometry.EllipticCurveGeom.j_baseChange` and
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.jMap_baseChange`) and with isomorphisms
  (`TauCeti.AlgebraicGeometry.EllipticCurveGeom.j_eq_of_iso`).

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.2 and 8.2.
* P. Deligne and M. Rapoport, *Les schémas de modules de courbes elliptiques*, II.1.
* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.1.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

namespace PointedWeierstrassChart

variable {S X : Scheme.{u}} {π : X ⟶ S} {zero : S ⟶ X}

-- The `j`-invariant of the equation of a chart, as a global function on the base of the chart.
private noncomputable def jSection (c : PointedWeierstrassChart π zero) : Γ(c.base, ⊤) :=
  c.baseIso.hom.appTop ((Scheme.ΓSpecIso c.ring).inv c.equation.j)

-- The `j`-invariant of the equation of a chart, as a morphism from its base to the `j`-line.
private noncomputable def jChartMap (c : PointedWeierstrassChart π zero) :
    c.base ⟶ Spec (.of (MvPolynomial PUnit.{u + 1} (ULift.{u} ℤ))) :=
  (AffineSpace.toSpecMvPolyIntEquiv PUnit).symm fun _ ↦ c.jSection

-- Two charts whose bases are related over a base change square have the same `j`-invariant: the
-- comparison of their projective models is a pointed base change square.
private theorem appTop_jSection {S' X' : Scheme.{u}} {π' : X' ⟶ S'} {zero' : S' ⟶ X'}
    {g : X' ⟶ X} {f : S' ⟶ S} (hg : IsPullback g π' π f) (h0 : zero' ≫ g = f ≫ zero)
    {k : PointedWeierstrassChart π' zero'} {c : PointedWeierstrassChart π zero}
    {h : k.base ⟶ c.base} (hh : h ≫ c.baseMap = k.baseMap ≫ f) :
    h.appTop c.jSection = k.jSection := by
  -- the comparison of the projective models lies over `Spec φ`
  obtain ⟨φ, hφ⟩ : ∃ φ : c.ring ⟶ k.ring, Spec.map φ = k.baseIso.inv ≫ h ≫ c.baseIso.hom :=
    ⟨Spec.preimage _, Spec.map_preimage _⟩
  have hF := isPullback_modelMap hg hh
  have hz := projModelZero_modelMap hg hh h0
  rw [← hφ, ← CommRingCat.ofHom_hom φ] at hF hz
  have hj := WeierstrassCurve.j_eq_of_isPullback hF hz
  have hh' : h ≫ c.baseIso.hom = k.baseIso.hom ≫ Spec.map φ := by simp [hφ]
  -- pull back along `h ≫ c.baseIso.hom = k.baseIso.hom ≫ Spec φ`, and move `φ` past `ΓSpecIso`
  rw [jSection, jSection, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hh',
    Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ← CommRingCat.comp_apply _ (Spec.map φ).appTop,
    ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply, ← hj]

-- The same statement for the morphisms to the `j`-line.
private theorem comp_jChartMap {S' X' : Scheme.{u}} {π' : X' ⟶ S'} {zero' : S' ⟶ X'}
    {g : X' ⟶ X} {f : S' ⟶ S} (hg : IsPullback g π' π f) (h0 : zero' ≫ g = f ≫ zero)
    {k : PointedWeierstrassChart π' zero'} {c : PointedWeierstrassChart π zero}
    {h : k.base ⟶ c.base} (hh : h ≫ c.baseMap = k.baseMap ≫ f) :
    h ≫ c.jChartMap = k.jChartMap := by
  refine (AffineSpace.toSpecMvPolyIntEquiv PUnit).injective (funext fun i ↦ ?_)
  rw [AffineSpace.toSpecMvPolyIntEquiv_comp, jChartMap, jChartMap, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]
  exact appTop_jSection hg h0 hh

end PointedWeierstrassChart

namespace EllipticCurveGeom

open PointedWeierstrassChart

variable {S : Scheme.{u}} (E : EllipticCurveGeom S)

-- The `j`-invariant of the equation of a chart, on the part of `S` over its base.
private noncomputable def pieceJMap (c : PointedWeierstrassChart E.structureMap E.zero) :
    pullback (𝟙 S) c.baseMap ⟶ Spec (.of (MvPolynomial PUnit.{u + 1} (ULift.{u} ℤ))) :=
  pullback.snd _ _ ≫ c.jChartMap

-- The `j`-invariants of the charts are compatible with restriction along morphisms of bases.
private theorem map_pieceJMap {k c : PointedWeierstrassChart E.structureMap E.zero}
    {h : k.base ⟶ c.base} (hh : h ≫ c.baseMap = k.baseMap) :
    pullback.map (𝟙 S) k.baseMap (𝟙 S) c.baseMap (𝟙 _) h (𝟙 _) (by simp) (by simp [hh]) ≫
      pieceJMap E c = pieceJMap E k := by
  rw [pieceJMap, pieceJMap, pullback.lift_snd_assoc, Category.assoc,
    comp_jChartMap (IsPullback.id_horiz E.structureMap) (by simp) (by simpa using hh)]

/-- The **`j`-invariant of an elliptic curve** `E` over `S`, as a morphism `S ⟶ Spec ℤ[j]` to the
`j`-line, where `ℤ[j] = MvPolynomial PUnit (ULift ℤ)`. On the base of every pointed Weierstrass
chart it is given by the `j`-invariant of the equation of the chart (`baseMap_appTop_j`); these
local morphisms glue because a pointed isomorphism of projective Weierstrass models preserves the
`j`-invariant. The corresponding global function on `S` is `EllipticCurveGeom.j E` (`jMap_eq`). -/
noncomputable def jMap : S ⟶ Spec (.of (MvPolynomial PUnit.{u + 1} (ULift.{u} ℤ))) :=
  glueMorphisms (pieceJMap E) (map_pieceJMap E)

/-- The **`j`-invariant of an elliptic curve** `E` over `S`, as a global function on `S`: the
coordinate of the morphism `jMap E` to the `j`-line. On the base of every pointed Weierstrass
chart it is the `j`-invariant of the equation of the chart (`baseMap_appTop_j`), and it is
compatible with base change (`j_baseChange`). -/
noncomputable def j : Γ(S, ⊤) :=
  AffineSpace.toSpecMvPolyIntEquiv PUnit E.jMap PUnit.unit

/-- The morphism `jMap E` to the `j`-line is the morphism with coordinate the `j`-invariant
`EllipticCurveGeom.j E`. -/
theorem jMap_eq : E.jMap = (AffineSpace.toSpecMvPolyIntEquiv PUnit).symm fun _ ↦ E.j :=
  (Equiv.eq_symm_apply _).mpr (funext fun _ ↦ rfl)

-- On the base of a chart, `jMap E` is the morphism given by the equation of the chart.
private theorem baseMap_comp_jMap (c : PointedWeierstrassChart E.structureMap E.zero) :
    c.baseMap ≫ E.jMap = c.jChartMap := by
  have h : pullback.fst (𝟙 S) c.baseMap ≫ E.jMap = pieceJMap E c :=
    fst_glueMorphisms _ (map_pieceJMap E) c
  calc c.baseMap ≫ E.jMap = pullback.lift (f := 𝟙 S) (g := c.baseMap) c.baseMap (𝟙 c.base)
        (by simp) ≫ pullback.fst _ _ ≫ E.jMap := by rw [pullback.lift_fst_assoc]
    _ = c.jChartMap := by rw [h, pieceJMap, pullback.lift_snd_assoc, Category.id_comp]

/-- **The `j`-invariant on a chart.** On the base of a pointed Weierstrass chart `c` of `E`, the
`j`-invariant of `E` is the `j`-invariant of the Weierstrass equation of `c`, read through the
isomorphism of the base of `c` with `Spec c.ring`. -/
theorem baseMap_appTop_j (c : PointedWeierstrassChart E.structureMap E.zero) :
    c.baseMap.appTop E.j = c.baseIso.hom.appTop ((Scheme.ΓSpecIso c.ring).inv c.equation.j) := by
  rw [j, ← AffineSpace.toSpecMvPolyIntEquiv_comp, baseMap_comp_jMap, jChartMap,
    Equiv.apply_symm_apply, jSection]

/-- **The `j`-invariant is determined by any atlas.** A global function on `S` which, on the base
of every chart of a pointed Weierstrass atlas of `E`, is the `j`-invariant of the equation of the
chart, is the `j`-invariant of `E`. -/
theorem eq_j_of_atlas (A : PointedWeierstrassAtlas E.structureMap E.zero) {x : Γ(S, ⊤)}
    (hx : ∀ i, (A.chart i).baseMap.appTop x =
      (A.chart i).baseIso.hom.appTop ((Scheme.ΓSpecIso (A.chart i).ring).inv
        (A.chart i).equation.j)) :
    x = E.j := by
  -- the morphisms to the `j`-line with coordinates `x` and `E.j` agree on every chart of `A`
  have hmap : (AffineSpace.toSpecMvPolyIntEquiv PUnit).symm (fun _ ↦ x) = E.jMap := by
    refine A.hom_ext (𝟙 S) _ _ fun i ↦ ?_
    rw [← Category.comp_id (pullback.fst _ _), pullback.condition, Category.assoc, Category.assoc,
      baseMap_comp_jMap]
    congr 1
    refine (AffineSpace.toSpecMvPolyIntEquiv PUnit).injective (funext fun _ ↦ ?_)
    rw [AffineSpace.toSpecMvPolyIntEquiv_comp, Equiv.apply_symm_apply, jChartMap,
      Equiv.apply_symm_apply, hx, jSection]
  have := congr($(congrArg (AffineSpace.toSpecMvPolyIntEquiv PUnit) hmap) PUnit.unit)
  rwa [Equiv.apply_symm_apply] at this

variable {E} {S' : Scheme.{u}} {E' : EllipticCurveGeom S'} {f : S' ⟶ S}
  {g : E'.carrier ⟶ E.carrier}

/-- **The `j`-invariant commutes with base change.** Let `g : E' ⟶ E` be a morphism of elliptic
curves lying over `f : S' ⟶ S`, such that the square formed by `g`, `f` and the structure
morphisms is a pullback square, and carrying the zero section of `E'` to that of `E`. Then `f`
pulls back the `j`-invariant of `E` to that of `E'`. -/
theorem appTop_j_of_isPullback (hg : IsPullback g E'.structureMap E.structureMap f)
    (h0 : E'.zero ≫ g = f ≫ E.zero) : f.appTop E.j = E'.j := by
  -- charts `k s` of `E'` around each point `s`, with bases mapping over `f` into charts of `E`
  choose k c h hh hk using E.exists_chart_comp_baseMap E' f
  refine E'.eq_j_of_atlas ⟨S', k, fun s ↦ ⟨s, hk s⟩⟩ fun s ↦ ?_
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← hh, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply, baseMap_appTop_j]
  exact appTop_jSection hg h0 (hh s)

/-- **The morphism to the `j`-line commutes with base change.** A morphism `g : E' ⟶ E` of elliptic
curves over `f : S' ⟶ S` forming a pullback square with the structure morphisms and carrying the
zero section to the zero section satisfies `f ≫ jMap E = jMap E'`. -/
@[reassoc]
theorem comp_jMap_of_isPullback (hg : IsPullback g E'.structureMap E.structureMap f)
    (h0 : E'.zero ≫ g = f ≫ E.zero) : f ≫ E.jMap = E'.jMap := by
  rw [jMap_eq, jMap_eq, ← appTop_j_of_isPullback hg h0]
  refine (AffineSpace.toSpecMvPolyIntEquiv PUnit).injective (funext fun _ ↦ ?_)
  rw [AffineSpace.toSpecMvPolyIntEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- **The `j`-invariant is an isomorphism invariant.** Elliptic curves over `S` whose total spaces
are isomorphic over `S`, by an isomorphism carrying the zero section to the zero section, have the
same `j`-invariant. -/
theorem j_eq_of_iso {E' : EllipticCurveGeom S} (e : E'.carrier ≅ E.carrier)
    (he : e.hom ≫ E.structureMap = E'.structureMap) (h0 : E'.zero ≫ e.hom = E.zero) :
    E'.j = E.j := by
  have hg : IsPullback e.hom E'.structureMap E.structureMap (𝟙 S) :=
    .of_horiz_isIso ⟨by simp [he]⟩
  rw [← appTop_j_of_isPullback hg (by simp [h0]), Scheme.Hom.id_appTop, CommRingCat.id_apply]

variable (E) (f : S' ⟶ S)

/-- The `j`-invariant of the base change `E.baseChange f` is the pullback of that of `E`. -/
@[simp]
theorem j_baseChange : (E.baseChange f).j = f.appTop E.j :=
  (appTop_j_of_isPullback (E.isPullback_baseChange f) (by simp)).symm

/-- The morphism to the `j`-line of the base change `E.baseChange f` is `f ≫ jMap E`. -/
@[simp]
theorem jMap_baseChange : (E.baseChange f).jMap = f ≫ E.jMap :=
  (comp_jMap_of_isPullback (E.isPullback_baseChange f) (by simp)).symm

end EllipticCurveGeom

end TauCeti.AlgebraicGeometry
