/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.BaseChange.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.PoleSheaf
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Degree.Sum
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Finite
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.FinitePresentation
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.ZeroSection
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange

/-!
# Pole sheaves along the zero section of an elliptic curve over a scheme

Let `E` be an elliptic curve over a scheme `S` (`EllipticCurveGeom S`). Its zero section
`E.zero : S ⟶ E.carrier` is a section of the separated smooth relative curve
`E.structureMap : E.carrier ⟶ S`, so its ideal sheaf `E.zeroSectionDivisor` cuts out a relative
effective Cartier divisor `[0]` on `E` over `S`, and for every `n : ℕ` the power
`E.zeroSectionDivisor ^ n` cuts out the relative effective Cartier divisor `n[0]`, finite locally
free of constant rank `n` over `S`.

Dualizing the invertible ideal sheaf `𝒪_E(-n[0])` yields the **pole sheaf** `𝒪_E(n[0])`
(`EllipticCurveGeom.poleSheaf E n`). Formation of `n[0]` and of `[𝒪_E(n[0])]` in the Picard group
commutes with arbitrary base change and with passage to pointed Weierstrass charts: on any chart
`c : PointedWeierstrassChart E.structureMap E.zero`, the restriction of `[𝒪_E(n[0])]` along
`c.toTotal` agrees with the pullback along `c.modelIso.hom` of `[𝒪_{c.equation}(n[0])]` on the
projective Weierstrass model `c.equation.projModel`.

Combining chart-wise ampleness of `𝒪(n[0])` on projective Weierstrass models (`n > 0`) with
descent of ampleness from a target-local open cover over a quasi-affine base yields global
ampleness of `𝒪_E(n[0])` for every `n > 0` whenever the base scheme `S` is quasi-affine (in
particular over any affine scheme `Spec R`).

## Main definitions

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.zeroSectionDivisor E`: the ideal sheaf of the zero
  section `E.zero`, cutting out `[0]` on `E`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.poleSheaf E n`: the invertible pole sheaf
  `𝒪_E(n[0])` (`n : ℕ`), defined as the dual of the invertible ideal sheaf of
  `E.zeroSectionDivisor ^ n`.

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isRelativeEffectiveCartier_zeroSectionDivisor` and
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isRelativeEffectiveCartier_zeroSectionDivisor_pow`:
  `[0]` and `n[0]` are relative effective Cartier divisors on `E` over `S`, finite locally free of
  rank `n` (`finrank_zeroSectionDivisor_pow`).
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.zeroSectionDivisor_eq_comap` and
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.pullback_mk_poleSheaf_of_isPullback`: `[0]`, `n[0]`,
  and `[𝒪_E(n[0])]` commute with arbitrary pointed base-change squares (and with projective
  Weierstrass models via `pullback_mk_poleSheaf_projModel_of_isPullback`).
* `TauCeti.AlgebraicGeometry.PointedWeierstrassChart.pullback_toTotal_mk_poleSheaf`: on any pointed
  Weierstrass chart `c` of `E`, `[𝒪_E(n[0])]` restricts to `[𝒪_{c.equation}(n[0])]`, hence is ample
  for `n > 0` (`isAmple_pullback_toTotal_poleSheaf`).
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.exists_opens_isAmple_pullback_poleSheaf`: for any
  scheme `S`, any `E : EllipticCurveGeom S`, and any `n > 0`, `S` is covered by open subschemes `U`
  such that `𝒪_E(n[0])` is ample on `E ×_S U`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isAmple_poleSheaf`: when `S` is quasi-affine,
  `𝒪_E(n[0])` is ample on `E` for every `n > 0`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §2.2.
* [R. Hartshorne, *Algebraic Geometry*][hartshorne1977], Section II.7.
* [The Stacks Project, *Morphisms*, Tag 0D32][stacks-project]: relative ampleness over a
  quasi-affine base.
-/

public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

namespace EllipticCurveGeom

variable {S : Scheme.{u}} (E : EllipticCurveGeom S)

/-! ### The zero-section divisor `[0]` and its multiples `n[0]` -/

/-- The relative divisor `[0]` on an elliptic curve `E` over `S`, represented by the ideal sheaf
of the zero section `E.zero : S ⟶ E.carrier`. -/
noncomputable def zeroSectionDivisor : E.carrier.IdealSheafData :=
  E.zero.ker

/-- `zeroSectionDivisor E` is the kernel ideal sheaf of `E.zero`. -/
theorem zeroSectionDivisor_def : E.zeroSectionDivisor = E.zero.ker :=
  (rfl)

/-- **The zero section cuts out a relative effective Cartier divisor** on `E` over `S`. -/
theorem isRelativeEffectiveCartier_zeroSectionDivisor :
    E.zeroSectionDivisor.IsRelativeEffectiveCartier E.structureMap :=
  Scheme.Hom.isRelativeEffectiveCartier_ker_of_smoothOfRelativeDimension E.zero E.zero_comp

/-- **Every multiple `n[0]` (`n : ℕ`) is a relative effective Cartier divisor** on `E` over `S`. -/
theorem isRelativeEffectiveCartier_zeroSectionDivisor_pow (n : ℕ) :
    (E.zeroSectionDivisor ^ n).IsRelativeEffectiveCartier E.structureMap :=
  TauCeti.isRelativeEffectiveCartier_pow E.isRelativeEffectiveCartier_zeroSectionDivisor n

/-- The closed subscheme `n[0]` is finite over `S`. -/
instance isFinite_zeroSectionDivisor_pow (n : ℕ) :
    IsFinite ((E.zeroSectionDivisor ^ n).subschemeι ≫ E.structureMap) :=
  (E.isRelativeEffectiveCartier_zeroSectionDivisor_pow n).isFinite

/-- The closed subscheme `n[0]` is flat over `S`. -/
instance flat_zeroSectionDivisor_pow (n : ℕ) :
    Flat ((E.zeroSectionDivisor ^ n).subschemeι ≫ E.structureMap) :=
  (E.isRelativeEffectiveCartier_zeroSectionDivisor_pow n).flat

/-- The closed subscheme `n[0]` is locally of finite presentation over `S`, hence finite locally
free together with `isFinite_zeroSectionDivisor_pow` and `flat_zeroSectionDivisor_pow`. -/
instance locallyOfFinitePresentation_zeroSectionDivisor_pow (n : ℕ) :
    LocallyOfFinitePresentation ((E.zeroSectionDivisor ^ n).subschemeι ≫ E.structureMap) := by
  have : Smooth E.structureMap := SmoothOfRelativeDimension.smooth 1 _
  exact TauCeti.locallyOfFinitePresentation_subschemeι_comp_of_isEffectiveCartier
    (E.isRelativeEffectiveCartier_zeroSectionDivisor_pow n).isEffectiveCartier

/-- The support of the zero-section divisor `[0]` is the image of `E.zero`. -/
theorem coe_support_zeroSectionDivisor :
    (E.zeroSectionDivisor.support : Set E.carrier) = Set.range E.zero := by
  rw [zeroSectionDivisor_def, Scheme.Hom.support_ker,
    E.zero.isClosedEmbedding.isClosed_range.closure_eq]

/-- The divisor `n[0]` has constant rank `n` over every point of `S`. -/
@[simp]
theorem finrank_zeroSectionDivisor_pow (n : ℕ) (s : S) :
    ((E.zeroSectionDivisor ^ n).subschemeι ≫ E.structureMap).finrank s = n := by
  have hpow : E.zeroSectionDivisor ^ n = ∏ _ : Fin n, E.zeroSectionDivisor := by simp
  have : IsFinite ((∏ _ : Fin n, E.zeroSectionDivisor).subschemeι ≫ E.structureMap) :=
    hpow ▸ inferInstance
  rw [hpow, finrank_prod_subschemeι_comp Finset.univ (fun _ : Fin n ↦ E.zeroSectionDivisor)
    (fun _ _ ↦ E.isRelativeEffectiveCartier_zeroSectionDivisor)]
  have hr : (E.zeroSectionDivisor.subschemeι ≫ E.structureMap).finrank = 1 :=
    Scheme.Hom.finrank_ker_comp_eq_one_of_comp_eq_id E.zero E.zero_comp
  simp [hr]

section BaseChangeDivisor

variable {E} {S' : Scheme.{u}} {E' : EllipticCurveGeom S'} {g : E'.carrier ⟶ E.carrier}
  {f : S' ⟶ S} (hg : IsPullback g E'.structureMap E.structureMap f) (h0 : E'.zero ≫ g = f ≫ E.zero)

include hg h0 in
/-- **The zero-section divisor `[0]` commutes with base change** along any pointed cartesian square
of elliptic curves. -/
theorem zeroSectionDivisor_eq_comap :
    E'.zeroSectionDivisor = E.zeroSectionDivisor.comap g := by
  rw [zeroSectionDivisor_def, zeroSectionDivisor_def]
  refine Scheme.IdealSheafData.ker_eq_comap_of_isPullback (g := f) E.zero ?_
  refine IsPullback.of_right ?_ h0 hg.flip
  rw [E'.zero_comp, E.zero_comp]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

include hg h0 in
/-- **Every multiple `n[0]` commutes with base change** along any pointed cartesian square of
elliptic curves. -/
theorem zeroSectionDivisor_pow_eq_comap (n : ℕ) :
    E'.zeroSectionDivisor ^ n = (E.zeroSectionDivisor ^ n).comap g := by
  rw [zeroSectionDivisor_eq_comap hg h0, Scheme.IdealSheafData.comap_pow]

end BaseChangeDivisor

/-- Under `E.baseChange f`, the zero-section divisor `[0]` is the inverse image of `[0]` on `E`. -/
@[simp]
theorem zeroSectionDivisor_baseChange {T : Scheme.{u}} (f : T ⟶ S) :
    (E.baseChange f).zeroSectionDivisor =
      E.zeroSectionDivisor.comap ((E.baseChangeIso f).hom ≫ pullback.fst E.structureMap f) :=
  zeroSectionDivisor_eq_comap (E.isPullback_baseChange f)
    (by simp [← Category.assoc, E.zero_baseChangeIso_hom, pullbackSection_fst])

/-- Under `E.baseChange f`, the multiple `n[0]` is the inverse image of `n[0]` on `E`. -/
theorem zeroSectionDivisor_pow_baseChange {T : Scheme.{u}} (f : T ⟶ S) (n : ℕ) :
    (E.baseChange f).zeroSectionDivisor ^ n =
      (E.zeroSectionDivisor ^ n).comap
        ((E.baseChangeIso f).hom ≫ pullback.fst E.structureMap f) := by
  rw [E.zeroSectionDivisor_baseChange f, Scheme.IdealSheafData.comap_pow]

/-- Along any pointed cartesian square from `E` to a projective Weierstrass model `W.projModel`,
the zero-section divisor `[0]` on `E` is the inverse image of `W.zeroSectionDivisor`. -/
theorem zeroSectionDivisor_eq_comap_projModel {E : EllipticCurveGeom S} {R : Type u} [CommRing R]
    {W : WeierstrassCurve R} {g : E.carrier ⟶ W.projModel} {f : S ⟶ Spec (.of R)}
    (hg : IsPullback g E.structureMap W.projModelOver f)
    (h0 : E.zero ≫ g = f ≫ W.projModelZero) :
    E.zeroSectionDivisor = W.zeroSectionDivisor.comap g := by
  rw [zeroSectionDivisor_def, WeierstrassCurve.zeroSectionDivisor_def]
  refine Scheme.IdealSheafData.ker_eq_comap_of_isPullback (g := f) W.projModelZero ?_
  refine IsPullback.of_right ?_ h0 hg.flip
  rw [E.zero_comp, W.projModelZero_projModelOver]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

/-- Along any pointed cartesian square from `E` to a projective Weierstrass model `W.projModel`,
`n[0]` on `E` is the inverse image of `W.zeroSectionDivisor ^ n`. -/
theorem zeroSectionDivisor_pow_eq_comap_projModel {E : EllipticCurveGeom S} {R : Type u}
    [CommRing R] {W : WeierstrassCurve R} {g : E.carrier ⟶ W.projModel} {f : S ⟶ Spec (.of R)}
    (hg : IsPullback g E.structureMap W.projModelOver f)
    (h0 : E.zero ≫ g = f ≫ W.projModelZero) (n : ℕ) :
    E.zeroSectionDivisor ^ n = (W.zeroSectionDivisor ^ n).comap g := by
  rw [zeroSectionDivisor_eq_comap_projModel hg h0, Scheme.IdealSheafData.comap_pow]

/-! ### The pole sheaves `𝒪_E(n[0])` -/

/-- The **pole sheaf** `𝒪_E(n[0])` (`n : ℕ`) on an elliptic curve `E` over `S`: the dual of the
invertible ideal sheaf `𝒪_E(-n[0])` of the relative effective Cartier divisor `n[0]`. -/
noncomputable def poleSheaf (n : ℕ) : InvertibleSheaf E.carrier :=
  (E.isRelativeEffectiveCartier_zeroSectionDivisor_pow n).isEffectiveCartier.toInvertibleSheaf.dual

/-- `poleSheaf E n` is the dual of the invertible ideal sheaf of `E.zeroSectionDivisor ^ n`. -/
theorem poleSheaf_def (n : ℕ) :
    E.poleSheaf n =
      (E.isRelativeEffectiveCartier_zeroSectionDivisor_pow
        n).isEffectiveCartier.toInvertibleSheaf.dual :=
  (rfl)

/-- In the Picard group of `E.carrier`, `[𝒪_E(n[0])] = [𝒪_E([0])] ^ n`. -/
theorem mk_poleSheaf (n : ℕ) :
    LineBundleClass.mk (E.poleSheaf n) = LineBundleClass.mk (E.poleSheaf 1) ^ n := by
  have h₁ := E.isRelativeEffectiveCartier_zeroSectionDivisor.isEffectiveCartier
  rw [poleSheaf_def, ← LineBundleClass.inv_mk,
    LineBundleClass.mk_toInvertibleSheaf_congr _ (TauCeti.isEffectiveCartier_pow h₁ n) rfl,
    LineBundleClass.mk_toInvertibleSheaf_pow h₁ n, ← inv_pow]
  congr 1
  rw [poleSheaf_def, ← LineBundleClass.inv_mk,
    LineBundleClass.mk_toInvertibleSheaf_congr _ h₁ (pow_one _)]

/-- `𝒪_E(0[0])` has trivial class in the Picard group of `E.carrier`. -/
@[simp]
theorem mk_poleSheaf_zero : LineBundleClass.mk (E.poleSheaf 0) = 1 := by
  rw [E.mk_poleSheaf 0, pow_zero]

/-- In the Picard group of `E.carrier`, `[𝒪_E((m + n)[0])] = [𝒪_E(m[0])] * [𝒪_E(n[0])]`. -/
theorem mk_poleSheaf_add (m n : ℕ) :
    LineBundleClass.mk (E.poleSheaf (m + n)) =
      LineBundleClass.mk (E.poleSheaf m) * LineBundleClass.mk (E.poleSheaf n) := by
  rw [E.mk_poleSheaf (m + n), E.mk_poleSheaf m, E.mk_poleSheaf n, pow_add]

/-- **Base-change functoriality of `𝒪_E(n[0])`.** Along any pointed cartesian square `g : E' ⟶ E`
of elliptic curves, the pole sheaf `𝒪_E(n[0])` pulls back in the Picard group to `𝒪_{E'}(n[0])`. -/
theorem pullback_mk_poleSheaf_of_isPullback {E : EllipticCurveGeom S} {S' : Scheme.{u}}
    {E' : EllipticCurveGeom S'} {g : E'.carrier ⟶ E.carrier} {f : S' ⟶ S}
    (hg : IsPullback g E'.structureMap E.structureMap f)
    (h0 : E'.zero ≫ g = f ≫ E.zero) (n : ℕ) :
    LineBundleClass.pullback g (LineBundleClass.mk (E.poleSheaf n)) =
      LineBundleClass.mk (E'.poleSheaf n) := by
  have hE := (E.isRelativeEffectiveCartier_zeroSectionDivisor_pow n).isEffectiveCartier
  have hE' := (E'.isRelativeEffectiveCartier_zeroSectionDivisor_pow n).isEffectiveCartier
  have hcomap : ((E.zeroSectionDivisor ^ n).comap g).IsEffectiveCartier :=
    zeroSectionDivisor_pow_eq_comap hg h0 n ▸ hE'
  rw [poleSheaf_def, poleSheaf_def, ← LineBundleClass.inv_mk, ← LineBundleClass.inv_mk,
    LineBundleClass.pullback_inv, hE.pullback_mk_toInvertibleSheaf hcomap,
    LineBundleClass.mk_toInvertibleSheaf_congr hcomap hE'
      (zeroSectionDivisor_pow_eq_comap hg h0 n).symm]

/-- Under `E.baseChange f`, `[𝒪_E(n[0])]` pulls back to `[𝒪_{E.baseChange f}(n[0])]`. -/
theorem pullback_mk_poleSheaf_baseChange {T : Scheme.{u}} (f : T ⟶ S) (n : ℕ) :
    LineBundleClass.pullback ((E.baseChangeIso f).hom ≫ pullback.fst E.structureMap f)
        (LineBundleClass.mk (E.poleSheaf n)) =
      LineBundleClass.mk ((E.baseChange f).poleSheaf n) :=
  pullback_mk_poleSheaf_of_isPullback (E.isPullback_baseChange f)
    (by simp [← Category.assoc, E.zero_baseChangeIso_hom, pullbackSection_fst]) n

/-- **Comparison with `WeierstrassCurve.poleSheaf`.** Along any pointed cartesian square from `E`
to the projective model of an elliptic Weierstrass curve `W`, `[𝒪_W(n[0])]` pulls back to
`[𝒪_E(n[0])]`. -/
theorem pullback_mk_poleSheaf_projModel_of_isPullback {E : EllipticCurveGeom S} {R : Type u}
    [CommRing R] {W : WeierstrassCurve R} [W.IsElliptic] {g : E.carrier ⟶ W.projModel}
    {f : S ⟶ Spec (.of R)} (hg : IsPullback g E.structureMap W.projModelOver f)
    (h0 : E.zero ≫ g = f ≫ W.projModelZero) (n : ℕ) :
    LineBundleClass.pullback g (LineBundleClass.mk (W.poleSheaf n)) =
      LineBundleClass.mk (E.poleSheaf n) := by
  have hW := (W.isRelativeEffectiveCartier_zeroSectionDivisor_pow n).isEffectiveCartier
  have hE := (E.isRelativeEffectiveCartier_zeroSectionDivisor_pow n).isEffectiveCartier
  have hcomap : ((W.zeroSectionDivisor ^ n).comap g).IsEffectiveCartier :=
    zeroSectionDivisor_pow_eq_comap_projModel hg h0 n ▸ hE
  rw [WeierstrassCurve.poleSheaf_def, poleSheaf_def, ← LineBundleClass.inv_mk,
    ← LineBundleClass.inv_mk, LineBundleClass.pullback_inv,
    hW.pullback_mk_toInvertibleSheaf hcomap,
    LineBundleClass.mk_toInvertibleSheaf_congr hcomap hE
      (zeroSectionDivisor_pow_eq_comap_projModel hg h0 n).symm]

end EllipticCurveGeom

/-! ### Compatibility on pointed Weierstrass charts and ampleness -/

namespace PointedWeierstrassChart

variable {S : Scheme.{u}} (E : EllipticCurveGeom S)
  (c : PointedWeierstrassChart E.structureMap E.zero)

/-- On a pointed Weierstrass chart `c` of `E`, the inverse image of `[0]` along `c.toTotal` agrees
with the inverse image of `c.equation.zeroSectionDivisor` along `c.modelIso.hom`: both equal the
ideal sheaf of `c.pulledZero`. -/
theorem zeroSectionDivisor_comap_toTotal :
    E.zeroSectionDivisor.comap c.toTotal =
      c.equation.zeroSectionDivisor.comap c.modelIso.hom := by
  have h₁ : c.pulledZero.ker = E.zeroSectionDivisor.comap c.toTotal := by
    rw [EllipticCurveGeom.zeroSectionDivisor_def]
    refine Scheme.IdealSheafData.ker_eq_comap_of_isPullback (g := c.baseMap) E.zero ?_
    refine IsPullback.of_right ?_ c.pulledZero_toTotal c.isPullback.flip
    rw [c.pulledZero_toBase, E.zero_comp]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  have hmodel : IsPullback c.modelIso.hom c.toBase c.equation.projModelOver c.baseIso.hom :=
    IsPullback.of_horiz_isIso ⟨c.modelIso_over⟩
  have h₂ : c.pulledZero.ker = c.equation.zeroSectionDivisor.comap c.modelIso.hom := by
    rw [WeierstrassCurve.zeroSectionDivisor_def]
    refine Scheme.IdealSheafData.ker_eq_comap_of_isPullback (g := c.baseIso.hom)
      c.equation.projModelZero ?_
    refine IsPullback.of_right ?_ c.modelIso_zero hmodel.flip
    rw [c.pulledZero_toBase, c.equation.projModelZero_projModelOver]
    exact IsPullback.of_horiz_isIso ⟨(Category.id_comp _).trans (Category.comp_id _).symm⟩
  exact h₁.symm.trans h₂

/-- On a pointed Weierstrass chart `c` of `E`, the inverse image of `n[0]` along `c.toTotal` agrees
with the inverse image of `c.equation.zeroSectionDivisor ^ n` along `c.modelIso.hom`. -/
theorem zeroSectionDivisor_pow_comap_toTotal (n : ℕ) :
    (E.zeroSectionDivisor ^ n).comap c.toTotal =
      (c.equation.zeroSectionDivisor ^ n).comap c.modelIso.hom := by
  rw [Scheme.IdealSheafData.comap_pow, Scheme.IdealSheafData.comap_pow,
    c.zeroSectionDivisor_comap_toTotal E]

/-- **Chart compatibility of `𝒪_E(n[0])`.** On a pointed Weierstrass chart `c` of `E`, the
restriction of `[𝒪_E(n[0])]` along `c.toTotal` equals the pullback of `[𝒪_{c.equation}(n[0])]`
along `c.modelIso.hom`. -/
theorem pullback_toTotal_mk_poleSheaf (n : ℕ) :
    LineBundleClass.pullback c.toTotal (LineBundleClass.mk (E.poleSheaf n)) =
      LineBundleClass.pullback c.modelIso.hom
        (LineBundleClass.mk (c.equation.poleSheaf n)) := by
  have hE := (E.isRelativeEffectiveCartier_zeroSectionDivisor_pow n).isEffectiveCartier
  have hW := (c.equation.isRelativeEffectiveCartier_zeroSectionDivisor_pow n).isEffectiveCartier
  have hcomapE : ((E.zeroSectionDivisor ^ n).comap c.toTotal).IsEffectiveCartier :=
    ((E.isRelativeEffectiveCartier_zeroSectionDivisor_pow n).comap_of_isPullback
      c.isPullback).isEffectiveCartier
  have hcomapW : ((c.equation.zeroSectionDivisor ^ n).comap c.modelIso.hom).IsEffectiveCartier :=
    c.zeroSectionDivisor_pow_comap_toTotal E n ▸ hcomapE
  rw [EllipticCurveGeom.poleSheaf_def, WeierstrassCurve.poleSheaf_def,
    ← LineBundleClass.inv_mk, ← LineBundleClass.inv_mk,
    LineBundleClass.pullback_inv, LineBundleClass.pullback_inv,
    hE.pullback_mk_toInvertibleSheaf hcomapE, hW.pullback_mk_toInvertibleSheaf hcomapW,
    LineBundleClass.mk_toInvertibleSheaf_congr hcomapE hcomapW
      (c.zeroSectionDivisor_pow_comap_toTotal E n)]

/-- On any pointed Weierstrass chart `c` of `E`, the restriction of `𝒪_E(n[0])` along `c.toTotal`
is ample for every `n > 0`. -/
theorem isAmple_pullback_toTotal_poleSheaf {n : ℕ} (hn : 0 < n) :
    (LineBundleClass.pullback c.toTotal (LineBundleClass.mk (E.poleSheaf n))).IsAmple := by
  rw [c.pullback_toTotal_mk_poleSheaf E n]
  exact (c.equation.isAmple_poleSheaf hn).pullback_of_isIso c.modelIso.hom

end PointedWeierstrassChart

namespace EllipticCurveGeom

variable {S : Scheme.{u}} (E : EllipticCurveGeom S)

/-- **Target-local ampleness of `𝒪_E(n[0])`.** Over any base scheme `S`, every point `s : S` has an
affine open neighbourhood `U` over which `𝒪_E(n[0])` (`n > 0`) restricts to an ample invertible
sheaf on `(E.structureMap ⁻¹ᵁ U.1).toScheme`. -/
theorem exists_isAffineOpen_isAmple_pullback_poleSheaf {n : ℕ} (hn : 0 < n) (s : S) :
    ∃ U : S.affineOpens, s ∈ U.1 ∧
      (LineBundleClass.pullback (E.structureMap ⁻¹ᵁ U.1).ι
        (LineBundleClass.mk (E.poleSheaf n))).IsAmple := by
  obtain ⟨A⟩ := E.localModel
  obtain ⟨i, x, rfl⟩ := A.covers s
  let c := A.chart i
  refine ⟨⟨c.baseMap.opensRange, isAffineOpen_opensRange c.baseMap⟩, ⟨x, rfl⟩, ?_⟩
  have : IsOpenImmersion c.toTotal :=
    MorphismProperty.of_isPullback c.isPullback.flip inferInstance
  -- Both `(E.structureMap ⁻¹ᵁ c.baseMap.opensRange).ι` and `c.toTotal` are open immersions into
  -- `E.carrier` with image `E.structureMap ⁻¹' Set.range c.baseMap`.
  have hrange : Set.range (E.structureMap ⁻¹ᵁ c.baseMap.opensRange).ι = Set.range c.toTotal := by
    rw [Scheme.Opens.range_ι]
    change E.structureMap ⁻¹' Set.range c.baseMap = Set.range c.toTotal
    rw [← Scheme.Pullback.range_fst, ← c.isPullback.isoPullback_hom_fst]
    ext y
    simp only [Set.mem_range, Scheme.Hom.comp_apply]
    exact ⟨fun ⟨z, hz⟩ ↦ ⟨c.isPullback.isoPullback.inv z, by
        have hinv : c.isPullback.isoPullback.hom (c.isPullback.isoPullback.inv z) = z := by
          rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
          rfl
        rw [hinv, hz]⟩,
      fun ⟨z, hz⟩ ↦ ⟨c.isPullback.isoPullback.hom z, hz⟩⟩
  let e := IsOpenImmersion.isoOfRangeEq (E.structureMap ⁻¹ᵁ c.baseMap.opensRange).ι
    c.toTotal hrange
  rw [← IsOpenImmersion.isoOfRangeEq_hom_fac (E.structureMap ⁻¹ᵁ c.baseMap.opensRange).ι
      c.toTotal hrange, ← LineBundleClass.pullback_comp]
  exact (c.isAmple_pullback_toTotal_poleSheaf E hn).pullback_of_isIso e.hom

/-- **Relative ampleness of `𝒪_E(n[0])` on open covers of the base.** Over any scheme `S`, every
point `s : S` has an open neighbourhood `U` such that `𝒪_E(n[0])` (`n > 0`) restricts to an ample
invertible sheaf on `(E.structureMap ⁻¹ᵁ U).toScheme`. -/
theorem exists_opens_isAmple_pullback_poleSheaf {n : ℕ} (hn : 0 < n) (s : S) :
    ∃ U : S.Opens, s ∈ U ∧
      (LineBundleClass.pullback (E.structureMap ⁻¹ᵁ U).ι
        (LineBundleClass.mk (E.poleSheaf n))).IsAmple := by
  obtain ⟨U, hsU, hU⟩ := E.exists_isAffineOpen_isAmple_pullback_poleSheaf hn s
  exact ⟨U.1, hsU, hU⟩

/-- **Global ampleness of `𝒪_E(n[0])` over a quasi-affine base.** For any elliptic curve `E` over a
quasi-affine scheme `S` (in particular over any affine scheme `Spec R`) and any `n > 0`, the pole
sheaf `𝒪_E(n[0])` is ample on `E.carrier`. -/
theorem isAmple_poleSheaf [S.IsQuasiAffine] {n : ℕ} (hn : 0 < n) :
    (LineBundleClass.mk (E.poleSheaf n)).IsAmple :=
  LineBundleClass.IsAmple.of_forall_exists_opens_of_isQuasiAffine E.structureMap
    (E.exists_opens_isAmple_pullback_poleSheaf hn)

end EllipticCurveGeom

end TauCeti.AlgebraicGeometry
