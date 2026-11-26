/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.Divisor
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.PoleSheaf
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.ZeroSection

/-!
# Pole sheaves along the zero section of an elliptic curve over a scheme

For `E : EllipticCurveGeom S`, dualizing the invertible ideal sheaf `𝒪_E(-n[0])` of the relative
effective Cartier divisor `n[0]` (`EllipticCurveGeom.zeroSectionDivisor`) gives the **pole sheaf**
`𝒪_E(n[0])` (`EllipticCurveGeom.poleSheaf E n`). Its class `[𝒪_E(n[0])]` in `Pic(E)` commutes with
arbitrary pointed cartesian squares, `E.baseChange f`, and pointed Weierstrass charts. Combining
chart-wise ampleness on projective Weierstrass models (`n > 0`) with ampleness descent over a
quasi-affine base (`LineBundleClass.IsAmple.of_forall_exists_opens_of_isQuasiAffine`) yields global
ampleness of `𝒪_E(n[0])` over any quasi-affine scheme `S`.

## Main definitions and results

* `EllipticCurveGeom.poleSheaf`: the invertible pole sheaf `𝒪_E(n[0])` (`n : ℕ`).
* `EllipticCurveGeom.mk_poleSheaf_eq_pow`, `mk_poleSheaf_zero`, `mk_poleSheaf_add`: Picard-group
  identities `[𝒪_E(n[0])] = [𝒪_E([0])] ^ n`.
* `EllipticCurveGeom.pullback_mk_poleSheaf_of_isPullback`, `pullback_mk_poleSheaf_baseChange`,
  `pullback_toTotal_mk_poleSheaf`: base-change and Weierstrass-chart functoriality.
* `EllipticCurveGeom.isAmple_pullback_toTotal_poleSheaf`,
  `exists_isAffineOpen_isAmple_pullback_poleSheaf`, `exists_opens_isAmple_pullback_poleSheaf`,
  `isAmple_poleSheaf`: local ampleness over any base `S` and global ampleness over quasi-affine `S`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §2.2.
* R. Hartshorne, *Algebraic Geometry*, Section II.7.
* [The Stacks Project, Tag 0D32](https://stacks.math.columbia.edu/tag/0D32).
-/

public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.EllipticCurveGeom

variable {S : Scheme.{u}} (E : EllipticCurveGeom S)

/-! ### The pole sheaves `𝒪_E(n[0])` -/

/-- The **pole sheaf** `𝒪_E(n[0])` (`n : ℕ`) on `E`, dual to the ideal sheaf `𝒪_E(-n[0])`. -/
noncomputable def poleSheaf (n : ℕ) : InvertibleSheaf E.carrier :=
  (E.isRelativeEffectiveCartier_zeroSectionDivisor_pow n).isEffectiveCartier.toInvertibleSheaf.dual

/-- `poleSheaf E n` is the dual of the invertible ideal sheaf of `E.zeroSectionDivisor ^ n`. -/
theorem poleSheaf_def (n : ℕ) :
    E.poleSheaf n = (E.isRelativeEffectiveCartier_zeroSectionDivisor_pow
      n).isEffectiveCartier.toInvertibleSheaf.dual := (rfl)

/-- The underlying `𝒪_E`-module of `𝒪_E(n[0])` is the dual of the ideal sheaf `𝒪_E(-n[0])`. -/
@[simp] theorem poleSheaf_obj (n : ℕ) :
    (E.poleSheaf n).obj = (E.zeroSectionDivisor ^ n).sheaf.dual := by
  rw [poleSheaf_def, InvertibleSheaf.dual_obj,
    Scheme.IdealSheafData.IsEffectiveCartier.toInvertibleSheaf_obj]

/-- In the Picard group of `E.carrier`, `[𝒪_E(n[0])] = [𝒪_E([0])] ^ n`. -/
theorem mk_poleSheaf_eq_pow (n : ℕ) :
    LineBundleClass.mk (E.poleSheaf n) = LineBundleClass.mk (E.poleSheaf 1) ^ n := by
  rw [poleSheaf_def, poleSheaf_def, LineBundleClass.mk_dual_toInvertibleSheaf_pow
      E.isRelativeEffectiveCartier_zeroSectionDivisor.isEffectiveCartier,
    LineBundleClass.mk_dual_toInvertibleSheaf_congr _ _ (pow_one _)]

/-- `𝒪_E(0[0])` has trivial class in the Picard group of `E.carrier`. -/
@[simp] theorem mk_poleSheaf_zero : LineBundleClass.mk (E.poleSheaf 0) = 1 :=
  LineBundleClass.mk_dual_toInvertibleSheaf_pow_zero _

/-- In the Picard group of `E.carrier`, `[𝒪_E((m + n)[0])] = [𝒪_E(m[0])] * [𝒪_E(n[0])]`. -/
theorem mk_poleSheaf_add (m n : ℕ) : LineBundleClass.mk (E.poleSheaf (m + n)) =
    LineBundleClass.mk (E.poleSheaf m) * LineBundleClass.mk (E.poleSheaf n) :=
  LineBundleClass.mk_dual_toInvertibleSheaf_pow_add _ _ _

/-! ### Base-change functoriality -/

section BaseChange

variable {E} {S' : Scheme.{u}} {E' : EllipticCurveGeom S'} {g : E'.carrier ⟶ E.carrier}
  {f : S' ⟶ S} (hg : IsPullback g E'.structureMap E.structureMap f) (h0 : E'.zero ≫ g = f ≫ E.zero)

include hg h0 in
/-- Along a pointed cartesian square `g : E' ⟶ E`, `[𝒪_E(n[0])]` pulls back to `[𝒪_{E'}(n[0])]`. -/
theorem pullback_mk_poleSheaf_of_isPullback (n : ℕ) :
    LineBundleClass.pullback g (LineBundleClass.mk (E.poleSheaf n)) =
      LineBundleClass.mk (E'.poleSheaf n) :=
  hg.pullback_mk_dual_toInvertibleSheaf_ker_pow E.zero_comp E'.zero_comp h0
    E.zeroSectionDivisor_def E'.zeroSectionDivisor_def _ _

end BaseChange

/-- Under `E.baseChange f`, `[𝒪_E(n[0])]` pulls back to `[𝒪_{E.baseChange f}(n[0])]`. -/
theorem pullback_mk_poleSheaf_baseChange {T : Scheme.{u}} (f : T ⟶ S) (n : ℕ) :
    LineBundleClass.pullback ((E.baseChangeIso f).hom ≫ pullback.fst E.structureMap f)
        (LineBundleClass.mk (E.poleSheaf n)) = LineBundleClass.mk ((E.baseChange f).poleSheaf n) :=
  pullback_mk_poleSheaf_of_isPullback (E.isPullback_baseChange f)
    (E.zero_baseChangeIso_hom_comp_fst f) n

/-! ### Compatibility on pointed Weierstrass charts and ampleness -/

section Chart

variable (c : PointedWeierstrassChart E.structureMap E.zero)

/-- **Chart compatibility of `𝒪_E(n[0])`.** On a pointed Weierstrass chart `c`, `[𝒪_E(n[0])]`
restricts along `c.toTotal` to the pullback of `[𝒪_{c.equation}(n[0])]` along `c.modelIso.hom`. -/
theorem pullback_toTotal_mk_poleSheaf (n : ℕ) :
    LineBundleClass.pullback c.toTotal (LineBundleClass.mk (E.poleSheaf n)) =
      LineBundleClass.pullback c.modelIso.hom (LineBundleClass.mk (c.equation.poleSheaf n)) := by
  have h := c.isPullback_modelIso_inv_toTotal.pullback_mk_dual_toInvertibleSheaf_ker_pow
    E.zero_comp c.equation.projModelZero_projModelOver c.projModelZero_modelIso_inv_toTotal
    E.zeroSectionDivisor_def c.equation.zeroSectionDivisor_def
    (E.isRelativeEffectiveCartier_zeroSectionDivisor_pow n).isEffectiveCartier
    (c.equation.isEffectiveCartier_zeroSectionDivisor_pow n)
  simpa only [E.poleSheaf_def, c.equation.poleSheaf_def, LineBundleClass.pullback_comp,
    Iso.hom_inv_id_assoc] using congrArg (LineBundleClass.pullback c.modelIso.hom) h

/-- On any pointed Weierstrass chart `c`, `𝒪_E(n[0])` restricts to an ample bundle for `n > 0`. -/
theorem isAmple_pullback_toTotal_poleSheaf {n : ℕ} (hn : 0 < n) :
    (LineBundleClass.pullback c.toTotal (LineBundleClass.mk (E.poleSheaf n))).IsAmple := by
  rw [E.pullback_toTotal_mk_poleSheaf c n]
  exact (c.equation.isAmple_poleSheaf hn).pullback c.modelIso.hom

end Chart

/-- Every `s : S` has an affine open neighbourhood `U` over which `𝒪_E(n[0])` (`n > 0`) is ample. -/
theorem exists_isAffineOpen_isAmple_pullback_poleSheaf {n : ℕ} (hn : 0 < n) (s : S) :
    ∃ U : S.affineOpens, s ∈ U.val ∧ (LineBundleClass.pullback (E.structureMap ⁻¹ᵁ U.val).ι
      (LineBundleClass.mk (E.poleSheaf n))).IsAmple := by
  obtain ⟨A⟩ := E.localModel
  obtain ⟨i, x, rfl⟩ := A.covers s
  let c := A.chart i
  have hp : IsPullback c.toTotal (c.toBase ≫ c.baseMap.isoOpensRange.hom) E.structureMap
      c.baseMap.opensRange.ι :=
    c.isPullback.of_iso (.refl _) (.refl _) c.baseMap.isoOpensRange (.refl _)
      (by simp) (by simp) (by simp) (by simp)
  refine ⟨⟨c.baseMap.opensRange, isAffineOpen_opensRange c.baseMap⟩, ⟨x, rfl⟩, ?_⟩
  rw [← pullbackRestrictIsoRestrict_inv_fst E.structureMap c.baseMap.opensRange,
    ← hp.isoPullback_inv_fst, ← Category.assoc, ← LineBundleClass.pullback_comp]
  exact (E.isAmple_pullback_toTotal_poleSheaf c hn).pullback _

/-- Every `s : S` has an open neighbourhood `U` over which `𝒪_E(n[0])` (`n > 0`) is ample. -/
theorem exists_opens_isAmple_pullback_poleSheaf {n : ℕ} (hn : 0 < n) (s : S) :
    ∃ U : S.Opens, s ∈ U ∧ (LineBundleClass.pullback (E.structureMap ⁻¹ᵁ U).ι
      (LineBundleClass.mk (E.poleSheaf n))).IsAmple :=
  let ⟨U, hsU, hU⟩ := E.exists_isAffineOpen_isAmple_pullback_poleSheaf hn s; ⟨U.val, hsU, hU⟩

/-- **Global ampleness of `𝒪_E(n[0])` over a quasi-affine base** (in particular `Spec R`). -/
theorem isAmple_poleSheaf [S.IsQuasiAffine] {n : ℕ} (hn : 0 < n) :
    (LineBundleClass.mk (E.poleSheaf n)).IsAmple :=
  LineBundleClass.IsAmple.of_forall_exists_opens_of_isQuasiAffine E.structureMap
    (E.exists_opens_isAmple_pullback_poleSheaf hn)

end TauCeti.AlgebraicGeometry.EllipticCurveGeom
