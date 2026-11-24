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

For `E : EllipticCurveGeom S`, the zero section `E.zero : S ⟶ E.carrier` cuts out a relative
effective Cartier divisor `[0]` (`zeroSectionDivisor`), and `n[0]` is finite locally free of rank
`n` over `S`. Dualizing `𝒪_E(-n[0])` gives the **pole sheaf** `𝒪_E(n[0])` (`poleSheaf E n`). Both
`n[0]` and `[𝒪_E(n[0])]` commute with pointed cartesian squares and pointed Weierstrass charts.
Combining chart-wise ampleness on projective Weierstrass models (`n > 0`) with descent over a
quasi-affine base yields global ampleness of `𝒪_E(n[0])` over any quasi-affine `S`.

## Main definitions and results

* `zeroSectionDivisor`, `poleSheaf`: relative divisor `[0]` and invertible pole sheaf `𝒪_E(n[0])`.
* `isRelativeEffectiveCartier_zeroSectionDivisor` / `_pow`, `finrank_zeroSectionDivisor_pow`.
* `zeroSectionDivisor_eq_comap_of_isPullback`, `pullback_mk_poleSheaf_of_isPullback`,
  `pullback_mk_poleSheaf_projModel_of_isPullback`, `pullback_mk_poleSheaf_of_isPullback_projModel`.
* `pullback_toTotal_mk_poleSheaf`, `isAmple_pullback_toTotal_poleSheaf`.
* `exists_isAffineOpen_isAmple_pullback_poleSheaf`, `exists_opens_isAmple_pullback_poleSheaf`,
  `isAmple_poleSheaf`.

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

/-! ### The zero-section divisor `[0]` and its multiples `n[0]` -/

/-- The relative divisor `[0]` on `E`, represented by the ideal sheaf of `E.zero`. -/
noncomputable def zeroSectionDivisor : E.carrier.IdealSheafData := E.zero.ker

/-- `zeroSectionDivisor E` is the kernel ideal sheaf of `E.zero`. -/
theorem zeroSectionDivisor_def : E.zeroSectionDivisor = E.zero.ker := (rfl)

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

/-- The closed subscheme `n[0]` is locally of finite presentation (hence finite locally free). -/
instance locallyOfFinitePresentation_zeroSectionDivisor_pow (n : ℕ) :
    LocallyOfFinitePresentation ((E.zeroSectionDivisor ^ n).subschemeι ≫ E.structureMap) :=
  have : Smooth E.structureMap := SmoothOfRelativeDimension.smooth 1 _
  TauCeti.locallyOfFinitePresentation_subschemeι_comp_of_isEffectiveCartier
    (E.isRelativeEffectiveCartier_zeroSectionDivisor_pow n).isEffectiveCartier

/-- The support of the zero-section divisor `[0]` is the image of `E.zero`. -/
theorem coe_support_zeroSectionDivisor :
    (E.zeroSectionDivisor.support : Set E.carrier) = Set.range E.zero := by
  rw [zeroSectionDivisor_def, Scheme.Hom.support_ker,
    E.zero.isClosedEmbedding.isClosed_range.closure_eq]

/-- The divisor `n[0]` has constant rank `n` over every point of `S`. -/
@[simp] theorem finrank_zeroSectionDivisor_pow (n : ℕ) (s : S) :
    ((E.zeroSectionDivisor ^ n).subschemeι ≫ E.structureMap).finrank s = n := by
  have hpow : E.zeroSectionDivisor ^ n = ∏ _ : Fin n, E.zeroSectionDivisor := by simp
  have : IsFinite ((∏ _ : Fin n, E.zeroSectionDivisor).subschemeι ≫ E.structureMap) :=
    hpow ▸ inferInstance
  rw [hpow, finrank_prod_subschemeι_comp Finset.univ (fun _ : Fin n ↦ E.zeroSectionDivisor)
    (fun _ _ ↦ E.isRelativeEffectiveCartier_zeroSectionDivisor)]
  have hr : (E.zeroSectionDivisor.subschemeι ≫ E.structureMap).finrank = 1 :=
    Scheme.Hom.finrank_ker_comp_eq_one_of_comp_eq_id E.zero E.zero_comp
  simp [hr]

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
  have h₁ := E.isRelativeEffectiveCartier_zeroSectionDivisor.isEffectiveCartier
  rw [poleSheaf_def,
    LineBundleClass.mk_dual_toInvertibleSheaf_congr _ (TauCeti.isEffectiveCartier_pow h₁ n) rfl,
    LineBundleClass.mk_dual_toInvertibleSheaf_pow h₁ n]
  congr 1; rw [poleSheaf_def, LineBundleClass.mk_dual_toInvertibleSheaf_congr _ h₁ (pow_one _)]

/-- `𝒪_E(0[0])` has trivial class in the Picard group of `E.carrier`. -/
@[simp] theorem mk_poleSheaf_zero : LineBundleClass.mk (E.poleSheaf 0) = 1 := by
  rw [E.mk_poleSheaf_eq_pow 0, pow_zero]

/-- In the Picard group of `E.carrier`, `[𝒪_E((m + n)[0])] = [𝒪_E(m[0])] * [𝒪_E(n[0])]`. -/
theorem mk_poleSheaf_add (m n : ℕ) : LineBundleClass.mk (E.poleSheaf (m + n)) =
    LineBundleClass.mk (E.poleSheaf m) * LineBundleClass.mk (E.poleSheaf n) := by
  rw [E.mk_poleSheaf_eq_pow (m + n), E.mk_poleSheaf_eq_pow m, E.mk_poleSheaf_eq_pow n, pow_add]

/-! ### Base-change functoriality and comparison with projective Weierstrass models -/

section BaseChange

variable {E} {S' : Scheme.{u}} {E' : EllipticCurveGeom S'} {g : E'.carrier ⟶ E.carrier}
  {f : S' ⟶ S} (hg : IsPullback g E'.structureMap E.structureMap f) (h0 : E'.zero ≫ g = f ≫ E.zero)

include hg h0 in
/-- `[0]` commutes with base change along any pointed cartesian square of elliptic curves. -/
theorem zeroSectionDivisor_eq_comap_of_isPullback :
    E'.zeroSectionDivisor = E.zeroSectionDivisor.comap g :=
  hg.ker_eq_comap_of_comp_eq_id E.zero_comp E'.zero_comp h0

include hg h0 in
/-- `n[0]` commutes with base change along any pointed cartesian square of elliptic curves. -/
theorem zeroSectionDivisor_pow_eq_comap_of_isPullback (n : ℕ) :
    E'.zeroSectionDivisor ^ n = (E.zeroSectionDivisor ^ n).comap g := by
  rw [zeroSectionDivisor_eq_comap_of_isPullback hg h0, Scheme.IdealSheafData.comap_pow]

include hg h0 in
/-- Along a pointed cartesian square `g : E' ⟶ E`, `[𝒪_E(n[0])]` pulls back to `[𝒪_{E'}(n[0])]`. -/
theorem pullback_mk_poleSheaf_of_isPullback (n : ℕ) :
    LineBundleClass.pullback g (LineBundleClass.mk (E.poleSheaf n)) =
      LineBundleClass.mk (E'.poleSheaf n) :=
  (E.isRelativeEffectiveCartier_zeroSectionDivisor_pow
    n).isEffectiveCartier.pullback_mk_dual_toInvertibleSheaf_of_eq_comap
    (E'.isRelativeEffectiveCartier_zeroSectionDivisor_pow n).isEffectiveCartier
    (zeroSectionDivisor_pow_eq_comap_of_isPullback hg h0 n)

end BaseChange

/-- Under `E.baseChange f`, `[0]` is the inverse image of `[0]` on `E`. -/
@[simp] theorem zeroSectionDivisor_baseChange {T : Scheme.{u}} (f : T ⟶ S) :
    (E.baseChange f).zeroSectionDivisor =
      E.zeroSectionDivisor.comap ((E.baseChangeIso f).hom ≫ pullback.fst E.structureMap f) :=
  zeroSectionDivisor_eq_comap_of_isPullback (E.isPullback_baseChange f)
    (by simp [← Category.assoc, E.zero_baseChangeIso_hom, pullbackSection_fst])

/-- Under `E.baseChange f`, `n[0]` is the inverse image of `n[0]` on `E`. -/
theorem zeroSectionDivisor_pow_baseChange {T : Scheme.{u}} (f : T ⟶ S) (n : ℕ) :
    (E.baseChange f).zeroSectionDivisor ^ n = (E.zeroSectionDivisor ^ n).comap
      ((E.baseChangeIso f).hom ≫ pullback.fst E.structureMap f) := by
  rw [E.zeroSectionDivisor_baseChange f, Scheme.IdealSheafData.comap_pow]

/-- Under `E.baseChange f`, `[𝒪_E(n[0])]` pulls back to `[𝒪_{E.baseChange f}(n[0])]`. -/
theorem pullback_mk_poleSheaf_baseChange {T : Scheme.{u}} (f : T ⟶ S) (n : ℕ) :
    LineBundleClass.pullback ((E.baseChangeIso f).hom ≫ pullback.fst E.structureMap f)
        (LineBundleClass.mk (E.poleSheaf n)) = LineBundleClass.mk ((E.baseChange f).poleSheaf n) :=
  pullback_mk_poleSheaf_of_isPullback (E.isPullback_baseChange f)
    (by simp [← Category.assoc, E.zero_baseChangeIso_hom, pullbackSection_fst]) n

section ToProjModel

variable {E} {R : Type u} [CommRing R] {W : WeierstrassCurve R} {g : E.carrier ⟶ W.projModel}
  {f : S ⟶ Spec (.of R)} (hg : IsPullback g E.structureMap W.projModelOver f)
  (h0 : E.zero ≫ g = f ≫ W.projModelZero)

include hg h0 in
/-- Along a pointed cartesian square from `E` to `W.projModel`, `[0]` pulls back from `W`. -/
theorem zeroSectionDivisor_eq_comap_projModel_of_isPullback :
    E.zeroSectionDivisor = W.zeroSectionDivisor.comap g := by
  rw [E.zeroSectionDivisor_def, W.zeroSectionDivisor_def]
  exact hg.ker_eq_comap_of_comp_eq_id W.projModelZero_projModelOver E.zero_comp h0

include hg h0 in
/-- Along a pointed cartesian square from `E` to `W.projModel`, `n[0]` pulls back from `W`. -/
theorem zeroSectionDivisor_pow_eq_comap_projModel_of_isPullback (n : ℕ) :
    E.zeroSectionDivisor ^ n = (W.zeroSectionDivisor ^ n).comap g := by
  rw [zeroSectionDivisor_eq_comap_projModel_of_isPullback hg h0, Scheme.IdealSheafData.comap_pow]

include hg h0 in
/-- Along a pointed cartesian square from `E` to `W.projModel`, `[𝒪_W(n[0])]` pulls back to `E`. -/
theorem pullback_mk_poleSheaf_projModel_of_isPullback (n : ℕ) :
    LineBundleClass.pullback g (LineBundleClass.mk (W.poleSheaf n)) =
      LineBundleClass.mk (E.poleSheaf n) := by
  rw [W.poleSheaf_def, E.poleSheaf_def]
  exact (W.isEffectiveCartier_zeroSectionDivisor_pow
    n).pullback_mk_dual_toInvertibleSheaf_of_eq_comap
    (E.isRelativeEffectiveCartier_zeroSectionDivisor_pow n).isEffectiveCartier
    (zeroSectionDivisor_pow_eq_comap_projModel_of_isPullback hg h0 n)

end ToProjModel

section FromProjModel

variable {E} {R : Type u} [CommRing R] {W : WeierstrassCurve R} {g : W.projModel ⟶ E.carrier}
  {f : Spec (.of R) ⟶ S} (hg : IsPullback g W.projModelOver E.structureMap f)
  (h0 : W.projModelZero ≫ g = f ≫ E.zero)

include hg h0 in
/-- Along a pointed cartesian square from `W.projModel` to `E`, `[0]` pulls back from `E`. -/
theorem zeroSectionDivisor_projModel_eq_comap_of_isPullback :
    W.zeroSectionDivisor = E.zeroSectionDivisor.comap g := by
  rw [W.zeroSectionDivisor_def, E.zeroSectionDivisor_def]
  exact hg.ker_eq_comap_of_comp_eq_id E.zero_comp W.projModelZero_projModelOver h0

include hg h0 in
/-- Along a pointed cartesian square from `W.projModel` to `E`, `n[0]` pulls back from `E`. -/
theorem zeroSectionDivisor_pow_projModel_eq_comap_of_isPullback (n : ℕ) :
    W.zeroSectionDivisor ^ n = (E.zeroSectionDivisor ^ n).comap g := by
  rw [zeroSectionDivisor_projModel_eq_comap_of_isPullback hg h0, Scheme.IdealSheafData.comap_pow]

include hg h0 in
/-- Along a pointed cartesian square from `W.projModel` to `E`, `[𝒪_E(n[0])]` pulls back to `W`. -/
theorem pullback_mk_poleSheaf_of_isPullback_projModel (n : ℕ) :
    LineBundleClass.pullback g (LineBundleClass.mk (E.poleSheaf n)) =
      LineBundleClass.mk (W.poleSheaf n) := by
  rw [E.poleSheaf_def, W.poleSheaf_def]
  exact (E.isRelativeEffectiveCartier_zeroSectionDivisor_pow
    n).isEffectiveCartier.pullback_mk_dual_toInvertibleSheaf_of_eq_comap
    (W.isEffectiveCartier_zeroSectionDivisor_pow n)
    (zeroSectionDivisor_pow_projModel_eq_comap_of_isPullback hg h0 n)

end FromProjModel

/-! ### Compatibility on pointed Weierstrass charts and ampleness -/

section Chart

variable (c : PointedWeierstrassChart E.structureMap E.zero)

/-- On a pointed Weierstrass chart `c`, `[0]` restricts to `c.equation.zeroSectionDivisor`. -/
theorem zeroSectionDivisor_comap_toTotal :
    E.zeroSectionDivisor.comap c.toTotal = c.equation.zeroSectionDivisor.comap c.modelIso.hom := by
  have h := congrArg (fun I ↦ I.comap c.modelIso.hom)
    (zeroSectionDivisor_projModel_eq_comap_of_isPullback c.isPullback_modelIso_inv_toTotal
      c.projModelZero_modelIso_inv_toTotal)
  simpa only [← Scheme.IdealSheafData.comap_comp, Iso.hom_inv_id_assoc] using h.symm

/-- On a pointed Weierstrass chart `c`, `n[0]` restricts to `c.equation.zeroSectionDivisor ^ n`. -/
theorem zeroSectionDivisor_pow_comap_toTotal (n : ℕ) :
    (E.zeroSectionDivisor ^ n).comap c.toTotal =
      (c.equation.zeroSectionDivisor ^ n).comap c.modelIso.hom := by
  rw [Scheme.IdealSheafData.comap_pow, Scheme.IdealSheafData.comap_pow,
    E.zeroSectionDivisor_comap_toTotal c]

/-- **Chart compatibility of `𝒪_E(n[0])`.** On a pointed Weierstrass chart `c`, `[𝒪_E(n[0])]`
restricts along `c.toTotal` to the pullback of `[𝒪_{c.equation}(n[0])]` along `c.modelIso.hom`. -/
theorem pullback_toTotal_mk_poleSheaf (n : ℕ) :
    LineBundleClass.pullback c.toTotal (LineBundleClass.mk (E.poleSheaf n)) =
      LineBundleClass.pullback c.modelIso.hom (LineBundleClass.mk (c.equation.poleSheaf n)) := by
  simpa only [LineBundleClass.pullback_comp, Iso.hom_inv_id_assoc] using
    congrArg (LineBundleClass.pullback c.modelIso.hom)
      (pullback_mk_poleSheaf_of_isPullback_projModel c.isPullback_modelIso_inv_toTotal
        c.projModelZero_modelIso_inv_toTotal n)

/-- On any pointed Weierstrass chart `c`, `𝒪_E(n[0])` restricts to an ample bundle for `n > 0`. -/
theorem isAmple_pullback_toTotal_poleSheaf {n : ℕ} (hn : 0 < n) :
    (LineBundleClass.pullback c.toTotal (LineBundleClass.mk (E.poleSheaf n))).IsAmple := by
  rw [E.pullback_toTotal_mk_poleSheaf c n]
  exact (c.equation.isAmple_poleSheaf hn).pullback_of_isIso c.modelIso.hom

end Chart

/-- Every `s : S` has an affine open neighbourhood `U` over which `𝒪_E(n[0])` (`n > 0`) is ample. -/
theorem exists_isAffineOpen_isAmple_pullback_poleSheaf {n : ℕ} (hn : 0 < n) (s : S) :
    ∃ U : S.affineOpens, s ∈ U.val ∧ (LineBundleClass.pullback (E.structureMap ⁻¹ᵁ U.val).ι
      (LineBundleClass.mk (E.poleSheaf n))).IsAmple := by
  obtain ⟨U, hsU, W, _, e, hover, hzero⟩ :=
    (isLocallyWeierstrass_iff E.zero_comp).mp E.isLocallyWeierstrass s
  refine ⟨U, hsU, ?_⟩
  have hg : IsPullback (e.inv ≫ pullback.fst E.structureMap U.val.ι) W.projModelOver E.structureMap
      (U.property.isoSpec.inv ≫ U.val.ι) :=
    (IsPullback.of_hasPullback E.structureMap U.val.ι).of_iso e (.refl _) U.property.isoSpec
      (.refl _) (by simp) hover.symm (by simp) (by simp)
  have h0 : W.projModelZero ≫ e.inv ≫ pullback.fst E.structureMap U.val.ι =
      (U.property.isoSpec.inv ≫ U.val.ι) ≫ E.zero := by rw [← hzero]; simp
  rw [← pullbackRestrictIsoRestrict_inv_fst E.structureMap U.val,
    ← Iso.hom_inv_id_assoc e (pullback.fst E.structureMap U.val.ι), ← Category.assoc,
    ← LineBundleClass.pullback_comp, pullback_mk_poleSheaf_of_isPullback_projModel hg h0 n]
  exact (W.isAmple_poleSheaf hn).pullback_of_isIso _

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
