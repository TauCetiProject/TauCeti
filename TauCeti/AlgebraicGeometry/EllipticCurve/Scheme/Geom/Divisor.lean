/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Section
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Divisor.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.BaseChange.Basic
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Degree.Sum
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Finite
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.FinitePresentation
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.ZeroSection
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange

/-!
# The zero-section divisor of an elliptic curve over a scheme

For `E : EllipticCurveGeom S`, the zero section `E.zero : S ⟶ E.carrier` cuts out a relative
effective Cartier divisor `[0]` (`EllipticCurveGeom.zeroSectionDivisor`), and every multiple
`n[0]` (`n : ℕ`) is finite locally free of constant rank `n` over `S`. Both `[0]` and `n[0]`
commute with arbitrary pointed cartesian squares (`zeroSectionDivisor_eq_comap_of_isPullback`),
base change (`zeroSectionDivisor_baseChange`), and pointed Weierstrass charts
(`zeroSectionDivisor_comap_toTotal`).

## Main definitions and results

* `EllipticCurveGeom.zeroSectionDivisor`: the relative divisor `[0]` on `E`, represented by
  `E.zero.ker`.
* `EllipticCurveGeom.isRelativeEffectiveCartier_zeroSectionDivisor` / `_pow` and
  `EllipticCurveGeom.finrank_zeroSectionDivisor_pow`: `n[0]` is a relative effective Cartier
  divisor of constant rank `n` over `S`.
* `EllipticCurveGeom.zeroSectionDivisor_eq_comap_of_isPullback` / `_pow_`,
  `EllipticCurveGeom.zeroSectionDivisor_baseChange` / `_pow_`, and
  `EllipticCurveGeom.zeroSectionDivisor_comap_toTotal` / `_pow_`: compatibility with pointed
  cartesian squares, base change, and pointed Weierstrass charts.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §2.2.
-/

public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.EllipticCurveGeom

variable {S : Scheme.{u}} (E : EllipticCurveGeom S)

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

end BaseChange

/-- Under `E.baseChange f`, `[0]` is the inverse image of `[0]` on `E`. -/
@[simp] theorem zeroSectionDivisor_baseChange {T : Scheme.{u}} (f : T ⟶ S) :
    (E.baseChange f).zeroSectionDivisor =
      E.zeroSectionDivisor.comap ((E.baseChangeIso f).hom ≫ pullback.fst E.structureMap f) :=
  zeroSectionDivisor_eq_comap_of_isPullback (E.isPullback_baseChange f)
    (E.zero_baseChangeIso_hom_comp_fst f)

/-- Under `E.baseChange f`, `n[0]` is the inverse image of `n[0]` on `E`. -/
theorem zeroSectionDivisor_pow_baseChange {T : Scheme.{u}} (f : T ⟶ S) (n : ℕ) :
    (E.baseChange f).zeroSectionDivisor ^ n = (E.zeroSectionDivisor ^ n).comap
      ((E.baseChangeIso f).hom ≫ pullback.fst E.structureMap f) := by
  rw [E.zeroSectionDivisor_baseChange f, Scheme.IdealSheafData.comap_pow]

section Chart

variable (c : PointedWeierstrassChart E.structureMap E.zero)

/-- On a pointed Weierstrass chart `c`, `[0]` restricts to `c.equation.zeroSectionDivisor`. -/
theorem zeroSectionDivisor_comap_toTotal :
    E.zeroSectionDivisor.comap c.toTotal = c.equation.zeroSectionDivisor.comap c.modelIso.hom := by
  have h := congrArg (fun I ↦ I.comap c.modelIso.hom)
    (c.isPullback_modelIso_inv_toTotal.ker_eq_comap_of_comp_eq_id
      E.zero_comp c.equation.projModelZero_projModelOver c.projModelZero_modelIso_inv_toTotal)
  rw [E.zeroSectionDivisor_def, c.equation.zeroSectionDivisor_def]
  simpa only [← Scheme.IdealSheafData.comap_comp, Iso.hom_inv_id_assoc] using h.symm

/-- On a pointed Weierstrass chart `c`, `n[0]` restricts to `c.equation.zeroSectionDivisor ^ n`. -/
theorem zeroSectionDivisor_pow_comap_toTotal (n : ℕ) :
    (E.zeroSectionDivisor ^ n).comap c.toTotal =
      (c.equation.zeroSectionDivisor ^ n).comap c.modelIso.hom := by
  rw [Scheme.IdealSheafData.comap_pow, Scheme.IdealSheafData.comap_pow,
    E.zeroSectionDivisor_comap_toTotal c]

end Chart

end TauCeti.AlgebraicGeometry.EllipticCurveGeom
