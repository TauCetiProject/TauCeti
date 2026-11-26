/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Curve.Homothety
public import TauCeti.RingTheory.FormalGroup.Rescale.Hom

/-!
# Curves on rescaled formal group laws

For a formal group law `F` over a commutative ring `R` and any scalar `s : R` (unit or not),
`FormalGroup.rescaleHom F s : FormalGroupHom (F.rescale s) F` sends `X` to `s X`. Pushing a curve
`γ` on `F.rescale s` forward along `F.rescaleHom s` multiplies its underlying power series by `s`,
is injective whenever `s` is left-regular, and sends the tautological curve of `F.rescale s` to
Cartier's homothety `[s]` of the tautological curve of `F`. Together with
`TauCeti.FormalGroupHom.rescale`, this relates curves and homomorphisms on `F.rescale s` to those on
`F` without requiring `s` to be invertible.

## Main results

* `FormalGroup.toPowerSeries_mapCurve_rescaleHom`: pushing a curve on `F.rescale s` forward along
  `F.rescaleHom s` scales its underlying power series by `s`.
* `FormalGroup.mapCurve_rescaleHom_injective`: pushing curves forward along `F.rescaleHom s` is
  injective whenever `s` is left-regular.
* `FormalGroup.mapCurve_rescaleHom_tautologicalCurve`: `F.rescaleHom s` sends the tautological curve
  of `F.rescale s` to `F.homothetyCurve s F.tautologicalCurve`.
* `TauCeti.FormalGroupHom.smul_toPowerSeries_mapCurve_rescale`: multiplying `(f.rescale s).mapCurve`
  by `s` recovers `f.mapCurve` composed with `(F.rescaleHom s).mapCurve`.

## References

* P. Cartier, *Modules associés à un groupe formel commutatif. Courbes typiques*, C. R. Acad. Sci.
  Paris Sér. A-B 265 (1967), A129–A132.
* [M. Hazewinkel, *Formal Groups and Applications*][hazewinkel1978], Chapter I, §1 and Chapter III,
  §16.
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.2 and IV.6.
-/

public section

namespace FormalGroup

open TauCeti (FormalGroupHom)

variable {R : Type*} [CommRing R]

/-- Pushing a curve on `F.rescale s` forward along `F.rescaleHom s` scales its power series by
`s`. -/
theorem toPowerSeries_mapCurve_rescaleHom (F : FormalGroup R) (s : R)
    (γ : (F.rescale s).Curve) :
    ((F.rescaleHom s).mapCurve γ).toPowerSeries = s • γ.toPowerSeries := by
  rw [FormalGroupHom.toPowerSeries_mapCurve, rescaleHom_toPowerSeries,
    PowerSeries.subst_smul γ.hasSubst, PowerSeries.subst_X γ.hasSubst]

/-- When `s` is left-regular, pushing curves forward along `F.rescaleHom s` is injective. -/
theorem mapCurve_rescaleHom_injective (F : FormalGroup R) {s : R} (hs : IsLeftRegular s) :
    Function.Injective (F.rescaleHom s).mapCurve := by
  intro γ₁ γ₂ h
  ext k
  have hk := congrArg (fun c : F.Curve ↦ PowerSeries.coeff k c.toPowerSeries) h
  rw [toPowerSeries_mapCurve_rescaleHom, toPowerSeries_mapCurve_rescaleHom,
    PowerSeries.coeff_smul, PowerSeries.coeff_smul, smul_eq_mul, smul_eq_mul] at hk
  exact hs hk

/-- Pushing the tautological curve of `F.rescale s` forward along `F.rescaleHom s` yields Cartier's
homothety `[s]` of the tautological curve of `F`. -/
theorem mapCurve_rescaleHom_tautologicalCurve (F : FormalGroup R) (s : R) :
    (F.rescaleHom s).mapCurve (F.rescale s).tautologicalCurve =
      F.homothetyCurve s F.tautologicalCurve := by
  apply Curve.ext
  rw [toPowerSeries_mapCurve_rescaleHom, toPowerSeries_homothetyCurve,
    toPowerSeries_tautologicalCurve, toPowerSeries_tautologicalCurve,
    PowerSeries.rescale_X, PowerSeries.smul_eq_C_mul]

/-- Pushing a curve `γ` on `F.rescale s` forward along a rescaled homomorphism `f.rescale s` and
scaling by `s` agrees with pushing `γ` along `F.rescaleHom s` and then `f`. -/
theorem _root_.TauCeti.FormalGroupHom.smul_toPowerSeries_mapCurve_rescale {F G : FormalGroup R}
    (f : FormalGroupHom F G) (s : R) (γ : (F.rescale s).Curve) :
    s • ((f.rescale s).mapCurve γ).toPowerSeries =
      (f.mapCurve ((F.rescaleHom s).mapCurve γ)).toPowerSeries := by
  have h := congrArg (fun g : FormalGroupHom (F.rescale s) G ↦ (g.mapCurve γ).toPowerSeries)
    (f.rescaleHom_comp_rescale s)
  rwa [FormalGroupHom.comp_mapCurve, FormalGroupHom.comp_mapCurve,
    toPowerSeries_mapCurve_rescaleHom] at h

end FormalGroup
