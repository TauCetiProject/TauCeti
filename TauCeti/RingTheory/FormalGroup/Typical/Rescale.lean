/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Curve.Rescale
public import TauCeti.RingTheory.FormalGroup.Typical

/-!
# Rescaling `p`-typical formal group laws and canonical `p`-typicalizations

For any commutative formal group law `F` over a commutative ring `R` and any scalar `s : R` (unit
or not, zero divisor or not), `FormalGroup.rescale F s` multiplies each degree-`n` coefficient of
`F(X, Y)` by `s ^ (n - 1)`. When `s` is not invertible, `F.rescale s` is not isomorphic to `F`, so
compatibility with `p`-typicality and canonical `p`-typicalization cannot be deduced from unit
homothety transport (`FormalGroup.isPTypical_homothety_smul_iff` and
`FormalGroup.pTypicalFormalGroup_homothety_smul`).

By proving compatibility first when the scale is left-regular via `FormalGroup.rescaleHom`,
lifting to the generic regular polynomial indeterminate `Polynomial.X` over `Polynomial R`, and
specializing along `Polynomial.evalRingHom s`, this file proves that over **every** commutative ring
`R` and for **every** `s : R`:

* rescaling preserves `p`-typicality (`FormalGroup.IsPTypical.rescale`);
* rescaling `F` by `s` rescales both Cartier's `p`-typicalization of the tautological curve and the
  canonical `p`-typicalization coordinate via `TauCeti.FormalGroupHom.rescale`, multiplying their
  degree-`n` coefficients by `s ^ (n - 1)`;
* canonical `p`-typicalization commutes with rescaling (`FormalGroup.pTypicalFormalGroup_rescale`).

## Main results

* `FormalGroup.IsPTypical.rescale`: if `F` is `p`-typical, then `F.rescale s` is `p`-typical for
  every `s : R`.
* `FormalGroup.inv_pTypicalCoordinate_rescale_toPowerSeries` and
  `FormalGroup.pTypicalCoordinate_rescale_toPowerSeries`: the canonical `p`-typicalization
  coordinate of `F.rescale s` and its inverse agree as power series with the rescaled isomorphisms
  `(F.pTypicalIso p hunit).toHom.rescale s` and `(F.pTypicalIso p hunit).invHom.rescale s`.
* `FormalGroup.coeff_pTypicalCoordinate_rescale`: degree-`n` coefficients of `F.pTypicalCoordinate`
  scale by `s ^ (n - 1)` under `F.rescale s`.
* `FormalGroup.pTypicalFormalGroup_rescale`: `(F.rescale s).pTypicalFormalGroup p hunit =
  (F.pTypicalFormalGroup p hunit).rescale s`.

## References

* P. Cartier, *Modules associés à un groupe formel commutatif. Courbes typiques*, C. R. Acad. Sci.
  Paris Sér. A-B 265 (1967), A129–A132.
* D. Quillen, *On the formal group laws of unoriented and complex cobordism theory*, Bull. Amer.
  Math. Soc. 75 (1969), 1293–1298.
* [M. Hazewinkel, *Formal Groups and Applications*][hazewinkel1978], Chapter I, §1 and Chapter III,
  §16.
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.2 and IV.6.
-/

public section

namespace FormalGroup

open TauCeti (FormalCoordinate FormalGroupHom FormalGroupIso)

variable {R : Type*} [CommRing R]

private theorem isPTypical_rescale_of_isLeftRegular {F : FormalGroup R} [F.IsComm] {p : ℕ}
    (hF : F.IsPTypical p) {s : R} (hs : IsLeftRegular s) : (F.rescale s).IsPTypical p := by
  rw [isPTypical_def, Curve.isPTypical_def]
  intro q hq hqp
  apply F.mapCurve_rescaleHom_injective hs
  have h0 : F.frobeniusCurve q hq.ne_zero (F.homothetyCurve s F.tautologicalCurve) = 0 :=
    (hF.tautologicalCurve.homothetyCurve s).frobeniusCurve_eq_zero hq hqp
  rw [(F.rescaleHom s).mapCurve_frobeniusCurve, mapCurve_rescaleHom_tautologicalCurve,
    map_zero, h0]

/-- Rescaling a `p`-typical commutative formal group law by any element `s : R` (zero divisor or
not) preserves `p`-typicality. -/
theorem IsPTypical.rescale {F : FormalGroup R} [F.IsComm] {p : ℕ} (hF : F.IsPTypical p) (s : R) :
    (F.rescale s).IsPTypical p := by
  have hgen : ((F.map Polynomial.C).rescale Polynomial.X).IsPTypical p :=
    isPTypical_rescale_of_isLeftRegular (hF.map Polynomial.C) Polynomial.isRegular_X.left
  have hlaw : ((F.map Polynomial.C).rescale Polynomial.X).map (Polynomial.evalRingHom s) =
      F.rescale s := by
    simp [Polynomial.evalRingHom, map_comp]
  exact (isPTypical_congr hlaw p).mp (hgen.map (Polynomial.evalRingHom s))

section CanonicalTypicalization

variable (F : FormalGroup R) [F.IsComm]

private theorem inv_pTypicalCoordinate_rescale_toPowerSeries_of_isLeftRegular (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {s : R} (hs : IsLeftRegular s) :
    ((F.rescale s).pTypicalCoordinate p hunit)⁻¹.toPowerSeries =
      ((F.pTypicalIso p hunit).invHom.rescale s).toPowerSeries := by
  have hreg : IsSMulRegular (PowerSeries R) s := .pi fun _ ↦ hs.isSMulRegular
  refine hreg ?_
  have hLHS : s • ((F.rescale s).pTypicalCoordinate p hunit)⁻¹.toPowerSeries =
      PowerSeries.rescale s
        (F.pTypicalProjectorCurve p hunit F.tautologicalCurve).toPowerSeries :=
    calc s • ((F.rescale s).pTypicalCoordinate p hunit)⁻¹.toPowerSeries
        = ((F.rescaleHom s).mapCurve
            ((F.rescale s).pTypicalProjectorCurve p hunit
              (F.rescale s).tautologicalCurve)).toPowerSeries := by
          rw [toPowerSeries_mapCurve_rescaleHom, inv_pTypicalCoordinate_toPowerSeries]
      _ = (F.pTypicalProjectorCurve p hunit
            ((F.rescaleHom s).mapCurve (F.rescale s).tautologicalCurve)).toPowerSeries := by
          rw [(F.rescaleHom s).mapCurve_pTypicalProjectorCurve]
      _ = (F.homothetyCurve s
            (F.pTypicalProjectorCurve p hunit F.tautologicalCurve)).toPowerSeries := by
          rw [mapCurve_rescaleHom_tautologicalCurve, F.pTypicalProjectorCurve_homothetyCurve]
      _ = PowerSeries.rescale s
            (F.pTypicalProjectorCurve p hunit F.tautologicalCurve).toPowerSeries :=
          F.toPowerSeries_homothetyCurve s _
  have hRHS : s • ((F.pTypicalIso p hunit).invHom.rescale s).toPowerSeries =
      PowerSeries.rescale s
        (F.pTypicalProjectorCurve p hunit F.tautologicalCurve).toPowerSeries := by
    rw [(F.pTypicalIso p hunit).invHom.smul_rescale s, pTypicalIso_invHom_toPowerSeries]
  exact hLHS.trans hRHS.symm

/-- Rescaling `F` by any `s : R` rescales the inverse of `F.pTypicalCoordinate` via
`FormalGroupHom.rescale`. -/
theorem inv_pTypicalCoordinate_rescale_toPowerSeries (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (s : R) :
    ((F.rescale s).pTypicalCoordinate p hunit)⁻¹.toPowerSeries =
      ((F.pTypicalIso p hunit).invHom.rescale s).toPowerSeries := by
  have hPoly : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : Polynomial R) :=
    fun q hq hqp ↦ Polynomial.C_eq_natCast (R := R) q ▸ Polynomial.isUnit_C.mpr (hunit q hq hqp)
  have hgen := inv_pTypicalCoordinate_rescale_toPowerSeries_of_isLeftRegular (F.map Polynomial.C) p
    hPoly Polynomial.isRegular_X.left
  have heval := congrArg (PowerSeries.map (Polynomial.evalRingHom s)) hgen
  have hlaw : ((F.map Polynomial.C).rescale Polynomial.X).map (Polynomial.evalRingHom s) =
      F.rescale s := by
    simp [Polynomial.evalRingHom, map_comp]
  have hLHS : PowerSeries.map (Polynomial.evalRingHom s)
      (((F.map Polynomial.C).rescale Polynomial.X).pTypicalCoordinate p hPoly)⁻¹.toPowerSeries =
      ((F.rescale s).pTypicalCoordinate p hunit)⁻¹.toPowerSeries := by
    rw [← FormalCoordinate.toPowerSeries_map, map_inv,
      map_pTypicalCoordinate ((F.map Polynomial.C).rescale Polynomial.X)
        (Polynomial.evalRingHom s) p hPoly]
    exact congrArg (fun c : FormalCoordinate R ↦ c⁻¹.toPowerSeries)
      (pTypicalCoordinate_congr hlaw p hunit)
  have hRHS : PowerSeries.map (Polynomial.evalRingHom s)
      (((F.map Polynomial.C).pTypicalIso p hPoly).invHom.rescale Polynomial.X).toPowerSeries =
      ((F.pTypicalIso p hunit).invHom.rescale s).toPowerSeries := by
    ext n
    rw [PowerSeries.coeff_map, FormalGroupHom.coeff_rescale, FormalGroupHom.coeff_rescale,
      pTypicalIso_invHom_toPowerSeries, pTypicalIso_invHom_toPowerSeries,
      ← F.map_tautologicalCurve Polynomial.C, ← F.map_pTypicalProjectorCurve Polynomial.C p hunit,
      Curve.toPowerSeries_map, map_mul, map_pow, PowerSeries.coeff_map,
      Polynomial.coe_evalRingHom, Polynomial.eval_X, Polynomial.eval_C]
  exact hLHS.symm.trans (heval.trans hRHS)

/-- Cartier's `p`-typicalization of the tautological curve of `F.rescale s` has underlying power
series equal to `(F.pTypicalIso p hunit).invHom.rescale s`. -/
theorem toPowerSeries_pTypicalProjectorCurve_rescale_tautologicalCurve (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (s : R) :
    ((F.rescale s).pTypicalProjectorCurve p hunit (F.rescale s).tautologicalCurve).toPowerSeries =
      ((F.pTypicalIso p hunit).invHom.rescale s).toPowerSeries := by
  rw [← inv_pTypicalCoordinate_toPowerSeries, F.inv_pTypicalCoordinate_rescale_toPowerSeries]

/-- Rescaling `F` by any `s : R` rescales the canonical `p`-typicalization coordinate via
`FormalGroupHom.rescale`. -/
theorem pTypicalCoordinate_rescale_toPowerSeries (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (s : R) :
    ((F.rescale s).pTypicalCoordinate p hunit).toPowerSeries =
      ((F.pTypicalIso p hunit).toHom.rescale s).toPowerSeries := by
  let φ_s : FormalCoordinate R :=
    { toPowerSeries := ((F.pTypicalIso p hunit).toHom.rescale s).toPowerSeries
      constantCoeff_toPowerSeries := ((F.pTypicalIso p hunit).toHom.rescale s).zero_constantCoeff
      isUnit_coeff_one := by
        rw [FormalGroupHom.coeff_rescale, Nat.sub_self, pow_zero, one_mul,
          pTypicalIso_toHom_toPowerSeries, coeff_one_pTypicalCoordinate]
        exact isUnit_one }
  let ψ_s : FormalCoordinate R :=
    { toPowerSeries := ((F.pTypicalIso p hunit).invHom.rescale s).toPowerSeries
      constantCoeff_toPowerSeries := ((F.pTypicalIso p hunit).invHom.rescale s).zero_constantCoeff
      isUnit_coeff_one := by
        rw [FormalGroupHom.coeff_rescale, Nat.sub_self, pow_zero, one_mul,
          pTypicalIso_invHom_toPowerSeries, coeff_one_pTypicalProjectorCurve,
          toPowerSeries_tautologicalCurve, PowerSeries.coeff_one_X]
        exact isUnit_one }
  have hmul : φ_s * ψ_s = 1 := by
    apply FormalCoordinate.ext
    have hcomp := congrArg FormalGroupHom.toPowerSeries
      (FormalGroupHom.rescale_comp (F.pTypicalIso p hunit).toHom
        (F.pTypicalIso p hunit).invHom s).symm
    rw [FormalGroupIso.toHom_comp_invHom, FormalGroupHom.rescale_id,
      FormalGroupHom.id_toPowerSeries, FormalGroupHom.comp_toPowerSeries] at hcomp
    exact hcomp.trans FormalCoordinate.toPowerSeries_one.symm
  have hinv_eq : ((F.rescale s).pTypicalCoordinate p hunit)⁻¹ = ψ_s :=
    FormalCoordinate.ext (F.inv_pTypicalCoordinate_rescale_toPowerSeries p hunit s)
  exact congrArg FormalCoordinate.toPowerSeries
    (inv_injective (hinv_eq.trans (inv_eq_of_mul_eq_one_right hmul).symm))

/-- Degree-`n` coefficients of `F.pTypicalCoordinate` scale by `s ^ (n - 1)` under
`F.rescale s`. -/
@[simp]
theorem coeff_pTypicalCoordinate_rescale (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (s : R) (n : ℕ) :
    PowerSeries.coeff n ((F.rescale s).pTypicalCoordinate p hunit).toPowerSeries =
      s ^ (n - 1) * PowerSeries.coeff n (F.pTypicalCoordinate p hunit).toPowerSeries := by
  rw [F.pTypicalCoordinate_rescale_toPowerSeries p hunit s, FormalGroupHom.coeff_rescale,
    pTypicalIso_toHom_toPowerSeries]

/-- Canonical `p`-typicalization commutes with rescaling by any element `s : R` (unit or not). -/
theorem pTypicalFormalGroup_rescale (p : ℕ)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (s : R) :
    (F.rescale s).pTypicalFormalGroup p hunit = (F.pTypicalFormalGroup p hunit).rescale s := by
  rw [pTypicalFormalGroup_def]
  exact ((F.pTypicalIso p hunit).toHom.rescale s).smul_eq
    (F.pTypicalCoordinate_rescale_toPowerSeries p hunit s).symm

end CanonicalTypicalization

end FormalGroup
