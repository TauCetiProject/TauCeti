/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.VariableChange
public import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.StrictHopfAlgebroid

/-!
# The universal strict Weierstrass formal coordinate transition

Over `A[r, s, t]` (`StrictArrowRing`), `strictFormalCoordinate` is the strict formal coordinate
transition carrying `formalGroup (WeierstrassCurve.map Universal.curve strictLeftUnit)` to
`formalGroup (WeierstrassCurve.map Universal.curve strictRightUnit)`. Its first four coefficients
are `1`, `-s`, `s² - r`, and `-t - s³ + 2 r s - a₁ r`, and it respects `strictCounit`,
`strictCoproduct`, `strictConjugation`, and specialization along `toStrict`.

## Main definitions and results

* `TauCeti.WeierstrassHopfAlgebroid.strictFormalCoordinate`: the universal strict Weierstrass formal
  coordinate transition over `StrictArrowRing`, with `strictFormalCoordinate_smul_formalGroup`.
* `TauCeti.WeierstrassHopfAlgebroid.coeff_one_strictFormalCoordinate`,
  `coeff_two_strictFormalCoordinate`, `coeff_three_strictFormalCoordinate`,
  `coeff_four_strictFormalCoordinate`: the low-degree coefficients `1`, `-s`, `s² - r`, and
  `-t - s³ + 2 r s - a₁ r`.
* `TauCeti.WeierstrassHopfAlgebroid.map_strictCounit_strictFormalCoordinate`,
  `map_strictCoproduct_strictFormalCoordinate`, `map_strictConjugation_strictFormalCoordinate`, and
  `map_toStrict_formalCoordinate`.

## References

* T. Bauer, *Computation of the homotopy of the spectrum tmf*, Geom. Topol. Monogr. 13 (2008), §3.
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1–IV.2.
-/

public section
noncomputable section

namespace TauCeti.WeierstrassHopfAlgebroid

open MvPolynomial _root_.WeierstrassCurve _root_.WeierstrassCurve.VariableChange
open TauCeti.WeierstrassChange

/-- The universal strict formal coordinate transition over `A[r, s, t]`, carrying
`formalGroup (WeierstrassCurve.map Universal.curve strictLeftUnit)` to
`formalGroup (WeierstrassCurve.map Universal.curve strictRightUnit)`. -/
def strictFormalCoordinate : TauCeti.FormalCoordinate StrictArrowRing :=
  ((heisenbergHom _ strictChange).formalCoordinate
    (WeierstrassCurve.map Universal.curve strictLeftUnit))⁻¹

/-- Definitional formula for `strictFormalCoordinate`. -/
theorem strictFormalCoordinate_def : strictFormalCoordinate =
    ((heisenbergHom _ strictChange).formalCoordinate
      (WeierstrassCurve.map Universal.curve strictLeftUnit))⁻¹ := (rfl)

/-- `strictFormalCoordinate` equals the formal coordinate transition of
`(heisenbergHom _ strictChange)⁻¹` from `WeierstrassCurve.map Universal.curve strictRightUnit`. -/
theorem strictFormalCoordinate_eq_formalCoordinate_inv : strictFormalCoordinate =
    (heisenbergHom _ strictChange)⁻¹.formalCoordinate
      (WeierstrassCurve.map Universal.curve strictRightUnit) := by
  rw [strictFormalCoordinate_def, map_strictRightUnit, formalCoordinate_inv]

/-- `strictFormalCoordinate` has unit linear coefficient `1`. -/
@[simp] theorem linearCoeff_strictFormalCoordinate :
    TauCeti.FormalCoordinate.linearCoeff strictFormalCoordinate = 1 := by
  simp [strictFormalCoordinate]

/-- `strictFormalCoordinate` lies in the subgroup of strict formal coordinates. -/
theorem strictFormalCoordinate_mem_ker_linearCoeff :
    strictFormalCoordinate ∈ (TauCeti.FormalCoordinate.linearCoeff (R := StrictArrowRing)).ker :=
  MonoidHom.mem_ker.mpr linearCoeff_strictFormalCoordinate

/-- `strictFormalCoordinate` transports
`formalGroup (WeierstrassCurve.map Universal.curve strictLeftUnit)` to
`formalGroup (WeierstrassCurve.map Universal.curve strictRightUnit)`. -/
theorem strictFormalCoordinate_smul_formalGroup :
    strictFormalCoordinate • formalGroup (WeierstrassCurve.map Universal.curve strictLeftUnit) =
      formalGroup (WeierstrassCurve.map Universal.curve strictRightUnit) := by
  rw [strictFormalCoordinate_def, map_strictRightUnit, formalGroup_smul]

/-- Base change of `strictFormalCoordinate` along `k : StrictArrowRing →+* R`. -/
theorem map_strictFormalCoordinate {R : Type*} [CommRing R] (k : StrictArrowRing →+* R) :
    strictFormalCoordinate.map k =
      ((heisenbergHom R (HeisenbergGroup.map k strictChange)).formalCoordinate
        (WeierstrassCurve.map Universal.curve (k.comp strictLeftUnit)))⁻¹ := by
  rw [strictFormalCoordinate_def, _root_.map_inv, ← VariableChange.map_formalCoordinate,
    VariableChange.map_heisenbergHom, WeierstrassCurve.map_map]

/-- Specializing `strictFormalCoordinate` along `(strictArrowEquiv R).symm (W, a)` recovers
`((heisenbergHom R a).formalCoordinate W)⁻¹`. -/
theorem map_strictArrowEquiv_symm_strictFormalCoordinate {R : Type*} [CommRing R]
    (W : WeierstrassCurve R) (a : TauCeti.HeisenbergGroup R) :
    strictFormalCoordinate.map ((strictArrowEquiv R).symm (W, a)) =
      ((heisenbergHom R a).formalCoordinate W)⁻¹ := by
  have h := (strictArrowEquiv R).apply_symm_apply (W, a)
  rw [strictArrowEquiv_apply, Prod.mk.injEq] at h
  rw [map_strictFormalCoordinate, h.1, h.2]

/-- Setting `u = 1` via `toStrict` carries the universal formal coordinate transition over
`Γ = A[u, u⁻¹, r, s, t]` to `strictFormalCoordinate⁻¹`. -/
@[simp] theorem map_toStrict_formalCoordinate :
    ((ChangeRing.universalChange (MvPolynomial Coeff ℤ)).formalCoordinate
      (WeierstrassCurve.map Universal.curve
        (algebraMap (MvPolynomial Coeff ℤ) ArrowRing))).map toStrict =
      strictFormalCoordinate⁻¹ := by
  rw [← VariableChange.map_formalCoordinate, WeierstrassCurve.map_map,
    universalChange_map_toStrict, toStrict_comp_algebraMap, strictFormalCoordinate_def, inv_inv]

/-- The linear coefficient of `strictFormalCoordinate` is `1`. -/
@[simp] theorem coeff_one_strictFormalCoordinate :
    PowerSeries.coeff 1 strictFormalCoordinate.toPowerSeries = 1 := by
  rw [strictFormalCoordinate_eq_formalCoordinate_inv, VariableChange.coeff_one_formalCoordinate]
  simp [inv_def]

/-- The coefficient of `z²` in `strictFormalCoordinate` is `-s` (`-X (.inr 1)`). -/
@[simp] theorem coeff_two_strictFormalCoordinate :
    PowerSeries.coeff 2 strictFormalCoordinate.toPowerSeries = -X (.inr 1) := by
  rw [strictFormalCoordinate_eq_formalCoordinate_inv, VariableChange.coeff_two_formalCoordinate]
  simp [inv_def]

/-- The coefficient of `z³` in `strictFormalCoordinate` is `s² - r` (`X (.inr 1) ^ 2 - X (.inr 0)`).
-/
@[simp] theorem coeff_three_strictFormalCoordinate :
    PowerSeries.coeff 3 strictFormalCoordinate.toPowerSeries = X (.inr 1) ^ 2 - X (.inr 0) := by
  rw [strictFormalCoordinate_eq_formalCoordinate_inv, VariableChange.coeff_three_formalCoordinate]
  simp [inv_def]; ring

/-- The coefficient of `z⁴` in `strictFormalCoordinate` is `-t - s³ + 2 r s - a₁ r`. -/
@[simp] theorem coeff_four_strictFormalCoordinate :
    PowerSeries.coeff 4 strictFormalCoordinate.toPowerSeries =
      -X (.inr 2) - X (.inr 1) ^ 3 + 2 * X (.inr 0) * X (.inr 1) -
        X (.inl .A₁) * X (.inr 0) := by
  rw [strictFormalCoordinate_eq_formalCoordinate_inv, VariableChange.coeff_four_formalCoordinate]
  simp [inv_def]; ring

/-- `strictCounit` maps `strictFormalCoordinate` to the identity coordinate `1`. -/
@[simp] theorem map_strictCounit_strictFormalCoordinate :
    strictFormalCoordinate.map strictCounit = 1 := by
  rw [map_strictFormalCoordinate, heisenbergGroupMap_strictCounit_strictChange, _root_.map_one,
    formalCoordinate_one, inv_one]

/-- `strictCoproduct` sends `strictFormalCoordinate` to the composite of the strict formal
coordinates of the right and left factors, by the cocycle law `formalCoordinate_mul`. -/
@[simp] theorem map_strictCoproduct_strictFormalCoordinate :
    strictFormalCoordinate.map strictCoproduct =
      strictFormalCoordinate.map strictRight * strictFormalCoordinate.map strictLeft := by
  set W₁ := WeierstrassCurve.map Universal.curve (strictLeft.comp strictLeftUnit)
  set C₁ := heisenbergHom StrictPairRing (HeisenbergGroup.map strictLeft strictChange)
  set C₂ := heisenbergHom StrictPairRing (HeisenbergGroup.map strictRight strictChange)
  -- (1) On the right factor, the source curve is `C₁ • W₁`.
  have hright : strictFormalCoordinate.map strictRight = (C₂.formalCoordinate (C₁ • W₁))⁻¹ := by
    rw [map_strictFormalCoordinate, strictRight_comp_strictLeftUnit, map_comp_strictRightUnit]
  -- (2) On the left factor, the source curve is `W₁`.
  have hleft : strictFormalCoordinate.map strictLeft = (C₁.formalCoordinate W₁)⁻¹ :=
    map_strictFormalCoordinate strictLeft
  -- Close by the cocycle identity for `(C₂ * C₁).formalCoordinate W₁`.
  rw [map_strictFormalCoordinate, heisenbergGroupMap_strictCoproduct_strictChange,
    strictCoproduct_comp_strictLeftUnit, _root_.map_mul, formalCoordinate_mul, mul_inv_rev,
    hright, hleft]

/-- `strictConjugation` maps `strictFormalCoordinate` to its inverse. -/
@[simp] theorem map_strictConjugation_strictFormalCoordinate :
    strictFormalCoordinate.map strictConjugation = strictFormalCoordinate⁻¹ := by
  rw [map_strictFormalCoordinate, heisenbergGroupMap_strictConjugation_strictChange,
    strictConjugation_comp_strictLeftUnit, _root_.map_inv,
    ← strictFormalCoordinate_eq_formalCoordinate_inv]

end TauCeti.WeierstrassHopfAlgebroid
