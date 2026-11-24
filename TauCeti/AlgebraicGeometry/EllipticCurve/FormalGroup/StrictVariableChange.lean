/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.VariableChange
public import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.StrictHopfAlgebroid
import Mathlib.Algebra.MvPolynomial.Monad

/-!
# The universal strict Weierstrass formal coordinate transition

Over `A[r, s, t] = StrictChangeRing ℤ[a₁, a₂, a₃, a₄, a₆]`, `Strict.formalCoordinate` carries
`formalGroup (WeierstrassCurve.map Universal.curve C)` to
`formalGroup (WeierstrassCurve.map Universal.curve rightUnit)`. Its first four coefficients are `1`,
`-s`, `s² - r`, and `-t - s³ + 2 r s - a₁ r`, and it respects `counit`, `coproduct`, and
`conjugation`.

## References

* T. Bauer, *Computation of the homotopy of the spectrum tmf*, Geom. Topol. Monogr. 13 (2008), §3.
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1–IV.2.
-/

public section
noncomputable section

namespace TauCeti.WeierstrassHopfAlgebroid.Strict

open MvPolynomial _root_.WeierstrassCurve _root_.WeierstrassCurve.VariableChange
open TauCeti.WeierstrassChange.StrictChangeRing

/-- The universal strict formal coordinate transition over `A[r, s, t]`, carrying
`formalGroup (WeierstrassCurve.map Universal.curve C)` to
`formalGroup (WeierstrassCurve.map Universal.curve rightUnit)`. -/
def formalCoordinate : TauCeti.FormalCoordinate ArrowRing :=
  ((universalChange (MvPolynomial Coeff ℤ)).formalCoordinate
    (WeierstrassCurve.map Universal.curve C))⁻¹
theorem formalCoordinate_def : formalCoordinate =
    ((universalChange (MvPolynomial Coeff ℤ)).formalCoordinate
      (WeierstrassCurve.map Universal.curve C))⁻¹ := (rfl)

/-- `Strict.formalCoordinate` equals the formal coordinate transition of `(universalChange _)⁻¹`
from `WeierstrassCurve.map Universal.curve rightUnit`. -/
theorem formalCoordinate_eq_formalCoordinate_inv : formalCoordinate =
    (universalChange (MvPolynomial Coeff ℤ))⁻¹.formalCoordinate
      (WeierstrassCurve.map Universal.curve rightUnit) := by
  rw [formalCoordinate_def, map_rightUnit, formalCoordinate_inv]

@[simp] theorem linearCoeff_formalCoordinate :
    TauCeti.FormalCoordinate.linearCoeff formalCoordinate = 1 := by simp [formalCoordinate]
theorem formalCoordinate_mem_ker_linearCoeff :
    formalCoordinate ∈ (TauCeti.FormalCoordinate.linearCoeff (R := ArrowRing)).ker :=
  MonoidHom.mem_ker.mpr linearCoeff_formalCoordinate

/-- `Strict.formalCoordinate` transports `formalGroup (WeierstrassCurve.map Universal.curve C)` to
`formalGroup (WeierstrassCurve.map Universal.curve rightUnit)`. -/
theorem formalCoordinate_smul_formalGroup :
    formalCoordinate • formalGroup (WeierstrassCurve.map Universal.curve C) =
      formalGroup (WeierstrassCurve.map Universal.curve rightUnit) := by
  rw [formalCoordinate_def, map_rightUnit, formalGroup_smul]

/-- Base change of `Strict.formalCoordinate` along `k : ArrowRing →+* R`. -/
theorem map_formalCoordinate {R : Type*} [CommRing R] (k : ArrowRing →+* R) :
    formalCoordinate.map k =
      (((universalChange (MvPolynomial Coeff ℤ)).map k).formalCoordinate
        (WeierstrassCurve.map Universal.curve (k.comp C)))⁻¹ := by
  rw [formalCoordinate_def, _root_.map_inv, ← VariableChange.map_formalCoordinate,
    WeierstrassCurve.map_map]
@[simp] theorem map_lift_formalCoordinate {R : Type*} [CommRing R] (W : WeierstrassCurve R)
    (a : TauCeti.HeisenbergGroup R) :
    formalCoordinate.map (lift (W.specialize, a)) = ((heisenbergHom R a).formalCoordinate W)⁻¹ := by
  simp [map_formalCoordinate, WeierstrassCurve.map_specialize]

/-- The linear coefficient of `Strict.formalCoordinate` is `1`. -/
@[simp] theorem coeff_one_formalCoordinate :
    PowerSeries.coeff 1 formalCoordinate.toPowerSeries = 1 := by
  rw [formalCoordinate_eq_formalCoordinate_inv, VariableChange.coeff_one_formalCoordinate]
  simp [inv_def]
/-- The coefficient of `z²` in `Strict.formalCoordinate` is `-s` (`-X 1`). -/
@[simp] theorem coeff_two_formalCoordinate :
    PowerSeries.coeff 2 formalCoordinate.toPowerSeries = -(X 1 : ArrowRing) := by
  rw [formalCoordinate_eq_formalCoordinate_inv, VariableChange.coeff_two_formalCoordinate]
  simp [inv_def]
/-- The coefficient of `z³` in `Strict.formalCoordinate` is `s² - r` (`X 1 ^ 2 - X 0`). -/
@[simp] theorem coeff_three_formalCoordinate :
    PowerSeries.coeff 3 formalCoordinate.toPowerSeries = X 1 ^ 2 - (X 0 : ArrowRing) := by
  rw [formalCoordinate_eq_formalCoordinate_inv, VariableChange.coeff_three_formalCoordinate]
  simp [inv_def]; ring
/-- The coefficient of `z⁴` in `Strict.formalCoordinate` is `-t - s³ + 2 r s - a₁ r`. -/
@[simp] theorem coeff_four_formalCoordinate :
    PowerSeries.coeff 4 formalCoordinate.toPowerSeries =
      -X 2 - X 1 ^ 3 + 2 * X 0 * X 1 - C (X .A₁) * (X 0 : ArrowRing) := by
  rw [formalCoordinate_eq_formalCoordinate_inv, VariableChange.coeff_four_formalCoordinate]
  simp [inv_def, variableChange_a₁]; ring

@[simp] theorem map_counit_formalCoordinate : formalCoordinate.map counit = 1 := by
  simp [Strict.map_formalCoordinate]
@[simp] theorem map_coproduct_formalCoordinate :
    formalCoordinate.map coproduct =
      formalCoordinate.map (MvPolynomial.map rightUnit) * formalCoordinate.map C := by
  rw [Strict.map_formalCoordinate, universalChange_map_coproduct, coproduct_comp_C,
    formalCoordinate_mul, mul_inv_rev,
    ← map_comp_rightUnit (C : ArrowRing →+* WeierstrassChange.StrictChangeRing ArrowRing),
    ← MvPolynomial.map_comp_C, ← universalChange_map_map (f := rightUnit),
    ← Strict.map_formalCoordinate, ← Strict.map_formalCoordinate]
@[simp] theorem map_conjugation_formalCoordinate :
    formalCoordinate.map conjugation = formalCoordinate⁻¹ := by
  rw [Strict.map_formalCoordinate, universalChange_map_conjugation, conjugation_comp_C,
    ← formalCoordinate_eq_formalCoordinate_inv]

end TauCeti.WeierstrassHopfAlgebroid.Strict
