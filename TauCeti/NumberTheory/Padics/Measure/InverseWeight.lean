/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Algebra
public import TauCeti.NumberTheory.Padics.Measure.Multiples
public import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# Dividing measures on `ℤ_p` by the coordinate on the units

Multiplying a measure `μ` on `ℤ_p` by the coordinate function `x` is the operator
`weight x`, whose Amice transform is the Mahler derivation. It is not injective, since it kills
`δ₀`, but it becomes invertible on the measures supported on the units `ℤ_pˣ`: the function
`x ↦ x⁻¹` on `ℤ_pˣ`, extended by `0` on `pℤ_p`, is continuous because `ℤ_pˣ` and `pℤ_p` are
complementary clopen subsets. Weighting by it is the operator `inverseWeight`, written `J`, and

`x · J μ = J (x · μ) = (restriction of μ to ℤ_pˣ)`.

Hence every measure supported on the units is `x · ν` for exactly one measure `ν` supported on the
units, namely `ν = J μ`. Iterating `J` twists a unit-supported measure by negative powers of the
coordinate, the inverse of the twists by positive powers that compute moments.

The statements are made for measures with values in a normed commutative `ℤ_p`-algebra `R`, the
coordinate being `x_R = ContinuousMap.id ℤ_[p] • 1 : C(ℤ_[p], R)` as in the moment formulas, and
are specialised to `R = ℤ_p`, where the coordinate is `x` itself.

## Main definitions

* `AbstractMeasure.ringInverse p R`: the continuous function `x ↦ x⁻¹` on `ℤ_pˣ`, `0` on `pℤ_p`,
  with values in `R`.
* `AbstractMeasure.inverseWeight`: the operator `J = weight (ringInverse p R)` on `D(ℤ_p, R)`.

## Main results

* `AbstractMeasure.weight_id_smul_one_inverseWeight` and
  `AbstractMeasure.inverseWeight_weight_id_smul_one`: `x · J μ` and `J (x · μ)` are both the
  restriction of `μ` to `ℤ_pˣ`.
* `AbstractMeasure.restrictMultiples_inverseWeight`: `J μ` is supported on `ℤ_pˣ`.
* `AbstractMeasure.inverseWeight_map_mulLeft`, `AbstractMeasure.inverseWeight_map_mulLeft_unit`:
  `J` commutes with dilation by `a`, up to the factor `ringInverse p R a`, which is `a⁻¹` for a
  unit `a`.
* `AbstractMeasure.existsUnique_unitSupported_div_id`: a measure supported on `ℤ_pˣ` is `x · ν`
  for a unique measure `ν` supported on `ℤ_pˣ`.

## References

* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, equation (4-3).
* P. Colmez, *Fonctions d'une variable p-adique*, §II.2.
-/

public noncomputable section

open ContinuousMap

namespace AbstractMeasure

open scoped AbstractMeasure

variable (p : ℕ) [Fact p.Prime] (R : Type*) [NormedCommRing R] [Algebra ℤ_[p] R]
  [ContinuousSMul ℤ_[p] R]

/-- The continuous function `x ↦ x⁻¹` on `ℤ_pˣ`, extended by `0` on `pℤ_p`, with values in a
`ℤ_p`-algebra `R`: the image in `R` of `Ring.inverse`, which is Mathlib's `PadicInt.inv`. -/
def ringInverse : C(ℤ_[p], R) :=
  ⟨fun x ↦ algebraMap ℤ_[p] R (Ring.inverse x),
    (continuous_algebraMap ℤ_[p] R).comp PadicInt.continuous_inverse⟩

variable {p R}

theorem ringInverse_apply (x : ℤ_[p]) :
    ringInverse p R x = algebraMap ℤ_[p] R (Ring.inverse x) :=
  (rfl)

/-- At a unit `u`, `ringInverse` is the inverse of `u`. -/
@[simp]
theorem ringInverse_unit (u : ℤ_[p]ˣ) :
    ringInverse p R u = algebraMap ℤ_[p] R ↑u⁻¹ := by
  rw [ringInverse_apply, Ring.inverse_unit]

/-- On `pℤ_p`, `ringInverse` vanishes. -/
@[simp]
theorem ringInverse_of_dvd {x : ℤ_[p]} (hx : (p : ℤ_[p]) ∣ x) : ringInverse p R x = 0 := by
  rw [ringInverse_apply, Ring.inverse_non_unit x (PadicInt.not_isUnit_iff_dvd.mpr hx), map_zero]

/-- `ringInverse` inverts the coordinate on `ℤ_pˣ`: the product of the two is the characteristic
function `1 - χ` of `ℤ_pˣ`. -/
theorem ringInverse_mul_id_smul_one :
    ringInverse p R * (ContinuousMap.id ℤ_[p] • 1) = 1 - pMultiplesIndicator p R := by
  ext x
  by_cases hx : (p : ℤ_[p]) ∣ x
  · simp [hx]
  · lift x to ℤ_[p]ˣ using not_not.mp (mt PadicInt.not_isUnit_iff_dvd.mp hx)
    simp [hx, ← Algebra.algebraMap_eq_smul_one, ← map_mul]

/-- `ringInverse` vanishes on `pℤ_p`, the support of the characteristic function `χ`. -/
theorem pMultiplesIndicator_mul_ringInverse :
    pMultiplesIndicator p R * ringInverse p R = 0 := by
  ext x
  rw [ContinuousMap.mul_apply, ContinuousMap.zero_apply]
  by_cases hx : (p : ℤ_[p]) ∣ x
  · rw [ringInverse_of_dvd hx, mul_zero]
  · rw [pMultiplesIndicator_eq_zero hx, zero_mul]

/-- Division of measures on `ℤ_p` by the coordinate on `ℤ_pˣ`: weighting by `x ↦ x⁻¹` on the
units, extended by `0` on `pℤ_p`. -/
def inverseWeight : D(ℤ_[p], R) →ₗ[R] D(ℤ_[p], R) :=
  weight (ringInverse p R)

/-- Division by the coordinate is weighting by `ringInverse`. -/
theorem inverseWeight_eq_weight :
    inverseWeight (p := p) (R := R) = weight (ringInverse p R) :=
  (rfl)

@[simp]
theorem inverseWeight_apply (μ : D(ℤ_[p], R)) (f : C(ℤ_[p], R)) :
    inverseWeight μ f = μ (ringInverse p R * f) := by
  rw [inverseWeight_eq_weight, weight_apply]

/-- Division by the coordinate scales a Dirac measure by the value of `ringInverse`. -/
theorem inverseWeight_dirac (x : ℤ_[p]) :
    inverseWeight (dirac R x) = ringInverse p R x • dirac R x := by
  rw [inverseWeight_eq_weight, weight_dirac]

/-- Division by the coordinate scales the Dirac measure at a unit `u` by `u⁻¹`. -/
@[simp]
theorem inverseWeight_dirac_unit (u : ℤ_[p]ˣ) :
    inverseWeight (dirac R (u : ℤ_[p])) = algebraMap ℤ_[p] R ↑u⁻¹ • dirac R (u : ℤ_[p]) := by
  rw [inverseWeight_dirac, ringInverse_unit]

/-- Division by the coordinate kills a Dirac measure on `pℤ_p`. -/
@[simp]
theorem inverseWeight_dirac_of_dvd {x : ℤ_[p]} (hx : (p : ℤ_[p]) ∣ x) :
    inverseWeight (dirac R x) = 0 := by
  rw [inverseWeight_dirac, ringInverse_of_dvd hx]
  exact zero_smul R (dirac R x)

/-- Division by the coordinate lands in the measures supported on `ℤ_pˣ`. -/
@[simp]
theorem restrictMultiples_inverseWeight (μ : D(ℤ_[p], R)) :
    restrictMultiples (inverseWeight μ) = 0 := by
  rw [restrictMultiples_eq_weight, inverseWeight_eq_weight, ← weight_mul,
    pMultiplesIndicator_mul_ringInverse, weight_zero]

/-- Multiplying `J μ` by the coordinate gives the restriction of `μ` to `ℤ_pˣ`. -/
@[simp]
theorem weight_id_smul_one_inverseWeight (μ : D(ℤ_[p], R)) :
    weight (ContinuousMap.id ℤ_[p] • 1) (inverseWeight μ) = unitRestriction μ := by
  rw [inverseWeight_eq_weight, ← weight_mul, mul_comm, ringInverse_mul_id_smul_one,
    unitRestriction_eq_weight]

/-- Dividing `x · μ` by the coordinate gives the restriction of `μ` to `ℤ_pˣ`. -/
@[simp]
theorem inverseWeight_weight_id_smul_one (μ : D(ℤ_[p], R)) :
    inverseWeight (weight (ContinuousMap.id ℤ_[p] • 1) μ) = unitRestriction μ := by
  rw [inverseWeight_eq_weight, ← weight_mul, ringInverse_mul_id_smul_one,
    unitRestriction_eq_weight]

/-- Division by the coordinate commutes with the dilation `x ↦ a x`, up to the factor
`ringInverse p R a`, which is `a⁻¹` for a unit `a` and `0` for `a ∈ pℤ_p`. -/
theorem inverseWeight_map_mulLeft (a : ℤ_[p]) (μ : D(ℤ_[p], R)) :
    inverseWeight (map (ContinuousMap.mulLeft a) μ) =
      ringInverse p R a • map (ContinuousMap.mulLeft a) (inverseWeight μ) := by
  have h : (ringInverse p R).comp (ContinuousMap.mulLeft a) =
      ContinuousMap.const ℤ_[p] (ringInverse p R a) * ringInverse p R := by
    ext x
    simp [ringInverse_apply, Ring.mul_inverse_rev, mul_comm]
  rw [inverseWeight_eq_weight, ← map_weight, h, weight_mul, weight_const, map_smul]

/-- Division by the coordinate commutes with the dilation `x ↦ a x` by a unit `a`, up to the
factor `a⁻¹`. -/
theorem inverseWeight_map_mulLeft_unit (a : ℤ_[p]ˣ) (μ : D(ℤ_[p], R)) :
    inverseWeight (map (ContinuousMap.mulLeft (a : ℤ_[p])) μ) =
      algebraMap ℤ_[p] R ↑a⁻¹ • map (ContinuousMap.mulLeft (a : ℤ_[p])) (inverseWeight μ) := by
  rw [inverseWeight_map_mulLeft, ringInverse_unit]

/-- **Division by `x` on unit-supported measures.** A measure `μ` on `ℤ_p` supported on `ℤ_pˣ` is
`x · ν` for a unique measure `ν` supported on `ℤ_pˣ`, namely `ν = inverseWeight μ`. -/
theorem existsUnique_unitSupported_div_id_smul_one (μ : D(ℤ_[p], R))
    (hμ : restrictMultiples μ = 0) :
    ∃! ν : D(ℤ_[p], R), restrictMultiples ν = 0 ∧ weight (ContinuousMap.id ℤ_[p] • 1) ν = μ := by
  refine ⟨inverseWeight μ, ⟨restrictMultiples_inverseWeight μ, ?_⟩, fun ν ⟨hν, hνμ⟩ ↦ ?_⟩
  · rw [weight_id_smul_one_inverseWeight,
      (unitRestriction_eq_self_iff_restrictMultiples_eq_zero μ).mpr hμ]
  · rw [← hνμ, inverseWeight_weight_id_smul_one,
      (unitRestriction_eq_self_iff_restrictMultiples_eq_zero ν).mpr hν]

/-- **Division by `x` on unit-supported integral measures.** An integral measure `μ` on `ℤ_p`
supported on `ℤ_pˣ` is `x · ν` for a unique integral measure `ν` supported on `ℤ_pˣ`, namely
`ν = inverseWeight μ`. -/
theorem existsUnique_unitSupported_div_id (μ : D(ℤ_[p], ℤ_[p])) (hμ : restrictMultiples μ = 0) :
    ∃! ν : D(ℤ_[p], ℤ_[p]), restrictMultiples ν = 0 ∧ weight (ContinuousMap.id ℤ_[p]) ν = μ := by
  have h : (ContinuousMap.id ℤ_[p] • 1 : C(ℤ_[p], ℤ_[p])) = ContinuousMap.id ℤ_[p] := by
    ext x
    simp
  simpa only [h] using existsUnique_unitSupported_div_id_smul_one μ hμ

end AbstractMeasure
