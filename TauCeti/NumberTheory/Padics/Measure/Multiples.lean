/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Division
public import TauCeti.NumberTheory.Padics.Measure.Weight
import TauCeti.NumberTheory.Padics.Measure.FiniteProjection
import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# Measures restricted to multiples of `p`

The characteristic function of `pℤ_p` weights a measure to its part supported on the multiples of
`p`. This gives an idempotent linear projector on the existing abstract-measure carrier. It is the
restriction operator that occurs in the Frobenius and psi calculus for bounded p-adic measures.

## Main definitions

* `AbstractMeasure.pMultiplesIndicator`: the continuous characteristic function of `pℤ_p`.
* `AbstractMeasure.restrictMultiples`: restriction of measures to `pℤ_p`, on the ambient carrier.

## References

* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, §3.5.3.
-/

public noncomputable section

open ContinuousMap

namespace AbstractMeasure

open scoped AbstractMeasure

variable (p : ℕ) [Fact p.Prime] (R : Type*) [NormedCommRing R]

local instance : ContinuousMul C(ℤ_[p], R) :=
  ContinuousMap.instContinuousMulOfLocallyCompactSpace

/-- The continuous characteristic function of the clopen subset `pℤ_p`. -/
def pMultiplesIndicator : C(ℤ_[p], R) :=
  fiberIndicator ⟨PadicInt.toZMod, PadicInt.continuous_toZMod⟩ 0

variable {p R}

/-- The characteristic function of `pℤ_p` is one on multiples of `p`. -/
@[simp]
theorem pMultiplesIndicator_eq_one {x : ℤ_[p]} (hx : (p : ℤ_[p]) ∣ x) :
    pMultiplesIndicator p R x = 1 := by
  simp [pMultiplesIndicator, PadicInt.toZMod_eq_zero_iff_dvd, hx]

/-- The characteristic function of `pℤ_p` vanishes away from multiples of `p`. -/
@[simp]
theorem pMultiplesIndicator_eq_zero {x : ℤ_[p]} (hx : ¬(p : ℤ_[p]) ∣ x) :
    pMultiplesIndicator p R x = 0 := by
  simp [pMultiplesIndicator, PadicInt.toZMod_eq_zero_iff_dvd, hx]

/-- Restriction of a measure on `ℤ_p` to `pℤ_p`, extended by zero on the ambient carrier. -/
def restrictMultiples : D(ℤ_[p], R) →ₗ[R] D(ℤ_[p], R) :=
  weight (pMultiplesIndicator p R)

/-- Restriction to multiples is weighting by the characteristic function of `pℤ_p`. -/
theorem restrictMultiples_eq_weight :
    restrictMultiples (p := p) (R := R) = weight (pMultiplesIndicator p R) :=
  (rfl)

/-- Restriction to multiples integrates a test function after multiplying it by the
characteristic function of `pℤ_p`. -/
@[simp]
theorem restrictMultiples_apply (μ : D(ℤ_[p], R)) (f : C(ℤ_[p], R)) :
    restrictMultiples μ f = μ (pMultiplesIndicator p R * f) := by
  rw [restrictMultiples_eq_weight, weight_apply]

/-- Restriction to multiples scales a Dirac measure by the characteristic function of `pℤ_p`. -/
theorem restrictMultiples_dirac (x : ℤ_[p]) :
    restrictMultiples (dirac R x) = pMultiplesIndicator p R x • dirac R x := by
  rw [restrictMultiples_eq_weight, weight_dirac]

/-- Restriction to multiples preserves a Dirac measure at a multiple of `p`. -/
@[simp]
theorem restrictMultiples_dirac_of_dvd {x : ℤ_[p]} (hx : (p : ℤ_[p]) ∣ x) :
    restrictMultiples (dirac R x) = dirac R x := by
  rw [restrictMultiples_dirac, pMultiplesIndicator_eq_one hx, one_smul]

/-- Restriction to multiples kills a Dirac measure away from `pℤ_p`. -/
@[simp]
theorem restrictMultiples_dirac_of_not_dvd {x : ℤ_[p]} (hx : ¬(p : ℤ_[p]) ∣ x) :
    restrictMultiples (dirac R x) = 0 := by
  rw [restrictMultiples_dirac, pMultiplesIndicator_eq_zero hx]
  exact zero_smul R (dirac R x)

/-- Restriction to multiples is idempotent. -/
@[simp]
theorem restrictMultiples_idem (μ : D(ℤ_[p], R)) :
    restrictMultiples (restrictMultiples μ) = restrictMultiples μ := by
  rw [restrictMultiples_eq_weight, ← weight_mul]
  congr 2
  ext x
  by_cases hx : (p : ℤ_[p]) ∣ x
  · rw [ContinuousMap.mul_apply, pMultiplesIndicator_eq_one hx, one_mul]
  · rw [ContinuousMap.mul_apply, pMultiplesIndicator_eq_zero hx, zero_mul]

end AbstractMeasure
