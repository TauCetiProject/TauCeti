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
# Measures restricted to multiples of `p` and to the units

The characteristic function of `pℤ_p` weights a measure to its part supported on the multiples of
`p`. This gives an idempotent linear projector on the existing abstract-measure carrier. It is the
restriction operator that occurs in the Frobenius and psi calculus for bounded p-adic measures.
The complementary projector `id - restrictMultiples` restricts a measure to the units `ℤ_pˣ`, the
complement of `pℤ_p`; its fixed points are the measures supported on the units.

## Main definitions

* `AbstractMeasure.pMultiplesIndicator`: the continuous characteristic function of `pℤ_p`.
* `AbstractMeasure.restrictMultiples`: restriction of measures to `pℤ_p`, on the ambient carrier.
* `AbstractMeasure.unitRestriction`: restriction of measures to `ℤ_pˣ`, on the ambient carrier.

## Main results

* `AbstractMeasure.unitRestriction_apply`: the unit restriction integrates `f` to
  `μ ((1 - χ) * f)`, where `χ` is the characteristic function of `pℤ_p`.
* `AbstractMeasure.unitRestriction_eq_self_iff`: a measure is its own unit restriction exactly when
  it annihilates every test function supported on `pℤ_p`.

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

/-- Restriction of a measure on `ℤ_p` to the units `ℤ_pˣ`, extended by zero on the ambient carrier:
weighting by the characteristic function `1 - χ` of `ℤ_pˣ`. -/
def unitRestriction : D(ℤ_[p], R) →ₗ[R] D(ℤ_[p], R) :=
  weight (1 - pMultiplesIndicator p R)

/-- The unit restriction is weighting by the characteristic function `1 - χ` of `ℤ_pˣ`. -/
theorem unitRestriction_eq_weight :
    unitRestriction (p := p) (R := R) = weight (1 - pMultiplesIndicator p R) :=
  (rfl)

/-- The unit restriction integrates a test function after multiplying it by the characteristic
function `1 - χ` of `ℤ_pˣ`. -/
@[simp]
theorem unitRestriction_apply (μ : D(ℤ_[p], R)) (f : C(ℤ_[p], R)) :
    unitRestriction μ f = μ ((1 - pMultiplesIndicator p R) * f) := by
  rw [unitRestriction_eq_weight, weight_apply]

/-- A measure is the sum of its restrictions to `pℤ_p` and to `ℤ_pˣ`. -/
@[simp]
theorem restrictMultiples_add_unitRestriction (μ : D(ℤ_[p], R)) :
    restrictMultiples μ + unitRestriction μ = μ := by
  rw [restrictMultiples_eq_weight, unitRestriction_eq_weight, ← weight_add, add_sub_cancel,
    weight_one]

/-- The unit restriction is the identity minus the restriction to multiples of `p`. -/
theorem unitRestriction_eq_sub :
    unitRestriction (p := p) (R := R) = LinearMap.id - restrictMultiples := by
  ext1 μ
  rw [LinearMap.sub_apply, LinearMap.id_apply, eq_sub_iff_add_eq',
    restrictMultiples_add_unitRestriction]

/-- Restricting the unit restriction to `pℤ_p` gives zero. -/
@[simp]
theorem restrictMultiples_unitRestriction (μ : D(ℤ_[p], R)) :
    restrictMultiples (unitRestriction μ) = 0 := by
  rw [unitRestriction_eq_sub, LinearMap.sub_apply, LinearMap.id_apply, map_sub,
    restrictMultiples_idem, sub_self]

/-- The unit restriction kills a measure restricted to `pℤ_p`. -/
@[simp]
theorem unitRestriction_restrictMultiples (μ : D(ℤ_[p], R)) :
    unitRestriction (restrictMultiples μ) = 0 := by
  rw [unitRestriction_eq_sub, LinearMap.sub_apply, LinearMap.id_apply, restrictMultiples_idem,
    sub_self]

/-- A measure is its own unit restriction exactly when its restriction to `pℤ_p` vanishes. -/
theorem unitRestriction_eq_self_iff_restrictMultiples_eq_zero (μ : D(ℤ_[p], R)) :
    unitRestriction μ = μ ↔ restrictMultiples μ = 0 := by
  rw [unitRestriction_eq_sub, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_self]

/-- A measure is supported on `ℤ_pˣ`, that is, it is its own unit restriction, exactly when it
annihilates every test function `χ * f` supported on `pℤ_p`. -/
theorem unitRestriction_eq_self_iff (μ : D(ℤ_[p], R)) :
    unitRestriction μ = μ ↔ ∀ f : C(ℤ_[p], R), μ (pMultiplesIndicator p R * f) = 0 := by
  rw [unitRestriction_eq_self_iff_restrictMultiples_eq_zero]
  refine ⟨fun h f ↦ ?_, fun h ↦ ?_⟩
  · have hf := DFunLike.congr_fun (congrArg toCLMEquiv h) f
    rwa [map_zero, _root_.zero_apply, coe_toCLMEquiv, restrictMultiples_apply] at hf
  · refine toCLMEquiv.injective (ContinuousLinearMap.ext fun f ↦ ?_)
    rw [map_zero, _root_.zero_apply, coe_toCLMEquiv, restrictMultiples_apply, h]

/-- The unit restriction is idempotent. -/
@[simp]
theorem unitRestriction_idem (μ : D(ℤ_[p], R)) :
    unitRestriction (unitRestriction μ) = unitRestriction μ :=
  (unitRestriction_eq_self_iff_restrictMultiples_eq_zero _).mpr
    (restrictMultiples_unitRestriction μ)

/-- The unit restriction scales a Dirac measure by the characteristic function of `ℤ_pˣ`. -/
theorem unitRestriction_dirac (x : ℤ_[p]) :
    unitRestriction (dirac R x) = (1 - pMultiplesIndicator p R x) • dirac R x := by
  rw [unitRestriction_eq_weight, weight_dirac, ContinuousMap.sub_apply, ContinuousMap.one_apply]

/-- The unit restriction kills a Dirac measure at a multiple of `p`. -/
@[simp]
theorem unitRestriction_dirac_of_dvd {x : ℤ_[p]} (hx : (p : ℤ_[p]) ∣ x) :
    unitRestriction (dirac R x) = 0 := by
  rw [unitRestriction_dirac, pMultiplesIndicator_eq_one hx, sub_self]
  exact zero_smul R (dirac R x)

/-- The unit restriction preserves a Dirac measure away from `pℤ_p`. -/
@[simp]
theorem unitRestriction_dirac_of_not_dvd {x : ℤ_[p]} (hx : ¬(p : ℤ_[p]) ∣ x) :
    unitRestriction (dirac R x) = dirac R x := by
  rw [unitRestriction_dirac, pMultiplesIndicator_eq_zero hx, sub_zero, one_smul]

end AbstractMeasure
