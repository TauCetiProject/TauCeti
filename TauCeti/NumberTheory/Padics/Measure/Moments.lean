/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Measure.AmiceTransform
public import Mathlib.RingTheory.PowerSeries.Binomial
public import TauCeti.NumberTheory.Padics.MahlerBasis
public import TauCeti.NumberTheory.Padics.Measure.Weight
public import TauCeti.RingTheory.PowerSeries.MahlerDerivation

/-!
# Moments of measures on `ℤ_p` and the Amice transform

The Amice transform of a measure `μ` on `ℤ_p` is the power series `A_μ` whose `n`-th coefficient is
`μ (x choose n)` (Mathlib's `AbstractMeasure.amiceTransform`). The Mahler basis satisfies the
recurrence

`x * (x choose n) = (n + 1) * (x choose (n + 1)) + n * (x choose n)`,

which says exactly that multiplying the measure by the coordinate function `x` acts on `A_μ` as the
Mahler derivation `∂ = (1 + T) d/dT`. Iterating, the moment `μ (x ^ k)` is the constant
coefficient of `∂ ^ k A_μ`, and over `ℚ_p` it is `k !` times the `k`-th coefficient of
`A_μ (exp T - 1)`. This is how the values of a p-adic L-function at negative integers are read
off from the power series of its measure.

The statements are made for a measure with values in any topological `ℤ_p`-algebra `R`, where the
coordinate function is `x_R = ContinuousMap.id ℤ_[p] • 1 : C(ℤ_[p], R)`, following the convention
`mahler n • 1` of `AbstractMeasure.amiceTransform`; the forms for `R = ℤ_p` use `x` itself.

## Main results

* `TauCeti.id_mul_mahler`: the recurrence `x * mahler n = (n + 1) • mahler (n + 1) + n • mahler n`.
* `AbstractMeasure.constantCoeff_amiceTransform`: the constant coefficient of `A_μ` is the total
  mass `μ 1`.
* `AbstractMeasure.amiceTransform_weight_id_smul_one`: `A (x_R μ) = ∂ A_μ`.
* `AbstractMeasure.ordinaryMoment_smul_one_eq_constantCoeff`: `μ (x_R ^ k)` is the constant
  coefficient of `∂ ^ k A_μ`.
* `AbstractMeasure.ordinaryMoment_smul_one_eq_factorial_coeff`: over a `ℚ`-algebra,
  `μ (x_R ^ k) = k ! * coeff k (A_μ (exp T - 1))`.
* `AbstractMeasure.amiceTransform_weight_id`, `AbstractMeasure.ordinaryMoment_eq_constantCoeff`
  and `AbstractMeasure.ordinaryMoment_eq_factorial_coeff`: the forms for `ℤ_p`-valued measures,
  the last with its moments compared in `ℚ_p`.

## References

* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, §3.5.1,
  Lemma 3.29 and Corollary 3.30; §4.1, Lemma 4.3.
* P. Colmez, *Fonctions d'une variable p-adique*, §II.2.
-/

public noncomputable section

open scoped AbstractMeasure PowerSeries

variable {p : ℕ} [Fact p.Prime]

namespace AbstractMeasure

variable {R : Type*} [CommRing R] [TopologicalSpace R]
  [Algebra ℤ_[p] R] [ContinuousSMul ℤ_[p] R] [IsTopologicalRing R]

/-- The constant coefficient of the Amice transform is the total mass. -/
@[simp]
theorem constantCoeff_amiceTransform (μ : D(ℤ_[p], R)) :
    PowerSeries.constantCoeff μ.amiceTransform = μ 1 := by
  have h : (mahler 0 • 1 : C(ℤ_[p], R)) = 1 :=
    ContinuousMap.ext fun x => by
      rw [ContinuousMap.smul_apply', mahler_apply, Ring.choose_zero_right, one_smul]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_amiceTransform, h]

/-- The Amice transform of a Dirac measure is the binomial series `(1 + X) ^ x`. -/
@[simp]
theorem amiceTransform_dirac (x : ℤ_[p]) :
    amiceTransform (dirac R x) = PowerSeries.binomialSeries R x := by
  ext n
  simp [coeff_amiceTransform, mahler_apply]

/-- The Amice transform of the measure `μ` multiplied by the coordinate function is the Mahler
derivation `(1 + T) d/dT` of the Amice transform of `μ`. -/
theorem amiceTransform_weight_id_smul_one (μ : D(ℤ_[p], R)) :
    (weight (ContinuousMap.id ℤ_[p] • 1 : C(ℤ_[p], R)) μ).amiceTransform =
      PowerSeries.mahlerDerivation R μ.amiceTransform := by
  ext n
  rw [coeff_amiceTransform, PowerSeries.coeff_mahlerDerivation, coeff_amiceTransform,
    coeff_amiceTransform, weight_apply]
  have h : (ContinuousMap.id ℤ_[p] • 1 : C(ℤ_[p], R)) * ((mahler n : C(ℤ_[p], ℤ_[p])) • 1)
      = (n + 1) • ((mahler (n + 1) : C(ℤ_[p], ℤ_[p])) • 1) +
        n • ((mahler n : C(ℤ_[p], ℤ_[p])) • 1) := by
    -- the Mahler recurrence, pushed into `R` through the algebra map
    refine ContinuousMap.ext fun x => ?_
    have hx := DFunLike.congr_fun (TauCeti.id_mul_mahler (p := p) n) x
    rw [ContinuousMap.mul_apply, ContinuousMap.add_apply, ContinuousMap.smul_apply,
      ContinuousMap.smul_apply, ContinuousMap.id_apply] at hx
    simp only [ContinuousMap.mul_apply, ContinuousMap.add_apply, ContinuousMap.smul_apply,
      ContinuousMap.smul_apply', ContinuousMap.one_apply, ContinuousMap.id_apply,
      ← Algebra.algebraMap_eq_smul_one, ← map_mul, hx, map_add, map_nsmul]
  rw [h, map_add, map_nsmul, map_nsmul, nsmul_eq_mul, nsmul_eq_mul]
  push_cast
  ring

/-- The iterated form of `amiceTransform_weight_id_smul_one`: multiplying by `x ^ k` acts on the
Amice transform as `∂ ^ k`. -/
theorem amiceTransform_iterate_weight_id_smul_one (μ : D(ℤ_[p], R)) (k : ℕ) :
    ((weight (ContinuousMap.id ℤ_[p] • 1 : C(ℤ_[p], R)))^[k] μ).amiceTransform =
      (PowerSeries.mahlerDerivation R)^[k] μ.amiceTransform := by
  induction k generalizing μ with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih,
      amiceTransform_weight_id_smul_one]

/-- The `k`-th moment `μ (x ^ k)` of a measure on `ℤ_p` is the constant coefficient of the `k`-th
Mahler derivative of its Amice transform. -/
theorem ordinaryMoment_smul_one_eq_constantCoeff (μ : D(ℤ_[p], R)) (k : ℕ) :
    μ ((ContinuousMap.id ℤ_[p] • 1 : C(ℤ_[p], R)) ^ k) =
      PowerSeries.constantCoeff ((PowerSeries.mahlerDerivation R)^[k] μ.amiceTransform) := by
  rw [← amiceTransform_iterate_weight_id_smul_one, constantCoeff_amiceTransform,
    iterate_weight_apply, mul_one]

/-- Over a `ℚ`-algebra, the `k`-th moment `μ (x ^ k)` of a measure on `ℤ_p` is `k !` times the
`k`-th coefficient of its Amice transform evaluated at `exp T - 1`. -/
theorem ordinaryMoment_smul_one_eq_factorial_coeff [Algebra ℚ R] (μ : D(ℤ_[p], R)) (k : ℕ) :
    μ ((ContinuousMap.id ℤ_[p] • 1 : C(ℤ_[p], R)) ^ k) =
      k.factorial * PowerSeries.coeff k (μ.amiceTransform.subst (PowerSeries.exp R - 1)) := by
  rw [ordinaryMoment_smul_one_eq_constantCoeff,
    PowerSeries.constantCoeff_iterate_mahlerDerivation]

/-- For `ℤ_p`-valued measures, multiplication by `x` acts on the Amice transform as the Mahler
derivation: `A (x μ) = (1 + T) d/dT A_μ`. -/
theorem amiceTransform_weight_id (μ : D(ℤ_[p], ℤ_[p])) :
    (weight (ContinuousMap.id ℤ_[p]) μ).amiceTransform =
      PowerSeries.mahlerDerivation ℤ_[p] μ.amiceTransform := by
  simpa only [smul_eq_mul, mul_one] using amiceTransform_weight_id_smul_one μ

/-- For `ℤ_p`-valued measures, multiplication by `x ^ k` acts on the Amice transform as `∂ ^ k`. -/
theorem amiceTransform_iterate_weight_id (μ : D(ℤ_[p], ℤ_[p])) (k : ℕ) :
    ((weight (ContinuousMap.id ℤ_[p]))^[k] μ).amiceTransform =
      (PowerSeries.mahlerDerivation ℤ_[p])^[k] μ.amiceTransform := by
  simpa only [smul_eq_mul, mul_one] using amiceTransform_iterate_weight_id_smul_one μ k

/-- The moments of a `ℤ_p`-valued measure on `ℤ_p` are the constant coefficients of the iterated
Mahler derivatives of its Amice transform. -/
theorem ordinaryMoment_eq_constantCoeff (μ : D(ℤ_[p], ℤ_[p])) (k : ℕ) :
    μ (ContinuousMap.id ℤ_[p] ^ k) =
      PowerSeries.constantCoeff ((PowerSeries.mahlerDerivation ℤ_[p])^[k] μ.amiceTransform) := by
  simpa only [smul_eq_mul, mul_one] using ordinaryMoment_smul_one_eq_constantCoeff μ k

/-- The moments of a `ℤ_p`-valued measure on `ℤ_p` as exponential coefficients: in `ℚ_p`,
`μ (x ^ k) = k ! * coeff k (A_μ (exp T - 1))`. -/
theorem ordinaryMoment_eq_factorial_coeff (μ : D(ℤ_[p], ℤ_[p])) (k : ℕ) :
    (μ (ContinuousMap.id ℤ_[p] ^ k) : ℚ_[p]) =
      k.factorial * PowerSeries.coeff k
        ((PowerSeries.map (algebraMap ℤ_[p] ℚ_[p]) μ.amiceTransform).subst
          (PowerSeries.exp ℚ_[p] - 1)) := by
  let D := PowerSeries.mahlerDerivation
  have hmap := PowerSeries.map_iterate_mahlerDerivation
    (algebraMap ℤ_[p] ℚ_[p]) μ.amiceTransform k
  calc
    (μ (ContinuousMap.id ℤ_[p] ^ k) : ℚ_[p]) =
        algebraMap ℤ_[p] ℚ_[p]
          (PowerSeries.constantCoeff ((D ℤ_[p])^[k] μ.amiceTransform)) := by
      rw [ordinaryMoment_eq_constantCoeff, PadicInt.algebraMap_apply]
    _ = PowerSeries.constantCoeff
        (PowerSeries.map (algebraMap ℤ_[p] ℚ_[p]) ((D ℤ_[p])^[k] μ.amiceTransform)) := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map]
    _ = PowerSeries.constantCoeff
        ((D ℚ_[p])^[k] (PowerSeries.map (algebraMap ℤ_[p] ℚ_[p]) μ.amiceTransform)) := by
      rw [hmap]
    _ = k.factorial * PowerSeries.coeff k
        ((PowerSeries.map (algebraMap ℤ_[p] ℚ_[p]) μ.amiceTransform).subst
          (PowerSeries.exp ℚ_[p] - 1)) := by
      rw [PowerSeries.constantCoeff_iterate_mahlerDerivation]

-- Weighting by `x` is not injective: it kills `δ₀`.
example : weight (ContinuousMap.id ℤ_[3]) (dirac ℤ_[3] 0) = 0 ∧ dirac ℤ_[3] 0 ≠ 0 := by
  refine ⟨?_, fun h => ?_⟩
  · rw [weight_dirac, ContinuousMap.id_apply]
    exact zero_smul ℤ_[3] (dirac ℤ_[3] (0 : ℤ_[3]))
  have h1 := congrArg (fun μ => toCLMEquiv μ 1) h
  simp only [map_zero, zero_apply, coe_toCLMEquiv, dirac_apply,
    ContinuousMap.one_apply] at h1
  exact one_ne_zero h1

example : weight (ContinuousMap.id ℤ_[3]) (dirac ℤ_[3] 1) = dirac ℤ_[3] 1 := by simp

-- Weighting depends on `g`: `x δ₂ = 2 δ₂`.
example : weight (ContinuousMap.id ℤ_[3]) (dirac ℤ_[3] 2) = (2 : ℤ_[3]) • dirac ℤ_[3] 2 := by
  simp

end AbstractMeasure
