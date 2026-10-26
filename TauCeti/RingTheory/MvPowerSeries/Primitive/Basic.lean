/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.RingTheory.MvPowerSeries.Derivative

import TauCeti.Algebra.Algebra.NatCast

/-!
# Termwise primitives of multivariate power series

Over a commutative `ℚ`-algebra `R`, the termwise primitive of `f = ∑ aᵥ Xᵛ` with respect to the
variable `Xᵢ` is

```text
∫ f dXᵢ = ∑ aᵥ Xᵛ⁺ᵉⁱ / (νᵢ + 1).
```

It is a right inverse of the formal partial derivative `∂/∂Xᵢ`, and it is the unique series with
derivative `f` that has no terms free of `Xᵢ`. Rational scalars are needed to divide by `νᵢ + 1`:
over a ring of characteristic `p` the series `Xᵢ ^ (p - 1)` is not a derivative, since the
derivative of `Xᵢ ^ p` vanishes.

## Main definitions

* `MvPowerSeries.primitive i`: the termwise primitive with respect to `Xᵢ`, as an `R`-linear map.

## Main results

* `MvPowerSeries.coeff_primitive` and `MvPowerSeries.coeff_add_single_primitive`: its
  coefficients.
* `MvPowerSeries.pderiv_primitive`: `∂/∂Xᵢ (∫ f dXᵢ) = f`.
* `MvPowerSeries.coeff_primitive_pderiv`: `∫ (∂f/∂Xᵢ) dXᵢ` is `f` with its terms free of `Xᵢ`
  removed.
* `MvPowerSeries.eq_primitive_iff`: `g = ∫ f dXᵢ` iff `∂g/∂Xᵢ = f` and `g` has no terms free of
  `Xᵢ`.
* `MvPowerSeries.primitive_monomial`: `∫ a Xᵛ dXᵢ = a Xᵛ⁺ᵉⁱ / (νᵢ + 1)`.
-/

public section

namespace MvPowerSeries

open Finsupp

section Semiring

variable {σ R : Type*} [Semiring R] [Algebra ℚ R]

/-- The **termwise primitive** `∑ aᵥ Xᵛ ↦ ∑ aᵥ Xᵛ⁺ᵉⁱ / (νᵢ + 1)` with respect to the variable
`Xᵢ`, over a `ℚ`-algebra. Its coefficient at `ν` is `aᵥ₋ₑᵢ / νᵢ`, which is zero when `νᵢ = 0`. -/
noncomputable def primitive (i : σ) : MvPowerSeries σ R →ₗ[R] MvPowerSeries σ R where
  toFun f n := (n i : ℚ)⁻¹ • coeff (n - single i 1) f
  map_add' f g := by
    ext n
    exact smul_add _ (coeff (n - single i 1) f) (coeff (n - single i 1) g)
  map_smul' r f := by
    ext n
    exact (smul_algebra_smul_comm ((n i : ℚ)⁻¹) r (coeff (n - single i 1) f)).symm

/-- The coefficient of the termwise primitive at `ν` is `aᵥ₋ₑᵢ / νᵢ`. -/
theorem coeff_primitive (i : σ) (f : MvPowerSeries σ R) (n : σ →₀ ℕ) :
    coeff n (primitive i f) = (n i : ℚ)⁻¹ • coeff (n - single i 1) f :=
  (rfl)

/-- The termwise primitive with respect to `Xᵢ` has no terms free of `Xᵢ`. -/
@[simp]
theorem coeff_primitive_of_eq_zero (i : σ) (f : MvPowerSeries σ R) {n : σ →₀ ℕ} (h : n i = 0) :
    coeff n (primitive i f) = 0 := by
  simp [coeff_primitive, h]

/-- The coefficient of the termwise primitive at `ν + eᵢ` is `aᵥ / (νᵢ + 1)`. -/
@[simp]
theorem coeff_add_single_primitive (i : σ) (f : MvPowerSeries σ R) (n : σ →₀ ℕ) :
    coeff (n + single i 1) (primitive i f) = ((n i : ℚ) + 1)⁻¹ • coeff n f := by
  simp [coeff_primitive]

/-- The termwise primitive of a monomial: `∫ a Xᵛ dXᵢ = a Xᵛ⁺ᵉⁱ / (νᵢ + 1)`. -/
@[simp]
theorem primitive_monomial (i : σ) (n : σ →₀ ℕ) (a : R) :
    primitive i (monomial n a) = monomial (n + single i 1) (((n i : ℚ) + 1)⁻¹ • a) := by
  classical
  ext m
  by_cases hm : m i = 0
  · have hne : m ≠ n + single i 1 := fun h ↦ by simp [h] at hm
    rw [coeff_primitive_of_eq_zero i _ hm]
    simp [coeff_monomial, hne]
  · obtain ⟨m, rfl⟩ : ∃ k, m = k + single i 1 := ⟨_, (sub_add_single_one_cancel hm).symm⟩
    simp only [coeff_add_single_primitive, coeff_monomial, add_left_inj]
    split_ifs with h
    · rw [h]
    · exact smul_zero _

/-- The termwise primitive of a constant: `∫ a dXᵢ = a Xᵢ`. -/
@[simp]
theorem primitive_C (i : σ) (a : R) : primitive i (C a) = monomial (single i 1) a := by
  simpa using primitive_monomial i 0 a

/-- The termwise primitive with respect to `Xᵢ` is injective. -/
theorem primitive_injective (i : σ) : Function.Injective (primitive (R := R) (σ := σ) i) := by
  intro f g h
  ext n
  have hn := congrArg (coeff (n + single i 1)) h
  rw [coeff_add_single_primitive, coeff_add_single_primitive] at hn
  exact (inv_ne_zero (Nat.cast_add_one_ne_zero (n i))).isUnit.smul_left_cancel.1 hn

end Semiring

section CommSemiring

variable {σ R : Type*} [CommSemiring R] [Algebra ℚ R]

/-- **The primitive is a right inverse of the derivative**: `∂/∂Xᵢ (∫ f dXᵢ) = f`. -/
@[simp]
theorem pderiv_primitive (i : σ) (f : MvPowerSeries σ R) : pderiv i (primitive i f) = f := by
  ext n
  rw [coeff_pderiv, coeff_add_single_primitive,
    TauCeti.inv_natCast_add_one_smul_mul_natCast_add_one]

/-- **The primitive of a derivative**: `∫ (∂f/∂Xᵢ) dXᵢ` is `f` with its terms free of `Xᵢ`
removed. -/
theorem coeff_primitive_pderiv (i : σ) (f : MvPowerSeries σ R) (n : σ →₀ ℕ) :
    coeff n (primitive i (pderiv i f)) = if n i = 0 then 0 else coeff n f := by
  split_ifs with h
  · exact coeff_primitive_of_eq_zero i _ h
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + single i 1 := ⟨_, (sub_add_single_one_cancel h).symm⟩
    rw [coeff_add_single_primitive, coeff_pderiv, ← smul_mul_assoc,
      TauCeti.inv_natCast_add_one_smul_mul_natCast_add_one]

/-- **Characterisation of the primitive**: `g = ∫ f dXᵢ` iff `∂g/∂Xᵢ = f` and `g` has no terms
free of `Xᵢ`. -/
theorem eq_primitive_iff {i : σ} {f g : MvPowerSeries σ R} :
    g = primitive i f ↔ pderiv i g = f ∧ ∀ n : σ →₀ ℕ, n i = 0 → coeff n g = 0 := by
  constructor
  · rintro rfl
    exact ⟨pderiv_primitive i f, fun n hn ↦ coeff_primitive_of_eq_zero i f hn⟩
  · rintro ⟨rfl, h⟩
    ext n
    rw [coeff_primitive_pderiv]
    split_ifs with hn
    · exact h n hn
    · rfl

end CommSemiring

end MvPowerSeries
