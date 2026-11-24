/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.Ideal
import TauCeti.RingTheory.PowerSeries.Ideal

/-!
# The Krull dimension of power series rings

For a Noetherian ring `R`, the variable `X` is a non-zero-divisor in the Jacobson radical of
`R⟦X⟧` with quotient `R`, so the Krull dimension of the ring of formal power series is

```text
dim R⟦X⟧ = dim R + 1.
```

By induction on the number of variables, the multivariate power series ring `MvPowerSeries σ R`
over a Noetherian ring `R` in finitely many variables has Krull dimension `dim R + Nat.card σ`
(`MvPowerSeries.ringKrullDim_of_isNoetherianRing_of_finite`).

This is the power series analogue of Mathlib's `Polynomial.ringKrullDim_of_isNoetherianRing` and
`MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite`.

## Main results

* `PowerSeries.ringKrullDim_of_isNoetherianRing`: for a Noetherian ring `R`,
  `dim R⟦X⟧ = dim R + 1`.
* `MvPowerSeries.ringKrullDim_of_isNoetherianRing_of_finite`: for a Noetherian ring `R` and a
  finite variable type `σ`, `dim (MvPowerSeries σ R) = dim R + Nat.card σ`.
-/

public section

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-- **The dimension of a power series ring.** Over a Noetherian ring `R`, adjoining a formal power
series variable raises the Krull dimension by exactly one. -/
theorem ringKrullDim_of_isNoetherianRing [IsNoetherianRing R] :
    ringKrullDim R⟦X⟧ = ringKrullDim R + 1 := by
  -- `X` is a non-zero-divisor in the Jacobson radical, so it cuts the dimension down by one, and
  -- the quotient by `X` is `R` through the constant coefficient
  have hX : IsRegular (X : R⟦X⟧) :=
    isRegular_iff_mem_nonZeroDivisors.mpr MvPowerSeries.X_mem_nonZeroDivisors
  have hJ : (X : R⟦X⟧) ∈ Ring.jacobson R⟦X⟧ :=
    Ring.mem_jacobson_iff.mpr fun _ ↦ isUnit_iff_constantCoeff.mpr (by simp)
  rw [← ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_jacobson
    hX.left.isSMulRegular hJ, ← ker_constantCoeff,
    ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective constantCoeff_surj)]

end PowerSeries

namespace MvPowerSeries

variable {σ R : Type*} [CommRing R]

/-- **The dimension of a multivariate power series ring in finitely many variables.** Over a
Noetherian ring `R`, adjoining finitely many formal power series variables raises the Krull
dimension by `Nat.card σ`. -/
@[simp]
theorem ringKrullDim_of_isNoetherianRing_of_finite [IsNoetherianRing R] [Finite σ] :
    ringKrullDim (MvPowerSeries σ R) = ringKrullDim R + Nat.card σ := by
  induction σ using Finite.induction_empty_option with
  | of_equiv e H =>
    convert ← H using 1
    · exact ringKrullDim_eq_of_ringEquiv (renameEquiv R e).toRingEquiv
    · rw [Nat.card_congr e]
  | h_empty =>
    rw [ringKrullDim_eq_of_ringEquiv (isEmptyEquiv _ _).toRingEquiv]
    simp
  | h_option IH =>
    rw [ringKrullDim_eq_of_ringEquiv (optionEquivLeft _ _).toRingEquiv,
      PowerSeries.ringKrullDim_of_isNoetherianRing, IH]
    simp [add_assoc]

end MvPowerSeries
