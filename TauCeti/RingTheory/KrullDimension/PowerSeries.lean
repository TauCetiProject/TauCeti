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
# The Krull dimension of a power series ring

For a Noetherian ring `R`, the variable `X` is a non-zero-divisor in the Jacobson radical of
`R⟦X⟧` with quotient `R`, so the Krull dimension of the ring of formal power series is

```text
dim R⟦X⟧ = dim R + 1.
```

By induction on the number of variables through `MvPowerSeries.finSuccEquiv`, adjoining finitely
many formal power series variables raises the Krull dimension by the number of variables:

```text
dim R⟦X_i : i ∈ σ⟧ = dim R + |σ|.
```

This is the power series analogue of Mathlib's `Polynomial.ringKrullDim_of_isNoetherianRing`.

## Main results

* `PowerSeries.ringKrullDim_of_isNoetherianRing`: for a Noetherian ring `R`,
  `dim R⟦X⟧ = dim R + 1`.
* `MvPowerSeries.ringKrullDim_of_isNoetherianRing`: for a Noetherian ring `R` and a finite type
  `σ`, `dim (MvPowerSeries σ R) = dim R + Nat.card σ`.
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

private theorem ringKrullDim_fin_of_isNoetherianRing [IsNoetherianRing R] (n : ℕ) :
    ringKrullDim (MvPowerSeries (Fin n) R) = ringKrullDim R + n := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, add_zero]
    exact ringKrullDim_eq_of_ringEquiv (isEmptyEquiv (Fin 0) R).toRingEquiv
  | succ n ih =>
    rw [ringKrullDim_eq_of_ringEquiv (finSuccEquiv R n).toRingEquiv,
      PowerSeries.ringKrullDim_of_isNoetherianRing, ih, Nat.cast_succ, add_assoc]

/-- **The dimension of a multivariate power series ring.** Over a Noetherian ring `R`, adjoining
finitely many formal power series variables raises the Krull dimension by the number of
variables. -/
theorem ringKrullDim_of_isNoetherianRing [Finite σ] [IsNoetherianRing R] :
    ringKrullDim (MvPowerSeries σ R) = ringKrullDim R + Nat.card σ := by
  cases nonempty_fintype σ
  rw [Nat.card_eq_fintype_card,
    ringKrullDim_eq_of_ringEquiv (renameEquiv R (Fintype.equivFin σ)).toRingEquiv,
    ringKrullDim_fin_of_isNoetherianRing]

end MvPowerSeries
