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

By induction on the variables, the multivariate formal power series ring in `ι` variables over a
Noetherian ring `R` has Krull dimension `dim R + card ι`
(`MvPowerSeries.ringKrullDim_of_isNoetherianRing_of_finite`,
`MvPowerSeries.ringKrullDim_of_isNoetherianRing`).

This is the power series analogue of Mathlib's `Polynomial.ringKrullDim_of_isNoetherianRing` and
`MvPolynomial.ringKrullDim_of_isNoetherianRing`.

## Main results

* `PowerSeries.ringKrullDim_of_isNoetherianRing`: for a Noetherian ring `R`,
  `dim R⟦X⟧ = dim R + 1`.
* `MvPowerSeries.ringKrullDim_of_isNoetherianRing_of_finite`: for a Noetherian ring `R` and a
  finite index type `ι`, `dim (MvPowerSeries ι R) = dim R + Nat.card ι`.
* `MvPowerSeries.ringKrullDim_of_isNoetherianRing`: for a Noetherian ring `R` and an arbitrary
  index type `ι`, `dim (MvPowerSeries ι R) = dim R + ENat.card ι`.
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

variable {R : Type*} [CommRing R]

/-- **The dimension of a finite-variable power series ring.** Over a Noetherian ring `R`, adjoining
finitely many formal power series variables raises the Krull dimension by the number of
variables. -/
theorem ringKrullDim_of_isNoetherianRing_of_finite [IsNoetherianRing R] {ι : Type*} [Finite ι] :
    ringKrullDim (MvPowerSeries ι R) = ringKrullDim R + Nat.card ι := by
  induction ι using Finite.induction_empty_option with
  | of_equiv e ih =>
    rw [ringKrullDim_eq_of_ringEquiv (renameEquiv R e).toRingEquiv.symm, ih, Nat.card_congr e]
  | h_empty =>
    rw [ringKrullDim_eq_of_ringEquiv (isEmptyEquiv _ R).toRingEquiv]
    simp
  | h_option ih =>
    simp only [Nat.card_eq_fintype_card, Fintype.card_option, Nat.cast_add, Nat.cast_one,
      ← add_assoc] at ih ⊢
    rw [ringKrullDim_eq_of_ringEquiv (optionEquivLeft _ R).toRingEquiv,
      PowerSeries.ringKrullDim_of_isNoetherianRing, ih]

/-- **The dimension of a multivariate power series ring.** Over a Noetherian ring `R`, the Krull
dimension of `MvPowerSeries ι R` is `dim R + ENat.card ι` (infinite when `R` is nontrivial and `ι`
is infinite). -/
theorem ringKrullDim_of_isNoetherianRing [IsNoetherianRing R] {ι : Type*} :
    ringKrullDim (MvPowerSeries ι R) = ringKrullDim R + ENat.card ι := by
  rcases subsingleton_or_nontrivial R with _ | _
  · have : Subsingleton (MvPowerSeries ι R) := Pi.instSubsingleton
    simp [ringKrullDim_eq_bot_of_subsingleton]
  by_cases h : Finite ι
  · rw [ringKrullDim_of_isNoetherianRing_of_finite, ENat.card_eq_coe_natCard, WithBot.coe_natCast]
  · have : Infinite ι := not_finite_iff_infinite.mp h
    have hne : ringKrullDim R ≠ ⊥ := WithBot.coe_bot_le.mp ringKrullDim_nonneg_of_nontrivial
    have htop : ringKrullDim R + (ENat.card ι : WithBot ℕ∞) = ⊤ := by
      cases hR : ringKrullDim R with
      | bot => exact absurd hR hne
      | coe b => simp [ENat.card_eq_top_of_infinite]
    rw [htop]
    cases hdim : ringKrullDim (MvPowerSeries ι R) with
    | bot =>
      exact absurd hdim (WithBot.coe_bot_le.mp ringKrullDim_nonneg_of_nontrivial)
    | coe a =>
      cases a with
      | top => rfl
      | coe n =>
        let e : Fin (n + 1) ↪ ι := Fin.valEmbedding.trans (Infinite.natEmbedding ι)
        have hsurj : Function.Surjective (killCompl (R := R) e).toRingHom :=
          fun p ↦ ⟨rename e p, killCompl_rename_app p⟩
        have hle : ringKrullDim (MvPowerSeries (Fin (n + 1)) R) ≤ (n : WithBot ℕ∞) := by
          simpa only [hdim, WithBot.coe_natCast] using ringKrullDim_le_of_surjective _ hsurj
        rw [ringKrullDim_of_isNoetherianRing_of_finite, Nat.card_fin] at hle
        have hlt : ((n + 1 : ℕ) : WithBot ℕ∞) ≤ (n : WithBot ℕ∞) := by
          calc ((n + 1 : ℕ) : WithBot ℕ∞)
            _ = 0 + (n + 1 : ℕ) := (zero_add _).symm
            _ ≤ ringKrullDim R + (n + 1 : ℕ) := by
                gcongr
                exact ringKrullDim_nonneg_of_nontrivial
            _ ≤ n := hle
        exact absurd (Nat.cast_le.mp hlt) (Nat.not_succ_le_self n)

end MvPowerSeries
