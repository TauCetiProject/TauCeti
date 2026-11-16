/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ENat.Lattice
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.SetTheory.Cardinal.ENat
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.Ideal
import TauCeti.RingTheory.MvPowerSeries.Equiv
import TauCeti.RingTheory.PowerSeries.Ideal

/-!
# The Krull dimension of a power series ring

For a Noetherian ring `R`, the variable `X` is a non-zero-divisor in the Jacobson radical of
`R⟦X⟧` with quotient `R`, so the Krull dimension of the ring of formal power series is

```text
dim R⟦X⟧ = dim R + 1.
```

By induction on the number of variables through `MvPowerSeries.optionEquivLeft`, the Krull
dimension of `MvPowerSeries σ R` over a Noetherian ring `R` is `dim R + |σ|`: for finite `σ` this
is `dim R + Nat.card σ`, and for infinite `σ` (over a nontrivial `R`) it is `⊤`, because
`MvPowerSeries σ R` surjects onto `MvPowerSeries (Fin n) R` for every `n`.

This is the power series analogue of Mathlib's `Polynomial.ringKrullDim_of_isNoetherianRing` and
`MvPolynomial.ringKrullDim_of_isNoetherianRing`.

## Main results

* `PowerSeries.ringKrullDim_of_isNoetherianRing`: for a Noetherian ring `R`,
  `dim R⟦X⟧ = dim R + 1`.
* `MvPowerSeries.ringKrullDim_of_isNoetherianRing_of_finite`: for a Noetherian ring `R` and a
  finite set of variables `σ`, `dim R⟦σ⟧ = dim R + Nat.card σ`.
* `MvPowerSeries.ringKrullDim_of_isNoetherianRing`: for a Noetherian ring `R` and any set of
  variables `σ`, `dim R⟦σ⟧ = dim R + ENat.card σ`.
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

variable {R : Type*} [CommRing R] [IsNoetherianRing R]

/-- **The dimension of a multivariate power series ring in finitely many variables.** Over a
Noetherian ring `R`, adjoining finitely many formal power series variables raises the Krull
dimension by the number of variables. -/
theorem ringKrullDim_of_isNoetherianRing_of_finite {σ : Type*} [Finite σ] :
    ringKrullDim (MvPowerSeries σ R) = ringKrullDim R + Nat.card σ := by
  induction σ using Finite.induction_empty_option with
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

/-- **The dimension of a multivariate power series ring.** Over a Noetherian ring `R`,
`dim R⟦σ⟧ = dim R + ENat.card σ`. -/
theorem ringKrullDim_of_isNoetherianRing {σ : Type*} :
    ringKrullDim (MvPowerSeries σ R) = ringKrullDim R + ENat.card σ := by
  rcases subsingleton_or_nontrivial R with _ | _
  · have : Subsingleton (MvPowerSeries σ R) := inferInstanceAs (Subsingleton ((σ →₀ ℕ) → R))
    simp [ringKrullDim_eq_bot_of_subsingleton]
  by_cases hσ : Finite σ
  · rw [ringKrullDim_of_isNoetherianRing_of_finite, ENat.card_eq_coe_natCard, WithBot.coe_natCast]
  · have : Infinite σ := not_finite_iff_infinite.mp hσ
    have htop : ringKrullDim R + ((⊤ : ℕ∞) : WithBot ℕ∞) = ⊤ :=
      top_unique <| by
        simpa [add_comm] using
          add_le_add_right (ringKrullDim_nonneg_of_nontrivial (R := R)) (⊤ : WithBot ℕ∞)
    rw [ENat.card_eq_top_of_infinite, htop]
    -- Setting all variables outside an `(n + 1)`-element subset to zero gives a surjection onto
    -- `MvPowerSeries (Fin (n + 1)) R`, whose Krull dimension is at least `n + 1`.
    refine eq_top_iff.mpr (le_of_forall_lt fun a ha ↦ ?_)
    induction a using WithBot.recBotCoe with
    | bot =>
      have : Nontrivial (MvPowerSeries σ R) := (C_injective (R := R) (σ := σ)).nontrivial
      exact lt_of_lt_of_le (WithBot.bot_lt_coe 0) ringKrullDim_nonneg_of_nontrivial
    | coe a =>
      induction a with
      | top => exact absurd ha (lt_irrefl _)
      | coe n =>
        classical
        let f : Fin (n + 1) ↪ σ := (Fin.valEmbedding).trans (Infinite.natEmbedding σ)
        let e : (Fin (n + 1) ⊕ {x : σ // x ∉ Set.range f}) ≃ σ :=
          (Equiv.sumCongr (Equiv.ofInjective f f.injective) (Equiv.refl _)).trans
            (Equiv.Set.sumCompl (Set.range f))
        let π : MvPowerSeries σ R →+* MvPowerSeries (Fin (n + 1)) R :=
          constantCoeff.comp <|
            (sumAlgEquiv R {x : σ // x ∉ Set.range f} (Fin (n + 1))).toRingHom.comp
              (renameEquiv R (e.symm.trans (Equiv.sumComm _ _))).toRingHom
        have hconst : Function.Surjective
            (constantCoeff (σ := {x : σ // x ∉ Set.range f})
              (R := MvPowerSeries (Fin (n + 1)) R)) :=
          fun g ↦ ⟨C g, constantCoeff_C g⟩
        have hπ : Function.Surjective π :=
          hconst.comp ((sumAlgEquiv _ _ _).surjective.comp (renameEquiv R _).surjective)
        have hle : ((n + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MvPowerSeries σ R) := by
          calc ((n + 1 : ℕ) : WithBot ℕ∞) = 0 + ((n + 1 : ℕ) : WithBot ℕ∞) := (zero_add _).symm
            _ ≤ ringKrullDim R + Nat.card (Fin (n + 1)) := by
              rw [Nat.card_eq_fintype_card, Fintype.card_fin]
              exact add_le_add (ringKrullDim_nonneg_of_nontrivial (R := R)) le_rfl
            _ = ringKrullDim (MvPowerSeries (Fin (n + 1)) R) :=
              ringKrullDim_of_isNoetherianRing_of_finite.symm
            _ ≤ ringKrullDim (MvPowerSeries σ R) := ringKrullDim_le_of_surjective π hπ
        exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self n) hle

end MvPowerSeries
