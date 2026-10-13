/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic
public import TauCeti.NumberTheory.ModularForms.Norm.Cusps
public import TauCeti.NumberTheory.Modular.ConjugateTranslation
import Mathlib.Algebra.GCDMonoid.Nat

/-!
# Cusp widths of `Γ₀(N)`

At the cusp represented by `γ = [a,b;c,d] ∈ SL₂(ℤ)`, the width of `Γ₀(N)` is
`N / gcd(N,c²)`. The formula holds at every positive level and every integral
representative, including infinity and negative denominators. Since `-I ∈ Γ₀(N)`,
the full-coset translation width is also the classical projective cusp width.

The translation-membership criterion is stated for integer exponents, and the
width formula uses the existing `CuspTranslationOrbit` carrier. This supplies the
arithmetic width in the cusp q-parameter and in the ramification of the finite
map from level `N` to level one.

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, §2.4.
-/

public section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup Function
open scoped MatrixGroups

namespace TauCeti

/-- A translation fixing `γ ∞` lies in `Γ₀(N)` exactly when its exponent times the
square of the cusp denominator is divisible by the level. -/
theorem conj_T_zpow_mem_Gamma0_iff (N : ℕ) (γ : SL(2, ℤ)) (j : ℤ) :
    γ * ModularGroup.T ^ j * γ⁻¹ ∈ Gamma0 N ↔ (N : ℤ) ∣ j * γ 1 0 ^ 2 := by
  rw [mem_Gamma0_iff_dvd]
  rw [γ.coe_conj_T_zpow j]
  simp [neg_mul]

/-- The exponents of the translations in `Γ₀(N)` fixing `γ ∞` are precisely the
multiples of `N / gcd(N,c²)`, where `c = γ₁₀`. -/
theorem conj_T_zpow_mem_Gamma0_iff_width_dvd (N : ℕ) [NeZero N]
    (γ : SL(2, ℤ)) (j : ℤ) :
    γ * ModularGroup.T ^ j * γ⁻¹ ∈ Gamma0 N ↔
      ((N / Nat.gcd N ((γ 1 0).natAbs ^ 2) : ℕ) : ℤ) ∣ j := by
  rw [conj_T_zpow_mem_Gamma0_iff, Int.natCast_dvd, Int.natAbs_mul, Int.natAbs_pow,
    Int.natCast_dvd]
  have hg : 0 < Nat.gcd N ((γ 1 0).natAbs ^ 2) := Nat.gcd_pos_of_pos_left _ (NeZero.pos N)
  rw [Nat.div_dvd_iff_dvd_mul (Nat.gcd_dvd_left _ _) hg]
  simpa only [gcd_eq_nat_gcd, mul_comm j.natAbs] using
    (dvd_gcd_mul_iff_dvd_mul (k := N) (m := (γ 1 0).natAbs ^ 2) (n := j.natAbs)).symm

namespace ModularForm

/-- **The width of a `Γ₀(N)` cusp translation orbit.** The coset of `γ` represents
`γ⁻¹ ∞` in the full-coset convention. Its denominator is `-γ₁₀`, so its width is
`N / gcd(N,γ₁₀²)`. This is also the projective width because `Γ₀(N)` contains `-I`. -/
@[simp↓ high]
theorem cuspTranslationOrbitWidth_Gamma0 (N : ℕ) [NeZero N] (γ : SL(2, ℤ)) :
    cuspTranslationOrbitWidth
      (⟦(QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ) :
        𝒮ℒ ⧸ ((Gamma0 N).map (mapGL ℝ)).subgroupOf 𝒮ℒ)⟧ :
          CuspTranslationOrbit ((Gamma0 N).map (mapGL ℝ))) =
      N / Nat.gcd N ((γ 1 0).natAbs ^ 2) := by
  rw [cuspTranslationOrbitWidth_mk]
  have hc : (γ⁻¹ 1 0).natAbs = (γ 1 0).natAbs := by
    simp
  have hperiod (m : ℕ) :
      minimalPeriod (TSL • ·)
        (QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ) :
          𝒮ℒ ⧸ ((Gamma0 N).map (mapGL ℝ)).subgroupOf 𝒮ℒ) ∣ m ↔
        N / Nat.gcd N ((γ 1 0).natAbs ^ 2) ∣ m := by
    rw [minimalPeriod_TSL_dvd_iff]
    have hconj :
        (((((mapGL ℝ).rangeRestrict γ)⁻¹ * TSL ^ m *
            (mapGL ℝ).rangeRestrict γ) : 𝒮ℒ) : GL (Fin 2) ℝ) =
          mapGL ℝ (γ⁻¹ * ModularGroup.T ^ (m : ℤ) * γ) := by
      have hT : ((TSL ^ m : 𝒮ℒ) : GL (Fin 2) ℝ) =
          mapGL ℝ (ModularGroup.T ^ (m : ℤ)) := by
        rw [← zpow_natCast, coe_TSL_zpow, TauCeti.Matrix.SpecialLinearGroup.coe_GL_eq_mapGL]
      simp only [InvMemClass.coe_inv, Subgroup.coe_mul, MonoidHom.coe_rangeRestrict,
        map_inv, hT, map_mul]
    rw [hconj, Subgroup.mem_map_iff_mem mapGL_injective]
    simpa only [inv_inv, hc, Int.natCast_dvd_natCast] using
      conj_T_zpow_mem_Gamma0_iff_width_dvd N γ⁻¹ (m : ℤ)
  exact Nat.dvd_antisymm ((hperiod _).mpr dvd_rfl) ((hperiod _).mp dvd_rfl)

end ModularForm

end TauCeti
