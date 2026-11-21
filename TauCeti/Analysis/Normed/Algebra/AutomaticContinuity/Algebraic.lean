/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm

import Mathlib.Analysis.Normed.Field.Ultra
import Mathlib.FieldTheory.Minpoly.Finite
import TauCeti.Analysis.Normed.Algebra.GelfandRadius
import TauCeti.Analysis.Normed.Unbundled.SpectralNorm.Basic
import TauCeti.Analysis.Normed.Unbundled.SpectralNorm.Irreducible

/-!
# Spectral contraction and automatic continuity into algebraic field extensions

Over a complete ultrametric normed field `K` (including trivially normed fields), every
`K`-algebra homomorphism `φ : B →ₐ[K] L` from an arbitrary Banach `K`-algebra `B` (not assumed
commutative, ultrametric, Noetherian, or unital-norm-normalized) into a field extension `L / K`
satisfies

`spectralNorm K L (φ b) ≤ gelfandRadius b ≤ ‖b‖`.

In particular, when `M / K` is an algebraic normed field extension, its norm is bounded by
`spectralNorm K M`, so every `K`-algebra homomorphism `B →ₐ[K] M` is contractive and automatically
continuous.

Completeness of `K` is essential: over the incomplete field `(ℚ, |·|₅)`, `X ^ 2 + X + 5` is
irreducible of spectral value `1` yet has a root in `ℚ_5` of `5`-adic norm `1 / 5`.

## Main results

* `AlgHom.spectralNorm_apply_le_gelfandRadius` and `AlgHom.spectralNorm_apply_le_norm`: spectral
  contraction into an arbitrary field extension `L / K`.
* `AlgHom.norm_apply_le_gelfandRadius_of_isAlgebraic`,
  `AlgHom.norm_apply_le_norm_of_isAlgebraic`, and `AlgHom.continuous_of_isAlgebraic`:
  contractivity and automatic continuity into algebraic normed field extensions `M / K`.

## References

* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert],
  §§3.7.5 and 3.8.1.
-/

public section

open Polynomial
open scoped IntermediateField

namespace AlgHom

variable {K B L : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NormedRing B] [NormedAlgebra K B] [CompleteSpace B]
  [Field L] [Algebra K L]

/-- Quantitative single-element step: for an integral image `φ x` of minimal-polynomial degree `d`,
`spectralNorm K L (φ x) ≤ d * ‖x‖`. -/
private theorem spectralNorm_apply_le_natDegree_mul_norm (φ : B →ₐ[K] L) {x : B}
    (hx : IsIntegral K (φ x)) :
    spectralNorm K L (φ x) ≤ (minpoly K (φ x)).natDegree * ‖x‖ := by
  -- Step 1: dispose of the easy cases `φ x = 0` and `spectralNorm K L (φ x) ≤ ‖x‖`.
  by_cases hφx : φ x = 0
  · rw [hφx, spectralNorm_zero]
    positivity
  set p := minpoly K (φ x)
  set d := p.natDegree
  set r := spectralNorm K L (φ x)
  have hp_monic : p.Monic := minpoly.monic hx
  have hp_irred : Irreducible p := minpoly.irreducible hx
  have hd : 0 < d := minpoly.natDegree_pos hx
  have hr : 0 < r := spectralNorm_zero_lt hφx hx.isAlgebraic
  rcases le_or_gt r ‖x‖ with hrx | hxr
  · have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    exact hrx.trans ((one_mul ‖x‖).symm.trans_le
      (mul_le_mul_of_nonneg_right hd1 (norm_nonneg x)))
  -- Step 2: write `(p.coeff 0)⁻¹ • aeval x p = 1 - z`; since `φ (1 - z) = 0`, `1 - z` is not a
  -- unit in the Banach algebra `B`, hence `1 ≤ ‖z‖`.
  have ha0_ne : p.coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hx hφx
  let z : B := -∑ j ∈ Finset.range d, ((p.coeff 0)⁻¹ * p.coeff (j + 1)) • x ^ (j + 1)
  have hz_eq : (p.coeff 0)⁻¹ • aeval x p = 1 - z := by
    rw [aeval_eq_sum_range' (Nat.lt_succ_self d), Finset.sum_range_succ', pow_zero, smul_add,
      Finset.smul_sum, smul_smul, inv_mul_cancel₀ ha0_ne, one_smul]
    simp only [z, smul_smul, sub_neg_eq_add, add_comm]
  have hnot_unit : ¬ IsUnit (1 - z) := by
    intro hu
    have h1z : φ (1 - z) = 0 := by
      rw [← hz_eq, map_smul, ← aeval_algHom_apply, minpoly.aeval, smul_zero]
    exact not_isUnit_zero (h1z ▸ hu.map φ)
  have hz_ge : 1 ≤ ‖z‖ := not_lt.mp fun hlt ↦ hnot_unit (isUnit_one_sub_of_norm_lt_one hlt)
  -- Step 3: bound each summand of `z` by `‖x‖ / r` to conclude `1 ≤ ‖z‖ ≤ d * (‖x‖ / r)`.
  have hdiv_le_one : ‖x‖ / r ≤ 1 := (div_le_one hr).mpr hxr.le
  have hz_le : ‖z‖ ≤ d * (‖x‖ / r) := by
    dsimp only [z]
    rw [norm_neg]
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun j _ ↦ (?_ : _ ≤ ‖x‖ / r)).trans (by simp [nsmul_eq_mul])
    have hcoeff : ‖(p.coeff 0)⁻¹ * p.coeff (j + 1)‖ ≤ r⁻¹ ^ (j + 1) :=
      hp_monic.norm_inv_coeff_zero_mul_coeff_le_inv_spectralValue_pow_of_irreducible hp_irred
        (j + 1)
    calc
      ‖((p.coeff 0)⁻¹ * p.coeff (j + 1)) • x ^ (j + 1)‖
          = ‖(p.coeff 0)⁻¹ * p.coeff (j + 1)‖ * ‖x ^ (j + 1)‖ := norm_smul _ _
      _ ≤ r⁻¹ ^ (j + 1) * ‖x‖ ^ (j + 1) :=
        mul_le_mul hcoeff (norm_pow_le' x (Nat.succ_pos j)) (norm_nonneg _) (by positivity)
      _ = (‖x‖ / r) ^ (j + 1) := by rw [div_eq_mul_inv, mul_comm ‖x‖, mul_pow]
      _ ≤ ‖x‖ / r := pow_le_of_le_one (by positivity) hdiv_le_one (Nat.succ_ne_zero j)
  have h1 : 1 ≤ d * (‖x‖ / r) := hz_ge.trans hz_le
  rwa [← mul_div_assoc, one_le_div hr] at h1

/-- **Spectral-norm bound by Gelfand radius.** Over a complete ultrametric normed field `K`
(including trivially normed fields), any `K`-algebra homomorphism `φ : B →ₐ[K] L` from a Banach
`K`-algebra `B` into a field extension `L / K` satisfies `spectralNorm K L (φ b) ≤ gelfandRadius b`
for every `b : B`. Neither commutativity, ultrametricity, Noetherianity, nor `‖1‖ = 1` is assumed
on `B`, and transcendental images have spectral norm `0`. Completeness of `K` is essential (for
example, `X ^ 2 + X + 5` is irreducible over `(ℚ, |·|_5)` of spectral value `1` yet has a root in
`ℚ_5` of `5`-adic norm `1 / 5`). -/
theorem spectralNorm_apply_le_gelfandRadius (φ : B →ₐ[K] L) (b : B) :
    spectralNorm K L (φ b) ≤ gelfandRadius b := by
  by_cases hb : IsAlgebraic K (φ b)
  · have hbij : IsIntegral K (φ b) := hb.isIntegral
    let E := K⟮φ b⟯
    have : FiniteDimensional K E := IntermediateField.adjoin.finiteDimensional hbij
    let g : E := IntermediateField.AdjoinSimple.gen K (φ b)
    have hg : algebraMap E L g = φ b := IntermediateField.AdjoinSimple.algebraMap_gen K (φ b)
    set N := Module.finrank K E
    refine TauCeti.le_gelfandRadius_of_bound (C := (N : ℝ)) fun n hn0 ↦ ?_
    have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    have hgn : algebraMap E L (g ^ n) = φ (b ^ n) := by rw [map_pow, map_pow, hg]
    have hdeg : (minpoly K (φ (b ^ n))).natDegree ≤ N := by
      rw [← hgn, minpoly.algebraMap_eq (algebraMap E L).injective]
      exact minpoly.natDegree_le (g ^ n)
    have hpow_spec : spectralNorm K L (φ b) ^ n = spectralNorm K L (φ (b ^ n)) := by
      rw [← hg, ← spectralNorm.eq_of_tower, ← isPowMul_spectralNorm g hn,
        spectralNorm.eq_of_tower (L := L), hgn]
    rw [hpow_spec]
    have hint : IsIntegral K (φ (b ^ n)) := by
      rw [← hgn]
      exact (Algebra.IsIntegral.isIntegral (g ^ n)).map (IsScalarTower.toAlgHom K E L)
    exact (φ.spectralNorm_apply_le_natDegree_mul_norm hint).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hdeg) (norm_nonneg _))
  · rw [TauCeti.spectralNorm_eq_zero_of_not_isAlgebraic hb]
    exact gelfandRadius_nonneg b

/-- Every `K`-algebra homomorphism from a Banach `K`-algebra `B` into a field extension `L / K`
over a complete ultrametric normed field `K` is bounded by the norm on `B`. -/
theorem spectralNorm_apply_le_norm (φ : B →ₐ[K] L) (b : B) :
    spectralNorm K L (φ b) ≤ ‖b‖ :=
  (φ.spectralNorm_apply_le_gelfandRadius b).trans (gelfandRadius_le_norm b)

/-- Over a complete ultrametric normed field `K`, any `K`-algebra homomorphism from a Banach
`K`-algebra `B` into an algebraic normed field extension `M / K` satisfies
`‖φ b‖ ≤ gelfandRadius b`. -/
theorem norm_apply_le_gelfandRadius_of_isAlgebraic {M : Type*} [NormedField M] [NormedAlgebra K M]
    [Algebra.IsAlgebraic K M] (φ : B →ₐ[K] M) (b : B) :
    ‖φ b‖ ≤ gelfandRadius b := by
  have : IsUltrametricDist M :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one fun n ↦ by
      rw [← map_natCast (algebraMap K M), norm_algebraMap']
      simpa using IsUltrametricDist.norm_nsmul_le (1 : K) n
  have hle : ‖φ b‖ ≤ spectralNorm K M (φ b) := by
    rw [← NormedAlgebra.toMulAlgebraNorm_apply K M (φ b), ← MulAlgebraNorm.coe_AlgebraNorm]
    exact norm_le_spectralNorm (MulRingNorm.isPowMul _) IsUltrametricDist.isNonarchimedean_norm
      (Algebra.IsAlgebraic.isAlgebraic (φ b))
  exact hle.trans (φ.spectralNorm_apply_le_gelfandRadius b)

/-- Over a complete ultrametric normed field `K`, any `K`-algebra homomorphism from a Banach
`K`-algebra `B` into an algebraic normed field extension `M / K` is contractive. -/
theorem norm_apply_le_norm_of_isAlgebraic {M : Type*} [NormedField M] [NormedAlgebra K M]
    [Algebra.IsAlgebraic K M] (φ : B →ₐ[K] M) (b : B) :
    ‖φ b‖ ≤ ‖b‖ :=
  (φ.norm_apply_le_gelfandRadius_of_isAlgebraic b).trans (gelfandRadius_le_norm b)

/-- **Automatic continuity into algebraic normed field extensions.** Over a complete ultrametric
normed field `K`, every `K`-algebra homomorphism from a Banach `K`-algebra `B` into an algebraic
normed field extension `M / K` is automatically continuous. -/
theorem continuous_of_isAlgebraic {M : Type*} [NormedField M] [NormedAlgebra K M]
    [Algebra.IsAlgebraic K M] (φ : B →ₐ[K] M) :
    Continuous φ :=
  φ.toLinearMap.mkContinuous 1 (fun b ↦ by simpa using φ.norm_apply_le_norm_of_isAlgebraic b)
    |>.continuous

end AlgHom
