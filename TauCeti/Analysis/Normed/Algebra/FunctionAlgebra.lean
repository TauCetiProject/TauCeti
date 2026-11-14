/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Unbundled.SmoothingSeminorm
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Finite
public import TauCeti.Analysis.Normed.Unbundled.SpectralNorm.Reduced
public import TauCeti.RingTheory.Huber.Uniform

import Mathlib.Algebra.Polynomial.Div
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.FieldTheory.Minpoly.Finite
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Integer
import TauCeti.Analysis.Normed.Operator.Embedding
import TauCeti.Analysis.Normed.Ring.Ultra
import TauCeti.Analysis.Normed.Unbundled.RootBound
import TauCeti.Analysis.Normed.Unbundled.SpectralNorm.Basic
import TauCeti.Analysis.Normed.Unbundled.SpectralNorm.Irreducible
import TauCeti.FieldTheory.Minpoly.TorsionFree
import TauCeti.RingTheory.Huber.Normed
import TauCeti.RingTheory.Huber.StrictMorphism
import TauCeti.RingTheory.Localization.Reduced

/-!
# Nonarchimedean Banach function algebras and finite torsion-free extensions

A commutative Banach algebra `A` is a *Banach function algebra* (in the sense of
Bosch–Güntzer–Remmert, §3.8.3) when its norm is equivalent to its spectral / smoothing seminorm
`smoothingFun (normRingSeminorm A)` (equivalently Mathlib's `gelfandRadius`).

This file establishes three pillars of the theory over nonarchimedean fields of arbitrary
characteristic:

1. **Gelfand radius and ultrametric smoothing without `‖1‖ ≤ 1`.** For every seminormed commutative
   ring `A`, `smoothingFun (normRingSeminorm A) a = gelfandRadius a` with no normalization on
   `‖(1 : A)‖`, and `gelfandRadius` forms a power-multiplicative `RingSeminorm A`
   (`TauCeti.gelfandRadiusRingSeminorm`). When `A` is ultrametric, `gelfandRadius` is moreover
   nonarchimedean (`TauCeti.isNonarchimedean_gelfandRadius`).
2. **Automatic continuity into algebraic field extensions.** Over a complete nontrivially normed
   ultrametric field `K`, any `K`-algebra homomorphism `φ : B →ₐ[K] L` from an arbitrary Banach
   `K`-algebra `B` (not assumed commutative, ultrametric, Noetherian, or unital-norm-normalized)
   into a field extension `L / K` satisfies `spectralNorm K L (φ b) ≤ gelfandRadius b ≤ ‖b‖`. In
   particular, `φ` is contractive and continuous whenever `L / K` is an algebraic normed extension.
3. **[BGR, §3.8.3, Theorem 7] for finite torsion-free extensions.** Let `B` be a Noetherian
   integrally closed ultrametric Banach `K`-algebra domain with isometric fraction field `F`, and
   let `A` be an ultrametric Banach `K`-algebra that is finite and torsion-free over `B` with
   continuous structure map `B → A`.
   * Without weak stability of `F` or reducedness of `A`, for every `a : A` we have
     `gelfandRadius a = spectralValue (minpoly B a)`.
   * When `A` is reduced, `F ⊗[B] A` is a finite reduced `F`-algebra and
     `smoothingFun (normRingSeminorm A) a = reducedSpectralAlgNorm F (F ⊗[B] A) (1 ⊗ₜ[B] a)`.
   * When `F` is moreover weakly stable (`TauCeti.IsWeaklyStable F`), `A` is a Banach function
     algebra: there exists `C > 0` such that for all `a : A`,
     `smoothingFun (normRingSeminorm A) a ≤ ‖a‖ ≤ C * smoothingFun (normRingSeminorm A) a`,
     and `A` is uniform (`TauCeti.Huber.IsUniform A`).

## Main definitions and results

* `TauCeti.gelfandRadiusRingSeminorm` and `Commute.gelfandRadius_add_le_max`: `RingSeminorm`
  bundling of `gelfandRadius` without `‖1‖ ≤ 1`, and ultrametricity under `IsUltrametricDist`.
* `TauCeti.smoothingFun_normRingSeminorm_eq_gelfandRadius`: equality of `smoothingFun` and
  `gelfandRadius` in any seminormed commutative ring.
* `AlgHom.spectralNorm_apply_le_gelfandRadius` and `AlgHom.continuous_of_isAlgebraic`: spectral
  contraction and automatic continuity from arbitrary Banach `K`-algebras into algebraic field
  extensions.
* `TauCeti.Huber.gelfandRadius_le_one_of_isPowerBounded` and
  `TauCeti.Huber.IsUniform.of_norm_le_mul_gelfandRadius`: uniformity criterion from a Gelfand
  radius bound.
* `TauCeti.gelfandRadius_eq_spectralValue_minpoly` and
  `TauCeti.smoothingFun_eq_reducedSpectralAlgNorm`: minimal-polynomial and base-change formulas in
  finite torsion-free extensions.
* `TauCeti.exists_pos_norm_le_mul_smoothingFun_of_isWeaklyStable`,
  `TauCeti.isUniform_of_isWeaklyStable`, and
  `AlgHom.exists_pos_norm_le_mul_smoothingFun_of_isWeaklyStable`: [BGR, §3.8.3, Theorem 7].

## References

* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert],
  §§3.7.5, 3.8.1, and 3.8.3 (Theorem 7).
-/

public section

open Filter Polynomial Topology
open scoped TensorProduct nonZeroDivisors IntermediateField

section GelfandRadius

/-- In an ultrametric seminormed ring, the Gelfand radius of a sum of commuting elements is at most
the maximum of their Gelfand radii. No normalization on `‖1‖` is needed. -/
theorem Commute.gelfandRadius_add_le_max {A : Type*} [SeminormedRing A] [IsUltrametricDist A]
    {a b : A} (h : Commute a b) :
    gelfandRadius (a + b) ≤ max (gelfandRadius a) (gelfandRadius b) := by
  refine le_of_forall_gt_imp_ge_of_dense fun r hr ↦ ?_
  have ha_lt : gelfandRadius a < r := (le_max_left _ _).trans_lt hr
  have hb_lt : gelfandRadius b < r := (le_max_right _ _).trans_lt hr
  have hr0 : 0 < r := (gelfandRadius_nonneg a).trans_lt ha_lt
  obtain ⟨Ca, hCa, ha⟩ := norm_pow_le_mul_pow_of_gelfandRadius_lt a ha_lt
  obtain ⟨Cb, hCb, hb⟩ := norm_pow_le_mul_pow_of_gelfandRadius_lt b hb_lt
  refine gelfandRadius_le_of_bound hr0.le (C := Ca * Cb * ‖(1 : A)‖) fun n ↦ ?_
  rw [h.add_pow]
  obtain ⟨k, hk, hle⟩ := IsUltrametricDist.isNonarchimedean_norm.finset_image_add_of_nonempty
    (fun k ↦ a ^ k * b ^ (n - k) * (n.choose k : A)) (Finset.nonempty_range_add_one)
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hnat : ‖(n.choose k : A)‖ ≤ ‖(1 : A)‖ := by
    simpa using IsUltrametricDist.norm_nsmul_le (1 : A) (n.choose k)
  calc
    ‖∑ m ∈ Finset.range (n + 1), a ^ m * b ^ (n - m) * (n.choose m : A)‖
        ≤ ‖a ^ k * b ^ (n - k) * (n.choose k : A)‖ := hle
    _ ≤ ‖a ^ k‖ * ‖b ^ (n - k)‖ * ‖(n.choose k : A)‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (Ca * r ^ k) * (Cb * r ^ (n - k)) * ‖(1 : A)‖ := by
      gcongr
      · exact ha k
      · exact hb (n - k)
    _ = Ca * Cb * ‖(1 : A)‖ * r ^ n := by
      have hrpow : r ^ k * r ^ (n - k) = r ^ n := by
        rw [← pow_add, Nat.add_sub_of_le hkn]
      calc
        (Ca * r ^ k) * (Cb * r ^ (n - k)) * ‖(1 : A)‖
            = Ca * Cb * ‖(1 : A)‖ * (r ^ k * r ^ (n - k)) := by ring
        _ = Ca * Cb * ‖(1 : A)‖ * r ^ n := by rw [hrpow]

namespace TauCeti

/-- In any seminormed commutative ring, `smoothingFun (normRingSeminorm A)` agrees with Mathlib's
`gelfandRadius`, without requiring `‖(1 : A)‖ ≤ 1`. -/
theorem smoothingFun_normRingSeminorm_eq_gelfandRadius {A : Type*} [SeminormedCommRing A] (a : A) :
    smoothingFun (normRingSeminorm A) a = gelfandRadius a := by
  have hnorm (x : A) : normRingSeminorm A x = ‖x‖ := rfl
  refine le_antisymm ?_ ?_
  · refine ge_of_tendsto' (tendsto_gelfandRadius' a) fun k ↦ ?_
    have hk : smoothingFun (normRingSeminorm A) a ≤
        normRingSeminorm A (a ^ (k : ℕ)) ^ (1 / (k : ℝ)) :=
      ciInf_le (smoothingSeminormSeq_bddBelow (normRingSeminorm A) a) k
    rwa [hnorm, one_div] at hk
  · refine le_ciInf fun k ↦ ?_
    rw [hnorm, one_div]
    exact gelfandRadius_le_norm_pow a k.ne_zero

/-- `smoothingFun (normRingSeminorm A) a ≤ ‖a‖` in any seminormed commutative ring. -/
theorem smoothingFun_normRingSeminorm_le_norm {A : Type*} [SeminormedCommRing A] (a : A) :
    smoothingFun (normRingSeminorm A) a ≤ ‖a‖ := by
  rw [smoothingFun_normRingSeminorm_eq_gelfandRadius]
  exact gelfandRadius_le_norm a

/-- In an ultrametric seminormed commutative ring, `gelfandRadius` is nonarchimedean. -/
theorem isNonarchimedean_gelfandRadius {A : Type*} [SeminormedCommRing A] [IsUltrametricDist A] :
    IsNonarchimedean (gelfandRadius : A → ℝ) := fun a b ↦
  (Commute.all a b).gelfandRadius_add_le_max

/-- In any seminormed commutative ring, `gelfandRadius` bundled as a `RingSeminorm`, without
requiring `‖(1 : A)‖ ≤ 1`. -/
noncomputable def gelfandRadiusRingSeminorm (A : Type*) [SeminormedCommRing A] :
    RingSeminorm A where
  toFun := gelfandRadius
  map_zero' := gelfandRadius_zero
  add_le' := gelfandRadius_add_le
  neg' := gelfandRadius_neg
  mul_le' := gelfandRadius_mul_le

/-- `gelfandRadiusRingSeminorm A` evaluates to `gelfandRadius`. -/
@[simp]
theorem gelfandRadiusRingSeminorm_apply {A : Type*} [SeminormedCommRing A] (a : A) :
    gelfandRadiusRingSeminorm A a = gelfandRadius a := (rfl)

/-- `gelfandRadiusRingSeminorm A` is power-multiplicative. -/
theorem isPowMul_gelfandRadiusRingSeminorm {A : Type*} [SeminormedCommRing A] :
    IsPowMul (gelfandRadiusRingSeminorm A) := fun a _n hn ↦
  gelfandRadius_pow_of_ne_zero a (Nat.one_le_iff_ne_zero.mp hn)

/-- In an ultrametric seminormed commutative ring, `gelfandRadiusRingSeminorm A` is
nonarchimedean. -/
theorem isNonarchimedean_gelfandRadiusRingSeminorm {A : Type*} [SeminormedCommRing A]
    [IsUltrametricDist A] : IsNonarchimedean (gelfandRadiusRingSeminorm A) :=
  isNonarchimedean_gelfandRadius

end TauCeti

end GelfandRadius

section AlgebraicTarget

namespace AlgHom

variable {K B L : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NormedRing B] [NormedAlgebra K B] [CompleteSpace B]
  [Field L] [Algebra K L]

/-- Quantitative single-element step: for an integral image `φ x` of minimal-polynomial degree `d`,
`spectralNorm K L (φ x) ≤ d * ‖x‖`. -/
private theorem spectralNorm_apply_le_natDegree_mul_norm (φ : B →ₐ[K] L) {x : B}
    (hx : IsIntegral K (φ x)) :
    spectralNorm K L (φ x) ≤ (minpoly K (φ x)).natDegree * ‖x‖ := by
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
  have ha0_ne : p.coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hx hφx
  have hr_eq : r = ‖p.coeff 0‖ ^ (1 / (d : ℝ)) :=
    Polynomial.spectralValue_eq_norm_coeff_zero_rpow_of_irreducible hp_monic hp_irred
  have ha0_norm : ‖p.coeff 0‖ = r ^ d := by
    have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
    rw [hr_eq, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), one_div_mul_cancel hdR,
      Real.rpow_one]
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
  have hdiv_le_one : ‖x‖ / r ≤ 1 := (div_le_one hr).mpr hxr.le
  have hz_le : ‖z‖ ≤ d * (‖x‖ / r) := by
    dsimp only [z]
    rw [norm_neg]
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun j hj ↦ (?_ : _ ≤ ‖x‖ / r)).trans (by simp [nsmul_eq_mul])
    have hjd : j + 1 ≤ d := Finset.mem_range.mp hj
    have hcoeff : ‖(p.coeff 0)⁻¹ * p.coeff (j + 1)‖ ≤ r⁻¹ ^ (j + 1) := by
      rw [norm_mul, norm_inv, ha0_norm]
      have h1 : ‖p.coeff (j + 1)‖ ≤ r ^ (d - (j + 1)) :=
        hp_monic.norm_coeff_le_spectralValue_pow (j + 1)
      calc
        (r ^ d)⁻¹ * ‖p.coeff (j + 1)‖ ≤ (r ^ d)⁻¹ * r ^ (d - (j + 1)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = r⁻¹ ^ (j + 1) := by
          have hrd : r ^ d = r ^ (j + 1) * r ^ (d - (j + 1)) := by
            rw [← pow_add, Nat.add_sub_of_le hjd]
          rw [hrd, mul_inv, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hr.ne'), mul_one, inv_pow]
    calc
      ‖((p.coeff 0)⁻¹ * p.coeff (j + 1)) • x ^ (j + 1)‖
          = ‖(p.coeff 0)⁻¹ * p.coeff (j + 1)‖ * ‖x ^ (j + 1)‖ := norm_smul _ _
      _ ≤ r⁻¹ ^ (j + 1) * ‖x‖ ^ (j + 1) :=
        mul_le_mul hcoeff (norm_pow_le' x (Nat.succ_pos j)) (norm_nonneg _) (by positivity)
      _ = (‖x‖ / r) ^ (j + 1) := by rw [div_eq_mul_inv, mul_comm ‖x‖, mul_pow]
      _ ≤ ‖x‖ / r := pow_le_of_le_one (by positivity) hdiv_le_one (Nat.succ_ne_zero j)
  have h1 : 1 ≤ d * (‖x‖ / r) := hz_ge.trans hz_le
  rwa [← mul_div_assoc, one_le_div hr] at h1

/-- **Spectral-norm bound by Gelfand radius.** Over a complete nontrivially normed ultrametric
field `K`, any `K`-algebra homomorphism `φ : B →ₐ[K] L` from a Banach `K`-algebra `B` into a field
extension `L / K` satisfies `spectralNorm K L (φ b) ≤ gelfandRadius b` for every `b : B`.
Neither commutativity, ultrametricity, Noetherianity, nor `‖1‖ = 1` is assumed on `B`, and
transcendental images have spectral norm `0`. -/
theorem spectralNorm_apply_le_gelfandRadius (φ : B →ₐ[K] L) (b : B) :
    spectralNorm K L (φ b) ≤ gelfandRadius b := by
  by_cases hb : IsAlgebraic K (φ b)
  · have hbij : IsIntegral K (φ b) := hb.isIntegral
    let E := K⟮φ b⟯
    have : FiniteDimensional K E := IntermediateField.adjoin.finiteDimensional hbij
    let g : E := IntermediateField.AdjoinSimple.gen K (φ b)
    have hg : algebraMap E L g = φ b := IntermediateField.AdjoinSimple.algebraMap_gen K (φ b)
    set N := Module.finrank K E
    have hN : 0 < N := Module.finrank_pos
    have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    have hlim : Tendsto (fun n : ℕ ↦ (N : ℝ) ^ (n : ℝ)⁻¹ * (‖b ^ n‖ ^ (n : ℝ)⁻¹))
        atTop (𝓝 (gelfandRadius b)) := by
      have hNlim : Tendsto (fun n : ℕ ↦ (N : ℝ) ^ (n : ℝ)⁻¹) atTop (𝓝 1) :=
        ((Real.continuous_const_rpow hNR.ne').tendsto' 0 1 (Real.rpow_zero _)).comp
          tendsto_inv_atTop_nhds_zero_nat
      simpa using hNlim.mul (tendsto_gelfandRadius b)
    refine ge_of_tendsto hlim (eventually_atTop.mpr ⟨1, fun n hn ↦ ?_⟩)
    have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
    have hgn : algebraMap E L (g ^ n) = φ (b ^ n) := by rw [map_pow, map_pow, hg]
    have hdeg : (minpoly K (φ (b ^ n))).natDegree ≤ N := by
      rw [← hgn, minpoly.algebraMap_eq (algebraMap E L).injective]
      exact minpoly.natDegree_le (g ^ n)
    have hpow_spec : spectralNorm K L (φ b) ^ n = spectralNorm K L (φ (b ^ n)) := by
      rw [← hg, ← spectralNorm.eq_of_tower, ← isPowMul_spectralNorm g hn,
        spectralNorm.eq_of_tower (L := L), hgn]
    have hstep : spectralNorm K L (φ b) ^ n ≤ N * ‖b ^ n‖ := by
      rw [hpow_spec]
      have hint : IsIntegral K (φ (b ^ n)) := by
        rw [← hgn]
        exact (Algebra.IsIntegral.isIntegral (g ^ n)).map (IsScalarTower.toAlgHom K E L)
      exact (φ.spectralNorm_apply_le_natDegree_mul_norm hint).trans
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hdeg) (norm_nonneg _))
    calc
      spectralNorm K L (φ b)
          = (spectralNorm K L (φ b) ^ n) ^ (n : ℝ)⁻¹ :=
        (Real.pow_rpow_inv_natCast (spectralNorm_nonneg _) hn0).symm
      _ ≤ ((N : ℝ) * ‖b ^ n‖) ^ (n : ℝ)⁻¹ :=
        Real.rpow_le_rpow (pow_nonneg (spectralNorm_nonneg _) n) hstep (by positivity)
      _ = (N : ℝ) ^ (n : ℝ)⁻¹ * (‖b ^ n‖ ^ (n : ℝ)⁻¹) :=
        Real.mul_rpow hNR.le (norm_nonneg _)
  · rw [TauCeti.spectralNorm_eq_zero_of_not_isAlgebraic hb]
    exact gelfandRadius_nonneg b

/-- Every `K`-algebra homomorphism from a Banach `K`-algebra `B` into a field extension `L / K`
over a complete nontrivially normed ultrametric field `K` is bounded by the norm on `B`. -/
theorem spectralNorm_apply_le_norm (φ : B →ₐ[K] L) (b : B) :
    spectralNorm K L (φ b) ≤ ‖b‖ :=
  (φ.spectralNorm_apply_le_gelfandRadius b).trans (gelfandRadius_le_norm b)

/-- Over a complete nontrivially normed ultrametric field `K`, any `K`-algebra homomorphism from a
Banach `K`-algebra `B` into an algebraic normed field extension `M / K` satisfies
`‖φ b‖ ≤ gelfandRadius b`. -/
theorem norm_apply_le_gelfandRadius_of_isAlgebraic {M : Type*} [NormedField M] [NormedAlgebra K M]
    [Algebra.IsAlgebraic K M] (φ : B →ₐ[K] M) (b : B) :
    ‖φ b‖ ≤ gelfandRadius b := by
  rw [NormedAlgebra.norm_eq_spectralNorm K (φ b)]
  exact φ.spectralNorm_apply_le_gelfandRadius b

/-- Over a complete nontrivially normed ultrametric field `K`, any `K`-algebra homomorphism from a
Banach `K`-algebra `B` into an algebraic normed field extension `M / K` is contractive. -/
theorem norm_apply_le_norm_of_isAlgebraic {M : Type*} [NormedField M] [NormedAlgebra K M]
    [Algebra.IsAlgebraic K M] (φ : B →ₐ[K] M) (b : B) :
    ‖φ b‖ ≤ ‖b‖ :=
  (φ.norm_apply_le_gelfandRadius_of_isAlgebraic b).trans (gelfandRadius_le_norm b)

/-- **Automatic continuity into algebraic normed field extensions.** Over a complete nontrivially
normed ultrametric field `K`, every `K`-algebra homomorphism from a Banach `K`-algebra `B` into an
algebraic normed field extension `M / K` is automatically continuous. -/
theorem continuous_of_isAlgebraic {M : Type*} [NormedField M] [NormedAlgebra K M]
    [Algebra.IsAlgebraic K M] (φ : B →ₐ[K] M) :
    Continuous φ :=
  φ.toLinearMap.mkContinuous 1 (fun b ↦ by simpa using φ.norm_apply_le_norm_of_isAlgebraic b)
    |>.continuous

end AlgHom

end AlgebraicTarget

section Uniformity

namespace TauCeti.Huber

/-- In a seminormed ring with a pseudouniformiser, every power-bounded element has Gelfand radius
at most `1`. -/
theorem IsPseudoUniformizer.gelfandRadius_le_one_of_isPowerBounded {R : Type*} [SeminormedRing R]
    {ϖ : R} (hϖ : IsPseudoUniformizer ϖ) {x : R} (hx : IsPowerBounded x) :
    gelfandRadius x ≤ 1 := by
  obtain ⟨M, hM⟩ := hϖ.isBounded_iff_forall_norm_le.mp (isPowerBounded_iff.mp hx)
  exact gelfandRadius_le_of_bound zero_le_one (C := M) fun n ↦ by
    simpa only [one_pow, mul_one] using hM (x ^ n) ⟨n, rfl⟩

/-- In a seminormed algebra over a nontrivially normed field, every power-bounded element has
Gelfand radius at most `1`. -/
theorem gelfandRadius_le_one_of_isPowerBounded (K : Type*) [NontriviallyNormedField K]
    {R : Type*} [SeminormedRing R] [NormedAlgebra K R] {x : R} (hx : IsPowerBounded x) :
    gelfandRadius x ≤ 1 := by
  obtain ⟨ϖ, hϖ0, hϖ1⟩ := NormedField.exists_norm_lt_one K
  have hϖ := (IsPseudoUniformizer.of_norm_lt_one
    (isUnit_iff_ne_zero.mpr (norm_pos_iff.mp hϖ0)) hϖ1).map (continuous_algebraMap K R)
  exact hϖ.gelfandRadius_le_one_of_isPowerBounded hx

/-- Any seminormed algebra over a nontrivially normed field whose norm is bounded by a constant
multiple of `gelfandRadius` is uniform (`TauCeti.Huber.IsUniform`). -/
theorem IsUniform.of_norm_le_mul_gelfandRadius (K : Type*) [NontriviallyNormedField K]
    {R : Type*} [SeminormedRing R] [NormedAlgebra K R]
    (h : ∃ C : ℝ, ∀ x : R, ‖x‖ ≤ C * gelfandRadius x) :
    IsUniform R := by
  obtain ⟨C, hC⟩ := h
  refine ⟨(isBounded_closedBall_zero (R := R) (max C 0)).subset fun x hx ↦ ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  calc
    ‖x‖ ≤ C * gelfandRadius x := hC x
    _ ≤ max C 0 * gelfandRadius x :=
      mul_le_mul_of_nonneg_right (le_max_left C 0) (gelfandRadius_nonneg x)
    _ ≤ max C 0 * 1 :=
      mul_le_mul_of_nonneg_left (gelfandRadius_le_one_of_isPowerBounded K hx) (le_max_right C 0)
    _ = max C 0 := mul_one _

/-- Any seminormed commutative algebra over a nontrivially normed field whose norm is bounded by a
constant multiple of `smoothingFun (normRingSeminorm A)` is uniform (`TauCeti.Huber.IsUniform`). -/
theorem IsUniform.of_norm_le_mul_smoothingFun (K : Type*) [NontriviallyNormedField K]
    {A : Type*} [SeminormedCommRing A] [NormedAlgebra K A]
    (h : ∃ C : ℝ, ∀ a : A, ‖a‖ ≤ C * smoothingFun (normRingSeminorm A) a) :
    IsUniform A := by
  refine IsUniform.of_norm_le_mul_gelfandRadius K ?_
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun a ↦ ?_⟩
  rw [← smoothingFun_normRingSeminorm_eq_gelfandRadius]
  exact hC a

end TauCeti.Huber

end Uniformity

section TorsionFreeExtension

namespace TauCeti

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- Base-changing a reduced commutative `B`-algebra `A` to a fraction ring `F` of `B` preserves
reducedness. -/
instance isReduced_tensorProduct_of_isFractionRing {B F A : Type*} [CommRing B] [CommRing F]
    [Algebra B F] [IsFractionRing B F] [CommRing A] [Algebra B A] [IsReduced A] :
    IsReduced (F ⊗[B] A) :=
  IsLocalization.isReduced (Algebra.algebraMapSubmonoid A B⁰) (F ⊗[B] A)

private theorem continuousSMul_of_continuous_algebraMap {B A : Type*} [SeminormedCommRing B]
    [SeminormedCommRing A] [Algebra B A] (hBA : Continuous (algebraMap B A)) :
    ContinuousSMul B A :=
  ⟨((hBA.comp continuous_fst).mul continuous_snd).congr fun p ↦ (Algebra.smul_def p.1 p.2).symm⟩

private theorem includeRight_injective {B F A : Type*} [CommRing B] [CommRing F]
    [Algebra B F] [IsFractionRing B F] [CommRing A] [Algebra B A] [Module.IsTorsionFree B A] :
    Function.Injective (Algebra.TensorProduct.includeRight : A →ₐ[B] F ⊗[B] A) :=
  (IsLocalizedModule.injective_iff_isRegular B⁰ (TensorProduct.mk B F A 1)).mpr
    fun c ↦ (isRegular_iff_mem_nonZeroDivisors.mpr c.2).isSMulRegular

section Extension

variable (K : Type*) [NontriviallyNormedField K]
  {B F A : Type*} [NormedCommRing B] [IsDomain B] [IsUltrametricDist B] [CompleteSpace B]
  [NormedAlgebra K B] [IsNoetherianRing B] [IsIntegrallyClosed B]
  [NormedField F] [IsUltrametricDist F] [Algebra B F] [IsFractionRing B F]
  [NormedCommRing A] [IsUltrametricDist A] [CompleteSpace A] [NormedAlgebra K A]
  [Algebra B A] [IsScalarTower K B A] [Module.Finite B A] [Module.IsTorsionFree B A]

include K

omit [IsFractionRing B F] in
/-- **Minimal-polynomial formula for the Gelfand radius in a finite torsion-free extension.**
Let `B` be a Noetherian integrally closed ultrametric Banach `K`-algebra domain admitting an
isometric algebra map into an ultrametric normed field `F`, and let `A` be an ultrametric Banach
`K`-algebra that is finite and torsion-free over `B` with continuous structure map `B → A`. Then
for every `a : A`, `gelfandRadius a = spectralValue (minpoly B a)`. Neither weak stability of `F`
nor reducedness of `A` is needed. -/
theorem gelfandRadius_eq_spectralValue_minpoly
    (hBF : ∀ b : B, ‖algebraMap B F b‖ = ‖b‖) (hBA : Continuous (algebraMap B A)) (a : A) :
    gelfandRadius a = spectralValue (minpoly B a) := by
  have ha_int : IsIntegral B a := Algebra.IsIntegral.isIntegral a
  rcases subsingleton_or_nontrivial A with hA | hA
  · have hdvd1 : minpoly B a ∣ 1 :=
      TauCeti.minpoly.isIntegrallyClosed_dvd_of_isTorsionFree ha_int (Subsingleton.elim _ _)
    have hp1 : minpoly B a = 1 :=
      (minpoly.monic ha_int).natDegree_eq_zero.mp <| Nat.eq_zero_of_le_zero <|
        (Polynomial.natDegree_le_of_dvd hdvd1 one_ne_zero).trans_eq natDegree_one
    rw [hp1, Polynomial.spectralValue_one, Subsingleton.elim a 0, gelfandRadius_zero]
  set p := minpoly B a
  have hp_monic : p.Monic := minpoly.monic ha_int
  set d := p.natDegree
  have hd : 0 < d := by
    refine Nat.pos_of_ne_zero fun hd0 ↦ ?_
    have h0 : aeval a p = 0 := minpoly.aeval B a
    rw [hp_monic.natDegree_eq_zero.mp hd0, map_one] at h0
    exact one_ne_zero h0
  have hp_ne_one : p ≠ 1 := fun h1 ↦ by simp [d, h1] at hd
  refine le_antisymm ?_ ?_
  · -- Upper bound: `gelfandRadiusRingSeminorm A` is power-multiplicative and nonarchimedean, and
    -- `algebraMap B A` is continuous `K`-linear, so `gelfandRadius (algebraMap B A b) ≤ ‖b‖`.
    let gK : B →L[K] A := ⟨Algebra.linearMap B A, hBA⟩
    have hg_rad (b : B) : gelfandRadius (algebraMap B A b) ≤ ‖b‖ := by
      refine (gelfandRadius_le_of_norm_pow_le ‖gK‖ fun n ↦ ?_).trans (gelfandRadius_le_norm b)
      rw [← map_pow]
      exact gK.le_opNorm (b ^ n)
    have hroot := (hp_monic.map (algebraMap B A)).apply_le_iSup_apply_coeff_rpow_of_eval_eq_zero
      isPowMul_gelfandRadiusRingSeminorm isNonarchimedean_gelfandRadiusRingSeminorm
      (x := a) (by rw [eval_map_algebraMap, minpoly.aeval])
    have hdeg : (p.map (algebraMap B A)).natDegree = d :=
      hp_monic.natDegree_map (algebraMap B A)
    refine hroot.trans (Real.iSup_le (fun i ↦ ?_) (spectralValue_nonneg p))
    let j : ℕ := i
    have hj : j < d := hdeg ▸ i.2
    change gelfandRadius ((p.map (algebraMap B A)).coeff j) ^
      (1 / (((p.map (algebraMap B A)).natDegree : ℝ) - (j : ℝ))) ≤ spectralValue p
    rw [coeff_map, hdeg]
    calc
      gelfandRadius (algebraMap B A (p.coeff j)) ^ (1 / ((d : ℝ) - (j : ℝ)))
          ≤ ‖p.coeff j‖ ^ (1 / ((d : ℝ) - (j : ℝ))) := by
        refine Real.rpow_le_rpow (gelfandRadius_nonneg _) (hg_rad _) ?_
        exact one_div_nonneg.mpr (sub_nonneg.mpr (Nat.cast_le.mpr hj.le))
      _ = spectralValueTerms p j := (spectralValueTerms_of_lt_natDegree p hj).symm
      _ ≤ spectralValue p := le_ciSup (spectralValueTerms_bddAbove p) j
  · -- Lower bound: `Φ : (Fin d → B) →ₗ[B] A`, `c ↦ ∑ i, c i • a ^ i` is injective by
    -- `isIntegrallyClosed_dvd_of_isTorsionFree` and strict by `isStrictMap_of_module_finite`, so
    -- the coefficients of `X ^ n %ₘ p` are bounded by `C * ‖a ^ n‖`.
    have : Huber.IsTateRing B := Huber.IsTateRing.of_normedAlgebra K B
    have : ContinuousSMul B A := continuousSMul_of_continuous_algebraMap hBA
    have : IsNoetherian B A := isNoetherian_of_isNoetherianRing_of_finite B A
    let Φ : (Fin d → B) →ₗ[B] A :=
      { toFun := fun c ↦ ∑ i : Fin d, c i • a ^ (i : ℕ)
        map_add' := fun c₁ c₂ ↦ by simp [add_smul, Finset.sum_add_distrib]
        map_smul' := fun b c ↦ by simp [Finset.smul_sum, smul_smul] }
    have hΦ_inj : Function.Injective Φ := by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro c hc
      let q : B[X] := ∑ i : Fin d, C (c i) * X ^ (i : ℕ)
      have hq_aeval : aeval a q = 0 := by
        simpa [q, Φ, map_sum, aeval_C, Algebra.smul_def] using hc
      have hdvd : p ∣ q := TauCeti.minpoly.isIntegrallyClosed_dvd_of_isTorsionFree ha_int hq_aeval
      have hq0 : q = 0 := by
        by_contra hq_ne
        have hlt : q.natDegree < d := by
          refine (natDegree_sum_le Finset.univ _).trans_lt ?_
          rw [Finset.fold_max_lt]
          refine ⟨hd, fun i _ ↦ ?_⟩
          exact (natDegree_C_mul_X_pow_le (c i) (i : ℕ)).trans_lt i.2
        exact hlt.not_ge (Polynomial.natDegree_le_of_dvd hdvd hq_ne)
      ext i
      have hci : q.coeff (i : ℕ) = c i := by
        simp [q, coeff_C_mul, coeff_X_pow, Fin.val_inj]
      rw [Pi.zero_apply, ← hci, hq0, coeff_zero]
    have hΦ_strict : IsStrictMap Φ := Φ.isStrictMap_of_module_finite
    obtain ⟨C, hC, hΦ_bound⟩ :=
      (Φ.restrictScalars K).exists_pos_norm_le_mul_norm_of_isStrictMap hΦ_strict hΦ_inj
    -- Compare with roots of `p_F := p.map (algebraMap B F)` in `AlgebraicClosure F`.
    let pF : F[X] := p.map (algebraMap B F)
    have hpF_monic : pF.Monic := hp_monic.map _
    have hspec_eq : spectralValue p = spectralValue pF :=
      ((algebraMap B F).spectralValue_map_of_norm_eq hBF p).symm
    rw [hspec_eq]
    classical
    let L := AlgebraicClosure F
    let f : AlgebraNorm F L := spectralAlgNorm F L
    have hmapL :
        mapAlg F L pF = ((mapAlg F L pF).roots.map fun x : L ↦ X - Polynomial.C x).prod := by
      have hmon : (mapAlg F L pF).Monic := by
        rw [mapAlg_eq_map]
        exact hpF_monic.map _
      exact (prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon
        (IsAlgClosed.splits (mapAlg F L pF)).natDegree_eq_card_roots.symm).symm
    rw [← max_norm_root_eq_spectralValue spectralAlgNorm_isPowMul
      isNonarchimedean_spectralNorm spectralAlgNorm_one pF _ hmapL]
    refine ciSup_le fun x ↦ ?_
    split_ifs with hx
    · have hxp : aeval x pF = 0 := by
        have hx0 := (mem_roots (by rw [mapAlg_eq_map]; exact (hpF_monic.map _).ne_zero)).mp hx
        rwa [mapAlg_eq_map, IsRoot.def, eval_map_algebraMap] at hx0
      let D : ℝ := 1 + C * ∑ i : Fin d, f (x ^ (i : ℕ))
      have hD : 0 < D := by
        have : 0 ≤ ∑ i : Fin d, f (x ^ (i : ℕ)) := Finset.sum_nonneg fun _ _ ↦ apply_nonneg f _
        positivity
      have hlim : Tendsto (fun n : ℕ ↦ D ^ (n : ℝ)⁻¹ * (‖a ^ n‖ ^ (n : ℝ)⁻¹))
          atTop (𝓝 (gelfandRadius a)) := by
        have hDlim : Tendsto (fun n : ℕ ↦ D ^ (n : ℝ)⁻¹) atTop (𝓝 1) :=
          ((Real.continuous_const_rpow hD.ne').tendsto' 0 1 (Real.rpow_zero _)).comp
            tendsto_inv_atTop_nhds_zero_nat
        simpa using hDlim.mul (tendsto_gelfandRadius a)
      refine ge_of_tendsto hlim (eventually_atTop.mpr ⟨1, fun n hn ↦ ?_⟩)
      have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
      let rn : B[X] := (X : B[X]) ^ n %ₘ p
      have hrn_deg : rn.natDegree < d := natDegree_modByMonic_lt (X ^ n) hp_monic hp_ne_one
      let cn : Fin d → B := fun i ↦ rn.coeff i
      have hΦ_cn : Φ cn = a ^ n := by
        have haeval : aeval a rn = a ^ n := by
          have hap : aeval a p = 0 := minpoly.aeval B a
          have hdiv := modByMonic_add_div ((X : B[X]) ^ n) p
          have h := congrArg (aeval a) hdiv
          simpa only [rn, map_add, map_mul, hap, zero_mul, add_zero, map_pow, aeval_X]
            using h
        rw [← haeval, aeval_eq_sum_range' hrn_deg, ← Fin.sum_univ_eq_sum_range]
        rfl
      have hcn_norm (i : Fin d) : ‖cn i‖ ≤ C * ‖a ^ n‖ :=
        (norm_le_pi_norm cn i).trans
          ((hΦ_bound cn).trans_eq (by rw [LinearMap.restrictScalars_apply, hΦ_cn]))
      have hx_pow : x ^ n = ∑ i : Fin d, algebraMap B F (cn i) • x ^ (i : ℕ) := by
        let rnF : F[X] := rn.map (algebraMap B F)
        have hrnF_deg : rnF.natDegree < d := natDegree_map_le.trans_lt hrn_deg
        have haevalx : aeval x rnF = x ^ n := by
          have hdiv := congrArg (Polynomial.map (algebraMap B F))
            (modByMonic_add_div ((X : B[X]) ^ n) p)
          have h := congrArg (aeval x) hdiv
          simpa only [rnF, pF, rn, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
            Polynomial.map_X, map_add, map_mul, hxp, zero_mul, add_zero, map_pow, aeval_X] using h
        rw [← haevalx, aeval_eq_sum_range' hrnF_deg, ← Fin.sum_univ_eq_sum_range]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [coeff_map]
      have hfx_pow : f x ^ n ≤ D * ‖a ^ n‖ := by
        calc
          f x ^ n = f (x ^ n) := (spectralAlgNorm_isPowMul x hn).symm
          _ = f (∑ i : Fin d, algebraMap B F (cn i) • x ^ (i : ℕ)) := by rw [hx_pow]
          _ ≤ ∑ i : Fin d, f (algebraMap B F (cn i) • x ^ (i : ℕ)) :=
            Finset.le_sum_of_subadditive f (map_zero f).le (map_add_le_add f) _ _
          _ = ∑ i : Fin d, ‖cn i‖ * f (x ^ (i : ℕ)) := by
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            rw [map_smul_eq_mul, hBF]
          _ ≤ ∑ i : Fin d, (C * ‖a ^ n‖) * f (x ^ (i : ℕ)) :=
            Finset.sum_le_sum fun i _ ↦
              mul_le_mul_of_nonneg_right (hcn_norm i) (apply_nonneg f _)
          _ = (C * ∑ i : Fin d, f (x ^ (i : ℕ))) * ‖a ^ n‖ := by
            rw [← Finset.mul_sum]
            ring
          _ ≤ D * ‖a ^ n‖ := by
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
            dsimp only [D]
            linarith
      calc
        f x = (f x ^ n) ^ (n : ℝ)⁻¹ :=
          (Real.pow_rpow_inv_natCast (apply_nonneg f x) hn0).symm
        _ ≤ (D * ‖a ^ n‖) ^ (n : ℝ)⁻¹ :=
          Real.rpow_le_rpow (by positivity) hfx_pow (by positivity)
        _ = D ^ (n : ℝ)⁻¹ * (‖a ^ n‖ ^ (n : ℝ)⁻¹) :=
          Real.mul_rpow hD.le (norm_nonneg _)
    · exact gelfandRadius_nonneg a

/-- **Smoothing seminorm via `reducedSpectralAlgNorm` on `F ⊗[B] A`.** Under the hypotheses of
`gelfandRadius_eq_spectralValue_minpoly`, when `A` is reduced, `F ⊗[B] A` is a finite reduced
`F`-algebra and `smoothingFun (normRingSeminorm A) a` coincides with
`reducedSpectralAlgNorm F (F ⊗[B] A) (1 ⊗ₜ[B] a)` (no weak stability needed). -/
theorem smoothingFun_eq_reducedSpectralAlgNorm [IsReduced A]
    (hBF : ∀ b : B, ‖algebraMap B F b‖ = ‖b‖) (hBA : Continuous (algebraMap B A)) (a : A) :
    smoothingFun (normRingSeminorm A) a =
      reducedSpectralAlgNorm F (F ⊗[B] A) ((1 : F) ⊗ₜ[B] a) := by
  let φ : A →ₐ[B] F ⊗[B] A := Algebra.TensorProduct.includeRight
  have hφ : Function.Injective φ := includeRight_injective
  have hmin : minpoly F ((1 : F) ⊗ₜ[B] a) = (minpoly B a).map (algebraMap B F) :=
    TauCeti.minpoly.isIntegrallyClosed_eq_field_fractions_of_injective F φ hφ
      (Algebra.IsIntegral.isIntegral a)
  rw [smoothingFun_normRingSeminorm_eq_gelfandRadius,
    gelfandRadius_eq_spectralValue_minpoly K hBF hBA a, reducedSpectralAlgNorm_def, hmin,
    (algebraMap B F).spectralValue_map_of_norm_eq hBF]

/-- **Bosch–Güntzer–Remmert, §3.8.3, Theorem 7.** Let `B` be a Noetherian integrally closed
ultrametric Banach `K`-algebra domain whose fraction field `F` is isometric and weakly stable
(`TauCeti.IsWeaklyStable F`), and let `A` be a reduced ultrametric Banach `K`-algebra that is
finite and torsion-free over `B` with continuous structure map `B → A`. Then `A` is a Banach
function algebra: there exists `C > 0` such that for every `a : A`,
`smoothingFun (normRingSeminorm A) a ≤ ‖a‖` and
`‖a‖ ≤ C * smoothingFun (normRingSeminorm A) a`. -/
theorem exists_pos_norm_le_mul_smoothingFun_of_isWeaklyStable [IsReduced A]
    (hBF : ∀ b : B, ‖algebraMap B F b‖ = ‖b‖) (hF : IsWeaklyStable F)
    (hBA : Continuous (algebraMap B A)) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : A,
      smoothingFun (normRingSeminorm A) a ≤ ‖a‖ ∧
        ‖a‖ ≤ C * smoothingFun (normRingSeminorm A) a := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · refine ⟨1, zero_lt_one, fun a ↦ ?_⟩
    simp [Subsingleton.elim a 0, smoothingFun_normRingSeminorm_eq_gelfandRadius]
  -- Embed `A` `B`-linearly into a finite free `B`-module `ι → B` by clearing denominators of the
  -- coordinates in an `F`-basis of `E := F ⊗[B] A`.
  let E := F ⊗[B] A
  let φ : A →ₐ[B] E := Algebra.TensorProduct.includeRight
  have hφ : Function.Injective φ := includeRight_injective
  have : Nontrivial E := hφ.nontrivial
  let ι := Module.Free.ChooseBasisIndex F E
  let b : Module.Basis ι F E := Module.Free.chooseBasis F E
  have : Nonempty ι := b.index_nonempty
  obtain ⟨m, q, hq_surj⟩ := Module.Finite.exists_fin' B A
  let u (j : Fin m) : A := q (Pi.single j 1)
  obtain ⟨d₀, hd₀_int⟩ := IsLocalization.exist_integer_multiples_of_finite B⁰
    (fun p : Fin m × ι ↦ b.repr (φ (u p.1)) p.2)
  have hd₀_ne : (d₀ : B) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp d₀.2
  have : 0 < ‖(d₀ : B)‖ := norm_pos_iff.mpr hd₀_ne
  let L₀ : Submodule B F := LinearMap.range (Algebra.linearMap B F)
  let eBF : L₀ ≃ₗ[B] B :=
    (LinearEquiv.ofInjective (Algebra.linearMap B F) (IsFractionRing.injective B F)).symm
  have heBF (z : L₀) : algebraMap B F (eBF z) = (z : F) := by
    change (LinearEquiv.ofInjective (Algebra.linearMap B F) (IsFractionRing.injective B F)
      (eBF z) : F) = (z : F)
    rw [LinearEquiv.apply_symm_apply]
  let fi (i : ι) : A →ₗ[B] F :=
    (LinearMap.lsmul F F (algebraMap B F (d₀ : B))).restrictScalars B ∘ₗ
      ((b.coord i).restrictScalars B) ∘ₗ φ.toLinearMap
  have hfi_mem (i : ι) (a : A) : fi i a ∈ L₀ := by
    obtain ⟨c, rfl⟩ := hq_surj a
    have hq_eq : q c = ∑ j : Fin m, c j • u j := by
      conv_lhs => rw [← Finset.univ_sum_single c]
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      have hsingle : Pi.single j (c j) = c j • Pi.single j (1 : B) := by
        ext k; simp [Pi.single_apply]
      rw [hsingle, map_smul]
    rw [hq_eq, map_sum]
    refine Submodule.sum_mem L₀ fun j _ ↦ ?_
    rw [map_smul]
    refine L₀.smul_mem (c j) ?_
    obtain ⟨x, hx⟩ := hd₀_int (j, i)
    exact ⟨x, hx.trans (by simp [fi, Algebra.smul_def])⟩
  let Ψ : A →ₗ[B] (ι → B) :=
    LinearMap.pi fun i ↦ eBF.toLinearMap ∘ₗ (fi i).codRestrict L₀ (hfi_mem i)
  have hΨ_spec (a : A) (i : ι) :
      algebraMap B F (Ψ a i) = algebraMap B F (d₀ : B) * b.repr (φ a) i := by
    have hcod : ((fi i).codRestrict L₀ (hfi_mem i)) a = ⟨fi i a, hfi_mem i a⟩ := rfl
    simp only [Ψ, LinearMap.pi_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, hcod, heBF]
    simp [fi]
  have hΨ_inj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro a ha
    apply hφ
    rw [map_zero]
    apply b.repr.injective
    ext i
    have hi : algebraMap B F (d₀ : B) * b.repr (φ a) i = 0 := by
      have h0 : Ψ a i = 0 := congrFun ha i
      rw [← hΨ_spec, h0, map_zero]
    have hd₀F : algebraMap B F (d₀ : B) ≠ 0 :=
      (map_ne_zero_iff (algebraMap B F) (IsFractionRing.injective B F)).mpr hd₀_ne
    simpa only [map_zero, Finsupp.coe_zero, Pi.zero_apply] using
      (mul_eq_zero.mp hi).resolve_left hd₀F
  have : Huber.IsTateRing B := Huber.IsTateRing.of_normedAlgebra K B
  have : ContinuousSMul B A := continuousSMul_of_continuous_algebraMap hBA
  have hΨ_strict : IsStrictMap Ψ := Ψ.isStrictMap_of_module_finite
  obtain ⟨C₁, hC₁, hΨ_bound⟩ :=
    (Ψ.restrictScalars K).exists_pos_norm_le_mul_norm_of_isStrictMap hΨ_strict hΨ_inj
  obtain ⟨C₂, _, hC₂, _, hb_comp⟩ := hF.exists_basis_reducedSpectralAlgNorm_comparison b
  refine ⟨C₁ * ‖(d₀ : B)‖ * C₂, by positivity,
    fun a ↦ ⟨smoothingFun_normRingSeminorm_le_norm a, ?_⟩⟩
  have hΨ_norm : ‖Ψ a‖ ≤ ‖(d₀ : B)‖ * b.norm (φ a) := by
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg _) (b.norm_nonneg _))).mpr fun i ↦ ?_
    rw [← hBF (Ψ a i), hΨ_spec a i, norm_mul, hBF]
    exact mul_le_mul_of_nonneg_left (b.norm_repr_le_norm i) (norm_nonneg _)
  calc
    ‖a‖ ≤ C₁ * ‖Ψ a‖ := hΨ_bound a
    _ ≤ C₁ * (‖(d₀ : B)‖ * b.norm (φ a)) := mul_le_mul_of_nonneg_left hΨ_norm hC₁.le
    _ ≤ C₁ * (‖(d₀ : B)‖ * (C₂ * reducedSpectralAlgNorm F E (φ a))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hb_comp (φ a)).1 (norm_nonneg _)) hC₁.le
    _ = C₁ * ‖(d₀ : B)‖ * C₂ * smoothingFun (normRingSeminorm A) a := by
      rw [smoothingFun_eq_reducedSpectralAlgNorm K hBF hBA a]
      dsimp only [E, φ, Algebra.TensorProduct.includeRight_apply]
      ring

/-- Under the hypotheses of `exists_pos_norm_le_mul_smoothingFun_of_isWeaklyStable`, `A` is a
uniform Huber ring (`TauCeti.Huber.IsUniform A`). -/
theorem isUniform_of_isWeaklyStable [IsReduced A]
    (hBF : ∀ b : B, ‖algebraMap B F b‖ = ‖b‖) (hF : IsWeaklyStable F)
    (hBA : Continuous (algebraMap B A)) :
    Huber.IsUniform A := by
  obtain ⟨C, _, hC⟩ := exists_pos_norm_le_mul_smoothingFun_of_isWeaklyStable K hBF hF hBA
  exact Huber.IsUniform.of_norm_le_mul_smoothingFun K ⟨C, fun a ↦ (hC a).2⟩

end Extension

end TauCeti

/-- `AlgHom` wrapper for `TauCeti.exists_pos_norm_le_mul_smoothingFun_of_isWeaklyStable`, taking a
continuous finite `K`-algebra homomorphism `g : B →ₐ[K] A` whose nonzero elements act without
torsion on `A`. -/
theorem AlgHom.exists_pos_norm_le_mul_smoothingFun_of_isWeaklyStable
    {K B F A : Type*} [NontriviallyNormedField K]
    [NormedCommRing B] [IsDomain B] [IsUltrametricDist B] [CompleteSpace B]
    [NormedAlgebra K B] [IsNoetherianRing B] [IsIntegrallyClosed B]
    [NormedField F] [IsUltrametricDist F] [Algebra B F] [IsFractionRing B F]
    [NormedCommRing A] [IsReduced A] [IsUltrametricDist A] [CompleteSpace A] [NormedAlgebra K A]
    (g : B →ₐ[K] A) (hg_cont : Continuous g) (hg_fin : g.Finite)
    (hg_tf : ∀ ⦃b : B⦄ ⦃a : A⦄, b ≠ 0 → g b * a = 0 → a = 0)
    (hBF : ∀ b : B, ‖algebraMap B F b‖ = ‖b‖) (hF : TauCeti.IsWeaklyStable F) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : A,
      smoothingFun (normRingSeminorm A) a ≤ ‖a‖ ∧
        ‖a‖ ≤ C * smoothingFun (normRingSeminorm A) a := by
  let _ : Algebra B A := g.toRingHom.toAlgebra
  have : IsScalarTower K B A := .of_algebraMap_eq fun c ↦ (g.commutes c).symm
  have : Module.Finite B A := hg_fin
  have : Module.IsTorsionFree B A := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun b a hba ↦ ?_
    by_cases hb : b = 0
    · exact Or.inl hb
    · exact Or.inr (hg_tf hb hba)
  exact TauCeti.exists_pos_norm_le_mul_smoothingFun_of_isWeaklyStable K hBF hF hg_cont

end TorsionFreeExtension
