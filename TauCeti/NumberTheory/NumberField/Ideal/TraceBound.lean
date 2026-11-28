/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Discriminant.Different
public import Mathlib.RingTheory.FractionalIdeal.Norm
import Mathlib.Analysis.MeanInequalities
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic

/-!
# Trace lower bounds for fractional ideals

A nonzero element in a fractional ideal has absolute field norm at least the absolute norm
of the ideal. For an element nonnegative at every complex embedding, the arithmetic–geometric
mean inequality then gives a lower bound for its trace. Applied to an inverse square different
times an inverse integral ideal, this bounds the trace lengths that arise from Hermitian duals.
For the short-basis application see `New.Space.exists_short_basis_stdSpace` in
`grh/src/Lib/Adelic/Reduction/FirstMinimumShortBases.lean` of lsernau/grh-lean (`72fead1`).
-/

public section

open scoped BigOperators ComplexOrder nonZeroDivisors NumberField

namespace FractionalIdeal

variable {K : Type*} [Field K] [NumberField K]

/-- The absolute field norm of a nonzero element of a fractional ideal is at least the
absolute ideal norm. -/
theorem absNorm_le_abs_norm_of_mem (I : FractionalIdeal (𝓞 K)⁰ K) {x : K}
    (hx : x ∈ I) (hx₀ : x ≠ 0) : absNorm I ≤ |Algebra.norm ℚ x| := by
  have hI : I ≠ 0 := by
    rintro rfl
    exact hx₀ ((mem_zero_iff _).mp hx)
  have hXI : spanSingleton (𝓞 K)⁰ x * I⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_iff₀ (pos_iff_ne_zero.mpr hI), one_mul]
    exact spanSingleton_le_iff_mem.mpr hx
  obtain ⟨J, hJ⟩ := le_one_iff_exists_coeIdeal.mp hXI
  have hJ₀ : J ≠ ⊥ := by
    intro h
    rw [h, coeIdeal_bot] at hJ
    exact mul_ne_zero (spanSingleton_ne_zero_iff.mpr hx₀) (inv_ne_zero hI) hJ.symm
  have hnorm : (1 : ℚ) ≤ J.absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hJ₀)
  rw [← coeIdeal_absNorm (K := K), hJ, map_mul, map_inv₀, absNorm_span_singleton,
    ← div_eq_mul_inv] at hnorm
  have hpos : 0 < absNorm I :=
    lt_of_le_of_ne (absNorm_nonneg _) (Ne.symm (absNorm_eq_zero_iff.not.mpr hI))
  simpa only [one_mul] using (le_div_iff₀ hpos).mp hnorm

/-- The trace of a nonzero element nonnegative at every complex embedding is at least the
field degree times the corresponding root of the absolute ideal norm. The embedding condition
expresses that each image lies on the nonnegative real ray. -/
theorem finrank_mul_absNorm_rpow_le_trace (I : FractionalIdeal (𝓞 K)⁰ K) {x : K}
    (hx : x ∈ I) (hx₀ : x ≠ 0) (hreal : ∀ σ : K →ₐ[ℚ] ℂ, 0 ≤ σ x) :
    (Module.finrank ℚ K : ℝ) * (absNorm I : ℝ) ^ (Module.finrank ℚ K : ℝ)⁻¹ ≤
      (Algebra.trace ℚ K x : ℝ) := by
  classical
  have hn : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hcard := AlgHom.card ℚ K ℂ
  have hweights : (0 : ℝ) < ∑ _ : K →ₐ[ℚ] ℂ, (1 : ℝ) := by simpa [hcard] using hn
  have hmean := Real.geom_mean_le_arith_mean Finset.univ (fun _ ↦ (1 : ℝ))
    (fun σ : K →ₐ[ℚ] ℂ ↦ ‖σ x‖) (by simp) hweights (fun _ _ ↦ norm_nonneg _)
  have htrace : (Algebra.trace ℚ K x : ℝ) = ∑ σ : K →ₐ[ℚ] ℂ, ‖σ x‖ := by
    have h := congrArg Complex.re (trace_eq_sum_embeddings ℂ (K := ℚ) (x := x))
    have hre (σ : K →ₐ[ℚ] ℂ) : (σ x).re = ‖σ x‖ := by
      simpa only [Complex.ofReal_re] using
        congrArg Complex.re (Complex.norm_of_nonneg' (hreal σ)).symm
    simpa [hre] using h
  have hnorm : (|Algebra.norm ℚ x| : ℝ) = ∏ σ : K →ₐ[ℚ] ℂ, ‖σ x‖ := by
    have h := congrArg norm (Algebra.norm_eq_prod_embeddings ℚ ℂ x)
    simpa [norm_prod] using h
  have hle : (absNorm I : ℝ) ≤ ∏ σ : K →ₐ[ℚ] ℂ, ‖σ x‖ := by
    rw [← hnorm]
    exact_mod_cast I.absNorm_le_abs_norm_of_mem hx hx₀
  have hI₀ : (0 : ℝ) ≤ absNorm I := by exact_mod_cast absNorm_nonneg I
  rw [htrace]
  have hroot := Real.rpow_le_rpow hI₀ hle (inv_nonneg.mpr hn.le)
  refine (mul_le_mul_of_nonneg_left hroot hn.le).trans ?_
  rw [mul_comm]
  apply (le_div_iff₀ hn).mp
  simpa [hcard] using hmean

end FractionalIdeal

namespace Ideal

variable {K : Type*} [Field K] [NumberField K]

/-- If `x` is nonzero, nonnegative at every embedding, and belongs to the inverse of
`𝔇_K² J`, its trace is at least `[K : ℚ] · (|disc K|² N(J))^(-1/[K : ℚ])`.
This is the scalar trace estimate for self-pairings in the trace dual of a Hermitian lattice. -/
theorem finrank_mul_rpow_inv_discr_sq_mul_absNorm_le_trace (J : Ideal (𝓞 K)) {x : K}
    (hx : x ∈ ((differentIdeal ℤ (𝓞 K) ^ 2 * J : Ideal (𝓞 K)) :
      FractionalIdeal (𝓞 K)⁰ K)⁻¹) (hx₀ : x ≠ 0)
    (hreal : ∀ σ : K →ₐ[ℚ] ℂ, 0 ≤ σ x) :
    (Module.finrank ℚ K : ℝ) *
        (((NumberField.discr K).natAbs : ℝ) ^ 2 * J.absNorm) ^ (-(Module.finrank ℚ K : ℝ)⁻¹) ≤
      (Algebra.trace ℚ K x : ℝ) := by
  have h := FractionalIdeal.finrank_mul_absNorm_rpow_le_trace _ hx hx₀ hreal
  rw [Real.rpow_neg_eq_inv_rpow]
  simpa only [map_inv₀, FractionalIdeal.coeIdeal_absNorm, map_mul, map_pow,
    NumberField.absNorm_differentIdeal K (𝓞 K), Rat.cast_mul, Rat.cast_pow, Rat.cast_inv,
    Rat.cast_natCast, Nat.cast_mul, Nat.cast_pow] using h

end Ideal
