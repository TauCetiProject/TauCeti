/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The root used to normalize CM theta periods

The scalar used in the theta period factor is the principal `f`-th root of
`υ⁻¹√A`, where `υ` is the unitary splitting character evaluated at a finite idele and `A` is
its idele norm. Reciprocity computes a power of the normalized value `υ/√A` in the base
field. This gives a power of the scalar in the same field, and controls the scalar under
embeddings fixing that field, even though those embeddings need not preserve complex norms.

The normalization is that of `New.Parameters.vacuumRoot` in
`grh/src/New/Derivatives/Field/WeilData.lean` of lsernau/grh-lean at `72fead1`.
-/

public section

namespace TauCeti

/-- The principal `f`-th root of the inverse splitting value times the square root of the
idele norm. -/
noncomputable def vacuumRoot (υ : ℂ) (A : ℝ) (f : ℕ) : ℂ :=
  (υ⁻¹ * (Real.sqrt A : ℂ)) ^ ((f : ℂ)⁻¹)

/-- Raising the vacuum scalar to the number of places recovers the inverse normalized
splitting value. -/
@[simp] theorem vacuumRoot_pow {f : ℕ} (hf : f ≠ 0) (υ : ℂ) (A : ℝ) :
    vacuumRoot υ A f ^ f = (υ / (Real.sqrt A : ℂ))⁻¹ := by
  rw [vacuumRoot, Complex.cpow_nat_inv_pow _ hf, inv_div, div_eq_mul_inv, mul_comm]

/-- A power of the normalized splitting value in the base field gives an explicit power
of the vacuum scalar in that field. -/
theorem vacuumRoot_pow_mul_of_normalized_pow_eq {K : Type*} [Field K] [Algebra K ℂ]
    {f n : ℕ} (hf : f ≠ 0) {υ : ℂ} {A : ℝ} {a : K}
    (ha : (υ / (Real.sqrt A : ℂ)) ^ n = algebraMap K ℂ a) :
    vacuumRoot υ A f ^ (f * n) = algebraMap K ℂ a⁻¹ := by
  rw [pow_mul, vacuumRoot_pow hf, inv_pow, ha, map_inv₀]

/-- Under an embedding into any normed field over the base field, the `f * n`-th power of the
norm of the vacuum scalar is the reciprocal of the norm of the reciprocity value. This also
applies to embeddings into nonarchimedean fields. -/
theorem _root_.AlgHom.norm_vacuumRoot_pow_mul {K L : Type*} [Field K] [Algebra K ℂ]
    [NormedDivisionRing L] [Algebra K L] (σ : ℂ →ₐ[K] L) {f n : ℕ} (hf : f ≠ 0)
    {υ : ℂ} {A : ℝ} {a : K} (ha : (υ / (Real.sqrt A : ℂ)) ^ n = algebraMap K ℂ a) :
    ‖σ (vacuumRoot υ A f)‖ ^ (f * n) = ‖algebraMap K L a‖⁻¹ := by
  rw [← norm_pow, ← map_pow, vacuumRoot_pow_mul_of_normalized_pow_eq hf ha,
    AlgHom.commutes, map_inv₀, norm_inv]

/-- For a unitary splitting value, the squared norm of every conjugate over the base field is
`R` when the idele norm is `R ^ f`. For a cyclotomic extension of an imaginary quadratic field,
`R` is the root discriminant divided by the square root of the quadratic discriminant. -/
theorem _root_.AlgHom.norm_sq_vacuumRoot {K : Type*} [Field K] [Algebra K ℂ]
    (σ : ℂ →ₐ[K] ℂ) {f n : ℕ} (hf : f ≠ 0) (hn : n ≠ 0) {υ : ℂ} (hυ : ‖υ‖ = 1)
    {R : ℝ} (hR : 0 ≤ R) {a : K}
    (ha : (υ / (Real.sqrt (R ^ f) : ℂ)) ^ n = algebraMap K ℂ a) :
    ‖σ (vacuumRoot υ (R ^ f) f)‖ ^ 2 = R := by
  have hfix : ‖σ (vacuumRoot υ (R ^ f) f)‖ = ‖vacuumRoot υ (R ^ f) f‖ := by
    apply (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) (mul_ne_zero hf hn)).1
    rw [σ.norm_vacuumRoot_pow_mul hf ha,
      ← (AlgHom.id K ℂ).norm_vacuumRoot_pow_mul hf ha, AlgHom.id_apply]
  rw [hfix]
  apply (pow_left_inj₀ (sq_nonneg _) hR hf).1
  rw [pow_right_comm, ← norm_pow, vacuumRoot_pow hf, inv_div, norm_div,
    hυ, div_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (pow_nonneg hR _)]

end TauCeti
