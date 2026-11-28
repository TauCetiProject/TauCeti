/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.RingTheory.Trace.Basic
import Mathlib.Algebra.Field.GeomSum

/-!
# Tight frames from powers of a root of unity

The powers of a cyclotomic generator, read through the complex embeddings over a fixed
base field, form a tight frame. Repeating the powers repeats the frame bound. In particular,
repeating them `n` times and dividing by `n` gives a resolution of the identity. This is the
normalization used to pull back the Hermitian forms of theta functions along the frame.

The cyclotomic frame is the one in `New.Parameters.isTightFrame_pow` of lsernau/grh-lean
(`grh/src/New/Derivatives/Vacuum/TightFrames.lean`, commit `72fead1`).
-/

open Matrix
open scoped ComplexConjugate

public section

namespace PowerBasis

variable {K E : Type*} [CommRing K] [Algebra K ℂ] {n : ℕ}

open Classical in
/-- If a power basis generator is an `n`-th root of unity, its first `n` powers
satisfy coordinate orthogonality under the complex embeddings. -/
theorem sum_conj_mul_apply_gen_pow [CommRing E] [Algebra K E] (pb : PowerBasis K E)
    (hζ : pb.gen ^ n = 1) (σ τ : E →ₐ[K] ℂ) :
    ∑ i : Fin n, conj (σ (pb.gen ^ (i : ℕ))) * τ (pb.gen ^ (i : ℕ)) =
      if σ = τ then (n : ℂ) else 0 := by
  by_cases hn : n = 0
  · subst n
    split_ifs <;> simp
  have hσ : (σ pb.gen) ^ n = 1 := by rw [← map_pow, hζ, map_one]
  have hσ₀ : σ pb.gen ≠ 0 := by
    intro h
    simp [h, zero_pow hn] at hσ
  have hc : conj (σ pb.gen) = (σ pb.gen)⁻¹ :=
    (Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one hσ hn)).symm
  simp only [map_pow, ← mul_pow, hc]
  by_cases h : σ = τ
  · subst τ
    simp [hσ₀]
  · have hratio : (σ pb.gen)⁻¹ * τ pb.gen ≠ 1 := by
      intro he
      apply h (pb.algHom_ext ?_)
      calc
        σ pb.gen = σ pb.gen * ((σ pb.gen)⁻¹ * τ pb.gen) := by rw [he, mul_one]
        _ = τ pb.gen := by rw [← mul_assoc, mul_inv_cancel₀ hσ₀, one_mul]
    rw [ite_eq_right h, Fin.sum_univ_eq_sum_range, geom_sum_eq hratio, mul_pow,
      inv_pow, hσ, ← map_pow, hζ, map_one]
    simp

open Classical in
/-- The frame operator of the first `n` powers of an `n`-th root of unity generating a
power basis, each repeated `r` times, is `rn` times the identity. -/
theorem conjTranspose_mul_self_embeddingsMatrix_repeat_pow [CommRing E] [Algebra K E]
    (pb : PowerBasis K E) (hζ : pb.gen ^ n = 1) (r : ℕ) :
    let A := Algebra.embeddingsMatrix K ℂ (fun i : Fin r × Fin n ↦ pb.gen ^ (i.2 : ℕ))
    Aᴴ * A = (r * n : ℂ) • (1 : Matrix (E →ₐ[K] ℂ) (E →ₐ[K] ℂ) ℂ) := by
  dsimp only
  ext σ τ
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Algebra.embeddingsMatrix_apply,
    Complex.star_def, Fintype.sum_prod_type, pb.sum_conj_mul_apply_gen_pow hζ,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp [nsmul_eq_mul]

open Classical in
/-- Taking `n` copies of each power divided by `n` gives the identity frame operator. -/
theorem conjTranspose_mul_self_embeddingsMatrix_repeat_pow_div [Field E] [Algebra K E]
    (pb : PowerBasis K E) [NeZero n] (hζ : pb.gen ^ n = 1) :
    let A := Algebra.embeddingsMatrix K ℂ (fun i : Fin n × Fin n ↦ pb.gen ^ (i.2 : ℕ) / (n : E))
    Aᴴ * A = 1 := by
  let B := Algebra.embeddingsMatrix K ℂ (fun i : Fin n × Fin n ↦ pb.gen ^ (i.2 : ℕ))
  have hA : Algebra.embeddingsMatrix K ℂ (fun i : Fin n × Fin n ↦ pb.gen ^ (i.2 : ℕ) / (n : E))
      = (n : ℂ)⁻¹ • B := by
    ext i σ
    simp [B, div_eq_inv_mul]
  have hB : Bᴴ * B = (n * n : ℂ) • (1 : Matrix (E →ₐ[K] ℂ) (E →ₐ[K] ℂ) ℂ) :=
    pb.conjTranspose_mul_self_embeddingsMatrix_repeat_pow hζ n
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  dsimp only
  rw [hA, Matrix.conjTranspose_smul, star_inv₀, star_natCast, Matrix.smul_mul, Matrix.mul_smul, hB,
    smul_smul, smul_smul]
  have hc : (n : ℂ)⁻¹ * (n : ℂ)⁻¹ * ((n : ℂ) * n) = 1 := by field_simp
  rw [hc, one_smul]

end PowerBasis
