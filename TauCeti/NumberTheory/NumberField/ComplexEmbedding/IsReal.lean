/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import TauCeti.LinearAlgebra.Complex.Determinant

/-!
# Values of nonreal complex embeddings

A complex embedding `φ : K →+* ℂ` of a field that is not real
(`NumberField.ComplexEmbedding.IsReal`) takes a value whose square has negative real part. A real
embedding has no such value, since then every `φ β` is real. For the same reason the image of a
`ℚ`-basis `v₀, v₁` of `K` under a nonreal embedding is an `ℝ`-basis of `ℂ`: otherwise all of `φ(K)`,
which contains `1`, would lie on one real line through `0`. This is how a fractional ideal of an
imaginary quadratic order becomes a lattice in `ℂ`.

## Main results

* `TauCeti.NumberField.exists_re_sq_neg_of_not_isReal`: a complex embedding that is not real takes
  a value whose square has negative real part.
* `TauCeti.NumberField.linearIndependent_real_of_span_rat_eq_top`: a nonreal embedding sends two
  elements spanning `K` over `ℚ` to two `ℝ`-linearly independent complex numbers.
-/

public section

open NumberField NumberField.ComplexEmbedding

namespace TauCeti.NumberField

variable {K : Type*} [Field K]

/-- A complex embedding that is not real takes a value whose square has negative real part. -/
theorem exists_re_sq_neg_of_not_isReal {φ : K →+* ℂ} (hφ : ¬ ComplexEmbedding.IsReal φ) :
    ∃ β : K, (φ β ^ 2).re < 0 := by
  have : CharZero K := φ.charZero
  obtain ⟨γ, hγ⟩ : ∃ γ, conjugate φ γ ≠ φ γ := by
    by_contra! h
    exact hφ (ComplexEmbedding.isReal_iff.2 (RingHom.ext h))
  have him : 0 < |(φ γ).im| := by
    refine abs_pos.2 fun h => hγ ?_
    rw [conjugate_coe_eq, Complex.conj_eq_iff_im]
    exact h
  have hbtwn : (φ γ).re - |(φ γ).im| < (φ γ).re + |(φ γ).im| := by linarith
  obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn hbtwn
  refine ⟨γ - q, ?_⟩
  have hlt : |(φ γ).re - q| < |(φ γ).im| := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
  have := sq_lt_sq.2 hlt
  simp only [map_sub, map_ratCast, sq, Complex.mul_re, Complex.sub_re, Complex.ratCast_re,
    Complex.sub_im, Complex.ratCast_im, sub_zero]
  nlinarith [sq_abs ((φ γ).re - q), sq_abs (φ γ).im]

/-- **A `ℚ`-basis of `K` gives an `ℝ`-basis of `ℂ`.** If `σ` is not real and `v₀, v₁` span `K`
over `ℚ`, then `σ v₀` and `σ v₁` are linearly independent over `ℝ`. -/
theorem linearIndependent_real_of_span_rat_eq_top [CharZero K] {σ : K →+* ℂ}
    (hσ : ¬ ComplexEmbedding.IsReal σ) {v₀ v₁ : K} (hv : Submodule.span ℚ {v₀, v₁} = ⊤) :
    LinearIndependent ℝ ![σ v₀, σ v₁] := by
  have hcoord : ∀ x : K, ∃ p q : ℚ, (p : ℂ) * σ v₀ + q * σ v₁ = σ x := by
    intro x
    obtain ⟨p, q, h⟩ := Submodule.mem_span_pair.mp (hv ▸ Submodule.mem_top : x ∈ _)
    refine ⟨p, q, ?_⟩
    rw [← h, Rat.smul_def, Rat.smul_def, map_add, map_mul, map_mul, map_ratCast, map_ratCast]
  refine linearIndependent_pair_iff_im_conj_mul_ne_zero.mpr fun hD ↦ hσ ?_
  -- The real determinant of `σ v₀, σ v₁` vanishes.
  replace hD : (σ v₀).re * (σ v₁).im - (σ v₁).re * (σ v₀).im = 0 := by
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im] at hD
    linear_combination hD
  -- Hence every `σ x` lies on the real line through `σ 1 = 1`.
  obtain ⟨p₁, q₁, h₁⟩ := hcoord 1
  rw [map_one] at h₁
  have h₁re := congrArg Complex.re h₁
  have h₁im := congrArg Complex.im h₁
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ratCast_re,
    Complex.ratCast_im, zero_mul, sub_zero, add_zero, Complex.one_re, Complex.one_im] at h₁re h₁im
  refine ComplexEmbedding.isReal_iff.mpr (RingHom.ext fun x ↦ ?_)
  rw [ComplexEmbedding.conjugate_coe_eq, Complex.conj_eq_iff_im]
  obtain ⟨p, q, hx⟩ := hcoord x
  rw [← hx]
  simp only [Complex.add_im, Complex.mul_im, Complex.ratCast_re, Complex.ratCast_im, zero_mul,
    add_zero]
  linear_combination -((p : ℝ) * (σ v₀).im + q * (σ v₁).im) * h₁re +
    ((p : ℝ) * (σ v₀).re + q * (σ v₁).re) * h₁im + ((q : ℝ) * p₁ - p * q₁) * hD

end TauCeti.NumberField
