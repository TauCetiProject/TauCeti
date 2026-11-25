/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings

/-!
# Values of nonreal complex embeddings

A complex embedding `φ : K →+* ℂ` of a field that is not real
(`NumberField.ComplexEmbedding.IsReal`) takes a value whose square has negative real part. A real
embedding has no such value, since then every `φ β` is real.

## Main results

* `TauCeti.NumberField.exists_re_sq_neg_of_not_isReal`: a complex embedding that is not real takes
  a value whose square has negative real part.
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

end TauCeti.NumberField
