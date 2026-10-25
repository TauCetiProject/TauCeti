/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Algebra.QuadraticAlgebra.AlgEquiv
public import TauCeti.Algebra.QuadraticAlgebra.Star
public import TauCeti.NumberTheory.NumberField.Quadratic.InfinitePlace

/-!
# The complex embeddings of an imaginary quadratic field

For a rational `a ≤ 0`, the model `QuadraticAlgebra ℚ a 0` of `ℚ(√a)` has a distinguished
complex embedding `QuadraticAlgebra.complexEmbedding`, sending the generator `ω` to `√(-a) · i`,
the square root of `a` with nonnegative imaginary part. Every complex embedding of the model is
this one or its complex conjugate, and complex conjugation of the distinguished embedding is
precomposition with the quadratic involution `QuadraticAlgebra.starAe`. For a nonsquare `a < 0`
the model is an imaginary quadratic field: the two embeddings are distinct and are told apart by
the sign of the imaginary part of the image of `ω`, so the field has a single infinite place, which
is complex, and its signature is `(0, 1)`.

The distinguished embedding fixes the orientation convention for imaginary quadratic fields: the
chosen square root of the radicand lies in the upper half-plane.

## Main definitions and results

* `QuadraticAlgebra.complexEmbedding`: the embedding `ω ↦ √(-a) · i`.
* `QuadraticAlgebra.complexEmbedding_star`: it intertwines `star` with complex conjugation.
* `QuadraticAlgebra.algHom_eq_or_eq_comp_starAe`: every `ℚ`-algebra map to `ℂ` is the
  distinguished embedding or its precomposition with `starAe`.
* `QuadraticAlgebra.complexEmbedding_comp_smulOmegaEquiv_of_pos`,
  `QuadraticAlgebra.complexEmbedding_comp_smulOmegaEquiv_of_neg`: along the rescaling isomorphism
  `QuadraticAlgebra.smulOmegaEquiv u h : ℚ(√d) ≃ₐ[ℚ] ℚ(√e)` with `d = u² e`, the distinguished
  embedding of `ℚ(√e)` pulls back to that of `ℚ(√d)` when `u > 0` and to its complex conjugate
  when `u < 0`.
* `QuadraticAlgebra.ringHom_eq_complexEmbedding_iff`: for `a < 0`, a ring homomorphism to `ℂ` is
  the distinguished embedding exactly when it sends `ω` into the upper half-plane.
* `QuadraticAlgebra.ringHom_eq_or_eq_conjugate`: the two complex embeddings of the field model.
* `QuadraticAlgebra.isConj_complexEmbedding`: complex conjugation induces `starAe`.
* `QuadraticAlgebra.not_isReal_complexEmbedding`: for `a < 0` the distinguished embedding is
  not real.
* `QuadraticAlgebra.eq_mk_complexEmbedding`: the unique infinite place.
* `QuadraticAlgebra.nrComplexPlaces_eq_one`: there is exactly one complex place; together with
  `NumberField.IsTotallyComplex.nrRealPlaces_eq_zero` (via `QuadraticAlgebra.isTotallyComplex_iff`)
  the signature is `(0, 1)`.
-/

public section

open Complex ComplexConjugate NumberField NumberField.InfinitePlace

namespace QuadraticAlgebra

variable {a : ℚ}

/-- For `a ≤ 0`, the complex number `√(-a) · i` squares to `a`. -/
private theorem sqrt_mul_I_mul_self (ha : a ≤ 0) :
    ((√(-(a : ℝ)) : ℂ) * I) * ((√(-(a : ℝ)) : ℂ) * I) = a := by
  have h : ((√(-(a : ℝ)) : ℂ)) * (√(-(a : ℝ)) : ℂ) = -(a : ℂ) := by
    rw [← ofReal_mul, Real.mul_self_sqrt (by simpa using ha)]
    push_cast
    ring
  linear_combination (I * I) * h - I_mul_I * (a : ℂ)

/-- **The distinguished complex embedding of `ℚ(√a)`** for `a ≤ 0`: the `ℚ`-algebra map
`QuadraticAlgebra ℚ a 0 →ₐ[ℚ] ℂ` sending `ω` to `√(-a) · i`, the square root of `a` with
nonnegative imaginary part. -/
noncomputable def complexEmbedding (ha : a ≤ 0) : QuadraticAlgebra ℚ a 0 →ₐ[ℚ] ℂ :=
  lift ⟨(√(-(a : ℝ)) : ℂ) * I, by simpa [Rat.smul_def] using sqrt_mul_I_mul_self ha⟩

@[simp] theorem complexEmbedding_omega (ha : a ≤ 0) :
    complexEmbedding ha ω = (√(-(a : ℝ)) : ℂ) * I := by
  simp [complexEmbedding]

theorem complexEmbedding_apply (ha : a ≤ 0) (z : QuadraticAlgebra ℚ a 0) :
    complexEmbedding ha z = (z.re : ℂ) + (z.im : ℂ) * ((√(-(a : ℝ)) : ℂ) * I) := by
  simp [complexEmbedding, Rat.smul_def]

@[simp] theorem re_complexEmbedding (ha : a ≤ 0) (z : QuadraticAlgebra ℚ a 0) :
    (complexEmbedding ha z).re = z.re := by
  simp [complexEmbedding_apply]

@[simp] theorem im_complexEmbedding (ha : a ≤ 0) (z : QuadraticAlgebra ℚ a 0) :
    (complexEmbedding ha z).im = z.im * √(-(a : ℝ)) := by
  simp [complexEmbedding_apply]

/-- The distinguished embedding intertwines the quadratic involution with complex conjugation. -/
@[simp] theorem complexEmbedding_star (ha : a ≤ 0) (z : QuadraticAlgebra ℚ a 0) :
    complexEmbedding ha (star z) = conj (complexEmbedding ha z) := by
  apply Complex.ext <;> simp

/-- **The two complex embeddings of `ℚ(√a)`.** For `a ≤ 0`, every `ℚ`-algebra map
`QuadraticAlgebra ℚ a 0 → ℂ` is the distinguished embedding or its precomposition with the
quadratic involution, since it sends `ω` to a square root of `a`. -/
theorem algHom_eq_or_eq_comp_starAe (ha : a ≤ 0) (φ : QuadraticAlgebra ℚ a 0 →ₐ[ℚ] ℂ) :
    φ = complexEmbedding ha ∨ φ = (complexEmbedding ha).comp (starAe : _ ≃ₐ[ℚ] _).toAlgHom := by
  have hφ : φ ω * φ ω = a := by
    rw [← map_mul]
    simp [omega_mul_omega_eq_algebraMap]
  rw [← sqrt_mul_I_mul_self ha] at hφ
  rcases mul_self_eq_mul_self_iff.mp hφ with h | h
  · exact Or.inl (algHom_ext (by simp [h]))
  · exact Or.inr (algHom_ext (by simp [h]))

/-- **The upper half-plane picks out the distinguished embedding.** For `a < 0`, a ring
homomorphism `QuadraticAlgebra ℚ a 0 →+* ℂ` is the distinguished embedding exactly when it sends
`ω` to a complex number with positive imaginary part. -/
theorem ringHom_eq_complexEmbedding_iff (ha : a < 0) (φ : QuadraticAlgebra ℚ a 0 →+* ℂ) :
    φ = (complexEmbedding ha.le : QuadraticAlgebra ℚ a 0 →+* ℂ) ↔ 0 < (φ ω).im := by
  have hpos : 0 < √(-(a : ℝ)) := Real.sqrt_pos.mpr (by simpa using ha)
  refine ⟨fun h => by simpa [h] using hpos, fun h => ?_⟩
  rcases algHom_eq_or_eq_comp_starAe ha.le φ.toRatAlgHom with h' | h'
  · exact RingHom.ext fun z => by simpa using AlgHom.congr_fun h' z
  · have him : (φ ω).im = -√(-(a : ℝ)) := by
      simpa using congrArg Complex.im (AlgHom.congr_fun h' ω)
    linarith

section smulOmegaEquiv

variable {d e : ℚ}

/-- The square root `√(-(u² e))` is `|u| √(-e)`. -/
private theorem sqrt_neg_sq_mul (u e : ℝ) : √(-(u ^ 2 * e)) = |u| * √(-e) := by
  rw [← mul_neg, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

/-- **Naturality of the distinguished embedding, positive scalar.** If `d = u² e` with `u > 0`,
the distinguished embedding of `ℚ(√e)` composed with the rescaling isomorphism
`smulOmegaEquiv u h : ℚ(√d) ≃ₐ[ℚ] ℚ(√e)` is the distinguished embedding of `ℚ(√d)`. -/
theorem complexEmbedding_comp_smulOmegaEquiv_of_pos (hd : d ≤ 0) (he : e ≤ 0) (u : ℚˣ)
    (h : d = u ^ 2 * e) (hu : 0 < (u : ℚ)) :
    (complexEmbedding he).comp (smulOmegaEquiv u h).toAlgHom = complexEmbedding hd := by
  refine algHom_ext ?_
  subst h
  have hu' : (0 : ℝ) < u := Rat.cast_pos.mpr hu
  apply Complex.ext <;> simp [Rat.smul_def, sqrt_neg_sq_mul, abs_of_pos hu']

/-- **Naturality of the distinguished embedding, negative scalar.** If `d = u² e` with `u < 0`,
the distinguished embedding of `ℚ(√e)` composed with the rescaling isomorphism
`smulOmegaEquiv u h : ℚ(√d) ≃ₐ[ℚ] ℚ(√e)` is the complex conjugate of the distinguished embedding
of `ℚ(√d)`, that is, its precomposition with the quadratic involution. -/
theorem complexEmbedding_comp_smulOmegaEquiv_of_neg (hd : d ≤ 0) (he : e ≤ 0) (u : ℚˣ)
    (h : d = u ^ 2 * e) (hu : (u : ℚ) < 0) :
    (complexEmbedding he).comp (smulOmegaEquiv u h).toAlgHom =
      (complexEmbedding hd).comp (starAe : _ ≃ₐ[ℚ] _).toAlgHom := by
  refine algHom_ext ?_
  subst h
  have hu' : (u : ℝ) < 0 := Rat.cast_lt_zero.mpr hu
  apply Complex.ext <;> simp [Rat.smul_def, sqrt_neg_sq_mul, abs_of_neg hu']

end smulOmegaEquiv

section Field

variable [Fact (¬ IsSquare a)]

/-- **The two complex embeddings of an imaginary quadratic field.** For a nonsquare `a ≤ 0`, every
complex embedding of the field `QuadraticAlgebra ℚ a 0` is the distinguished embedding or its
complex conjugate. -/
theorem ringHom_eq_or_eq_conjugate (ha : a ≤ 0) (φ : QuadraticAlgebra ℚ a 0 →+* ℂ) :
    φ = (complexEmbedding ha : QuadraticAlgebra ℚ a 0 →+* ℂ) ∨
      φ = ComplexEmbedding.conjugate (complexEmbedding ha : QuadraticAlgebra ℚ a 0 →+* ℂ) := by
  rcases algHom_eq_or_eq_comp_starAe ha φ.toRatAlgHom with h | h
  · exact Or.inl (RingHom.ext fun z => by simpa using AlgHom.congr_fun h z)
  · refine Or.inr (RingHom.ext fun z => ?_)
    simpa [ComplexEmbedding.conjugate_coe_eq] using AlgHom.congr_fun h z

/-- **Complex conjugation induces the quadratic involution.** Under the distinguished embedding,
complex conjugation restricts to `starAe`, the nontrivial automorphism of `QuadraticAlgebra ℚ a 0`
over `ℚ`. -/
theorem isConj_complexEmbedding (ha : a ≤ 0) :
    ComplexEmbedding.IsConj (complexEmbedding ha : QuadraticAlgebra ℚ a 0 →+* ℂ) starAe :=
  RingHom.ext fun z => by simp [ComplexEmbedding.conjugate_coe_eq]

/-- For a negative nonsquare `a`, the distinguished embedding is not real: the field
`QuadraticAlgebra ℚ a 0` is totally complex. -/
theorem not_isReal_complexEmbedding (ha : a < 0) :
    ¬ ComplexEmbedding.IsReal (complexEmbedding ha.le : QuadraticAlgebra ℚ a 0 →+* ℂ) :=
  have := isTotallyComplex_iff.mpr ha
  isComplex_mk_iff.mp (IsTotallyComplex.isComplex _)

/-- **An imaginary quadratic field has a single infinite place**: every infinite place of
`QuadraticAlgebra ℚ a 0`, for a nonsquare `a ≤ 0`, is the one defined by the distinguished
embedding. -/
theorem eq_mk_complexEmbedding (ha : a ≤ 0) (w : InfinitePlace (QuadraticAlgebra ℚ a 0)) :
    w = InfinitePlace.mk (complexEmbedding ha : QuadraticAlgebra ℚ a 0 →+* ℂ) := by
  rw [← mk_embedding w]
  rcases ringHom_eq_or_eq_conjugate ha w.embedding with h | h
  · rw [h]
  · rw [h, mk_conjugate_eq]

/-- An imaginary quadratic field has exactly one complex place, so its signature is `(0, 1)`. -/
theorem nrComplexPlaces_eq_one (ha : a < 0) : nrComplexPlaces (QuadraticAlgebra ℚ a 0) = 1 :=
  have := isTotallyComplex_iff.mpr ha
  nrComplexPlaces_eq_one_of_finrank_eq_two (finrank_eq_two a 0)

end Field

end QuadraticAlgebra
