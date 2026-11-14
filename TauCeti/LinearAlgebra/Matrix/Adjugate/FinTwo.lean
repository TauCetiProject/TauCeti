/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import TauCeti.LinearAlgebra.Matrix.Adjugate.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basis

/-!
# Adjugation of two-by-two matrices

The adjugate of a two-by-two matrix is linear over any commutative ring, including in
characteristic two. It is the unique function reversing products for which every matrix plus its
image is scalar; linearity is not needed for this characterization. These facts identify Clifford
reversal with adjugation in the two-by-two matrix models of Spin(3) and Spin(4).
The product characterization also identifies adjugation in each factor of `M₂ × M₂`.

For complex matrices, composing adjugation with conjugate transpose gives a real-algebra
endomorphism. This packages the multiplicative map used by real low-rank matrix models.

When `A * A = 1` and `det A = 1`, adjugation fixes `A`, so `2 • A = trace A • 1`; over a domain
away from characteristic two, every `2 × 2` involution of determinant one is therefore `±1`.
-/

public section

namespace Matrix

variable {K : Type*} [CommRing K]

/-- The adjugate of a two-by-two matrix is its trace times the identity minus itself. -/
@[simp]
theorem adjugate_fin_two_eq_trace_smul_one_sub (A : Matrix (Fin 2) (Fin 2) K) :
    adjugate A = trace A • 1 - A := by
  rw [adjugate_fin_two, trace_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The adjugate as a linear map on `2 × 2` matrices over a commutative ring. -/
noncomputable def adjugateFinTwoLinearMap :
    Matrix (Fin 2) (Fin 2) K →ₗ[K] Matrix (Fin 2) (Fin 2) K :=
  (traceLinearMap (Fin 2) K K).smulRight (1 : Matrix (Fin 2) (Fin 2) K) -
    LinearMap.id

/-- Applying `adjugateFinTwoLinearMap` computes the ordinary matrix adjugate. -/
@[simp] theorem adjugateFinTwoLinearMap_apply (A : Matrix (Fin 2) (Fin 2) K) :
    adjugateFinTwoLinearMap A = adjugate A := by
  simp [adjugateFinTwoLinearMap, adjugate_fin_two_eq_trace_smul_one_sub]

/-- Adjugation followed by conjugate transpose, as a real-algebra endomorphism of complex
`2 × 2` matrices. -/
noncomputable def starAdjugateFinTwoAlgHom :
    Matrix (Fin 2) (Fin 2) ℂ →ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun A := star (adjugate A)
  map_zero' := by
    rw [← adjugateFinTwoLinearMap_apply, map_zero, star_zero]
  map_add' A B := by
    rw [← adjugateFinTwoLinearMap_apply, map_add,
      adjugateFinTwoLinearMap_apply, adjugateFinTwoLinearMap_apply, star_add]
  map_one' := by simp
  map_mul' A B := by simp [adjugate_mul_distrib, star_mul]
  commutes' r := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Algebra.algebraMap_eq_smul_one] <;> ring

/-- Applying `starAdjugateFinTwoAlgHom` computes the conjugate transpose of the adjugate. -/
theorem starAdjugateFinTwoAlgHom_apply (A : Matrix (Fin 2) (Fin 2) ℂ) :
    starAdjugateFinTwoAlgHom A = star (adjugate A) := by rfl

/-- An anti-multiplicative function with scalar translates sends an off-diagonal unit
to its negative. -/
private theorem map_single_eq_neg_of_ne {R : Type*} [NonAssocRing R]
    (f : Matrix (Fin 2) (Fin 2) R → Matrix (Fin 2) (Fin 2) R)
    (hmul : ∀ A B, f (A * B) = f B * f A)
    (hscalar : ∀ A, ∃ r : R, A + f A = r • 1)
    (i j : Fin 2) (hij : i ≠ j) :
    f (single i j 1) = -(single i j 1) := by
  obtain ⟨r, hr⟩ := hscalar (single i j 1)
  obtain ⟨s, hs⟩ := hscalar (single j i 1)
  obtain ⟨t, ht⟩ := hscalar (single i i 1)
  have hf := eq_sub_of_add_eq' hr
  have hg := eq_sub_of_add_eq' hs
  have hd := eq_sub_of_add_eq' ht
  have hp := hmul (single i j 1) (single j i 1)
  simp only [single_mul_single_same, mul_one] at hp
  rw [hf, hg, hd] at hp
  have hr0 : r = 0 := by
    have h := congrArg (fun A => A j i) hp
    simpa [sub_mul, mul_sub, smul_one_eq_diagonal, hij, Ne.symm hij] using h
  simp [hf, hr0, smul_one_eq_diagonal]

/-- An anti-multiplicative function for which every matrix plus its image is scalar
is adjugation. No additivity or homogeneity assumption is needed. -/
theorem eq_adjugate_of_antimultiplicative_of_exists_add_eq_smul_one
    (f : Matrix (Fin 2) (Fin 2) K → Matrix (Fin 2) (Fin 2) K)
    (hmul : ∀ A B, f (A * B) = f B * f A)
    (hscalar : ∀ A, ∃ r : K, A + f A = r • 1)
    (A : Matrix (Fin 2) (Fin 2) K) : f A = adjugate A := by
  obtain ⟨r, hr⟩ := hscalar A
  have hf := eq_sub_of_add_eq' hr
  obtain ⟨s, hs⟩ := hscalar (A * single 0 1 1)
  have hp := hmul A (single 0 1 1)
  rw [map_single_eq_neg_of_ne f hmul hscalar 0 1 (by decide),
    eq_sub_of_add_eq' hs, hf] at hp
  have h : -A 0 0 = -r + A 1 1 := by
    simpa [neg_mul, mul_sub] using congrArg (fun B => B 0 1) hp
  have hr : r = trace A := by
    rw [trace_fin_two]
    apply neg_injective
    simpa [neg_add, sub_eq_add_neg, add_assoc, add_comm] using
      (congrArg (· - A 1 1) h).symm
  rw [hf, hr, adjugate_fin_two_eq_trace_smul_one_sub]

/-- An additive anti-multiplicative map on a product of two-by-two matrix algebras is
coordinatewise adjugation if each component of every element plus its image is scalar. -/
theorem eq_adjugate_prod_of_antimultiplicative_of_exists_add_eq_smul_one
    (f : (Matrix (Fin 2) (Fin 2) K × Matrix (Fin 2) (Fin 2) K) →+
      Matrix (Fin 2) (Fin 2) K × Matrix (Fin 2) (Fin 2) K)
    (hmul : ∀ A B, f (A * B) = f B * f A)
    (hscalar : ∀ A, ∃ r s : K, A + f A = (r • 1, s • 1))
    (A : Matrix (Fin 2) (Fin 2) K × Matrix (Fin 2) (Fin 2) K) :
    f A = (adjugate A.1, adjugate A.2) := by
  have hfirst (B : Matrix (Fin 2) (Fin 2) K) : (f (B, 0)).1 = adjugate B := by
    apply eq_adjugate_of_antimultiplicative_of_exists_add_eq_smul_one
      (fun C => (f (C, 0)).1)
    · intro C D
      simpa only [Prod.mk_mul_mk, zero_mul, Prod.fst_mul] using
        congrArg Prod.fst (hmul (C, 0) (D, 0))
    · intro C
      obtain ⟨r, s, h⟩ := hscalar (C, 0)
      exact ⟨r, congrArg Prod.fst h⟩
  have hsecond (B : Matrix (Fin 2) (Fin 2) K) : (f (0, B)).2 = adjugate B := by
    apply eq_adjugate_of_antimultiplicative_of_exists_add_eq_smul_one
      (fun C => (f (0, C)).2)
    · intro C D
      simpa only [Prod.mk_mul_mk, zero_mul, Prod.snd_mul] using
        congrArg Prod.snd (hmul (0, C) (0, D))
    · intro C
      obtain ⟨r, s, h⟩ := hscalar (0, C)
      exact ⟨s, congrArg Prod.snd h⟩
  -- The orthogonal factor identities force the mixed components to vanish.
  have hzero1 (B : Matrix (Fin 2) (Fin 2) K) : (f (0, B)).1 = 0 := by
    have h := congrArg Prod.fst (hmul (1, 0) (0, B))
    simpa [Prod.mk_mul_mk, ← Prod.zero_eq_mk, hfirst] using h.symm
  have hzero2 (B : Matrix (Fin 2) (Fin 2) K) : (f (B, 0)).2 = 0 := by
    have h := congrArg Prod.snd (hmul (0, 1) (B, 0))
    simpa [Prod.mk_mul_mk, ← Prod.zero_eq_mk, hsecond] using h.symm
  have h := f.map_add (A.1, 0) (0, A.2)
  simp only [Prod.mk_add_mk, add_zero, zero_add, Prod.mk.eta] at h
  rw [h]
  exact Prod.ext (by simp [hfirst, hzero1]) (by simp [hsecond, hzero2])

/-- For a `2 × 2` matrix `A` with `A * A = 1` and `det A = 1`, twice `A` is `trace A` times the
identity: its inverse `A` equals its adjugate `trace A • 1 - A`. -/
theorem two_smul_eq_trace_smul_one_of_mul_self_eq_one_of_det_eq_one
    {A : Matrix (Fin 2) (Fin 2) K} (hA : A * A = 1) (hdet : A.det = 1) :
    (2 : K) • A = A.trace • 1 := by
  have hadj : adjugate A = A := by
    rw [adjugate_eq_det_smul_of_mul_eq_one hA, hdet, one_smul]
  rw [adjugate_fin_two_eq_trace_smul_one_sub, sub_eq_iff_eq_add] at hadj
  simpa [two_smul] using hadj.symm

/-- **Every `2 × 2` involution of determinant one over a domain away from characteristic two is
`1` or `-1`.** Both hypotheses on `K` are sharp: over `ℚ × ℚ` the scalar matrix `(1, -1) • 1` has
square `1` and determinant `1` without being `±1`, and over `𝔽₂` the transvection `!![1, 1; 0, 1]`
has square `1` and determinant `1` without being scalar. -/
theorem eq_one_or_eq_neg_one_of_mul_self_eq_one_of_det_eq_one [NoZeroDivisors K]
    (h2 : (2 : K) ≠ 0) {A : Matrix (Fin 2) (Fin 2) K} (hA : A * A = 1) (hdet : A.det = 1) :
    A = 1 ∨ A = -1 := by
  have h2A := two_smul_eq_trace_smul_one_of_mul_self_eq_one_of_det_eq_one hA hdet
  -- Squaring `2 • A = trace A • 1` and reading the `(0, 0)` entry gives `trace A ^ 2 = 4`.
  have hsq : ((2 : K) • A) * ((2 : K) • A) = (A.trace • (1 : Matrix (Fin 2) (Fin 2) K)) *
      (A.trace • 1) := congrArg (fun M => M * M) h2A
  simp only [smul_mul_smul_comm, hA, one_mul] at hsq
  have htr : (2 : K) * 2 = A.trace * A.trace := by
    simpa [smul_smul] using congrFun (congrFun hsq 0) 0
  have htr' : (A.trace - 2) * (A.trace + 2) = 0 := by
    calc (A.trace - 2) * (A.trace + 2) = A.trace * A.trace - 2 * 2 := by ring
      _ = 0 := sub_eq_zero.mpr htr.symm
  rcases mul_eq_zero.mp htr' with h | h
  · left
    rw [sub_eq_zero.mp h] at h2A
    ext i j
    exact mul_left_cancel₀ h2 (by simpa [smul_eq_mul] using congrFun (congrFun h2A i) j)
  · right
    rw [eq_neg_of_add_eq_zero_left h, neg_smul, ← smul_neg] at h2A
    ext i j
    exact mul_left_cancel₀ h2 (by simpa [smul_eq_mul] using congrFun (congrFun h2A i) j)

/-- **Power form of `Matrix.eq_one_or_eq_neg_one_of_mul_self_eq_one_of_det_eq_one`.** -/
theorem eq_one_or_eq_neg_one_of_sq_eq_one_of_det_eq_one [NoZeroDivisors K]
    (h2 : (2 : K) ≠ 0) {A : Matrix (Fin 2) (Fin 2) K} (hA : A ^ 2 = 1) (hdet : A.det = 1) :
    A = 1 ∨ A = -1 :=
  eq_one_or_eq_neg_one_of_mul_self_eq_one_of_det_eq_one h2 (by rwa [← sq]) hdet

end Matrix
