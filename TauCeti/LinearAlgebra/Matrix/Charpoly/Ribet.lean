/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TwoSidedIdeal.Basic
public import TauCeti.LinearAlgebra.Matrix.Charpoly.PolynomialExtension

/-!
# Ribet's polynomial

Let `R` be a commutative ring, `L` a commutative `R`-algebra, `Λ` an `R`-algebra and
`ρ : Λ →ₐ[R] Matrix σ σ L` an `R`-algebra homomorphism such that `Λ` is spanned over `R` by
elements `w` for which the characteristic polynomial of `ρ w` has all coefficients in the image of
`R`. Let `𝔞` be a two-sided ideal of `Λ` containing the kernel of `ρ`, `y : N → Λ` a finite family
spanning the left ideal `I`, `ρ₀ ∈ Λ`, and `B` a square matrix over `Λ` whose rows are tied to `y`
modulo `𝔞` and `I ρ₀`: `(B *ᵥ y) i ∈ 𝔞 + I ρ₀` for every `i`.

`AlgHom.exists_ribet_polynomial` produces a polynomial `P ∈ R[X]` whose constant term is the
determinant of the block matrix `(ρ (B i j))_{i,j}` and such that `z * P(ρ₀) ∈ 𝔞` for every
`z ∈ I`; moreover the traces `tr ρ (ρ₁ * P(ρ₀))` lie in the image of `R`, and if `ρ z` is the
scalar `δ ∈ R` for some `z ∈ I`, then `δ * tr ρ (ρ₁ * P(ρ₀))` is the trace of the image of an
element of `𝔞`. This is the polynomial of Ribet's method for constructing congruences between
Galois representations, where `Λ` is a group algebra and `𝔞` an ideal of elements whose traces
lie in a prescribed module.

## Implementation notes

Writing `(B *ᵥ y) i = a i + (B₁ *ᵥ y) i * ρ₀` with `a i ∈ 𝔞`, the matrix `B - X • B₁` over the
polynomial ring `Λ[X]`, with `X` central, kills `y` modulo `𝔞` when `Λ[X]` acts on `Λ` by left
multiplication on the coefficients and right multiplication by `ρ₀` on `X`. Amitsur's theorem
over the base ring `R[X]` (`AlgHom.charpoly_coeff_mem_range_of_span`) and its block form
(`AlgHom.charpoly_comp_map_coeff_mem_range`) show that the block matrix of `B - X • B₁` has
characteristic polynomial over `R[X]`, so the Cayley–Hamilton theorem
(`AlgHom.exists_mul_eq_smul_one_of_charpoly_coeff_mem_range`) gives a matrix `V` over `Λ[X]` and
`P ∈ R[X]`, the determinant of that block matrix, with `V * (B - X • B₁) = P` up to the kernel of
`ρ`. Applied to `y`, this gives `y i * P(ρ₀) ∈ 𝔞`, and at `X = 0` the determinant is that of the
block matrix of `B`.

## References

* K. A. Ribet, *A modular construction of unramified p-extensions of `ℚ(μ_p)`*, Invent. Math.
  **34** (1976), 151–162.
* J. Bellaïche and G. Chenevier, *Families of Galois representations and Selmer groups*,
  Astérisque **324** (2009), Chapter 1.
* S. A. Amitsur, *On the characteristic polynomial of a sum of matrices*, Linear and Multilinear
  Algebra **8** (1980), no. 3, 177–182.

## Provenance

The statement and the route through the polynomial ring `Λ[X]` follow
`New.Selmer.exists_ribet_polynomial` (file `src/New/Congruences/FirstOrder/RibetMethod.lean`) in
grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

open Polynomial Matrix TauCeti

namespace AlgHom

variable {R L Λ σ N : Type*} [CommRing R] [CommRing L] [Algebra R L] [Fintype σ] [DecidableEq σ]
  [Fintype N]

section Ribet

variable [Ring Λ] [Algebra R Λ] [DecidableEq N]

attribute [local instance] Polynomial.algebra

/-- The core of Ribet's polynomial: if `(B *ᵥ y) i - (B₁ *ᵥ y) i * ρ₀ ∈ 𝔞` for every `i`, some
`P ∈ R[X]` has constant term the determinant of the block matrix of `B` and `y i * P(ρ₀) ∈ 𝔞`
for every `i`. -/
private theorem exists_polynomial_of_mulVec_sub_mem (ρ : Λ →ₐ[R] Matrix σ σ L)
    (hρ : ∀ (w : Λ) (k : ℕ), (ρ w).charpoly.coeff k ∈ (algebraMap R L).range)
    (𝔞 : TwoSidedIdeal Λ) (h𝔞 : ∀ w, ρ w = 0 → w ∈ 𝔞) (y : N → Λ) (ρ₀ : Λ)
    (B B₁ : Matrix N N Λ) (hB : ∀ i, (B *ᵥ y) i - (B₁ *ᵥ y) i * ρ₀ ∈ 𝔞) :
    ∃ P : R[X], algebraMap R L (P.eval 0) = (Matrix.comp N N σ σ L (B.map ρ)).det ∧
      ∀ i, y i * aeval ρ₀ P ∈ 𝔞 := by
  let ρX := polynomialExtension ρ
  let BX : Matrix N N Λ[X] := of fun i j ↦ C (B i j) - X * C (B₁ i j)
  let φX : Matrix N N Λ[X] →ₐ[R[X]] Matrix (N × σ) (N × σ) L[X] :=
    (Matrix.compAlgEquiv N σ L[X] R[X]).toAlgHom.comp ρX.mapMatrix
  obtain ⟨V, F, hdet, hVB, -⟩ := exists_mul_eq_smul_one_of_charpoly_coeff_mem_range φX
    (charpoly_comp_map_coeff_mem_range ρX (charpoly_polynomialExtension_coeff_mem_range ρ hρ) BX)
  refine ⟨F, ?_, fun i ↦ ?_⟩
  · -- At `X = 0` the block matrix of `B - X • B₁` is that of `B`.
    have h0 : (evalRingHom 0).mapMatrix (φX BX) = Matrix.comp N N σ σ L (B.map ρ) := by
      ext ⟨i, s⟩ ⟨j, t⟩
      simp [φX, BX, ρX, ← coeff_zero_eq_eval_zero, coeff_polynomialExtension_apply, -map_sub,
        -map_mul]
    rw [← h0, ← RingHom.map_det, hdet, Polynomial.algebraMap_def, coe_mapRingHom, coe_evalRingHom,
      eval_zero_map]
  · -- `V * BX` differs from the scalar `F` by a matrix whose coefficients lie in `ker ρ ⊆ 𝔞`.
    let K := V * BX - algebraMap R[X] (Matrix N N Λ[X]) F
    have hK : ∀ i j k, (K i j).coeff k ∈ 𝔞 := by
      have hφK : φX K = 0 := by
        simp [K, hVB, Algebra.algebraMap_eq_smul_one]
      intro i j k
      refine h𝔞 _ (Matrix.ext fun s t ↦ ?_)
      have := congrArg (fun M : Matrix (N × σ) (N × σ) L[X] ↦ (M (i, s) (j, t)).coeff k) hφK
      simpa [φX, ρX, coeff_polynomialExtension_apply] using this
    have hBX : ∀ i, matrixPolynomialMulRightAction R ρ₀ BX y i ∈ 𝔞 := fun i ↦ by
      convert hB i using 1
      simp [matrixPolynomialMulRightAction_apply, BX, mulVec, dotProduct, Finset.sum_mul, mul_assoc]
    have hVBX : matrixPolynomialMulRightAction R ρ₀ (V * BX) y i ∈ 𝔞 := by
      rw [map_mul, mul_apply_eq_comp, matrixPolynomialMulRightAction_apply]
      exact sum_mem fun j _ ↦ 𝔞.polynomialMulRightAction_mem ρ₀ _ (hBX j)
    have hKy : matrixPolynomialMulRightAction R ρ₀ K y i ∈ 𝔞 := by
      rw [matrixPolynomialMulRightAction_apply]
      exact sum_mem fun j _ ↦ 𝔞.polynomialMulRightAction_mem_of_coeff_mem ρ₀ (hK i j) _
    have hsub : V * BX - K = algebraMap R[X] (Matrix N N Λ[X]) F := sub_sub_cancel _ _
    have h := 𝔞.sub_mem hVBX hKy
    rwa [← Pi.sub_apply, ← LinearMap.sub_apply, ← map_sub, hsub,
      matrixPolynomialMulRightAction_algebraMap] at h

/-- **Ribet's polynomial.** Let `ρ : Λ →ₐ[R] Matrix σ σ L` be an `R`-algebra homomorphism such
that `Λ` is spanned over `R` by elements `w` for which the characteristic polynomial of `ρ w` has
all coefficients in the image of `R`. Let `𝔞` be a two-sided ideal of `Λ` containing the kernel of
`ρ`, `y : N → Λ` with left span `I`, `ρ₀ ∈ Λ`, and `B` a square matrix over `Λ` with
`(B *ᵥ y) i ∈ 𝔞 + I ρ₀` for every `i`. Then some `P ∈ R[X]` satisfies:

* its constant term is the determinant of the block matrix `(ρ (B i j))_{i,j}`;
* `z * P(ρ₀) ∈ 𝔞` for every `z ∈ I`;
* `tr ρ (ρ₁ * P(ρ₀))` lies in the image of `R` for every `ρ₁ ∈ Λ`;
* if `ρ z` is the scalar `δ ∈ R` for some `z ∈ I`, then for every `ρ₁ ∈ Λ`,
  `δ * tr ρ (ρ₁ * P(ρ₀))` is the trace of `ρ a` for some `a ∈ 𝔞`. -/
theorem exists_ribet_polynomial (ρ : Λ →ₐ[R] Matrix σ σ L)
    (hρ : Submodule.span R {w : Λ | ∀ k, (ρ w).charpoly.coeff k ∈ (algebraMap R L).range} = ⊤)
    (𝔞 : TwoSidedIdeal Λ) (h𝔞 : ∀ w, ρ w = 0 → w ∈ 𝔞) (y : N → Λ) (ρ₀ : Λ) (B : Matrix N N Λ)
    (hB : ∀ i, ∃ a ∈ 𝔞, ∃ z ∈ Submodule.span Λ (Set.range y), (B *ᵥ y) i = a + z * ρ₀) :
    ∃ P : R[X], algebraMap R L (P.eval 0) = (Matrix.comp N N σ σ L (B.map ρ)).det ∧
      (∀ z ∈ Submodule.span Λ (Set.range y), z * aeval ρ₀ P ∈ 𝔞) ∧
      (∀ ρ₁ : Λ, (ρ (ρ₁ * aeval ρ₀ P)).trace ∈ (algebraMap R L).range) ∧
      ∀ (ρ₁ : Λ) (δ : R), (∃ z ∈ Submodule.span Λ (Set.range y), ρ z = algebraMap R _ δ) →
        ∃ a ∈ 𝔞, algebraMap R L δ * (ρ (ρ₁ * aeval ρ₀ P)).trace = (ρ a).trace := by
  have hall : ∀ (w : Λ) (k : ℕ), (ρ w).charpoly.coeff k ∈ (algebraMap R L).range :=
    charpoly_coeff_mem_range_of_span ρ hρ fun _ hw ↦ hw
  -- Write `(B *ᵥ y) i = a i + (B₁ *ᵥ y) i * ρ₀` with `a i ∈ 𝔞`.
  choose a ha z hz hBz using hB
  choose B₁ hB₁ using fun i ↦ (Submodule.mem_span_range_iff_exists_fun Λ).1 (hz i)
  obtain ⟨P, hP0, hPy⟩ := exists_polynomial_of_mulVec_sub_mem ρ hall 𝔞 h𝔞 y ρ₀ B (of B₁)
    fun i ↦ by
      have h : (of B₁ *ᵥ y) i = z i := by simp [mulVec, dotProduct, ← hB₁]
      rw [h, hBz, add_sub_cancel_right]
      exact ha i
  have hPI : ∀ z ∈ Submodule.span Λ (Set.range y), z * aeval ρ₀ P ∈ 𝔞 := by
    intro z hz
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun Λ).1 hz
    simpa [Finset.sum_mul, mul_assoc] using sum_mem fun j _ ↦ 𝔞.mul_mem_left (c j) _ (hPy j)
  refine ⟨P, hP0, hPI, fun ρ₁ ↦ ?_, fun ρ₁ δ ⟨z, hzI, hzδ⟩ ↦ ⟨ρ₁ * (z * aeval ρ₀ P),
    𝔞.mul_mem_left _ _ (hPI z hzI), ?_⟩⟩
  · rcases isEmpty_or_nonempty σ with hσ | hσ
    · simp [Matrix.trace]
    · rw [trace_eq_neg_charpoly_coeff]
      exact neg_mem (hall _ _)
  · rw [map_mul, map_mul, map_mul ρ z, hzδ, ← mul_assoc, ← Algebra.commutes, mul_assoc,
      ← Algebra.smul_def δ (ρ ρ₁ * _), trace_smul, Algebra.smul_def]

end Ribet

end AlgHom
