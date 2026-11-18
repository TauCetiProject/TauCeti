/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import TauCeti.RingTheory.Polynomial.HasseWronskian
import Mathlib.Algebra.CharP.Two
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Examples of Hasse Wronskians and their degree and multiplicity estimates

The Hasse Wronskian of the monomials `1, X, …, X^(ℓ - 1)` is the determinant of a unitriangular
matrix, so it is `1`; the degree estimate
`natDegree W(g) + (0 + 1 + ⋯ + (ℓ - 1)) ≤ ∑ⱼ natDegree gⱼ` is then an equality. For
`(1, X, X²)` the classical Wronskian is `0! · 1! · 2! = 2` times it: the normalisation matters.
Further, `W(1, X) = 1`, `W(X, 2X) = 0` and `W(1, 1) = 0`; the last shows that the degree estimate
needs `W(g) ≠ 0`, since `0 + 1 ≤ 0` fails.

For a space `V` of polynomials with a basis `b` of `ℓ` members and a nonzero `f ∈ V` vanishing
to order `μ` at `a`, the Hasse Wronskian `W(b)` vanishes to order at least `μ + 1 - ℓ` at `a` in
characteristic zero. For `ℓ = 1` this is an equality, since `W(b) = b₀` is a nonzero multiple of
`f`. For `V = span (1, X^μ)` with `μ ≥ 1` it is attained: `W(1, X^μ) = μ X^(μ - 1)` vanishes to
order `μ - 1 = (μ + 1) - 2` at zero.

Characteristic zero is needed for the nonvanishing criterion and the numerical bound. Over `𝔽₂`
the polynomials `1` and `X²` are linearly independent, but `W(1, X²) = 0`: the divisibility
`X ∣ W(1, X²)` holds, while the bound `(2 + 1) - 2 = 1` on its root multiplicity at zero fails.
And a commutative ring is too weak for dependence to force vanishing: over `ℤ/4ℤ` the constant
`2` is dependent, since `2 · 2 = 0`, but `W(2) = 2 ≠ 0`; over the characteristic-zero ring `ℚ × ℚ`
the constant `(1, 0)` behaves in the same way.
-/

public section

open Finset Polynomial

namespace TauCeti.HasseWronskianExample

/-- For the monomials `1, X, …, X^(ℓ - 1)` over `ℤ` the degree estimate is the equality
`0 + (0 + 1 + ⋯ + (ℓ - 1)) = 0 + 1 + ⋯ + (ℓ - 1)`. -/
example (ℓ : ℕ) :
    (hasseWronskian fun j : Fin ℓ ↦ (X : ℤ[X]) ^ (j : ℕ)).natDegree + ∑ k : Fin ℓ, (k : ℕ) =
      ∑ j : Fin ℓ, ((X : ℤ[X]) ^ (j : ℕ)).natDegree := by
  simp

/-- The Hasse Wronskian of `(1, X, X²)` over `ℚ` is `1`, the case `m = 3` of
`Polynomial.hasseWronskian_X_pow`. -/
theorem hasseWronskian_one_X_X_sq : hasseWronskian ![(1 : ℚ[X]), X, X ^ 2] = 1 := by
  convert hasseWronskian_X_pow ℚ 3 using 2
  ext1 j
  fin_cases j <;> simp

/-- The classical Wronskian of `(1, X, X²)` is `2`, not `1`. -/
example : (derivative' : Derivation ℚ ℚ[X] ℚ[X]).wronskian ![1, X, X ^ 2] = 2 := by
  rw [← prod_factorial_mul_hasseWronskian, hasseWronskian_one_X_X_sq, Fin.prod_univ_three]
  norm_num

example : hasseWronskian ![(1 : ℚ[X]), X] = 1 := by
  simp [wronskian]

example : hasseWronskian ![(X : ℚ[X]), 2 * X] = 0 := by
  simp [wronskian]
  ring

/-- The degree estimate needs `W(g) ≠ 0`: here `W(1, 1) = 0` and `0 + 1 ≤ 0` fails. -/
example : hasseWronskian ![(1 : ℚ[X]), 1] = 0 := by
  simp [wronskian]

/-- For two polynomials the degree estimate is `natDegree W(g₀, g₁) + 1 ≤ deg g₀ + deg g₁`, which
is Mathlib's `Polynomial.natDegree_wronskian_lt_add`. -/
example {R : Type*} [CommRing R] (g : Fin 2 → R[X]) (hg : hasseWronskian g ≠ 0) :
    (hasseWronskian g).natDegree + 1 ≤ (g 0).natDegree + (g 1).natDegree := by
  simpa using natDegree_hasseWronskian_add_sum_le hg

/-- For a space of dimension one the multiplicity bound is an equality: `W(b) = b₀` is a nonzero
multiple of `f`. -/
example {K : Type*} [Field K] {V : Submodule K K[X]} (b : Module.Basis (Fin 1) K V) {f : V}
    (hf : f ≠ 0) (a : K) :
    (hasseWronskian fun j ↦ (b j : K[X])).rootMultiplicity a =
      (f : K[X]).rootMultiplicity a + 1 - 1 := by
  have hc : b.repr f 0 ≠ 0 := fun h ↦ hf (b.repr.map_eq_zero_iff.mp (Finsupp.ext fun i ↦ by
    rwa [Subsingleton.elim i 0]))
  have hf' : (f : K[X]) = C (b.repr f 0) * (b 0 : K[X]) := by
    conv_lhs => rw [← b.sum_repr f]
    simp [smul_eq_C_mul]
  rw [hasseWronskian_fin_one, hf', rootMultiplicity_C_mul hc, Nat.add_sub_cancel]

/-- For `V = span (1, X^μ)` with `μ ≥ 1` the multiplicity bound `(μ + 1) - 2` at zero is attained:
`W(1, X^μ) = μ X^(μ - 1)`. -/
example (μ : ℕ) (hμ : 1 ≤ μ) :
    (hasseWronskian ![(1 : ℚ[X]), X ^ μ]).rootMultiplicity 0 = (μ + 1) - 2 := by
  have hW : hasseWronskian ![(1 : ℚ[X]), X ^ μ] = C (μ : ℚ) * (X - C 0) ^ (μ - 1) := by
    simp [wronskian, derivative_X_pow]
  rw [hW, rootMultiplicity_C_mul (by exact_mod_cast (by omega : μ ≠ 0)),
    rootMultiplicity_X_sub_C_pow]
  omega

/-- Over `𝔽₂` the polynomials `1` and `X²` are linearly independent. -/
example : LinearIndependent (ZMod 2) ![(1 : (ZMod 2)[X]), X ^ 2] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  exact ⟨by simpa [coeff_one, coeff_X_pow] using congrArg (fun p ↦ p.coeff 0) h,
    by simpa [coeff_one, coeff_X_pow] using congrArg (fun p ↦ p.coeff 2) h⟩

/-- Over `𝔽₂` the Hasse Wronskian of the independent family `(1, X²)` vanishes. -/
theorem hasseWronskian_one_X_sq_zmod_two : hasseWronskian ![(1 : (ZMod 2)[X]), X ^ 2] = 0 := by
  have h : (1 : (ZMod 2)[X]) + 1 = 0 := CharTwo.add_self_eq_zero 1
  simp [wronskian, h]

/-- Over `𝔽₂`, for `V = span (1, X²)` and `f = X²`, the divisibility `X ∣ W(1, X²)` holds but the
numerical bound `(2 + 1) - 2 ≤ rootMultiplicity 0 W(1, X²)` fails. -/
example : (X - C 0) ^ (((X : (ZMod 2)[X]) ^ 2).rootMultiplicity 0 + 1 - 2) ∣
      hasseWronskian ![(1 : (ZMod 2)[X]), X ^ 2] ∧
    ¬((X : (ZMod 2)[X]) ^ 2).rootMultiplicity 0 + 1 - 2 ≤
      (hasseWronskian ![(1 : (ZMod 2)[X]), X ^ 2]).rootMultiplicity 0 := by
  have hX : ((X : (ZMod 2)[X]) ^ 2).rootMultiplicity 0 = 2 := by
    simpa using rootMultiplicity_X_sub_C_pow (0 : ZMod 2) 2
  rw [hasseWronskian_one_X_sq_zmod_two, hX]
  simp

/-- Over `ℤ/4ℤ` the constant `2` is linearly dependent, but its Hasse Wronskian is `2 ≠ 0`. -/
example : ¬LinearIndependent (ZMod 4) ![C (2 : ZMod 4)] ∧
    hasseWronskian ![C (2 : ZMod 4)] = C 2 ∧ C (2 : ZMod 4) ≠ 0 := by
  refine ⟨fun h ↦ ?_, by simp, by rw [ne_eq, C_eq_zero]; decide⟩
  have := linearIndependent_iff'.mp h univ (fun _ ↦ 2)
    (by simp only [Fin.sum_univ_one, Matrix.cons_val_zero]
        rw [smul_eq_C_mul, ← C_mul, C_eq_zero]; decide) 0 (mem_univ _)
  exact absurd this (by decide)

/-- Over `ℚ × ℚ` the constant `(1, 0)` is linearly dependent, but its Hasse Wronskian is
`(1, 0) ≠ 0`. -/
example : ¬LinearIndependent (ℚ × ℚ) ![C ((1, 0) : ℚ × ℚ)] ∧
    hasseWronskian ![C ((1, 0) : ℚ × ℚ)] = C (1, 0) ∧ C ((1, 0) : ℚ × ℚ) ≠ 0 := by
  refine ⟨fun h ↦ ?_, by simp, by simp [C_eq_zero]⟩
  have := linearIndependent_iff'.mp h univ (fun _ ↦ (0, 1))
    (by simp only [Fin.sum_univ_one, Matrix.cons_val_zero]
        rw [smul_eq_C_mul, ← C_mul, C_eq_zero]; simp) 0 (mem_univ _)
  simp at this

end TauCeti.HasseWronskianExample
