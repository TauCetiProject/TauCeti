/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Basic
public import TauCeti.Algebra.Homology.EulerCharacteristic.ChainComplex
import Mathlib.Tactic.LinearCombination

/-!
# The Morse inequalities for chain complexes of vector spaces

Let `K` be a chain complex of vector spaces indexed by `ℕ`, with differentials `Kᵢ₊₁ ⟶ Kᵢ`, and
write `cᵢ = dim Kᵢ`, `bᵢ = dim Hᵢ(K)` and `qᵢ = dim im (Kᵢ₊₁ ⟶ Kᵢ)`, with `q₋₁ = 0`.  When `Kᵢ`
is finite-dimensional, rank--nullity gives `cᵢ = bᵢ + qᵢ + qᵢ₋₁`, and this file draws the three
numerical consequences that are known as the Morse inequalities when `K` is the cellular chain
complex of a CW model of a manifold whose cells correspond to the critical points of a Morse
function.  Since `finrank` is `0` on infinite-dimensional spaces, each needs finite-dimensional
terms.

* **Weak inequalities.**  `bᵢ ≤ cᵢ` whenever `Kᵢ` is finite-dimensional, which holds for any
  homological complex and is proved with the other dimension bounds for complexes of vector
  spaces (`HomologicalComplex.finrank_homology_le_finrank_X`).
* **Strong inequalities.**  For every `n` such that `K₀, …, Kₙ` are finite-dimensional,
  `bₙ - bₙ₋₁ + ⋯ ± b₀ ≤ cₙ - cₙ₋₁ + ⋯ ± c₀`
  (`ChainComplex.sum_range_neg_one_pow_mul_finrank_homology_le`).
* **The Morse polynomial identity.**  If `K₀, …, Kₙ` are finite-dimensional and `Kₙ₊₁ ⟶ Kₙ`
  vanishes, then `∑ᵢ₌₀ⁿ cᵢ tⁱ = ∑ᵢ₌₀ⁿ bᵢ tⁱ + (1 + t) Q(t)` in `ℕ[t]`, where `Q(t) = ∑ᵢ₌₀ⁿ⁻¹ qᵢ tⁱ`
  records the ranks of the differentials (`ChainComplex.sum_range_monomial_finrank_X_eq`).
  Without the vanishing hypothesis the identity holds after adding `qₙ tⁿ⁺¹` to the left side
  (`ChainComplex.sum_range_monomial_finrank_X_add_monomial_eq`).

The polynomial identity implies the strong inequalities, since the alternating partial sums of
the coefficients of `(1 + t) Q(t)` are the coefficients of `Q`, which are natural numbers.  The
weak inequalities and the Euler--Poincaré equality alone do not imply it: the counts
`c = (2, 0, 0, 2)` and `b = (1, 0, 0, 1)` satisfy both, while `c₁ - c₀ < b₁ - b₀`.

## References

* J. Milnor, *Morse Theory*, Section 5.
-/

public section

open CategoryTheory Module Polynomial

universe u v

section

variable {k : Type u} [DivisionRing k]

namespace ChainComplex

variable (K : ChainComplex (ModuleCat.{v} k) ℕ)

/-- **The strong Morse inequalities.**  If the terms of `K` through degree `n` are
finite-dimensional, then `bₙ - bₙ₋₁ + ⋯ ± b₀ ≤ cₙ - cₙ₋₁ + ⋯ ± c₀`, where `bᵢ` is the dimension
of `Hᵢ(K)` and `cᵢ` that of `Kᵢ`.  The difference of the two sides is the rank of `Kₙ₊₁ ⟶ Kₙ`. -/
theorem sum_range_neg_one_pow_mul_finrank_homology_le (n : ℕ)
    (hfinite : ∀ i ≤ n, Module.Finite k (K.X i)) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - i) * finrank k (K.homology i) ≤
      ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - i) * finrank k (K.X i) := by
  -- Pull the sign `(-1) ^ n` out of both sums, using that `(-1) ^ m` squares to `1`.
  have hsq (m : ℕ) : ((-1 : ℤ) ^ m) ^ 2 = 1 := by rw [pow_right_comm, neg_one_sq, one_pow]
  have hrw (x : ℕ → ℤ) : ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - i) * x i =
      (-1) ^ n * ∑ i ∈ Finset.range (n + 1), (-1) ^ i * x i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have h : (-1 : ℤ) ^ n = (-1) ^ (n - i) * (-1) ^ i := by
      rw [← pow_add, Nat.sub_add_cancel (Finset.mem_range_succ_iff.1 hi)]
    linear_combination (-(-1 : ℤ) ^ i * x i) * h - (-1 : ℤ) ^ (n - i) * x i * hsq i
  rw [hrw, hrw, K.sum_range_finrank_X_eq_sum_range_finrank_homology_add n hfinite]
  -- The two sides now differ by `((-1) ^ n) ^ 2 * dim im (Kₙ₊₁ ⟶ Kₙ) ≥ 0`.
  have hq : (0 : ℤ) ≤ finrank k (LinearMap.range (K.d (n + 1) n).hom) := Nat.cast_nonneg _
  linear_combination -(finrank k (LinearMap.range (K.d (n + 1) n).hom) : ℤ) * hsq n + hq

/-- **The truncated Morse polynomial identity.**  If the terms of `K` through degree `n` are
finite-dimensional, then in `ℕ[X]`
`∑ᵢ₌₀ⁿ cᵢ Xⁱ + qₙ Xⁿ⁺¹ = ∑ᵢ₌₀ⁿ bᵢ Xⁱ + (1 + X) ∑ᵢ₌₀ⁿ qᵢ Xⁱ`, where `cᵢ` is the dimension of `Kᵢ`,
`bᵢ` that of `Hᵢ(K)` and `qᵢ` the rank of `Kᵢ₊₁ ⟶ Kᵢ`. -/
theorem sum_range_monomial_finrank_X_add_monomial_eq (n : ℕ)
    (hfinite : ∀ i ≤ n, Module.Finite k (K.X i)) :
    ∑ i ∈ Finset.range (n + 1), monomial i (finrank k (K.X i)) +
        monomial (n + 1) (finrank k (LinearMap.range (K.d (n + 1) n).hom)) =
      ∑ i ∈ Finset.range (n + 1), monomial i (finrank k (K.homology i)) +
        (1 + X) * ∑ i ∈ Finset.range (n + 1),
          monomial i (finrank k (LinearMap.range (K.d (i + 1) i).hom)) := by
  simp only [← C_mul_X_pow_eq_monomial]
  induction n with
  | zero =>
    let _ := hfinite 0 le_rfl
    simp only [zero_add, Finset.sum_range_one, pow_zero, mul_one, pow_one, K.finrank_X_zero,
      map_add]
    ring
  | succ n ih =>
    let _ := hfinite (n + 1) le_rfl
    have ih := ih fun i hi ↦ hfinite i (hi.trans n.le_succ)
    rw [Finset.sum_range_succ, Finset.sum_range_succ _ (n + 1), Finset.sum_range_succ _ (n + 1),
      K.finrank_X_succ n]
    simp only [map_add]
    -- Split off the left side of the identity in degree `n` and substitute it.
    calc _ = (∑ i ∈ Finset.range (n + 1), C (finrank k (K.X i)) * X ^ i +
            C (finrank k (LinearMap.range (K.d (n + 1) n).hom)) * X ^ (n + 1)) +
          C (finrank k (K.homology (n + 1))) * X ^ (n + 1) +
          (1 + X) * (C (finrank k (LinearMap.range (K.d (n + 2) (n + 1)).hom)) * X ^ (n + 1)) := by
          ring
      _ = _ := by rw [ih]; ring

/-- **The Morse polynomial identity.**  If the terms of `K` through degree `n` are
finite-dimensional and the differential `Kₙ₊₁ ⟶ Kₙ` vanishes, then in `ℕ[X]`
`∑ᵢ₌₀ⁿ cᵢ Xⁱ = ∑ᵢ₌₀ⁿ bᵢ Xⁱ + (1 + X) Q`, where `cᵢ` is the dimension of `Kᵢ`, `bᵢ` that of
`Hᵢ(K)`, and `Q = ∑ᵢ₌₀ⁿ⁻¹ qᵢ Xⁱ` with `qᵢ` the rank of `Kᵢ₊₁ ⟶ Kᵢ`: the coefficient of `Xⁱ` in
`Q` is that rank for `i < n` and zero otherwise. -/
theorem sum_range_monomial_finrank_X_eq {n : ℕ}
    (hfinite : ∀ i ≤ n, Module.Finite k (K.X i)) (hn : K.d (n + 1) n = 0) :
    ∑ i ∈ Finset.range (n + 1), monomial i (finrank k (K.X i)) =
      ∑ i ∈ Finset.range (n + 1), monomial i (finrank k (K.homology i)) +
        (1 + X) * ∑ i ∈ Finset.range n,
          monomial i (finrank k (LinearMap.range (K.d (i + 1) i).hom)) := by
  have h := K.sum_range_monomial_finrank_X_add_monomial_eq n hfinite
  rw [Finset.sum_range_succ
      (fun i ↦ monomial i (finrank k (LinearMap.range (K.d (i + 1) i).hom))) n, hn,
    ModuleCat.hom_zero, LinearMap.range_zero, finrank_bot] at h
  simpa only [map_zero, add_zero] using h

end ChainComplex

end
