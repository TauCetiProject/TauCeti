/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Basic
public import TauCeti.Algebra.BigOperators.AlternatingSum
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

Conversely, the strong inequalities together with the Euler--Poincaré equality imply the
polynomial identity, which is how it is obtained when no chain complex is at hand.  For sequences
of natural numbers `b` and `c`:

* `TauCeti.sum_range_monomial_add_monomial_eq_of_eq_add`: the relations `cᵢ = bᵢ + qᵢ + qᵢ₋₁`
  give the polynomial identity, over any semiring.
* `TauCeti.exists_sum_range_monomial_eq_add_mul`: if the strong inequalities hold below degree
  `n` and the Euler--Poincaré equality holds in degree `n`, then
  `∑ᵢ₌₀ⁿ cᵢ tⁱ = ∑ᵢ₌₀ⁿ bᵢ tⁱ + (1 + t) Q(t)` with `Q ∈ ℕ[t]`, and the coefficient of `tⁱ` in `Q`
  is the gap `(cᵢ - cᵢ₋₁ + ⋯ ± c₀) - (bᵢ - bᵢ₋₁ + ⋯ ± b₀)` in the `i`-th strong inequality.
* `TauCeti.eq_of_forall_sum_range_neg_one_pow_mul_le`: **the lacunary principle.** If the strong
  inequalities hold in every degree and no two consecutive `cᵢ` are both nonzero, then `b = c`.

## References

* J. Milnor, *Morse Theory*, Section 5.
* R. Bott, *Lectures on Morse theory, old and new*, Bulletin of the American Mathematical
  Society 7 (1982), 331--358, Section 1.
-/

public section

open CategoryTheory Module Polynomial

universe u v

namespace TauCeti

/-- **The polynomial form of `cᵢ = bᵢ + qᵢ + qᵢ₋₁`.**  If `c₀ = b₀ + q₀` and
`cᵢ₊₁ = bᵢ₊₁ + qᵢ₊₁ + qᵢ` for `i < n`, then
`∑ᵢ₌₀ⁿ cᵢ Xⁱ + qₙ Xⁿ⁺¹ = ∑ᵢ₌₀ⁿ bᵢ Xⁱ + (1 + X) ∑ᵢ₌₀ⁿ qᵢ Xⁱ`. -/
theorem sum_range_monomial_add_monomial_eq_of_eq_add {R : Type*} [Semiring R]
    {b c q : ℕ → R} {n : ℕ} (h₀ : c 0 = b 0 + q 0)
    (hsucc : ∀ i < n, c (i + 1) = b (i + 1) + q (i + 1) + q i) :
    ∑ i ∈ Finset.range (n + 1), monomial i (c i) + monomial (n + 1) (q n) =
      ∑ i ∈ Finset.range (n + 1), monomial i (b i) +
        (1 + X) * ∑ i ∈ Finset.range (n + 1), monomial i (q i) := by
  -- Multiplying by `1 + X` shifts a copy of `∑ᵢ qᵢ Xⁱ` up by one degree.
  rw [add_mul, one_mul, Finset.mul_sum]
  simp only [X_mul_monomial]
  induction n with
  | zero =>
    simp only [zero_add, Finset.sum_range_one, h₀, map_add]
    abel
  | succ n ih =>
    have ih := ih fun i hi ↦ hsucc i (hi.trans n.lt_succ_self)
    rw [Finset.sum_range_succ, Finset.sum_range_succ _ (n + 1), Finset.sum_range_succ _ (n + 1),
      Finset.sum_range_succ (fun i ↦ monomial (i + 1) (q i)) (n + 1), hsucc n n.lt_succ_self]
    simp only [map_add]
    -- Split off the left side of the identity in degree `n` and substitute it.
    calc _ = (∑ i ∈ Finset.range (n + 1), monomial i (c i) + monomial (n + 1) (q n)) +
          monomial (n + 1) (b (n + 1)) + monomial (n + 1) (q (n + 1)) +
          monomial (n + 1 + 1) (q (n + 1)) := by abel
      _ = _ := by rw [ih]; abel

/-- **The Morse polynomial identity from the strong inequalities.**  Let `b` and `c` be sequences
of natural numbers satisfying the strong Morse inequalities
`bₘ - bₘ₋₁ + ⋯ ± b₀ ≤ cₘ - cₘ₋₁ + ⋯ ± c₀` for `m < n` and the Euler--Poincaré equality
`∑ᵢ₌₀ⁿ (-1)ⁱ bᵢ = ∑ᵢ₌₀ⁿ (-1)ⁱ cᵢ`.  Then `∑ᵢ₌₀ⁿ cᵢ Xⁱ = ∑ᵢ₌₀ⁿ bᵢ Xⁱ + (1 + X) Q` for a polynomial
`Q` with natural number coefficients: the coefficient of `Xⁱ` in `Q` is the gap
`(cᵢ - cᵢ₋₁ + ⋯ ± c₀) - (bᵢ - bᵢ₋₁ + ⋯ ± b₀)` in the `i`-th strong inequality for `i < n`, and
zero for `i ≥ n`. -/
theorem exists_sum_range_monomial_eq_add_mul {b c : ℕ → ℕ} {n : ℕ}
    (hstrong : ∀ m < n, ∑ i ∈ Finset.range (m + 1), (-1 : ℤ) ^ (m - i) * b i ≤
      ∑ i ∈ Finset.range (m + 1), (-1 : ℤ) ^ (m - i) * c i)
    (heuler : ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * b i =
      ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * c i) :
    ∃ Q : ℕ[X], ∑ i ∈ Finset.range (n + 1), monomial i (c i) =
        ∑ i ∈ Finset.range (n + 1), monomial i (b i) + (1 + X) * Q ∧
      (∀ i < n, (Q.coeff i : ℤ) = ∑ j ∈ Finset.range (i + 1), (-1 : ℤ) ^ (i - j) * c j -
        ∑ j ∈ Finset.range (i + 1), (-1 : ℤ) ^ (i - j) * b j) ∧
      ∀ i, n ≤ i → Q.coeff i = 0 := by
  -- The gap `sₘ` in the `m`-th strong inequality is nonnegative for `m < n` and zero for `m = n`.
  set s : ℕ → ℤ := fun m ↦ ∑ j ∈ Finset.range (m + 1), (-1 : ℤ) ^ (m - j) * c j -
    ∑ j ∈ Finset.range (m + 1), (-1 : ℤ) ^ (m - j) * b j with hs_def
  have hs₀ : s 0 = c 0 - b 0 := by simp [hs_def]
  have hsucc (m : ℕ) : s (m + 1) = c (m + 1) - b (m + 1) - s m := by
    simp only [hs_def, ← smul_eq_mul, sum_range_succ_neg_one_pow_sub_smul]
    abel
  have hsn : s n = 0 := by
    simp only [hs_def, ← smul_eq_mul, sum_range_neg_one_pow_sub_smul]
    simp only [smul_eq_mul, heuler, sub_self]
  have hpos (m : ℕ) (hm : m ≤ n) : 0 ≤ s m := by
    rcases hm.lt_or_eq with hm | rfl
    · exact sub_nonneg.2 (hstrong m hm)
    · exact hsn.ge
  clear_value s
  -- Hence `cₘ = bₘ + qₘ + qₘ₋₁` with `qₘ = sₘ` in `ℕ`.
  have hq (m : ℕ) (hm : m ≤ n) : ((s m).toNat : ℤ) = s m := Int.toNat_of_nonneg (hpos m hm)
  have h := sum_range_monomial_add_monomial_eq_of_eq_add (n := n) (q := fun m ↦ (s m).toNat)
    (b := b) (c := c) (by have := hq 0 (Nat.zero_le n); omega) fun i hi ↦ by
      have := hq i hi.le
      have := hq (i + 1) hi
      have := hsucc i
      omega
  refine ⟨∑ i ∈ Finset.range n, monomial i (s i).toNat, ?_, fun i hi ↦ ?_, fun i hi ↦ ?_⟩
  · have e : ∑ i ∈ Finset.range (n + 1), monomial i (s i).toNat =
        ∑ i ∈ Finset.range n, monomial i (s i).toNat := by
      rw [Finset.sum_range_succ, hsn, Int.toNat_zero, map_zero, add_zero]
    simpa only [hsn, Int.toNat_zero, map_zero, add_zero, e] using h
  · simp only [finsetSum_coeff, coeff_monomial, Finset.sum_ite_eq', Finset.mem_range, hi,
      ↓reduceIte]
    rw [hq i hi.le, hs_def]
  · simp only [finsetSum_coeff, coeff_monomial, Finset.sum_ite_eq', Finset.mem_range,
      hi.not_gt, ↓reduceIte]

/-- **The lacunary principle.**  Let `b` and `c` be sequences of natural numbers satisfying the
strong Morse inequalities `bₘ - bₘ₋₁ + ⋯ ± b₀ ≤ cₘ - cₘ₋₁ + ⋯ ± c₀` in every degree `m`.  If no two
consecutive `cᵢ` are both nonzero, then `b = c`. -/
theorem eq_of_forall_sum_range_neg_one_pow_mul_le {b c : ℕ → ℕ}
    (hstrong : ∀ m, ∑ i ∈ Finset.range (m + 1), (-1 : ℤ) ^ (m - i) * b i ≤
      ∑ i ∈ Finset.range (m + 1), (-1 : ℤ) ^ (m - i) * c i)
    (hc : ∀ i, c i = 0 ∨ c (i + 1) = 0) : b = c := by
  set s : ℕ → ℤ := fun m ↦ ∑ j ∈ Finset.range (m + 1), (-1 : ℤ) ^ (m - j) * c j -
    ∑ j ∈ Finset.range (m + 1), (-1 : ℤ) ^ (m - j) * b j with hs_def
  have hs₀ : s 0 = c 0 - b 0 := by simp [hs_def]
  have hsucc (m : ℕ) : s (m + 1) = c (m + 1) - b (m + 1) - s m := by
    simp only [hs_def, ← smul_eq_mul, sum_range_succ_neg_one_pow_sub_smul]
    abel
  have hpos (m : ℕ) : 0 ≤ s m := sub_nonneg.2 (hstrong m)
  clear_value s
  -- The gap `sₘ` is at most `cₘ` and at most `cₘ₊₁`, so it vanishes.
  have hzero (m : ℕ) : s m = 0 := by
    have hle : s m ≤ c m := by
      cases m with
      | zero => rw [hs₀]; omega
      | succ m => have := hsucc m; have := hpos m; omega
    have := hsucc m
    have := hpos m
    have := hpos (m + 1)
    have := hc m
    omega
  funext i
  cases i with
  | zero => have := hzero 0; omega
  | succ i => have := hsucc i; have := hzero i; have := hzero (i + 1); omega

/-- Scaling a weighted sum of natural numbers `cᵢ` by a natural number `d` gives the same weighted
sum of the products `cᵢ d`: `d ∑ᵢ sᵢ cᵢ = ∑ᵢ sᵢ (cᵢ d)`. This turns the strong inequalities for
counts `cᵢ` weighted by the dimension `d` of a coefficient space into strong inequalities for the
sequence `cᵢ d`, to which the results above apply. -/
theorem natCast_mul_sum_mul_natCast {ι R : Type*} [CommSemiring R] (d : ℕ) (s : ι → R)
    (c : ι → ℕ) (t : Finset ι) :
    (d : R) * ∑ i ∈ t, s i * c i = ∑ i ∈ t, s i * ((c i * d : ℕ) : R) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  push_cast
  ring

end TauCeti

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
  -- Pull the sign `(-1) ^ n` out of both sums.
  simp only [← smul_eq_mul, TauCeti.sum_range_neg_one_pow_sub_smul]
  simp only [smul_eq_mul]
  rw [K.sum_range_finrank_X_eq_sum_range_finrank_homology_add n hfinite]
  -- The two sides now differ by `((-1) ^ n) ^ 2 * dim im (Kₙ₊₁ ⟶ Kₙ) ≥ 0`.
  have hsq : ((-1 : ℤ) ^ n) ^ 2 = 1 := by rw [pow_right_comm, neg_one_sq, one_pow]
  have hq : (0 : ℤ) ≤ finrank k (LinearMap.range (K.d (n + 1) n).hom) := Nat.cast_nonneg _
  linear_combination -(finrank k (LinearMap.range (K.d (n + 1) n).hom) : ℤ) * hsq + hq

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
  have := hfinite 0 (Nat.zero_le n)
  exact TauCeti.sum_range_monomial_add_monomial_eq_of_eq_add
    (q := fun i ↦ finrank k (LinearMap.range (K.d (i + 1) i).hom)) K.finrank_X_zero fun i hi ↦
      have := hfinite (i + 1) hi
      K.finrank_X_succ i

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
