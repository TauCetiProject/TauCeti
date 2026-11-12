/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Inequalities

/-!
# The coefficientwise Morse polynomial identity

For a Morse function on a compact boundaryless manifold, a single polynomial `Q : ℕ[X]`
expresses the strong Morse inequalities in every degree, including degrees above the dimension:

`cⱼ = bⱼ + coeff ((1 + X) * Q) j`.

Here `cⱼ` is the extended-natural count of critical points of index `j` and `bⱼ` is the
dimension of native singular homology. In particular the identity itself asserts that each
critical count is finite. Finiteness of the homology is supplied by
`TauCeti.IsMorse.finite_singularHomology`; no infinite-dimensional homology is assigned a finite
Betti number in applying the identity.

`TauCeti.IsMorse.exists_criticalCount_mul_eq_finrank_add_coeff` allows coefficients in any
finite-dimensional module over a division ring. `TauCeti.morse_inequalities` uses the division
ring itself as coefficients, so that the left side is the critical count without a factor.

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, Section 5.
-/

public section

open Module Polynomial
open scoped ContDiff Manifold

universe u

namespace TauCeti

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
  {k : Type u} [DivisionRing k]

/-- **The coefficientwise Morse polynomial identity with module coefficients.** There is one
polynomial `Q` with natural coefficients such that, in every degree, the critical count times
`dim V` is the dimension of singular homology plus the coefficient of `(1 + X) * Q`.
The equality is in `ℕ∞`, retaining the original critical counts rather than their `toNat` values.
-/
theorem IsMorse.exists_criticalCount_mul_eq_finrank_add_coeff (hf : IsMorse I f)
    (V : ModuleCat.{u} k) [Module.Finite k V] :
    ∃ Q : ℕ[X], ∀ j : ℕ,
      criticalCount I f j * (finrank k V : ℕ∞) =
        ((finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) j).obj V).obj
          (TopCat.of M)) + ((1 + X) * Q).coeff j : ℕ) : ℕ∞) := by
  classical
  obtain ⟨Q, hQ, -, -⟩ := hf.exists_sum_range_monomial_eq_add_mul V (n := finrank ℝ E) le_rfl
  -- Both coefficient sequences vanish above the dimension; the same Q therefore works
  -- without a truncation or a degree hypothesis on j.
  have hcount (j : ℕ) : (criticalCount I f j).toNat * finrank k V =
      (∑ i ∈ Finset.range (finrank ℝ E + 1),
        monomial i ((criticalCount I f i).toNat * finrank k V)).coeff j := by
    by_cases hj : j < finrank ℝ E + 1
    · simp [Finsupp.single_apply, Finset.mem_range, hj]
    · rw [criticalCount_eq_zero_of_finrank_lt (by omega)]
      simp [Finsupp.single_apply, Finset.mem_range, hj]
  have hbetti (j : ℕ) :
      (∑ i ∈ Finset.range (finrank ℝ E + 1), monomial i
        (finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) i).obj V).obj
          (TopCat.of M)))).coeff j =
      finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) j).obj V).obj
        (TopCat.of M)) := by
    by_cases hj : j < finrank ℝ E + 1
    · simp [Finsupp.single_apply, Finset.mem_range, hj]
    · simp [Finsupp.single_apply, Finset.mem_range, hj,
        hf.finrank_singularHomology_eq_zero_of_finrank_lt V (by omega : finrank ℝ E < j)]
  refine ⟨Q, fun j ↦ ?_⟩
  have hj := hcount j
  rw [hQ, coeff_add, hbetti] at hj
  -- Compact Morse critical sets are finite, so casting back recovers the actual counts.
  have hcast := congrArg (fun n : ℕ ↦ (n : ℕ∞)) hj
  simpa only [Nat.cast_mul, ENat.natCast_toNat (hf.criticalCount_ne_top j)] using hcast

/-- **The strong Morse inequalities in polynomial form.** For a Morse function on a compact
boundaryless manifold and coefficients in a division ring, the extended-natural number of
index-`j` critical points equals the `j`-th singular Betti number plus the `j`-th coefficient of
`(1 + X) * Q`, for one polynomial `Q : ℕ[X]` and every `j`. In particular every critical count
is finite. -/
theorem morse_inequalities (hf : IsMorse I f) (k : Type u) [DivisionRing k] :
    ∃ Q : ℕ[X], ∀ j : ℕ,
      criticalCount I f j =
        ((bettiNumber k M j + ((1 + X) * Q).coeff j : ℕ) : ℕ∞) := by
  simpa [bettiNumber_def] using
    hf.exists_criticalCount_mul_eq_finrank_add_coeff (ModuleCat.of k k)

end TauCeti
