/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.EulerCharacteristic.MorseInequalities
public import TauCeti.Algebra.Homology.ModuleCat.Finrank
public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Singular
public import TauCeti.AlgebraicTopology.Singular.BettiNumber

/-!
# The Morse inequalities for CW complexes

Let `(C, D)` be a relative CW complex with `cᵢ` relative `i`-cells, and let `bᵢ` be the dimension
of the relative singular homology `Hᵢ(C, D; M)` with coefficients in a finite-dimensional module
`M` over a division ring `k`.  Applying the Morse inequalities for chain complexes to the cellular
chain complex, and the cellular--singular comparison, gives:

* **weak inequalities** `bᵢ ≤ cᵢ · dim M`
  (`TauCeti.finrank_singularHomology_complexBasePair_le`);
* **strong inequalities**
  `bₙ - bₙ₋₁ + ⋯ ± b₀ ≤ (cₙ - cₙ₋₁ + ⋯ ± c₀) · dim M`, which need only finitely many cells
  through degree `n`
  (`TauCeti.sum_range_neg_one_pow_mul_finrank_singularHomology_complexBasePair_le`);
* **the Morse polynomial identity**
  `∑ᵢ₌₀ⁿ cᵢ dim M · tⁱ = ∑ᵢ₌₀ⁿ bᵢ tⁱ + (1 + t) Q(t)` in `ℕ[t]` when there are no
  `(n + 1)`-cells, where the coefficient of `tⁱ` in `Q` is the rank of the cellular differential
  in degree `i + 1` for `i < n`, and zero otherwise
  (`TauCeti.sum_range_monomial_natCard_cell_mul_finrank_eq`).

The same statements for the ordinary singular homology of an absolute CW complex are obtained
through the quotient map for the empty subspace.  When the cells of a CW model of a manifold
correspond to the critical points of a Morse function, with an `i`-cell for each critical point of
index `i`, these are the Morse inequalities for that function.

## References

* J. Milnor, *Morse Theory*, Section 5.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, Theorem 2.35.
-/

public section

noncomputable section

open CategoryTheory Module Topology Topology.RelCWComplex
open Polynomial (monomial)

universe w

namespace TauCeti

variable {X : Type w} [TopologicalSpace X] [T2Space X] {k : Type w} [DivisionRing k]

section Relative

variable {D : Set X} (C : Set X) [RelCWComplex C D] (M : ModuleCat.{w} k) [Module.Finite k M]

/-- **The weak Morse inequality for a CW pair.**  In a degree with finitely many relative cells,
the relative singular homology has dimension at most the number of cells times `dim M`. -/
theorem finrank_singularHomology_complexBasePair_le (n : ℕ) [Finite (cell C n)] :
    finrank k ((complexBasePair C).singularHomology M n : ModuleCat k) ≤
      Nat.card (cell C n) * finrank k M := by
  have := finite_cellularChainComplex_X C M n
  rw [← (cellularSingularHomologyIso C M n).toLinearEquiv.finrank_eq,
    ← finrank_cellularChainComplex_X]
  exact (cellularChainComplex C M).finrank_homology_le_finrank_X n

/-- **The strong Morse inequalities for a CW pair.**  If there are finitely many relative cells
through degree `n`, then `bₙ - bₙ₋₁ + ⋯ ± b₀ ≤ (cₙ - cₙ₋₁ + ⋯ ± c₀) · dim M`, where `bᵢ` is the
dimension of the relative singular homology and `cᵢ` the number of relative `i`-cells. -/
theorem sum_range_neg_one_pow_mul_finrank_singularHomology_complexBasePair_le {n : ℕ}
    (hfinite : ∀ i ≤ n, Finite (cell C i)) :
    ∑ i ∈ Finset.range (n + 1),
        (-1 : ℤ) ^ (n - i) * finrank k ((complexBasePair C).singularHomology M i : ModuleCat k) ≤
      finrank k M * ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - i) * Nat.card (cell C i) := by
  simp_rw [← (cellularSingularHomologyIso C M _).toLinearEquiv.finrank_eq]
  refine ((cellularChainComplex C M).sum_range_neg_one_pow_mul_finrank_homology_le n fun i hi ↦
    have := hfinite i hi
    finite_cellularChainComplex_X C M i).trans_eq ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [finrank_cellularChainComplex_X]
  push_cast
  ring

/-- **The Morse polynomial identity for a CW pair.**  If there are finitely many relative cells
through degree `n` and none in degree `n + 1`, then in `ℕ[X]`
`∑ᵢ₌₀ⁿ cᵢ dim M · Xⁱ = ∑ᵢ₌₀ⁿ bᵢ Xⁱ + (1 + X) Q`, where `cᵢ` is the number of relative `i`-cells,
`bᵢ` the dimension of the relative singular homology, and the coefficient of `Xⁱ` in `Q` is the
rank of the cellular differential in degree `i + 1` for `i < n`, and zero otherwise. -/
theorem sum_range_monomial_natCard_cell_mul_finrank_eq {n : ℕ}
    (hfinite : ∀ i ≤ n, Finite (cell C i)) (hn : IsEmpty (cell C (n + 1))) :
    ∑ i ∈ Finset.range (n + 1), monomial i (Nat.card (cell C i) * finrank k M) =
      ∑ i ∈ Finset.range (n + 1),
          monomial i (finrank k ((complexBasePair C).singularHomology M i : ModuleCat k)) +
        (1 + Polynomial.X) * ∑ i ∈ Finset.range n,
          monomial i
            (finrank k (LinearMap.range ((cellularChainComplex C M).d (i + 1) i).hom)) := by
  have hX : Limits.IsZero ((cellularChainComplex C M).X (n + 1)) := by
    rw [cellularChainComplex_X]
    exact isZero_cellularChainGroup C (n + 1) M
  simp_rw [← (cellularSingularHomologyIso C M _).toLinearEquiv.finrank_eq]
  rw [← (cellularChainComplex C M).sum_range_monomial_finrank_X_eq
    (fun i hi ↦
      have := hfinite i hi
      finite_cellularChainComplex_X C M i)
    (hX.eq_of_src _ 0)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [finrank_cellularChainComplex_X]

end Relative

section Absolute

variable (C : Set X) [CWComplex C] (M : ModuleCat.{w} k) [Module.Finite k M]

/-- **The weak Morse inequality for a CW complex.**  In a degree with finitely many cells, the
singular homology has dimension at most the number of cells times `dim M`. -/
theorem finrank_singularHomology_le_of_cwComplex (n : ℕ) [Finite (cell C n)] :
    finrank k (((AlgebraicTopology.singularHomologyFunctor.{w} (ModuleCat.{w} k) n).obj M).obj
        (TopCat.of C)) ≤
      Nat.card (cell C n) * finrank k M := by
  rw [finrank_singularHomology_eq_complexBasePair]
  exact finrank_singularHomology_complexBasePair_le C M n

/-- **The strong Morse inequalities for a CW complex.**  If there are finitely many cells through
degree `n`, then `bₙ - bₙ₋₁ + ⋯ ± b₀ ≤ (cₙ - cₙ₋₁ + ⋯ ± c₀) · dim M`, where `bᵢ` is the dimension
of the singular homology and `cᵢ` the number of `i`-cells. -/
theorem sum_range_neg_one_pow_mul_finrank_singularHomology_le_of_cwComplex {n : ℕ}
    (hfinite : ∀ i ≤ n, Finite (cell C i)) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - i) *
        finrank k (((AlgebraicTopology.singularHomologyFunctor.{w} (ModuleCat.{w} k) i).obj M).obj
          (TopCat.of C)) ≤
      finrank k M * ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - i) * Nat.card (cell C i) := by
  simp_rw [finrank_singularHomology_eq_complexBasePair]
  exact sum_range_neg_one_pow_mul_finrank_singularHomology_complexBasePair_le C M hfinite

/-- **The Morse polynomial identity for a CW complex.**  If there are finitely many cells through
degree `n` and none in degree `n + 1`, then in `ℕ[X]`
`∑ᵢ₌₀ⁿ cᵢ dim M · Xⁱ = ∑ᵢ₌₀ⁿ bᵢ Xⁱ + (1 + X) Q`, where `cᵢ` is the number of `i`-cells, `bᵢ` the
dimension of the singular homology, and the coefficient of `Xⁱ` in `Q` is the rank of the cellular
differential in degree `i + 1` for `i < n`, and zero otherwise. -/
theorem sum_range_monomial_natCard_cell_mul_finrank_eq_of_cwComplex {n : ℕ}
    (hfinite : ∀ i ≤ n, Finite (cell C i)) (hn : IsEmpty (cell C (n + 1))) :
    ∑ i ∈ Finset.range (n + 1), monomial i (Nat.card (cell C i) * finrank k M) =
      ∑ i ∈ Finset.range (n + 1), monomial i
          (finrank k (((AlgebraicTopology.singularHomologyFunctor.{w} (ModuleCat.{w} k) i).obj
            M).obj (TopCat.of C))) +
        (1 + Polynomial.X) * ∑ i ∈ Finset.range n,
          monomial i
            (finrank k (LinearMap.range ((cellularChainComplex C M).d (i + 1) i).hom)) := by
  simp_rw [finrank_singularHomology_eq_complexBasePair]
  exact sum_range_monomial_natCard_cell_mul_finrank_eq C M hfinite hn

/-- **The Morse polynomial identity for a CW complex, coefficientwise.**  If there are finitely
many cells through degree `n` and none above it, then in every degree `j` the number `cⱼ` of
`j`-cells is the Betti number `bⱼ` over `k` plus the coefficient of `Xʲ` in `(1 + X) Q`, where the
coefficient of `Xⁱ` in `Q` is the rank of the cellular differential in degree `i + 1` for `i < n`,
and zero otherwise.  Above `n` all three terms vanish. -/
theorem natCard_cell_eq_bettiNumber_add_coeff_of_cwComplex {n : ℕ}
    (hfinite : ∀ i ≤ n, Finite (cell C i)) (hn : ∀ i, n < i → IsEmpty (cell C i)) (j : ℕ) :
    Nat.card (cell C j) = bettiNumber k C j +
      ((1 + Polynomial.X) * ∑ i ∈ Finset.range n, monomial i (finrank k (LinearMap.range
        ((cellularChainComplex C (ModuleCat.of k k)).d (i + 1) i).hom))).coeff j := by
  have h := congrArg (fun p : Polynomial ℕ => p.coeff j)
    (sum_range_monomial_natCard_cell_mul_finrank_eq_of_cwComplex C (ModuleCat.of k k) hfinite
      (hn (n + 1) n.lt_succ_self))
  simp only [Polynomial.coeff_add, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial_apply,
    Finset.sum_ite_eq', Finset.mem_range, finrank_self, mul_one] at h
  rw [bettiNumber_def]
  split_ifs at h with hj
  · exact h
  · -- Above `n` there are no cells, so the weak inequality forces the homology to vanish.
    have := hn j (by omega)
    have hb := finrank_singularHomology_le_of_cwComplex C (ModuleCat.of k k) j
    rw [Nat.card_of_isEmpty] at hb ⊢
    omega

end Absolute

end TauCeti
