/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.Convex.Gauge
import TauCeti.Algebra.Module.ZLattice.AdaptedBasis

/-!
# A lattice basis of controlled gauge from an independent family

Let `L` be a discrete `ℤ`-submodule of a finite-dimensional real normed space `E`, let `B` be a
convex, symmetric, absorbent subset of `E`, and let `a 0, …, a (n - 1)` be `ℝ`-linearly
independent vectors of `L` with `n = finrank ℝ E`. The vectors `a i` need not be a `ℤ`-basis of
`L`, but some `ℤ`-basis `b` of `L` is almost as short, measured by the gauge of `B`:
`gauge B (b j) ≤ max (gauge B (a j)) ((∑ i ≤ j, gauge B (a i)) / 2)` for every `j`.

Applied to a family of vectors realizing the successive minima `λ 0 ≤ λ 1 ≤ ⋯` of `L` with
respect to a closed convex body, this gives the lattice basis from the successive minima: its
`i`-th member (indices from `0`) lies in `max 1 ((i + 1) / 2) · λ i` times the body. Against
Minkowski's second theorem this costs the factor
`∏ i < n, max 1 ((i + 1) / 2) = n! / 2 ^ (n - 1)` (`TauCeti.prod_max_one_add_one_div_two`).

## Main results

* `ZLattice.exists_basis_gauge_le`: the basis of controlled gauge.
* `ZLattice.exists_basis_gauge_le_max_one_mul`: when the gauges of the `a i` increase, the
  `j`-th basis vector has gauge at most `max 1 ((j + 1) / 2)` times that of `a j`.

## Implementation notes

The coordinate-level construction `ZLattice.exists_basis_triangular` supplies a reduced basis
adapted to the flag of the given real basis. Expanding each basis vector in those coordinates,
then using subadditivity and absolute homogeneity of the gauge, gives the estimate.

## References

* J. W. S. Cassels, *An Introduction to the Geometry of Numbers*, Springer, 1959: Chapter I,
  Theorem I (bases adapted to a flag), and Chapter V, Lemma 8 (the basis from the minima).
* Y. Bugeaud and K. Győry, *Bounds for the solutions of unit equations*, Acta Arith. **74**
  (1996), 67–80, §3.

The construction and its proof are adapted from the Apache-2.0 formalization in
`rwst/Subspace-Theorems` (files `ArithmeticHeights/AdaptedBasis.lean` and
`ArithmeticHeights/MinimaBasis.lean`), by Ralf Stephan.
-/

public section

open Module Submodule

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **A lattice basis of controlled gauge.** Let `L` be a discrete `ℤ`-submodule of a
finite-dimensional real normed space `E`, and `B` a convex, symmetric, absorbent subset of `E`.
For `ℝ`-linearly independent vectors `a 0, …, a (n - 1)` of `L` with `n = finrank ℝ E`, there is
a `ℤ`-basis `b` of `L` with
`gauge B (b j) ≤ max (gauge B (a j)) ((∑ i ≤ j, gauge B (a i)) / 2)` for every `j`.

The family `a` need not be a basis of `L`, and `L` is not assumed to be a full lattice: that
follows from the hypotheses on `a`. This is the form of Cassels' Chapter V, Lemma 8 which does not
mention successive minima. -/
theorem exists_basis_gauge_le [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L]
    {B : Set E} (hB₀ : Convex ℝ B) (hB₁ : ∀ x ∈ B, -x ∈ B) (hB₂ : Absorbent ℝ B) {n : ℕ}
    (hn : n = finrank ℝ E) {a : Fin n → E} (haL : ∀ i, a i ∈ L) (ha : LinearIndependent ℝ a) :
    ∃ b : Basis (Fin n) ℤ L, ∀ j : Fin n,
      gauge B (b j : E) ≤ max (gauge B (a j)) ((∑ i ∈ Finset.Iic j, gauge B (a i)) / 2) := by
  set e := basisOfLinearIndependentOfCardEqFinrank' a ha (by simp [hn])
  have he : ⇑e = a := coe_basisOfLinearIndependentOfCardEqFinrank' ..
  obtain ⟨b, hb⟩ := exists_basis_triangular e (by simpa [he] using haL)
  refine ⟨b, fun j ↦ ?_⟩
  obtain ⟨htri, h | h⟩ := hb j
  · rw [h, he]
    exact le_max_left _ _
  refine le_max_of_le_right ?_
  have hbal : Balanced ℝ B := (balanced_iff_neg_mem hB₀).2 hB₁
  -- Expand `b j` in the basis `a`; only the coordinates `i ≤ j` are nonzero.
  have hexp : (b j : E) = ∑ i ∈ Finset.Iic j, e.repr (b j) i • a i := by
    conv_lhs => rw [← e.sum_repr (b j)]
    rw [he]
    refine (Finset.sum_subset (Finset.subset_univ _) fun i _ hi ↦ ?_).symm
    rw [htri i (by simpa using hi), zero_smul]
  calc gauge B (b j) = gauge B (∑ i ∈ Finset.Iic j, e.repr (b j) i • a i) := congrArg _ hexp
    _ ≤ ∑ i ∈ Finset.Iic j, gauge B (e.repr (b j) i • a i) := gauge_sum_le hB₀ hB₂ _ _
    _ = ∑ i ∈ Finset.Iic j, |e.repr (b j) i| * gauge B (a i) := by
        simp [gauge_smul hbal, Real.norm_eq_abs]
    _ ≤ ∑ i ∈ Finset.Iic j, 1 / 2 * gauge B (a i) :=
        Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_right (h i) (gauge_nonneg _)
    _ = (∑ i ∈ Finset.Iic j, gauge B (a i)) / 2 := by
        rw [← Finset.mul_sum]
        ring

/-- **A lattice basis from an increasing independent family.** If, in
`ZLattice.exists_basis_gauge_le`, the gauges of `a 0, a 1, …` increase, as they do for vectors
realizing the successive minima of `L` with respect to `B`, then some `ℤ`-basis `b` of `L` has
`gauge B (b j) ≤ max 1 ((j + 1) / 2) * gauge B (a j)` for every `j`. -/
theorem exists_basis_gauge_le_max_one_mul [FiniteDimensional ℝ E] (L : Submodule ℤ E)
    [DiscreteTopology L] {B : Set E} (hB₀ : Convex ℝ B) (hB₁ : ∀ x ∈ B, -x ∈ B)
    (hB₂ : Absorbent ℝ B) {n : ℕ} (hn : n = finrank ℝ E) {a : Fin n → E} (haL : ∀ i, a i ∈ L)
    (ha : LinearIndependent ℝ a) (hmono : Monotone fun i ↦ gauge B (a i)) :
    ∃ b : Basis (Fin n) ℤ L, ∀ j : Fin n,
      gauge B (b j : E) ≤ max 1 ((((j : ℕ) : ℝ) + 1) / 2) * gauge B (a j) := by
  obtain ⟨b, hb⟩ := exists_basis_gauge_le L hB₀ hB₁ hB₂ hn haL ha
  refine ⟨b, fun j ↦ (hb j).trans ?_⟩
  rw [max_mul_of_nonneg _ _ (gauge_nonneg _), one_mul]
  refine max_le_max le_rfl ?_
  calc (∑ i ∈ Finset.Iic j, gauge B (a i)) / 2 ≤ (∑ _i ∈ Finset.Iic j, gauge B (a j)) / 2 := by
        gcongr with i hi
        exact hmono (Finset.mem_Iic.1 hi)
    _ = ((((j : ℕ) : ℝ) + 1) / 2) * gauge B (a j) := by
        rw [Finset.sum_const, Fin.card_Iic, nsmul_eq_mul]
        push_cast
        ring

end ZLattice
