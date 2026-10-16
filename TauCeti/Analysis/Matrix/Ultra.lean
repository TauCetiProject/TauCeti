/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Ring.Basic
public import TauCeti.Algebra.BigOperators.ZPow
public import TauCeti.LinearAlgebra.Matrix.Charpoly.Reverse
public import TauCeti.LinearAlgebra.Matrix.Minor

/-!
# Determinant estimates for matrices over ultrametric normed rings

Over an ultrametric normed commutative ring `R` with `‖1‖ = 1`, the Leibniz expansion of a
determinant is a sum of signed products, so the ultrametric inequality bounds the determinant by
the largest of those products rather than by their sum. If the entries satisfy
`‖A i j‖ ≤ c i * d j`, every Leibniz product is bounded by `(∏ i, c i) * ∏ j, d j`, and hence so is
the determinant (`Matrix.norm_det_le_prod_mul_prod`). No multiplicativity of the norm and no
nonnegativity of `c` or `d` is assumed; the norm need only be submultiplicative.

Taking `d = 1` gives the bound of a determinant by the product of row bounds
(`Matrix.norm_det_le_prod_of_norm_le`), and hence the corresponding bound for a principal minor
(`Matrix.norm_principalMinor_le`). Applied to the principal minors of the expansion
`Matrix.coeff_charpolyRev`, these bounds control the coefficients of `det (1 - X A)`
(`Matrix.norm_coeff_charpolyRev_le`). These are the estimates from which convergence and growth of
Fredholm determinants of compact operators on nonarchimedean Banach spaces are derived.

The two-sided form `‖A i j‖ ≤ σ ^ (w i - w' j)`, with integer weights `w`, `w'` and
`0 < σ ≤ 1`, bounds the `k`-th coefficient by `σ ^ m` whenever `m` is a lower bound for the sums
`∑ i ∈ s, (w i - w' i)` over the `k`-element sets `s` (`Matrix.norm_coeff_charpolyRev_le_zpow`).
The bound depends only on the differences `w i - w' i` along the diagonal, although the entry
bounds compare a row weight with an unrelated column weight.

## Main results

* `Matrix.norm_det_le_prod_mul_prod`, `Matrix.norm_det_le_prod_of_norm_le`,
  `Matrix.norm_principalMinor_le`: determinant and principal-minor bounds.
* `Matrix.norm_coeff_charpolyRev_le`, `Matrix.norm_coeff_charpolyRev_le_of_norm_le`,
  `Matrix.norm_coeff_charpolyRev_le_zpow`: coefficient bounds for `det (1 - X A)`.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §§4–5.
* K. S. Kedlaya, *A little p-adic numerical analysis*, MIT 18.787 notes (2007), §3.
-/

public section

open Equiv Finset Polynomial

namespace Matrix

variable {ι R : Type*} [Fintype ι] [DecidableEq ι]
  [NormedCommRing R] [NormOneClass R] [IsUltrametricDist R]

/-- **Two-sided determinant bound.** Over an ultrametric normed ring with `‖1‖ = 1`, if
`‖A i j‖ ≤ c i * d j` for all entries, then `‖det A‖ ≤ (∏ i, c i) * ∏ j, d j`. -/
theorem norm_det_le_prod_mul_prod {A : Matrix ι ι R} {c d : ι → ℝ}
    (h : ∀ i j, ‖A i j‖ ≤ c i * d j) : ‖A.det‖ ≤ (∏ i, c i) * ∏ j, d j := by
  rw [det_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonempty univ_nonempty fun σ _ ↦ ?_
  calc ‖Perm.sign σ • ∏ i, A (σ i) i‖ = ‖∏ i, A (σ i) i‖ := by
        rcases Int.units_eq_one_or (Perm.sign σ) with hσ | hσ <;> simp [hσ]
    _ ≤ ∏ i, ‖A (σ i) i‖ := norm_prod_le _ _
    _ ≤ ∏ i, c (σ i) * d i := prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun i _ ↦ h _ _
    _ = (∏ i, c i) * ∏ j, d j := by rw [prod_mul_distrib, Equiv.prod_comp]

/-- **Row bound.** Over an ultrametric normed ring with `‖1‖ = 1`, the determinant is bounded by
the product of bounds for its rows. -/
theorem norm_det_le_prod_of_norm_le {A : Matrix ι ι R} {c : ι → ℝ} (h : ∀ i j, ‖A i j‖ ≤ c i) :
    ‖A.det‖ ≤ ∏ i, c i := by
  simpa using norm_det_le_prod_mul_prod (d := 1) (by simpa using h)

omit [Fintype ι] in
/-- **Minor bound.** Over an ultrametric normed ring with `‖1‖ = 1`, a principal minor is
bounded by the product of the row bounds over its indices. -/
theorem norm_principalMinor_le {A : Matrix ι ι R} {r : ι → ℝ} (hA : ∀ i j, ‖A i j‖ ≤ r i)
    (s : Finset ι) : ‖A.principalMinor s‖ ≤ ∏ i ∈ s, r i := by
  rw [principalMinor_def, ← prod_coe_sort s r]
  exact norm_det_le_prod_of_norm_le fun i j ↦ hA i j

/-- **Coefficient bound.** If `‖A i j‖ ≤ c i * d j` for all entries and `C ≥ 0` bounds
`(∏ i ∈ s, c i) * ∏ i ∈ s, d i` for every `k`-element set `s`, then `C` bounds the `k`-th
coefficient of `det (1 - X A)`. -/
theorem norm_coeff_charpolyRev_le {A : Matrix ι ι R} {c d : ι → ℝ}
    (h : ∀ i j, ‖A i j‖ ≤ c i * d j) {k : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hs : ∀ s : Finset ι, s.card = k → (∏ i ∈ s, c i) * ∏ i ∈ s, d i ≤ C) :
    ‖A.charpolyRev.coeff k‖ ≤ C := by
  rw [coeff_charpolyRev]
  have hsum : ‖∑ s ∈ univ.powersetCard k,
      (A.submatrix (Subtype.val : s → ι) Subtype.val).det‖ ≤ C := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC fun s hs' ↦ ?_
    refine (norm_det_le_prod_mul_prod (A := A.submatrix (Subtype.val : s → ι) Subtype.val)
      fun i j ↦ h i j).trans ?_
    rw [prod_coe_sort s c, prod_coe_sort s d]
    exact hs s (mem_powersetCard.mp hs').2
  rcases neg_one_pow_eq_or R k with hk | hk <;> simpa [hk] using hsum

/-- **Coefficient bound from row bounds.** If `c i` bounds the `i`-th row of `A` and `C ≥ 0`
bounds `∏ i ∈ s, c i` for every `k`-element set `s`, then `C` bounds the `k`-th coefficient of
`det (1 - X A)`. -/
theorem norm_coeff_charpolyRev_le_of_norm_le {A : Matrix ι ι R} {c : ι → ℝ}
    (h : ∀ i j, ‖A i j‖ ≤ c i) {k : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hs : ∀ s : Finset ι, s.card = k → ∏ i ∈ s, c i ≤ C) :
    ‖A.charpolyRev.coeff k‖ ≤ C :=
  norm_coeff_charpolyRev_le (d := 1) (by simpa using h) hC (by simpa using hs)

/-- **Two-sided weighted coefficient bound.** Let `0 < σ ≤ 1` and let `w`, `w'` be integer
weights with `‖A i j‖ ≤ σ ^ (w i - w' j)`. If `m ≤ ∑ i ∈ s, (w i - w' i)` for every `k`-element
set `s`, then `‖coeff k (det (1 - X A))‖ ≤ σ ^ m`. -/
theorem norm_coeff_charpolyRev_le_zpow {A : Matrix ι ι R} {σ : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ ≤ 1)
    {w w' : ι → ℤ} (h : ∀ i j, ‖A i j‖ ≤ σ ^ (w i - w' j)) {k : ℕ} {m : ℤ}
    (hm : ∀ s : Finset ι, s.card = k → m ≤ ∑ i ∈ s, (w i - w' i)) :
    ‖A.charpolyRev.coeff k‖ ≤ σ ^ m := by
  refine norm_coeff_charpolyRev_le (c := fun i ↦ σ ^ w i) (d := fun j ↦ σ ^ (-w' j))
    (fun i j ↦ ?_) (zpow_nonneg hσ₀.le m) fun s hs ↦ ?_
  · rw [← zpow_add₀ hσ₀.ne', ← sub_eq_add_neg]
    exact h i j
  · rw [prod_zpow_eq_zpow_sum₀ s hσ₀.ne', prod_zpow_eq_zpow_sum₀ s hσ₀.ne', ← zpow_add₀ hσ₀.ne',
      ← sum_add_distrib]
    simp_rw [← sub_eq_add_neg]
    exact zpow_le_zpow_right_of_le_one₀ hσ₀ hσ₁ (hm s hs)

end Matrix
