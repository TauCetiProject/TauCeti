/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.BigOperators.ZPow
public import TauCeti.Analysis.Normed.Ring.Ultra
public import TauCeti.Analysis.Polynomial.Ultra
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

Over a normed field, with no ultrametric assumption, a principal minor whose rows are rescaled by
nonzero `(d i)⁻¹` to a minor of norm one has norm exactly `∏ i ∈ s, ‖d i‖`
(`Matrix.norm_principalMinor_eq_prod`).

Two-sided entry bounds also control each principal minor by the product of the diagonal
factors `c i * d i` (`Matrix.norm_principalMinor_le_prod_mul`).
The two-sided form `‖A i j‖ ≤ σ ^ (w i - w' j)`, with integer weights `w`, `w'` and
`0 < σ ≤ 1`, bounds each principal minor by `σ ^ (∑ i ∈ s, (w i - w' i))`
(`Matrix.norm_principalMinor_le_zpow`) and the `k`-th coefficient by `σ ^ m` whenever `m` is a
lower bound for the sums
`∑ i ∈ s, (w i - w' i)` over the `k`-element sets `s` (`Matrix.norm_coeff_charpolyRev_le_zpow`).
The bound depends only on the differences `w i - w' i` along the diagonal, although the entry
bounds compare a row weight with an unrelated column weight.

## Main results

* `Matrix.norm_det_le_prod_mul_prod`, `Matrix.norm_det_le_prod_of_norm_le`,
  `Matrix.norm_principalMinor_le`, `Matrix.norm_principalMinor_le_prod_mul`,
  `Matrix.norm_principalMinor_le_zpow`: determinant and principal-minor bounds.
* `Matrix.norm_principalMinor_eq_prod`: the exact norm of a principal minor from a normalised
  minor of norm one.
* `TauCeti.norm_coeff_charpolyRev_le_of_principalMinor_le`,
  `Matrix.norm_coeff_charpolyRev_le`, `Matrix.norm_coeff_charpolyRev_le_of_norm_le`,
  `Matrix.norm_coeff_charpolyRev_le_zpow`: coefficient bounds for `det (1 - X A)`.
* `Matrix.norm_coeff_det_le_of_natDegree_le_one`: the same bounds for the coefficients of
  determinants of polynomials of degree at most one, from the product bound
  `TauCeti.norm_coeff_prod_le_of_natDegree_le_one`.
* `Matrix.norm_sum_coeff_charpolyRev_smul_pow_apply_le`: the entries of the coefficients of the
  Fredholm resolvent `adjugate (1 - X A)` obey the row-bound estimate of `det (1 - X A)`.
* `TauCeti.norm_det_sub_le`, `TauCeti.norm_principalMinor_sub_le`: perturbation bounds on
  entrywise bounded sets, also over seminormed rings.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §§4–5.
* K. S. Kedlaya, *A little p-adic numerical analysis*, MIT 18.787 notes (2007), §3.
-/

public section

open Equiv Finset Polynomial

namespace TauCeti

/-- A common nonnegative bound on the size-`k` principal minors bounds the `k`-th
coefficient of `det (1 - X A)` over an ultrametric seminormed commutative ring. -/
theorem norm_coeff_charpolyRev_le_of_principalMinor_le {ι R : Type*}
    [Fintype ι] [DecidableEq ι] [SeminormedCommRing R] [IsUltrametricDist R]
    {A : Matrix ι ι R} {k : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hs : ∀ s : Finset ι, s.card = k → ‖A.principalMinor s‖ ≤ C) :
    ‖A.charpolyRev.coeff k‖ ≤ C := by
  rw [Matrix.coeff_charpolyRev]
  have hsum : ‖∑ s ∈ univ.powersetCard k,
      (A.submatrix (Subtype.val : s → ι) Subtype.val).det‖ ≤ C := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC fun s hs' ↦ ?_
    simpa only [Matrix.principalMinor_def] using hs s (mem_powersetCard.mp hs').2
  rcases neg_one_pow_eq_or R k with hk | hk <;> simpa [hk] using hsum

end TauCeti

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

omit [Fintype ι] in
/-- Two-sided entry bounds bound each principal minor by the product of their diagonal
products. Neither factor separately needs to be bounded. -/
theorem norm_principalMinor_le_prod_mul {A : Matrix ι ι R} {c d : ι → ℝ}
    (hA : ∀ i j, ‖A i j‖ ≤ c i * d j) (s : Finset ι) :
    ‖A.principalMinor s‖ ≤ ∏ i ∈ s, c i * d i := by
  rw [principalMinor_def, prod_mul_distrib, ← prod_coe_sort s c, ← prod_coe_sort s d]
  exact norm_det_le_prod_mul_prod fun i j ↦ hA i j

omit [Fintype ι] in
/-- An integer two-sided weight bound controls a principal minor by the sum of the
weight differences on its index set, including negative differences. -/
theorem norm_principalMinor_le_zpow {A : Matrix ι ι R} {σ : ℝ} (hσ : 0 < σ)
    {w w' : ι → ℤ} (hA : ∀ i j, ‖A i j‖ ≤ σ ^ (w i - w' j)) (s : Finset ι) :
    ‖A.principalMinor s‖ ≤ σ ^ (∑ i ∈ s, (w i - w' i)) := by
  have h (i j : ι) : ‖A i j‖ ≤ σ ^ w i * σ ^ (-w' j) := by
    simpa only [← zpow_add₀ hσ.ne', sub_eq_add_neg] using hA i j
  simpa only [← zpow_add₀ hσ.ne', ← sub_eq_add_neg,
    prod_zpow_eq_zpow_sum₀ s hσ.ne'] using norm_principalMinor_le_prod_mul h s

/-- **Coefficient bound.** If `‖A i j‖ ≤ c i * d j` for all entries and `C ≥ 0` bounds
`(∏ i ∈ s, c i) * ∏ i ∈ s, d i` for every `k`-element set `s`, then `C` bounds the `k`-th
coefficient of `det (1 - X A)`. -/
theorem norm_coeff_charpolyRev_le {A : Matrix ι ι R} {c d : ι → ℝ}
    (h : ∀ i j, ‖A i j‖ ≤ c i * d j) {k : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hs : ∀ s : Finset ι, s.card = k → (∏ i ∈ s, c i) * ∏ i ∈ s, d i ≤ C) :
    ‖A.charpolyRev.coeff k‖ ≤ C := by
  refine TauCeti.norm_coeff_charpolyRev_le_of_principalMinor_le hC fun s hs' ↦ ?_
  exact (norm_principalMinor_le_prod_mul h s).trans
    (by simpa only [prod_mul_distrib] using hs s hs')

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
    ‖A.charpolyRev.coeff k‖ ≤ σ ^ m :=
  TauCeti.norm_coeff_charpolyRev_le_of_principalMinor_le (zpow_nonneg hσ₀.le m) fun s hs ↦
    (norm_principalMinor_le_zpow hσ₀ h s).trans
      (zpow_le_zpow_right_of_le_one₀ hσ₀ hσ₁ (hm s hs))

/-- **Coefficients of a determinant of linear polynomials.** Over an ultrametric normed ring
with `‖1‖ = 1`, let `M` be a matrix of polynomials of degree at most one whose constant
coefficients have norm at most one and whose linear coefficients in row `i` have norm at most
`r i`. If `c ≥ 0` bounds `∏ i ∈ s, r i` for every `m`-element set `s`, then `c` bounds the
`m`-th coefficient of `det M`. -/
theorem norm_coeff_det_le_of_natDegree_le_one {M : Matrix ι ι R[X]} {r : ι → ℝ}
    (hdeg : ∀ i j, (M i j).natDegree ≤ 1) (h₀ : ∀ i j, ‖(M i j).coeff 0‖ ≤ 1)
    (h₁ : ∀ i j, ‖(M i j).coeff 1‖ ≤ r i) {m : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (hs : ∀ s : Finset ι, s.card = m → ∏ i ∈ s, r i ≤ c) :
    ‖M.det.coeff m‖ ≤ c := by
  rw [det_apply, finsetSum_coeff]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hc fun σ _ ↦ ?_
  rw [coeff_smul, norm_units_zsmul]
  refine TauCeti.norm_coeff_prod_le_of_natDegree_le_one (fun i _ ↦ hdeg _ _) (fun i _ ↦ h₀ _ _)
    (fun i _ ↦ h₁ _ _) hc fun t _ ht ↦ ?_
  simpa only [prod_map, Equiv.coe_toEmbedding] using
    hs (t.map σ.toEmbedding) (by rw [card_map, ht])

/-- **Fredholm resolvent bound.** If `r i` bounds the `i`-th row of `A` and `c ≥ 0` bounds
`∏ i ∈ s, r i` for every `m`-element set `s`, then `c` bounds every entry of the `m`-th
coefficient `∑ k ∈ range (m + 1), c k • A ^ (m - k)` of `adjugate (1 - X A)`, where `c k` are
the coefficients of `det (1 - X A)`. This is the same bound as for the `m`-th coefficient of
`det (1 - X A)` itself (`Matrix.norm_coeff_charpolyRev_le_of_norm_le`). -/
theorem norm_sum_coeff_charpolyRev_smul_pow_apply_le {A : Matrix ι ι R} {r : ι → ℝ}
    (hA : ∀ i j, ‖A i j‖ ≤ r i) {m : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (hs : ∀ s : Finset ι, s.card = m → ∏ i ∈ s, r i ≤ c) (i j : ι) :
    ‖(∑ k ∈ range (m + 1), A.charpolyRev.coeff k • A ^ (m - k)) i j‖ ≤ c := by
  rw [← coeff_adjugate_one_sub_X_smul_apply, adjugate_apply]
  -- Row `j` of the matrix is constant, and every other row `k` is `δ k - X A k`.
  have hM : ∀ k l, updateRow (1 - (X : R[X]) • A.map C) j (Pi.single i 1) k l =
      if k = j then (if l = i then 1 else 0) else (if k = l then 1 else 0) - X * C (A k l) := by
    intro k l
    rcases eq_or_ne k j with rfl | hk
    · rw [updateRow_self, Pi.single_apply, ite_eq_left rfl]
    · rw [updateRow_ne hk, sub_apply, one_apply, smul_apply, map_apply, smul_eq_mul,
        ite_eq_right hk]
  refine norm_coeff_det_le_of_natDegree_le_one (r := r) (fun k l ↦ ?_) (fun k l ↦ ?_)
    (fun k l ↦ ?_) hc hs <;> rw [hM]
  · split_ifs <;> compute_degree!
  · split_ifs <;> simp
  · split_ifs <;> simp [coeff_one, (norm_nonneg _).trans (hA k l), hA k l]

section NormedField

variable {K : Type*} [NormedField K]

/-- **Minors of a normalised matrix.** If the matrix with entries `(d i)⁻¹ * A i j` has a principal
minor of norm one on `s`, and the `d i` with `i ∈ s` are nonzero, then the principal minor of `A`
on `s` has norm `∏ i ∈ s, ‖d i‖`. -/
theorem norm_principalMinor_eq_prod {ι : Type*} [DecidableEq ι] {A : Matrix ι ι K} {d : ι → K}
    {s : Finset ι} (hd : ∀ i ∈ s, d i ≠ 0)
    (hminor : ‖(of fun i j ↦ (d i)⁻¹ * A i j).principalMinor s‖ = 1) :
    ‖A.principalMinor s‖ = ∏ i ∈ s, ‖d i‖ := by
  -- On `s` the matrix `A` is the normalised matrix with row `i` scaled back by `d i`.
  have hA : (of fun i j ↦ d i * (of fun i j ↦ (d i)⁻¹ * A i j) i j).principalMinor s =
      A.principalMinor s := by
    rw [principalMinor_def, principalMinor_def]
    congr 1
    ext i j
    simp [mul_inv_cancel_left₀ (hd i i.2)]
  rw [← hA, principalMinor_mul_column, norm_mul, hminor, mul_one, norm_prod]

end NormedField

end Matrix

namespace TauCeti

/-- Determinants over an ultrametric normed ring are Lipschitz on entrywise bounded sets,
with constant `M ^ (Fintype.card ι - 1)` and no factorial loss. This includes empty matrices. -/
theorem norm_det_sub_le {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [SeminormedCommRing R] [NormOneClass R] [IsUltrametricDist R]
    {A B : Matrix ι ι R} {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 ≤ ε)
    (hA : ∀ i j, ‖A i j‖ ≤ M) (hB : ∀ i j, ‖B i j‖ ≤ M)
    (hAB : ∀ i j, ‖A i j - B i j‖ ≤ ε) :
    ‖A.det - B.det‖ ≤ ε * M ^ (Fintype.card ι - 1) := by
  simp only [Matrix.det_apply, ← Finset.sum_sub_distrib, ← smul_sub]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun σ _ ↦ ?_
  rw [norm_units_zsmul]
  simpa using norm_prod_sub_prod_le (s := Finset.univ) hM hε
    (fun i _ ↦ hA (σ i) i) (fun i _ ↦ hB (σ i) i) (fun i _ ↦ hAB (σ i) i)

/-- Principal minors are Lipschitz on entrywise bounded sets, independently of the choice of
indices. The empty principal minors are both one, so the estimate also includes `s = ∅`. -/
theorem norm_principalMinor_sub_le {ι R : Type*} [DecidableEq ι]
    [SeminormedCommRing R] [NormOneClass R] [IsUltrametricDist R]
    {A B : Matrix ι ι R} {M ε : ℝ} {s : Finset ι}
    (hM : 0 ≤ M) (hε : 0 ≤ ε) (hA : ∀ i j, ‖A i j‖ ≤ M) (hB : ∀ i j, ‖B i j‖ ≤ M)
    (hAB : ∀ i j, ‖A i j - B i j‖ ≤ ε) :
    ‖A.principalMinor s - B.principalMinor s‖ ≤ ε * M ^ (s.card - 1) := by
  simp only [Matrix.principalMinor_def, ← Fintype.card_coe]
  exact norm_det_sub_le hM hε (fun i j ↦ hA i j) (fun i j ↦ hB i j)
    (fun i j ↦ hAB i j)

end TauCeti
