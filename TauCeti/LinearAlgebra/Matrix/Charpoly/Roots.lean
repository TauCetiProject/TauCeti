/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Multiset.Fintype
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

/-!
# Characteristic roots of matrices

Over any field, if `p(A)` is invertible then `p` does not vanish at any characteristic root of `A`.

Over an algebraically closed field, the characteristic polynomial of a square matrix of positive
size has a root. This file records that fact as a `Nonempty` instance on the root multiset, so that
families indexed by the characteristic roots, counted with algebraic multiplicity, have a nonempty
index type.

It also records the determinant form of the spectral mapping theorem: for a polynomial `p`, the
determinant of `p(A)` is the product of `p(λ)` over the characteristic roots `λ` of `A`, counted
with algebraic multiplicity. Mathlib's `Matrix.det_eq_prod_roots_charpoly` is the case `p = X`.

## Main results

* `Matrix.eval_ne_zero_of_det_aeval_ne_zero`: if `det (p(A)) ≠ 0`, then `p(λ) ≠ 0` for every
  characteristic root `λ` of `A`.
* `Matrix.nonempty_roots_charpoly` — a square matrix of positive size over an algebraically closed
  field has a characteristic root.
* `Matrix.det_aeval_eq_prod_roots_charpoly`: `det (p(A)) = ∏ p(λ)` over the characteristic roots
  `λ` of `A`.
-/

public section

open Polynomial

namespace Matrix

/-- If `det (p(A)) ≠ 0` for a square matrix `A` over a field, then `p` does not vanish at any
characteristic root of `A`: by spectral mapping, `p(λ)` is in the spectrum of `p(A)`. -/
theorem eval_ne_zero_of_det_aeval_ne_zero {n K : Type*} [Fintype n] [DecidableEq n] [Field K]
    (A : Matrix n n K) (p : K[X]) (h : (aeval A p).det ≠ 0) {x : K} (hx : x ∈ A.charpoly.roots) :
    p.eval x ≠ 0 := by
  intro hx0
  have hmem : p.eval x ∈ spectrum K (aeval A p) := spectrum.subset_polynomial_aeval A p
    ⟨x, mem_spectrum_iff_isRoot_charpoly.2 (isRoot_of_mem_roots hx), rfl⟩
  rw [hx0, spectrum.zero_mem_iff, isUnit_iff_isUnit_det] at hmem
  exact hmem (isUnit_iff_ne_zero.2 h)

variable {n K : Type*} [Fintype n] [DecidableEq n] [Nonempty n] [Field K] [IsAlgClosed K]
  [DecidableEq K]

/-- A square matrix of positive size over an algebraically closed field has a characteristic
root. -/
instance nonempty_roots_charpoly (A : Matrix n n K) : Nonempty A.charpoly.roots := by
  rw [← Fintype.card_pos_iff, Multiset.card_coe, IsAlgClosed.card_roots_eq_natDegree,
    charpoly_natDegree_eq_dim]
  exact Fintype.card_pos

omit [Nonempty n] [DecidableEq K] in
/-- **Spectral mapping for determinants.** Over an algebraically closed field, the determinant of
`p(A)` is the product of `p(λ)` over the characteristic roots `λ` of `A`, counted with algebraic
multiplicity. -/
theorem det_aeval_eq_prod_roots_charpoly (A : Matrix n n K) (p : K[X]) :
    (aeval A p).det = (A.charpoly.roots.map p.eval).prod := by
  have hcard : A.charpoly.roots.card = Fintype.card n := by
    rw [IsAlgClosed.card_roots_eq_natDegree, charpoly_natDegree_eq_dim]
  -- `q ↦ det (aeval A q)` is multiplicative, and its source `K[X]` is commutative.
  let φ : K[X] →* K := detMonoidHom.comp (aeval (R := K) A).toMonoidHom
  have hφ (q : K[X]) : φ q = (aeval A q).det := (rfl)
  -- The linear factors: `det (A - μ) = ∏_λ (λ - μ)`.
  have hlin (μ : K) : φ (X - C μ) = (A.charpoly.roots.map (· - μ)).prod := by
    -- `X - C μ` evaluates at `A` to `-(μ - A)`, whose determinant is `(-1) ^ n χ_A(μ)`.
    have hscalar : aeval A (X - C μ) = -(scalar n μ - A) := by
      simp [Algebra.algebraMap_eq_smul_one, smul_one_eq_diagonal]
    have hneg : (A.charpoly.roots.map (· - μ)).prod =
        (-1) ^ A.charpoly.roots.card * (A.charpoly.roots.map (μ - ·)).prod := by
      simpa [Function.comp_def] using Multiset.prod_map_neg (A.charpoly.roots.map (μ - ·))
    rw [hφ, hscalar, det_neg, ← eval_charpoly,
      (IsAlgClosed.splits _).eval_eq_prod_roots_of_monic (charpoly_monic A), hneg, hcard]
  -- Factor `p = c ∏_μ (X - μ)` and compare both sides as `c ^ n ∏_λ ∏_μ (λ - μ)`.
  conv_lhs => rw [← hφ, (IsAlgClosed.splits p).eq_prod_roots, map_mul, map_multiset_prod,
    Multiset.map_map]
  simp only [Function.comp_def, hlin, (IsAlgClosed.splits p).eval_eq_prod_roots,
    Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, hcard, hφ, aeval_C,
    Algebra.algebraMap_eq_smul_one, det_smul, det_one, mul_one]
  rw [Multiset.prod_map_prod_map]

end Matrix
