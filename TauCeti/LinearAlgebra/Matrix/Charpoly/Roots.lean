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
import TauCeti.Algebra.Polynomial.Reverse
import TauCeti.LinearAlgebra.Matrix.Charpoly.Resultant

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

More generally, over an integral domain, when the characteristic polynomial of `A` splits, the
characteristic roots of `p(A)` are the values `p(λ)` at the characteristic roots `λ` of `A`,
counted with algebraic multiplicity. So the determinant of `p(A)` is the product of the `p(λ)`
and its trace is their sum; Mathlib's `Matrix.det_eq_prod_roots_charpoly_of_splits` and
`Matrix.trace_eq_sum_roots_charpoly_of_splits` are the case `p = X`. These are proved by
evaluating the resultant formulas `Matrix.det_aeval_eq_resultant` and
`Matrix.charpoly_aeval_eq_resultant` over the split characteristic polynomial. In particular
`det (1 - X A)`, the reverse of `χ_A = ∏ (X - λ)`, factors as `∏ (1 - λ X)`.

## Main results

* `Matrix.eval_ne_zero_of_det_aeval_ne_zero`: if `det (p(A)) ≠ 0`, then `p(λ) ≠ 0` for every
  characteristic root `λ` of `A`.
* `Matrix.nonempty_roots_charpoly` — a square matrix of positive size over an algebraically closed
  field has a characteristic root.
* `Matrix.charpoly_roots_filter_ne_zero_mul_eq` — the nonzero characteristic roots of rectangular
  products `A * B` and `B * A` agree, counted with multiplicity.
* `Matrix.det_aeval_eq_prod_roots_charpoly`: `det (p(A)) = ∏ p(λ)` over the characteristic roots
  `λ` of `A`.
* `Matrix.det_aeval_eq_prod_roots_charpoly_of_splits`: the same when the characteristic
  polynomial of `A` splits.
* `Matrix.charpoly_aeval_eq_prod_roots_charpoly_of_splits`: the characteristic polynomial of
  `p(A)` is `∏ (X - p(λ))`.
* `Matrix.trace_aeval_eq_sum_roots_charpoly_of_splits`: `tr (p(A)) = ∑ p(λ)`; for `p = X ^ k` the
  trace of `A ^ k` is the `k`-th power sum of the characteristic roots.
* `Matrix.charpolyRev_eq_prod_roots_charpoly_of_splits`: `det (1 - X A) = ∏ (1 - λ X)`.
-/

public section

open Polynomial

namespace Matrix

section RectangularProducts

variable {m n K : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
  [CommRing K] [IsDomain K]

/-- Rectangular products `A * B` and `B * A` have the same nonzero characteristic roots,
counted with algebraic multiplicity. -/
theorem charpoly_roots_filter_ne_zero_mul_eq (A : Matrix m n K) (B : Matrix n m K) :
    letI : DecidableEq K := Classical.decEq K
    Multiset.filter (fun z : K => z ≠ 0) (A * B).charpoly.roots =
      Multiset.filter (fun z : K => z ≠ 0) (B * A).charpoly.roots := by
  classical
  have hA_ne : (A * B).charpoly ≠ (0 : Polynomial K) :=
    (Matrix.charpoly_monic _).ne_zero
  have hB_ne : (B * A).charpoly ≠ (0 : Polynomial K) :=
    (Matrix.charpoly_monic _).ne_zero
  have hroots := congrArg Polynomial.roots (Matrix.charpoly_mul_comm' A B)
  rw [Polynomial.roots_mul
        (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) hA_ne),
      Polynomial.roots_mul
        (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) hB_ne),
      Polynomial.roots_X_pow, Polynomial.roots_X_pow] at hroots
  have hroots_nonzero :=
    congrArg (Multiset.filter (fun z : K => z ≠ 0)) hroots
  simpa only [Multiset.filter_add, Multiset.filter_nsmul, Multiset.filter_singleton,
    ne_eq, not_true_eq_false, ite_false, Multiset.empty_eq_zero, nsmul_zero, zero_add] using
    hroots_nonzero

end RectangularProducts
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

section Splits

variable {n K : Type*} [Fintype n] [DecidableEq n] [CommRing K] [IsDomain K] {A : Matrix n n K}

/-- **Spectral mapping for determinants.** If the characteristic polynomial of `A` splits, the
determinant of `p(A)` is the product of `p(λ)` over the characteristic roots `λ` of `A`, counted
with algebraic multiplicity. -/
theorem det_aeval_eq_prod_roots_charpoly_of_splits (hA : A.charpoly.Splits) (p : K[X]) :
    (aeval A p).det = (A.charpoly.roots.map p.eval).prod := by
  -- `det p(A) = Res(χ_A, p)`, which is `∏ p(λ)` as `χ_A` is monic and splits.
  rw [det_aeval_eq_resultant A p le_rfl, ← charpoly_natDegree_eq_dim A,
    resultant_eq_prod_eval _ _ _ le_rfl hA, (charpoly_monic A).leadingCoeff, one_pow, one_mul]

/-- **Spectral mapping for characteristic polynomials.** If the characteristic polynomial of `A`
splits, the characteristic polynomial of `p(A)` is `∏ (X - p(λ))` over the characteristic roots
`λ` of `A`, counted with algebraic multiplicity. -/
theorem charpoly_aeval_eq_prod_roots_charpoly_of_splits (hA : A.charpoly.Splits) (p : K[X]) :
    (aeval A p).charpoly = (A.charpoly.roots.map fun μ ↦ X - C (p.eval μ)).prod := by
  -- `χ_{p(A)}(T) = Res_X(χ_A(X), T - p(X))`, which is `∏ (T - p(λ))` as `χ_A` splits.
  have hm := (charpoly_monic A).map (C : K →+* K[X])
  have hdeg : (C X - p.map C).natDegree ≤ p.natDegree :=
    (natDegree_sub_le _ _).trans (max_le (by simp) natDegree_map_le)
  rw [charpoly_aeval_eq_resultant A p le_rfl, ← charpoly_natDegree_eq_dim A,
    ← (charpoly_monic A).natDegree_map C, resultant_eq_prod_eval _ _ _ hdeg (hA.map C),
    hm.leadingCoeff, one_pow, one_mul, hA.roots_map_of_injective C_injective]
  simp [Multiset.map_map, eval_map]

/-- **Spectral mapping for traces.** If the characteristic polynomial of `A` splits, the trace of
`p(A)` is the sum of `p(λ)` over the characteristic roots `λ` of `A`, counted with algebraic
multiplicity. -/
theorem trace_aeval_eq_sum_roots_charpoly_of_splits (hA : A.charpoly.Splits) (p : K[X]) :
    (aeval A p).trace = (A.charpoly.roots.map p.eval).sum := by
  have hp := charpoly_aeval_eq_prod_roots_charpoly_of_splits hA p
  have hs : (aeval A p).charpoly.Splits := hp ▸ Splits.multisetProd fun f hf ↦ by
    obtain ⟨μ, -, rfl⟩ := Multiset.mem_map.1 hf
    exact Splits.X_sub_C _
  rw [trace_eq_sum_roots_charpoly_of_splits hs, hp]
  simpa [Multiset.map_map, Function.comp_def] using
    congrArg Multiset.sum (roots_multiset_prod_X_sub_C (A.charpoly.roots.map p.eval))

/-- If the characteristic polynomial of `A` splits, `det (1 - X A)` is the product of the linear
factors `1 - λ X` over the characteristic roots `λ` of `A`, counted with algebraic
multiplicity. -/
theorem charpolyRev_eq_prod_roots_charpoly_of_splits (hA : A.charpoly.Splits) :
    A.charpolyRev = (A.charpoly.roots.map fun μ ↦ 1 - C μ * X).prod := by
  -- `det (1 - X A)` is the reverse of `χ_A = ∏ (X - λ)`, and reversal is multiplicative.
  rw [← reverse_charpoly, hA.eq_prod_roots_of_monic A.charpoly_monic,
    reverse_multiset_prod_of_monic fun q hq ↦ by
      obtain ⟨μ, -, rfl⟩ := Multiset.mem_map.1 hq
      exact monic_X_sub_C μ,
    Multiset.map_map, roots_multiset_prod_X_sub_C]
  simpa using congrArg Multiset.prod (Multiset.map_congr rfl fun μ _ ↦ by
    simpa using reverse_X_pow_sub_C 1 μ)

end Splits

section IsAlgClosed

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
    (aeval A p).det = (A.charpoly.roots.map p.eval).prod :=
  det_aeval_eq_prod_roots_charpoly_of_splits (IsAlgClosed.splits _) p

end IsAlgClosed

end Matrix
