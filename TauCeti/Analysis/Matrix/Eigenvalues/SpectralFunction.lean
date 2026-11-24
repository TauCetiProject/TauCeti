/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Values of spectral functions of Hermitian matrices

For a function `f : ℝⁿ → ℝ` the *spectral function* of `f` sends a Hermitian matrix `A` to
`f(λ(A))`, where `λ(A)` is the decreasingly sorted eigenvalue vector
`Matrix.IsHermitian.eigenvalues₀`. This file computes its values.

The sorted eigenvalue vector is determined by the characteristic polynomial: if
`A.charpoly = ∏ k, (X - μ k)`, then `λ(A)` is a rearrangement `μ ∘ σ` of `μ`, and equals `μ` when
`μ` is antitone. So a function `f` invariant under the rearrangements of `μ` takes the value `f μ`
at `λ(A)`: the eigenvalues may be listed in any order. In particular the spectral function of a
real diagonal matrix `diag μ` is `f μ`, the sum of the sorted eigenvalues is the real part of the
trace, their product is the determinant, and shifting `A` by `t • 1` shifts every sorted eigenvalue
by `t`, so that the spectral function of `μ ↦ f (μ + t)` at `A` is that of `f` at `A + t • 1`.

## Main results

* `Matrix.IsHermitian.eigenvalues₀_eq_of_charpoly_eq`: an antitone `μ` with
  `A.charpoly = ∏ k, (X - μ k)` is the sorted eigenvalue vector of `A`.
* `Matrix.IsHermitian.exists_perm_eigenvalues₀_eq_comp`: for any such `μ`, the sorted eigenvalue
  vector is a rearrangement of `μ`.
* `Matrix.IsHermitian.apply_eigenvalues₀_of_charpoly_eq`,
  `Matrix.IsHermitian.apply_eigenvalues₀_diagonal`: the value of a symmetric function at the
  sorted eigenvalues may be computed from any listing of the eigenvalues, and at `diag μ` it is
  `f μ`.
* `Matrix.IsHermitian.sum_eigenvalues₀`, `Matrix.IsHermitian.det_eq_prod_eigenvalues₀`: the
  spectral functions of the first and last elementary symmetric functions are the trace and the
  determinant.
* `Matrix.IsHermitian.eigenvalues₀_add_smul_one`,
  `Matrix.IsHermitian.apply_eigenvalues₀_add_smul_one`: the sorted eigenvalues of `A + t • 1`,
  and the spectral function of a shifted function.
-/

public section

namespace Matrix

open Polynomial

variable {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι] {A : Matrix ι ι 𝕜}

namespace IsHermitian

/-- **The characteristic polynomial determines the sorted eigenvalues.** If the characteristic
polynomial of a Hermitian matrix `A` is `∏ k, (X - μ k)` for an antitone real vector `μ`, then
`μ` is the sorted eigenvalue vector of `A`. -/
theorem eigenvalues₀_eq_of_charpoly_eq (hA : A.IsHermitian) {μ : Fin (Fintype.card ι) → ℝ}
    (hμ : Antitone μ) (h : A.charpoly = ∏ k, (X - C (μ k : 𝕜))) : hA.eigenvalues₀ = μ := by
  rw [← List.ofFn_inj, ← hA.sort_roots_charpoly_eq_eigenvalues₀, h,
    roots_prod _ _ (by simp [Finset.prod_ne_zero_iff, X_sub_C_ne_zero])]
  simp only [roots_X_sub_C, Multiset.bind_singleton, Fin.univ_val_map, Multiset.map_coe,
    List.map_ofFn, Function.comp_def, RCLike.ofReal_re, Multiset.coe_sort]
  -- Sorting the decreasing list `List.ofFn μ` returns it unchanged.
  apply List.mergeSort_of_pairwise
  simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
  exact hμ.sortedGE_ofFn

/-- **The sorted eigenvalues are a rearrangement of any listing of the eigenvalues.** If the
characteristic polynomial of a Hermitian matrix `A` is `∏ k, (X - μ k)` for a real vector `μ`,
then the sorted eigenvalue vector of `A` is `μ ∘ σ` for a permutation `σ`. -/
theorem exists_perm_eigenvalues₀_eq_comp (hA : A.IsHermitian) {μ : Fin (Fintype.card ι) → ℝ}
    (h : A.charpoly = ∏ k, (X - C (μ k : 𝕜))) :
    ∃ σ : Equiv.Perm (Fin (Fintype.card ι)), hA.eigenvalues₀ = μ ∘ σ :=
  ⟨Tuple.sortDesc μ, hA.eigenvalues₀_eq_of_charpoly_eq (Tuple.antitone_sortDesc μ) <| by
    rw [h]
    exact (Equiv.prod_comp (Tuple.sortDesc μ) fun k ↦ X - C (μ k : 𝕜)).symm⟩

/-- **Values of a spectral function from any listing of the eigenvalues.** If the characteristic
polynomial of a Hermitian matrix `A` is `∏ k, (X - μ k)` and `f` is invariant under the
rearrangements of `μ`, then `f` takes the value `f μ` at the sorted eigenvalue vector of `A`. -/
theorem apply_eigenvalues₀_of_charpoly_eq {α : Type*} (hA : A.IsHermitian)
    {μ : Fin (Fintype.card ι) → ℝ} (h : A.charpoly = ∏ k, (X - C (μ k : 𝕜)))
    {f : (Fin (Fintype.card ι) → ℝ) → α} (hf : ∀ σ : Equiv.Perm (Fin (Fintype.card ι)),
      f (μ ∘ σ) = f μ) :
    f hA.eigenvalues₀ = f μ := by
  obtain ⟨σ, hσ⟩ := hA.exists_perm_eigenvalues₀_eq_comp h
  rw [hσ, hf]

/-- **The spectral function of a real diagonal matrix.** For a real vector `d` indexed by `ι`,
listed along any equivalence `e : Fin n ≃ ι`, a function `f` invariant under the rearrangements of
`d ∘ e` takes the value `f (d ∘ e)` at the sorted eigenvalue vector of `diagonal d`. -/
theorem apply_eigenvalues₀_diagonal {α : Type*} {d : ι → ℝ}
    (hd : (diagonal fun i ↦ (d i : 𝕜)).IsHermitian) (e : Fin (Fintype.card ι) ≃ ι)
    {f : (Fin (Fintype.card ι) → ℝ) → α}
    (hf : ∀ σ : Equiv.Perm (Fin (Fintype.card ι)), f (d ∘ e ∘ σ) = f (d ∘ e)) :
    f hd.eigenvalues₀ = f (d ∘ e) :=
  hd.apply_eigenvalues₀_of_charpoly_eq (by
    rw [charpoly_diagonal]
    exact (Equiv.prod_comp e fun i ↦ X - C (d i : 𝕜)).symm) hf

/-- **The trace is the spectral function of the sum**: the sorted eigenvalues of a Hermitian
matrix sum to the real part of its trace. -/
theorem sum_eigenvalues₀ (hA : A.IsHermitian) : ∑ k, hA.eigenvalues₀ k = RCLike.re A.trace := by
  rw [hA.trace_eq_sum_eigenvalues, map_sum]
  simp only [RCLike.ofReal_re, IsHermitian.eigenvalues]
  exact (Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin _)).symm hA.eigenvalues₀).symm

/-- **The determinant is the spectral function of the product**: the determinant of a Hermitian
matrix is the product of its sorted eigenvalues. -/
theorem det_eq_prod_eigenvalues₀ (hA : A.IsHermitian) :
    A.det = ∏ k, (hA.eigenvalues₀ k : 𝕜) := by
  rw [hA.det_eq_prod_eigenvalues]
  simp only [IsHermitian.eigenvalues]
  exact Equiv.prod_comp (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
    fun k ↦ (hA.eigenvalues₀ k : 𝕜)

/-- The characteristic polynomial of a Hermitian matrix is `∏ k, (X - λ k)` over its sorted
eigenvalues `λ`. -/
theorem charpoly_eq_prod_eigenvalues₀ (hA : A.IsHermitian) :
    A.charpoly = ∏ k, (X - C (hA.eigenvalues₀ k : 𝕜)) := by
  rw [hA.charpoly_eq]
  simp only [IsHermitian.eigenvalues]
  exact Equiv.prod_comp (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
    fun k ↦ X - C (hA.eigenvalues₀ k : 𝕜)

/-- **Scalar shifts.** The sorted eigenvalues of `A + t • 1` are those of `A` shifted by `t`. -/
theorem eigenvalues₀_add_smul_one (hA : A.IsHermitian) (t : ℝ)
    (hAt : (A + t • (1 : Matrix ι ι 𝕜)).IsHermitian) :
    hAt.eigenvalues₀ = hA.eigenvalues₀ + fun _ ↦ t := by
  refine hAt.eigenvalues₀_eq_of_charpoly_eq
    (hA.eigenvalues₀_antitone.add_const t) ?_
  have hshift : A + t • (1 : Matrix ι ι 𝕜) = A - scalar ι (-(t : 𝕜)) := by
    ext i j
    by_cases hij : i = j <;> simp [hij, scalar_apply, RCLike.real_smul_eq_coe_mul]
  rw [hshift, charpoly_sub_scalar, hA.charpoly_eq_prod_eigenvalues₀, prod_comp]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  simp only [sub_comp, X_comp, C_comp, Pi.add_apply, RCLike.ofReal_add, C_add, map_neg]
  ring

/-- **Spectral functions under scalar shifts.** For `g μ = f (μ + t)`, the spectral function of `g`
at `A` is the spectral function of `f` at `A + t • 1`. -/
theorem apply_eigenvalues₀_add_smul_one {α : Type*} (hA : A.IsHermitian) (t : ℝ)
    (hAt : (A + t • (1 : Matrix ι ι 𝕜)).IsHermitian) (f : (Fin (Fintype.card ι) → ℝ) → α) :
    f (hA.eigenvalues₀ + fun _ ↦ t) = f hAt.eigenvalues₀ := by
  rw [hA.eigenvalues₀_add_smul_one t hAt]

end IsHermitian

end Matrix
