/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Eigenvalues.Basic

/-!
# Values of spectral functions of Hermitian matrices

For a function `f : ℝⁿ → ℝ` the *spectral function* of `f` sends a Hermitian matrix `A` to
`f(λ(A))`, where `λ(A)` is the decreasingly sorted eigenvalue vector
`Matrix.IsHermitian.eigenvalues₀`. This file computes its values.

The sorted eigenvalue vector is determined by the characteristic polynomial: if
`A.charpoly = ∏ k, (X - μ k)`, then `λ(A)` is a rearrangement `μ ∘ σ` of `μ`, and equals `μ` when
`μ` is antitone (`Matrix.IsHermitian.eigenvalues₀_eq_of_charpoly_eq`). So a function `f`
invariant under the rearrangements of `μ` takes the value `f μ` at `λ(A)`: the eigenvalues may
be listed in any order. In particular the spectral function of a real diagonal matrix `diag μ` is
`f μ`.

The general facts about sorted eigenvalues that spectral functions build on live in
`TauCeti.Analysis.Matrix.Eigenvalues.Basic`: the sum of the sorted eigenvalues is the real part of
the trace (`Matrix.IsHermitian.sum_eigenvalues₀_eq_re_trace`), their product is the determinant
(`Matrix.IsHermitian.det_eq_prod_eigenvalues₀`), and shifting `A` by `t • 1` shifts every sorted
eigenvalue by `t` (`Matrix.IsHermitian.eigenvalues₀_add_smul_one`), so that the spectral function
of `μ ↦ f (μ + t)` at `A` is that of `f` at `A + t • 1`.

## Main results

* `Matrix.IsHermitian.exists_perm_eigenvalues₀_eq_comp`: if `A.charpoly = ∏ k, (X - μ k)`, the
  sorted eigenvalue vector is a rearrangement of `μ`.
* `Matrix.IsHermitian.apply_eigenvalues₀_of_charpoly_eq`,
  `Matrix.IsHermitian.apply_eigenvalues₀_diagonal`: the value of a symmetric function at the
  sorted eigenvalues may be computed from any listing of the eigenvalues, and at `diag μ` it is
  `f μ`.
-/

public section

namespace Matrix

open Polynomial

variable {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι] {A : Matrix ι ι 𝕜}

namespace IsHermitian

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

end IsHermitian

end Matrix
