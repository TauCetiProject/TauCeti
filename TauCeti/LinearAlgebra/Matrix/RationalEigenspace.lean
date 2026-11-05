/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Rational eigenspaces after scalar extension

For a matrix `M` over a commutative `k`-algebra `Q`, `rationalEigenspace` consists of the vectors
over `k` that become eigenvectors of `M` after scalar extension to `Q`: it is the preimage of the
eigenspace `Module.End.eigenspace M.mulVecLin s` under `k^n → Q^n`. If `M` is diagonalized by an
invertible matrix over `k`, these eigenspaces span `k^n`.

## Main declarations

* `Matrix.rationalEigenspace`: the subspace of rational eigenvectors.
* `Matrix.mem_rationalEigenspace`: its membership criterion after scalar extension.
* `Matrix.iSup_rationalEigenspace_eq_top`: spanning under rational diagonalization.
-/

public section

namespace Matrix

variable {k Q : Type*} [CommRing Q]

section CommSemiring

variable [CommSemiring k] [Algebra k Q]

/-- The `k`-subspace of rational vectors which the matrix `M` over `Q` scales by `s`: the preimage
of the `s`-eigenspace of `M` under scalar extension `k^n → Q^n`. -/
def rationalEigenspace {n : Type*} [Fintype n] (M : Matrix n n Q) (s : Q) :
    Submodule k (n → k) :=
  ((Module.End.eigenspace M.mulVecLin s).restrictScalars k).comap
    (LinearMap.compLeft (Algebra.linearMap k Q) n)

/-- Membership in a rational eigenspace is the eigenvector equation after scalar extension. -/
@[simp]
theorem mem_rationalEigenspace {n : Type*} [Fintype n] {M : Matrix n n Q} {s : Q}
    {v : n → k} :
    v ∈ rationalEigenspace (k := k) M s ↔
      M *ᵥ (algebraMap k Q ∘ v) = s • (algebraMap k Q ∘ v) := by
  simp [rationalEigenspace, LinearMap.compLeft, Function.comp_def]

end CommSemiring

variable [CommRing k] [Algebra k Q]

/-- If `P₀` diagonalizes `M` with eigenvalues in the image of `e`, the corresponding rational
eigenspaces span because they contain the columns of `P₀`. -/
theorem iSup_rationalEigenspace_eq_top {n ι : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n Q} {P₀ : Matrix n n k} (hP₀ : IsUnit P₀) (e : ι → Q) {t : n → ι}
    (h : M * P₀.map (algebraMap k Q) = P₀.map (algebraMap k Q) * diagonal fun i ↦ e (t i)) :
    ⨆ s, rationalEigenspace (k := k) M (e s) = ⊤ := by
  have hcol (j : n) : P₀.col j ∈ rationalEigenspace (k := k) M (e (t j)) := by
    rw [mem_rationalEigenspace, ← col_map, ← col_mul_eq_mulVec_col, h]
    ext i
    simp [mul_comm]
  have hspan : Submodule.span k (Set.range P₀.col) = ⊤ := by
    rw [← range_mulVecLin, LinearMap.range_eq_top]
    exact mulVec_surjective_iff_isUnit.2 hP₀
  rw [eq_top_iff, ← hspan, Submodule.span_le, Set.range_subset_iff]
  exact fun j ↦ Submodule.mem_iSup_of_mem (t j) (hcol j)

end Matrix
