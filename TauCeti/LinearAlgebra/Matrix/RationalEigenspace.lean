/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Rational eigenspaces after scalar extension

For a matrix over a commutative algebra `Q` over a field `k`, `rationalEigenspace` consists of
vectors over `k` that become eigenvectors after scalar extension to `Q`. If a matrix is
diagonalized over `k`, these eigenspaces span the vector space over `k`.

## Main declarations

* `TauCeti.rationalEigenspace`: the subspace of rational eigenvectors.
* `TauCeti.mem_rationalEigenspace`: its membership criterion after scalar extension.
* `TauCeti.iSup_rationalEigenspace_eq_top`: spanning under rational diagonalization.
-/

public section

open Matrix

namespace TauCeti

variable {k Q : Type*} [Field k] [CommRing Q] [Algebra k Q]

/-- The `k`-subspace of rational vectors which the matrix `M` over `Q` scales by `s`. -/
def rationalEigenspace {n : Type*} [Fintype n] (M : Matrix n n Q) (s : Q) :
    Submodule k (n → k) :=
  LinearMap.ker (((M.mulVecLin - s • LinearMap.id).restrictScalars k) ∘ₗ
    LinearMap.compLeft (Algebra.linearMap k Q) n)

/-- Membership in a rational eigenspace is the eigenvector equation after scalar extension. -/
@[simp]
theorem mem_rationalEigenspace {n : Type*} [Fintype n] {M : Matrix n n Q} {s : Q}
    {v : n → k} :
    v ∈ rationalEigenspace (k := k) M s ↔
      M *ᵥ (algebraMap k Q ∘ v) = s • (algebraMap k Q ∘ v) := by
  simp [rationalEigenspace, sub_eq_zero, LinearMap.compLeft, Function.comp_def]

/-- If `P₀` diagonalizes `M` with eigenvalues in the image of `e`, the corresponding rational
eigenspaces span because they contain the columns of `P₀`. -/
theorem iSup_rationalEigenspace_eq_top {n ι : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n Q} {P₀ : Matrix n n k} (hP₀ : IsUnit P₀) (e : ι → Q) {t : n → ι}
    (h : M * P₀.map (algebraMap k Q) = P₀.map (algebraMap k Q) * diagonal fun i ↦ e (t i)) :
    ⨆ s, rationalEigenspace (k := k) M (e s) = ⊤ := by
  have hcol (j : n) : P₀.col j ∈ rationalEigenspace (k := k) M (e (t j)) := by
    rw [mem_rationalEigenspace]
    funext i
    have hij := congr_fun (congr_fun h i) j
    rw [mul_diagonal, mul_apply] at hij
    simp only [map_apply] at hij
    simp only [mulVec, dotProduct, Function.comp_apply, col_apply, Pi.smul_apply, smul_eq_mul,
      hij, mul_comm]
  have hspan : Submodule.span k (Set.range P₀.col) = ⊤ := by
    rw [← range_mulVecLin, LinearMap.range_eq_top]
    exact mulVec_surjective_iff_isUnit.2 hP₀
  refine eq_top_iff.2 (hspan ▸ Submodule.span_le.2 ?_)
  rintro _ ⟨j, rfl⟩
  exact Submodule.mem_iSup_of_mem (t j) (hcol j)

end TauCeti
