/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.Arakelov.IntMatrix
-- Proof-only: Minkowski's convex body theorem against Vaaler's slice of the cube.
import TauCeti.Algebra.Module.ZLattice.CubeSlice

/-!
# Siegel's lemma in the sup norm, after Bombieri and Vaaler

A nonzero subspace `V` of `ℚ^ι` of dimension `k` contains a nonzero integral vector `z` with
`‖z‖ ≤ H(V) ^ (1 / k)`, where `‖z‖ = max_i |z i|` is the sup norm and `H(V)` is the absolute
Euclidean height `Submodule.subspaceHeight V`. For the space of solutions of a system `A x = 0`
of `p` independent linear equations with integer coefficients in `n > p` unknowns, this is
Bombieri and Vaaler's sup-norm form of Siegel's lemma: there is a nonzero integral solution with
`‖x‖ ≤ (√det (A Aᵀ) / g) ^ (1 / (n - p))`, where `g` is the greatest common divisor of the
maximal minors of `A`. The classical bound of Siegel, in Mathlib as
`Int.Matrix.exists_ne_zero_int_vec_norm_le`, is `‖x‖ ≤ (n · max |A i j|) ^ (p / (n - p))`. By
Hadamard's inequality, `√det (A Aᵀ)` is at most the product of the Euclidean norms of the rows of
`A`, so the bound here is at most `(√n · max |A i j|) ^ (p / (n - p))`; and unlike the classical
bound, it depends on `A` only through its rational row space, since it is the height of the
solution space.

The lattice of integral points of `V` has covolume `H(V)` in the real span of `V`
(`Submodule.covolume_intLattice`), so the statement is the case of integral lattices of
`ZLattice.exists_ne_zero_mem_abs_le_covolume_rpow`, which combines Minkowski's convex body theorem
with Vaaler's cube-slicing theorem.

## Main results

* `Submodule.exists_ne_zero_mem_intPoints_norm_le`: a nonzero integral point of `V` of sup norm at
  most `H(V) ^ (1 / k)`.
* `Matrix.exists_ne_zero_mulVec_eq_zero_norm_le`: Bombieri and Vaaler's Theorem 1 over `ℤ`.

## References

* E. Bombieri and J. Vaaler, *On Siegel's lemma*, Invent. Math. **73** (1983), 11–32,
  Theorem 1.
* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  §2.9.
-/

public section

noncomputable section

open Module TauCeti

namespace Submodule

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- **Siegel's lemma for a rational subspace, in the sup norm.** A nonzero subspace `V` of `ℚ^ι`
contains a nonzero integral point `z` whose sup norm is at most `H(V) ^ (1 / k)`, where `H(V)` is
the absolute Euclidean height of `V` and `k` its dimension. -/
theorem exists_ne_zero_mem_intPoints_norm_le {V : Submodule ℚ (ι → ℚ)} (hV : V ≠ ⊥) :
    ∃ z ∈ V.intPoints, z ≠ 0 ∧ ‖z‖ ≤ V.subspaceHeight ^ (finrank ℚ V : ℝ)⁻¹ := by
  have hW : V.realSpan ≠ ⊥ := by
    rwa [ne_eq, ← finrank_eq_zero, finrank_realSpan, finrank_eq_zero]
  obtain ⟨w, hw, hw0, hwle⟩ := ZLattice.exists_ne_zero_mem_abs_le_covolume_rpow V.intLattice hW
  rw [covolume_intLattice, finrank_realSpan] at hwle
  -- The integral point of `V` with the coordinates of `w`.
  set z := V.intPointsEquivIntLattice.symm ⟨w, hw⟩
  have hz (i : ι) : (((z : ι → ℤ) i : ℤ) : ℝ) = (w : EuclideanSpace ℝ ι) i :=
    intCast_intPointsEquivIntLattice_symm_apply V ⟨w, hw⟩ i
  refine ⟨z, z.2, fun h ↦ hw0 ?_, ?_⟩
  · ext i
    simp [← hz, h]
  · rw [pi_norm_le_iff_of_nonneg (Real.rpow_pos_of_pos (subspaceHeight_pos V) _).le]
    intro i
    rw [Int.norm_eq_abs, hz]
    exact hwle i

end Submodule

namespace Matrix

variable {ι : Type*} [Fintype ι] [LinearOrder ι] {p : ℕ}

/-- **Bombieri and Vaaler's Siegel lemma over `ℤ`, in the sup norm.** Let `A` be a `p × n` integer
matrix with linearly independent rows and `p < n`, and let `g` be the greatest common divisor of
its maximal minors. Then `A x = 0` has a nonzero integral solution `x` with
`‖x‖ ≤ (√det (A Aᵀ) / g) ^ (1 / (n - p))`, where `‖x‖ = max_i |x i|`. -/
theorem exists_ne_zero_mulVec_eq_zero_norm_le {A : Matrix (Fin p) ι ℤ}
    (hA : LinearIndependent ℚ (A.map ((↑) : ℤ → ℚ)).row) (hp : p < Fintype.card ι) :
    ∃ x : ι → ℤ, x ≠ 0 ∧ A *ᵥ x = 0 ∧
      ‖x‖ ≤ (√((A * Aᵀ).det : ℝ) / ((Finset.univ.gcd (plucker A.row) : ℤ) : ℝ)) ^
        ((Fintype.card ι : ℝ) - p)⁻¹ := by
  -- The solution space has dimension `n - p`, by rank–nullity.
  have hfin : finrank ℚ (LinearMap.ker (A.map ((↑) : ℤ → ℚ)).mulVecLin) =
      Fintype.card ι - p := by
    have h := LinearMap.finrank_range_add_finrank_ker (A.map ((↑) : ℤ → ℚ)).mulVecLin
    rw [← Matrix.rank, hA.rank_matrix, Fintype.card_fin, Module.finrank_fintype_fun_eq_card] at h
    omega
  set V := LinearMap.ker (A.map ((↑) : ℤ → ℚ)).mulVecLin
  have hV : V ≠ ⊥ := by
    rw [ne_eq, ← Submodule.finrank_eq_zero, hfin]
    omega
  -- Its height is `√det (A Aᵀ) / g`.
  have hg : ((Finset.univ.gcd (plucker A.row) : ℤ) : ℝ) ≠ 0 :=
    Int.cast_ne_zero.mpr fun h ↦ (gcd_plucker_row_eq_zero_iff A).mp h hA
  have hH : V.subspaceHeight =
      √((A * Aᵀ).det : ℝ) / ((Finset.univ.gcd (plucker A.row) : ℤ) : ℝ) := by
    rw [eq_div_iff hg, mul_comm]
    exact gcd_plucker_row_mul_subspaceHeight_ker_mulVecLin A
  obtain ⟨x, hx, hx0, hxle⟩ := Submodule.exists_ne_zero_mem_intPoints_norm_le hV
  refine ⟨x, hx0, ?_, ?_⟩
  · rw [Submodule.mem_intPoints, LinearMap.mem_ker, mulVecLin_apply] at hx
    ext i
    simpa using (RingHom.map_mulVec (Int.castRingHom ℚ) A x i).trans (congrFun hx i)
  · rwa [hH, hfin, Nat.cast_sub hp.le] at hxle

end Matrix
