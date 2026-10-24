/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.Arakelov.IntMatrix
import TauCeti.NumberTheory.GeometryOfNumbers.CubeSlice
import TauCeti.NumberTheory.GeometryOfNumbers.SupNormMinima

/-!
# Integral kernel bases of bounded sup norm

The integral points of a rational subspace `V` of dimension `k` have a `ℤ`-basis whose
product of sup norms is at most `k! / 2 ^ (k - 1)` times `V.subspaceHeight`.
For the kernel of an integer matrix `A` with independent rows, this gives a basis of the
whole integral kernel with

```text
∏ l, ‖b l‖ ≤ k! / 2 ^ (k - 1) * √det (A Aᵀ) / minorGcd A.
```

Here `‖·‖` is the sup norm on integer tuples, and `k` is the number of columns minus the
number of rows. In particular, the result includes square matrices of full rank: the basis
is empty and both sides of the bound are one.

The factor `k! / 2 ^ (k - 1)` is the cost of passing from independent vectors to a basis of
the whole lattice. Independent primitive vectors with product bounded by the covolume are
already supplied by `Matrix.exists_linearIndependent_mulVec_eq_zero_prod_norm_le`; they need
not generate the integral kernel. The basis statement combines Cassels' basis from the
successive minima (`Submodule.exists_basis_intPoints_prod_norm_le_prod_successiveMin`)
with the cube-slice bound from Minkowski's second theorem and Vaaler's volume estimate
(`Submodule.prod_successiveMin_intLattice_le_subspaceHeight`). The arithmetic constant comes
from `Matrix.covolume_intLattice_ker_mulVecLin`.

## References

* J. W. S. Cassels, *An Introduction to the Geometry of Numbers*, Springer, 1959,
  Chapter V, Lemma 8.
* E. Bombieri and J. Vaaler, *On Siegel's lemma*, Invent. Math. **73** (1983), 11–32.
* I. Aliev and M. Henk, *Minkowski's successive minima in convex and discrete geometry*,
  Commun. Math. **31** (2023), 35–59, §6.
-/

public section

open Matrix Module

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- The integral points of the rational kernel of an integer matrix are precisely its
integral kernel. -/
@[simp]
theorem intPoints_ker_mulVecLin {m : Type*} (A : Matrix m ι ℤ) :
    (LinearMap.ker (A.map ((↑) : ℤ → ℚ)).mulVecLin).intPoints =
      LinearMap.ker A.mulVecLin := by
  ext z
  simp only [Submodule.mem_intPoints, LinearMap.mem_ker, Matrix.mulVecLin_apply, funext_iff,
    Pi.zero_apply]
  exact forall_congr' fun i ↦ by
    have hcast : ((A *ᵥ z) i : ℚ) =
        (A.map ((↑) : ℤ → ℚ) *ᵥ (fun j ↦ (z j : ℚ))) i := by
      simpa only [Int.coe_castRingHom, Function.comp_def] using
        RingHom.map_mulVec (Int.castRingHom ℚ) A z i
    rw [← hcast, Int.cast_eq_zero]

variable [LinearOrder ι]

/-- A rational subspace of dimension `k` has a basis of its integral points whose product of
sup norms is bounded by `k! / 2 ^ (k - 1)` times its absolute Euclidean height. The basis
generates all integral points, rather than merely a sublattice of finite index. -/
theorem exists_basis_intPoints_prod_norm_le (V : Submodule ℚ (ι → ℚ)) :
    ∃ b : Basis (Fin (finrank ℚ V)) ℤ V.intPoints,
      ∏ l, ‖(b l : ι → ℤ)‖ ≤
        (finrank ℚ V).factorial / 2 ^ (finrank ℚ V - 1) * V.subspaceHeight := by
  obtain ⟨b, hb⟩ := V.exists_basis_intPoints_prod_norm_le_prod_successiveMin
  have hmin := V.prod_successiveMin_intLattice_le_subspaceHeight
    Submodule.coe_cubeSlice.ge (fun _ ↦ Submodule.neg_mem_cubeSlice.2)
  have hle := hb.trans (mul_le_mul_of_nonneg_left hmin (by positivity))
  have hresult : ∃ b : Basis (Fin (finrank ℝ V.realSpan)) ℤ V.intPoints,
      ∏ l, ‖(b l : ι → ℤ)‖ ≤
        (finrank ℝ V.realSpan).factorial / 2 ^ (finrank ℝ V.realSpan - 1) * V.subspaceHeight :=
    ⟨b, hle⟩
  rwa [Submodule.finrank_realSpan] at hresult

/-- An integer matrix with independent rows has a basis of its entire integral kernel whose
product of sup norms is at most `k! / 2 ^ (k - 1) * √det (A Aᵀ) / minorGcd A`, where `k` is
the number of columns minus the number of rows. The conclusion also includes `k = 0`. -/
theorem exists_basis_ker_mulVecLin_prod_norm_le {p : ℕ} {A : Matrix (Fin p) ι ℤ}
    (hA : LinearIndependent ℚ (A.map ((↑) : ℤ → ℚ)).row) :
    ∃ b : Basis (Fin (Fintype.card ι - p)) ℤ (LinearMap.ker A.mulVecLin),
      ∏ l, ‖(b l : ι → ℤ)‖ ≤
        (Fintype.card ι - p).factorial / 2 ^ (Fintype.card ι - p - 1) *
          √((A * Aᵀ).det : ℝ) / (A.minorGcd : ℝ) := by
  have hfin : finrank ℚ (LinearMap.ker (A.map ((↑) : ℤ → ℚ)).mulVecLin) =
      Fintype.card ι - p := by
    have h := (A.map ((↑) : ℤ → ℚ)).mulVecLin.finrank_range_add_finrank_ker
    rw [← Matrix.rank, hA.rank_matrix, Fintype.card_fin,
      Module.finrank_fintype_fun_eq_card] at h
    omega
  have hheight : (LinearMap.ker (A.map ((↑) : ℤ → ℚ)).mulVecLin).subspaceHeight =
      √((A * Aᵀ).det : ℝ) / (A.minorGcd : ℝ) :=
    (Submodule.covolume_intLattice _).symm.trans (Matrix.covolume_intLattice_ker_mulVecLin hA)
  have hresult := exists_basis_intPoints_prod_norm_le
    (LinearMap.ker (A.map ((↑) : ℤ → ℚ)).mulVecLin)
  rw [intPoints_ker_mulVecLin, hfin, hheight] at hresult
  simpa only [mul_div_assoc] using hresult

/-- For the row `(0, 0, 1)`, the bound is one and the basis spans the entire coordinate plane.
The independent vectors `(1, 1, 0)` and `(1, -1, 0)` have the same product of norms but fail
this spanning requirement. -/
example : ∃ b : Basis (Fin 2) ℤ (LinearMap.ker (!![(0 : ℤ), 0, 1]).mulVecLin),
    ∏ l, ‖(b l : Fin 3 → ℤ)‖ ≤ 1 := by
  have hA : LinearIndependent ℚ ((!![(0 : ℤ), 0, 1]).map ((↑) : ℤ → ℚ)).row := by
    simp [funext_iff, Fin.forall_fin_succ]
  have hg : (!![(0 : ℤ), 0, 1]).minorGcd = 1 :=
    Int.eq_one_of_dvd_one (Matrix.minorGcd_nonneg _) (by
      convert Matrix.minorGcd_dvd (!![(0 : ℤ), 0, 1])
        ⟨fun _ ↦ (2 : Fin 3), fun _ _ _ ↦ Subsingleton.elim _ _⟩ using 1; decide)
  have hd : ((!![(0 : ℤ), 0, 1]) * (!![(0 : ℤ), 0, 1])ᵀ).det = 1 := by
    rw [Matrix.det_unique]
    decide
  have h := exists_basis_ker_mulVecLin_prod_norm_le hA
  rw [Fintype.card_fin, show 3 - 1 = 2 by decide, hg, hd] at h
  norm_num at h
  simpa using h

end TauCeti
