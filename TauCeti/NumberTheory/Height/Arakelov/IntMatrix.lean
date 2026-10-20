/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.GeneratorParityCheck
public import TauCeti.NumberTheory.Height.Arakelov.Covolume

/-!
# The height of the row space and the kernel of an integer matrix

Let `A` be a `p × ι` integer matrix and let `g` be the greatest common divisor of its maximal
minors, the Plücker coordinates `TauCeti.plucker A.row` of its rows. The absolute Euclidean height
of the rational row space of `A`, and that of the rational solution space of `A y = 0`, satisfy
`g · subspaceHeight (ker A) = √det (A Aᵀ)`,
which holds without any rank hypothesis: if the rows of `A` are linearly dependent, then all
maximal minors vanish and both sides are zero. If the rows of `A` are linearly independent, then
`g ≠ 0` and both heights are `√det (A Aᵀ) / g`.

With `Submodule.covolume_intLattice` this computes the covolume of the lattice of integral
solutions of `A y = 0`: for `A` with linearly independent rows it is `√det (A Aᵀ) / g`. This is
the quantity bounding the product of the sup norms of independent integral solutions in Bombieri
and Vaaler's version of Siegel's lemma, and the identity shows that it is unchanged when `A` is
replaced by any integer matrix with the same rational row space.

## Main results

* `Matrix.gcd_plucker_row_mul_subspaceHeight_span_range_row`: the identity for the row space.
* `Matrix.gcd_plucker_row_mul_subspaceHeight_ker_mulVecLin`: the identity for the kernel.
* `Matrix.covolume_intLattice_ker_mulVecLin`: the covolume of the lattice of integral solutions.

## Implementation notes

The height of the row space is the Euclidean height of the Plücker coordinates of the rows
(`Submodule.subspaceHeight_span_range`). Dividing out the greatest common divisor
(`TauCeti.gcd_mul_height2_intCast`) leaves the Euclidean norm of the maximal minors, whose square
is `det (A Aᵀ)` by the Cauchy–Binet formula (`TauCeti.det_mul_transpose_eq_sum_plucker_mul`). The
kernel is the orthogonal complement of the row space for the dot product
(`Matrix.checkedBy_eq_euclideanDual_generatedBy`), which has the same height
(`Submodule.subspaceHeight_euclideanDual`).

## References

* E. Bombieri and J. Vaaler, *On Siegel's lemma*, Invent. Math. **73** (1983), 11–32, Theorem 2.
* I. Aliev and M. Henk, *Minkowski's successive minima in convex and discrete geometry*,
  Commun. Math. **31** (2023), no. 2, 35–59, §6.

The proof plan follows Ralf Stephan's `Int.Matrix.minorGcd_mul_arakelovMulHeight_ker` and
`NumberField.gcd_mul_arakelovMulHeight_intCast` in `ArithmeticHeights/BombieriVaaler.lean` of
[`rwst/Subspace-Theorems`](https://github.com/rwst/Subspace-Theorems/blob/09835cb23557ae5ae0cf55a9c4ab9055f5d60338/ArithmeticHeights/BombieriVaaler.lean),
commit `09835cb23557ae5ae0cf55a9c4ab9055f5d60338` (Apache 2.0).
-/

public section

noncomputable section

open Set Submodule TauCeti

namespace Matrix

variable {ι : Type*} [Fintype ι] [LinearOrder ι] {p : ℕ}

/-- **The height of the row space of an integer matrix.** The greatest common divisor of the
maximal minors of an integer matrix `A`, times the absolute Euclidean height of the rational row
space of `A`, is `√det (A Aᵀ)`. If the rows are linearly dependent, both sides vanish. -/
theorem gcd_plucker_row_mul_subspaceHeight_span_range_row (A : Matrix (Fin p) ι ℤ) :
    ((Finset.univ.gcd (plucker A.row) : ℤ) : ℝ) *
        (span ℚ (range (A.map ((↑) : ℤ → ℚ)).row)).subspaceHeight =
      √((A * Aᵀ).det : ℝ) := by
  rw [det_mul_transpose_eq_sum_plucker_sq]
  by_cases hA : LinearIndependent ℚ (A.map ((↑) : ℤ → ℚ)).row
  · have h := plucker_row_map (Int.castRingHom ℚ) A
    rw [Int.coe_castRingHom] at h
    rw [subspaceHeight_span_range hA, h, gcd_mul_height2_intCast]
    simp
  · -- Dependent rows have vanishing maximal minors.
    have h0 : plucker A.row = 0 := funext fun s ↦
      Finset.gcd_eq_zero_iff.mp ((gcd_plucker_row_eq_zero_iff A).mpr hA) s (Finset.mem_univ s)
    simp [h0, Finset.gcd_eq_zero_iff.mpr]

/-- **The height of the kernel of an integer matrix.** The greatest common divisor of the maximal
minors of an integer matrix `A`, times the absolute Euclidean height of the space of rational
solutions of `A y = 0`, is `√det (A Aᵀ)`. If the rows are linearly dependent, both sides
vanish. -/
theorem gcd_plucker_row_mul_subspaceHeight_ker_mulVecLin (A : Matrix (Fin p) ι ℤ) :
    ((Finset.univ.gcd (plucker A.row) : ℤ) : ℝ) *
        (LinearMap.ker (A.map ((↑) : ℤ → ℚ)).mulVecLin).subspaceHeight =
      √((A * Aᵀ).det : ℝ) := by
  rw [← checkedBy_def, checkedBy_eq_euclideanDual_generatedBy, subspaceHeight_euclideanDual,
    generatedBy_eq_span_rows, gcd_plucker_row_mul_subspaceHeight_span_range_row]

/-- **The covolume of the lattice of integral solutions of `A y = 0`.** For an integer matrix `A`
with linearly independent rows, the lattice of integral solutions of `A y = 0` has covolume
`√det (A Aᵀ)` divided by the greatest common divisor of the maximal minors of `A`. -/
theorem covolume_intLattice_ker_mulVecLin {A : Matrix (Fin p) ι ℤ}
    (hA : LinearIndependent ℚ (A.map ((↑) : ℤ → ℚ)).row) :
    ZLattice.covolume (LinearMap.ker (A.map ((↑) : ℤ → ℚ)).mulVecLin).intLattice =
      √((A * Aᵀ).det : ℝ) / ((Finset.univ.gcd (plucker A.row) : ℤ) : ℝ) := by
  have hg : Finset.univ.gcd (plucker A.row) ≠ 0 := fun h ↦ (gcd_plucker_row_eq_zero_iff A).mp h hA
  rw [covolume_intLattice, ← gcd_plucker_row_mul_subspaceHeight_ker_mulVecLin,
    mul_div_cancel_left₀ _ (Int.cast_ne_zero.mpr hg)]

end Matrix

open Matrix in
/-- The row `(2, 2)` has maximal minors `2, 2` and Gram determinant `8`, so its kernel, the line
through `(1, -1)`, has height `√8 / 2 = √2`. -/
example : (LinearMap.ker (!![(2 : ℚ), 2]).mulVecLin).subspaceHeight = √2 := by
  have hA : (!![(2 : ℤ), 2]).map ((↑) : ℤ → ℚ) = !![(2 : ℚ), 2] := by
    ext i j
    fin_cases i
    fin_cases j <;> rfl
  have hp : plucker (!![(2 : ℤ), 2]).row = fun _ ↦ 2 := by
    ext s
    rw [plucker_apply, Matrix.det_unique, Matrix.of_apply]
    generalize Set.powersetCard.ofFinEmbEquiv.symm s default = j
    fin_cases j <;> rfl
  have hg : Finset.univ.gcd (fun _ : Set.powersetCard (Fin 2) 1 ↦ (2 : ℤ)) = 2 := by
    have : Nonempty (Set.powersetCard (Fin 2) 1) := ⟨Set.powersetCard.ofSingleton 0⟩
    rw [Finset.gcd_eq_gcd_image, Finset.image_const Finset.univ_nonempty, Finset.gcd_singleton]
    rfl
  have hdet : (!![(2 : ℤ), 2] * (!![(2 : ℤ), 2])ᵀ).det = 8 := by
    rw [Matrix.det_unique]
    decide
  have h := (!![(2 : ℤ), 2]).gcd_plucker_row_mul_subspaceHeight_ker_mulVecLin
  rw [hA, hp, hg, hdet] at h
  have h8 : √(8 : ℝ) = 2 * √2 := by
    rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  push_cast at h
  rw [h8] at h
  linarith

end
