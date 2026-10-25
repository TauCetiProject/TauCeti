/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.GeneratorParityCheck
public import TauCeti.LinearAlgebra.Matrix.MaximalMinor
public import TauCeti.NumberTheory.Height.Arakelov.Covolume
import TauCeti.LinearAlgebra.Matrix.Gram
import TauCeti.LinearAlgebra.Matrix.Rank

/-!
# The height of the row space and the kernel of an integer matrix

Let `A` be a `p × ι` integer matrix and let `g = Matrix.minorGcd A` be the greatest common divisor
of its maximal minors, equivalently of the Plücker coordinates `TauCeti.plucker A.row` of its rows
(`Matrix.minorGcd_eq_gcd_plucker`). The absolute Euclidean height
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

* `Matrix.minorGcd_mul_subspaceHeight_span_range_row`: the identity for the row space.
* `Matrix.minorGcd_mul_subspaceHeight_ker_mulVecLin`: the identity for the kernel.
* `Matrix.intPoints_ker_mulVecLin`: the integral points of the rational solution space of
  `A y = 0` are the integral solutions.
* `Matrix.covolume_intLattice_ker_mulVecLin`: the covolume of the lattice of integral solutions.
* `Matrix.sqrt_det_div_minorGcd_mul_left` and `Matrix.sqrt_det_div_minorGcd_unit_mul`: the
  quotient `√det (A Aᵀ) / g` is unchanged by `A ↦ B * A` for `det B ≠ 0`, in particular for
  `B ∈ GL_m(ℤ)`, unlike Siegel's bound in terms of the entries of `A`. This is proved directly,
  without a rank hypothesis: the maximal minors are multiplied by `det B` and the Gram determinant
  by `det B ^ 2`.

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
theorem minorGcd_mul_subspaceHeight_span_range_row (A : Matrix (Fin p) ι ℤ) :
    (A.minorGcd : ℝ) * (span ℚ (range (A.map ((↑) : ℤ → ℚ)).row)).subspaceHeight =
      √((A * Aᵀ).det : ℝ) := by
  rw [minorGcd_eq_gcd_plucker, det_mul_transpose_eq_sum_plucker_sq]
  by_cases hA : LinearIndependent ℚ (A.map ((↑) : ℤ → ℚ)).row
  · have h := plucker_row_map (Int.castRingHom ℚ) A
    rw [Int.coe_castRingHom] at h
    rw [subspaceHeight_span_range hA, h, gcd_mul_height2_intCast]
    simp
  · -- Dependent rows have vanishing maximal minors.
    have hg : A.minorGcd = 0 :=
      not_not.1 (mt minorGcd_ne_zero_iff.1 (mt linearIndependent_rat_row_iff.2 hA))
    rw [minorGcd_eq_gcd_plucker] at hg
    have h0 : plucker A.row = 0 := funext fun s ↦ Finset.gcd_eq_zero_iff.mp hg s (Finset.mem_univ s)
    simp [h0, Finset.gcd_eq_zero_iff.mpr]

/-- **The height of the kernel of an integer matrix.** The greatest common divisor of the maximal
minors of an integer matrix `A`, times the absolute Euclidean height of the space of rational
solutions of `A y = 0`, is `√det (A Aᵀ)`. If the rows are linearly dependent, both sides
vanish. -/
theorem minorGcd_mul_subspaceHeight_ker_mulVecLin (A : Matrix (Fin p) ι ℤ) :
    (A.minorGcd : ℝ) * (LinearMap.ker (A.map ((↑) : ℤ → ℚ)).mulVecLin).subspaceHeight =
      √((A * Aᵀ).det : ℝ) := by
  rw [← checkedBy_def, checkedBy_eq_euclideanDual_generatedBy, subspaceHeight_euclideanDual,
    generatedBy_eq_span_rows, minorGcd_mul_subspaceHeight_span_range_row]

omit [LinearOrder ι] in
/-- The integral points of the space of rational solutions of `A y = 0` are the integral solutions
of `A y = 0`. -/
theorem intPoints_ker_mulVecLin {m : Type*} (A : Matrix m ι ℤ) :
    (LinearMap.ker (A.map ((↑) : ℤ → ℚ)).mulVecLin).intPoints = LinearMap.ker A.mulVecLin := by
  ext z
  have h : A.map ((↑) : ℤ → ℚ) *ᵥ (fun i ↦ (z i : ℚ)) = fun i ↦ ((A *ᵥ z) i : ℚ) :=
    funext fun i ↦ (RingHom.map_mulVec (Int.castRingHom ℚ) A z i).symm
  simp [h, funext_iff]

/-- **The covolume of the lattice of integral solutions of `A y = 0`.** For an integer matrix `A`
with linearly independent rows, the lattice of integral solutions of `A y = 0` has covolume
`√det (A Aᵀ)` divided by the greatest common divisor of the maximal minors of `A`. -/
theorem covolume_intLattice_ker_mulVecLin {A : Matrix (Fin p) ι ℤ}
    (hA : LinearIndependent ℚ (A.map ((↑) : ℤ → ℚ)).row) :
    ZLattice.covolume (LinearMap.ker (A.map ((↑) : ℤ → ℚ)).mulVecLin).intLattice =
      √((A * Aᵀ).det : ℝ) / (A.minorGcd : ℝ) := by
  have hg : A.minorGcd ≠ 0 := minorGcd_ne_zero_iff.2 (linearIndependent_rat_row_iff.1 hA)
  rw [covolume_intLattice, ← minorGcd_mul_subspaceHeight_ker_mulVecLin,
    mul_div_cancel_left₀ _ (Int.cast_ne_zero.mpr hg)]

section Invariance

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]

/-- The quotient `√det (A * Aᵀ) / minorGcd A` is unchanged by `A ↦ B * A` for any square integer
matrix `B` with `det B ≠ 0`: both numerator and denominator are multiplied by `|det B|`. -/
theorem sqrt_det_div_minorGcd_mul_left {B : Matrix m m ℤ} (hB : B.det ≠ 0)
    (A : Matrix m n ℤ) :
    √((B * A * (B * A)ᵀ).det : ℝ) / ((B * A).minorGcd : ℝ) =
      √((A * Aᵀ).det : ℝ) / (A.minorGcd : ℝ) := by
  rw [det_mul_transpose_mul_left, minorGcd_mul_left, ← Int.abs_eq_normalize]
  push_cast [-Int.cast_det]
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs, mul_div_mul_left _ _ (by simpa)]

/-- The quotient `√det (A * Aᵀ) / minorGcd A` is invariant under `A ↦ U * A` for `U ∈ GL_m(ℤ)`. -/
theorem sqrt_det_div_minorGcd_unit_mul (U : GL m ℤ) (A : Matrix m n ℤ) :
    √(((U : Matrix m m ℤ) * A * ((U : Matrix m m ℤ) * A)ᵀ).det : ℝ) /
        (((U : Matrix m m ℤ) * A).minorGcd : ℝ) =
      √((A * Aᵀ).det : ℝ) / (A.minorGcd : ℝ) :=
  sqrt_det_div_minorGcd_mul_left (isUnits_det_units U).ne_zero A

end Invariance

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
  have h := (!![(2 : ℤ), 2]).minorGcd_mul_subspaceHeight_ker_mulVecLin
  rw [minorGcd_eq_gcd_plucker, hA, hp, hg, hdet] at h
  have h8 : √(8 : ℝ) = 2 * √2 := by
    rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  push_cast at h
  rw [h8] at h
  linarith

end
