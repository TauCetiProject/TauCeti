/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Alexander
public import TauCeti.LinearAlgebra.Matrix.Signature

/-!
# The signature of a Seifert matrix

The *signature* of a knot is the signature of the symmetrised Seifert matrix `V + Vᵀ` of any
Seifert surface for it. Because `Matrix.signature` reads only the quadratic form
`x ↦ x ⬝ᵥ V *ᵥ x`, which sees `V` only through `V + Vᵀ`, that invariant is `Matrix.signature V`
on the nose (`Matrix.signature_add_transpose`), and no separate definition is introduced here.

What makes it an invariant of the knot rather than of the chosen surface is that it is unchanged
by the two moves generating S-equivalence of Seifert matrices: congruence `V ↦ P * V * Pᵀ` by a
matrix with unit determinant — over `ℤ` exactly a change of basis of the first homology of the
surface — and the two enlargements `TauCeti.KnotTheory.enlargeColumn` and
`TauCeti.KnotTheory.enlargeRow` that record adding a tube to the surface. Congruence invariance is
already `Matrix.signature_congr`; the enlargements are the content of this file. An enlargement
adds a hyperbolic plane, which is what makes it invisible to the signature even though it changes
the size of the matrix by two.

The normalisation is pinned by the same two examples as the Alexander polynomial: the trefoil has
signature `-2` and the figure-eight knot signature `0`. Together with `Matrix.signature_of_isEmpty`
for the unknot, these show the invariant is not vacuous, and already distinguish the trefoil from
the unknot and from the figure-eight knot. The mirror image, whose Seifert matrix is `-Vᵀ`,
negates the signature.

This is the classical (Murasugi) signature, that is the Tristram--Levine signature at `ω = -1`;
the whole Tristram--Levine family lives over `ℂ` and needs the Hermitian form
`(1 - ω) V + (1 - star ω) Vᵀ`, which is not built here.

The block identities behind the enlargements hold over an arbitrary commutative ring, and the
signature statements over an arbitrary linearly ordered field; the knot-theoretic case is a
Seifert matrix over `ℤ` read in `ℚ` or `ℝ`, and the two example theorems are stated that way.

## Main results

* `TauCeti.KnotTheory.add_transpose_enlargeColumn`: the symmetrisation of a column enlargement,
  in blocks.
* `TauCeti.KnotTheory.signature_enlargeColumn` and `TauCeti.KnotTheory.signature_enlargeRow`: the
  signature is unchanged by the two enlargements of a Seifert matrix.
* `TauCeti.KnotTheory.signature_trefoilSeifertMatrix` and
  `TauCeti.KnotTheory.signature_figureEightSeifertMatrix`: the classical values `-2` and `0`.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 8
  (the signature of a knot and its invariance under S-equivalence).
* H. Murasugi, *On a certain numerical invariant of link types*, Trans. Amer. Math. Soc. 117
  (1965), 387--422.
* C. Livingston, *A survey of classical knot concordance*, in *Handbook of Knot Theory* (2005).
-/

public section

open Matrix

namespace TauCeti.KnotTheory

section CommRing

variable {R : Type*} [CommRing R] {ι : Type*}

/-- The symmetrisation of a column enlargement, in blocks: the old symmetrised matrix, the
enlargement vector, and a hyperbolic plane. -/
theorem add_transpose_enlargeColumn (V : Matrix ι ι R) (ξ : ι → R) :
    enlargeColumn V ξ + (enlargeColumn V ξ)ᵀ =
      Matrix.fromBlocks (V + Vᵀ) (enlargeBlock ξ) (enlargeBlock ξ)ᵀ !![0, 1; 1, 0] := by
  ext p q
  rcases p with i | i <;> rcases q with j | j
  · simp
  · fin_cases j <;> simp
  · fin_cases i <;> simp
  · fin_cases i <;> fin_cases j <;> simp

/-- A row enlargement and the column enlargement of the transpose have the same
symmetrisation. -/
theorem add_transpose_enlargeRow (V : Matrix ι ι R) (η : ι → R) :
    enlargeRow V η + (enlargeRow V η)ᵀ = enlargeColumn Vᵀ η + (enlargeColumn Vᵀ η)ᵀ := by
  ext p q
  rcases p with i | i <;> rcases q with j | j
  · simp [Matrix.transpose_apply, add_comm]
  · fin_cases j <;> simp [Matrix.transpose_apply]
  · fin_cases i <;> simp [Matrix.transpose_apply]
  · fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply]

/-- The trefoil Seifert matrix, read in an arbitrary commutative ring. -/
theorem map_trefoilSeifertMatrix :
    trefoilSeifertMatrix.map ((↑) : ℤ → R) = !![-1, 1; 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The figure-eight Seifert matrix, read in an arbitrary commutative ring. -/
theorem map_figureEightSeifertMatrix :
    figureEightSeifertMatrix.map ((↑) : ℤ → R) = !![1, 1; 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

end CommRing

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {ι : Type*} [Fintype ι]

section Enlargement

/-- **The signature is unchanged by a column enlargement of a Seifert matrix.** The enlargement
adds a hyperbolic plane, which contributes nothing to the signature. -/
@[simp]
theorem signature_enlargeColumn (V : Matrix ι ι 𝕜) (ξ : ι → 𝕜) :
    Matrix.signature (enlargeColumn V ξ) = Matrix.signature V := by
  classical
  set E : Matrix ι (Fin 2) 𝕜 := enlargeBlock ξ with hE
  set F : Matrix ι (Fin 2) 𝕜 := Matrix.of fun i => ![0, -ξ i] with hF
  set H : Matrix (Fin 2) (Fin 2) 𝕜 := !![0, 1; 1, 0] with hH
  have hFE : F * Eᵀ = 0 := by
    ext i j
    simp [hF, hE, Matrix.mul_apply, Fin.sum_univ_two]
  have hEF : E + F * H = 0 := by
    ext i k
    fin_cases k <;> simp [hF, hE, hH, Matrix.mul_apply, Fin.sum_univ_two]
  have hHT : Hᵀ = H := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hH]
  have hEH : Eᵀ + H * Fᵀ = 0 := by
    have h := congrArg Matrix.transpose hEF
    rwa [Matrix.transpose_add, Matrix.transpose_mul, hHT, Matrix.transpose_zero] at h
  have hQdet : IsUnit (Matrix.fromBlocks (1 : Matrix ι ι 𝕜) F 0 1).det := by
    rw [Matrix.det_fromBlocks_zero₂₁]
    simp
  have hcong : Matrix.fromBlocks (1 : Matrix ι ι 𝕜) F 0 1 *
      (enlargeColumn V ξ + (enlargeColumn V ξ)ᵀ) *
      (Matrix.fromBlocks (1 : Matrix ι ι 𝕜) F 0 1)ᵀ
      = Matrix.fromBlocks (V + Vᵀ) 0 0 H := by
    rw [add_transpose_enlargeColumn, ← hE, ← hH, Matrix.fromBlocks_transpose,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero,
      Matrix.transpose_one, Matrix.transpose_zero, hFE, hEF, zero_add, add_zero, hEH]
  rw [← Matrix.signature_add_transpose (enlargeColumn V ξ), ← Matrix.signature_congr hQdet,
    hcong, Matrix.signature_fromBlocks_zero, hH, Matrix.signature_hyperbolicGram, add_zero,
    Matrix.signature_add_transpose]

/-- **The signature is unchanged by a row enlargement of a Seifert matrix.** -/
@[simp]
theorem signature_enlargeRow (V : Matrix ι ι 𝕜) (η : ι → 𝕜) :
    Matrix.signature (enlargeRow V η) = Matrix.signature V := by
  rw [← Matrix.signature_add_transpose (enlargeRow V η), add_transpose_enlargeRow,
    Matrix.signature_add_transpose, signature_enlargeColumn, Matrix.signature_transpose]

end Enlargement

section Examples

/-- **The signature of the trefoil is `-2`.** Its symmetrised Seifert matrix `!![-2, 1; 1, -2]`
is negative definite, being congruent to `diagonal ![-2, -3/2]`. -/
theorem signature_trefoilSeifertMatrix :
    Matrix.signature (trefoilSeifertMatrix.map ((↑) : ℤ → 𝕜)) = -2 := by
  have hA : trefoilSeifertMatrix.map ((↑) : ℤ → 𝕜) + (trefoilSeifertMatrix.map ((↑) : ℤ → 𝕜))ᵀ
      = !![-2, 1; 1, -2] := by
    rw [map_trefoilSeifertMatrix]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply] <;> ring
  have hP : IsUnit (!![(1 : 𝕜), 0; 1 / 2, 1]).det := by
    rw [Matrix.det_fin_two_of, isUnit_iff_ne_zero]
    norm_num
  have hd : !![(1 : 𝕜), 0; 1 / 2, 1] * !![(-2 : 𝕜), 1; 1, -2] * (!![(1 : 𝕜), 0; 1 / 2, 1])ᵀ
      = Matrix.diagonal ![-2, -3 / 2] := by
    rw [Matrix.diagonal_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
  rw [← Matrix.signature_add_transpose, hA, Matrix.signature_eq_of_congr_diagonal hP hd,
    Fin.sum_univ_two]
  norm_num

/-- **The signature of the figure-eight knot is `0`.** Its symmetrised Seifert matrix
`!![2, 1; 1, -2]` is indefinite, being congruent to `diagonal ![2, -5/2]`. -/
theorem signature_figureEightSeifertMatrix :
    Matrix.signature (figureEightSeifertMatrix.map ((↑) : ℤ → 𝕜)) = 0 := by
  have hA :
      figureEightSeifertMatrix.map ((↑) : ℤ → 𝕜) + (figureEightSeifertMatrix.map ((↑) : ℤ → 𝕜))ᵀ
      = !![2, 1; 1, -2] := by
    rw [map_figureEightSeifertMatrix]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply] <;> ring
  have hP : IsUnit (!![(1 : 𝕜), 0; -(1 / 2), 1]).det := by
    rw [Matrix.det_fin_two_of, isUnit_iff_ne_zero]
    norm_num
  have hd : !![(1 : 𝕜), 0; -(1 / 2), 1] * !![(2 : 𝕜), 1; 1, -2] * (!![(1 : 𝕜), 0; -(1 / 2), 1])ᵀ
      = Matrix.diagonal ![2, -5 / 2] := by
    rw [Matrix.diagonal_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
  rw [← Matrix.signature_add_transpose, hA, Matrix.signature_eq_of_congr_diagonal hP hd,
    Fin.sum_univ_two]
  norm_num

/-- The trefoil and the figure-eight knot have different signatures, so their Seifert matrices
are not S-equivalent. -/
theorem signature_trefoil_ne_signature_figureEight :
    Matrix.signature (trefoilSeifertMatrix.map ((↑) : ℤ → 𝕜)) ≠
      Matrix.signature (figureEightSeifertMatrix.map ((↑) : ℤ → 𝕜)) := by
  rw [signature_trefoilSeifertMatrix, signature_figureEightSeifertMatrix]
  norm_num

end Examples

end TauCeti.KnotTheory
