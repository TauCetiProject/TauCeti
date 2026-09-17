/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.HermitianSignature
public import TauCeti.KnotTheory.Signature

/-!
# The Tristram--Levine signature of a Seifert matrix

For a Seifert matrix `V` and a parameter `ω` on the unit circle, the *Tristram--Levine form* is
the Hermitian matrix `(1 - ω) V + (1 - conj ω) Vᵀ` over `ℂ`, and the *Tristram--Levine signature*
`σ_ω(V)` is its signature. It is a one-parameter extension of the classical (Murasugi)
signature, recovered at `ω = -1`
(`TauCeti.KnotTheory.tristramLevineSignature_neg_one`), and the family is not constant: for the
trefoil the value changes from `-2` at `ω = -1` to `0` at the unit-circle point `(3 + 4i)/5`,
both computed below.

The form is Hermitian for every `ω : ℂ`, so no hypothesis on `ω` is imposed here. This file
constructs an invariant of a chosen Seifert matrix and proves congruence invariance, but not
invariance under S-equivalence or knot concordance. Classically, the ordinary signature at
unit-circle parameters away from the relevant Alexander-polynomial roots is a knot-concordance
invariant; values at roots require an additional convention such as the averaged signature. The
value at `ω = 1` is `0` for every `V`.

Congruence `V ↦ P * V * Pᵀ` by a matrix with unit determinant — over `ℤ` a change of basis of
the first homology of the Seifert surface — leaves `σ_ω` unchanged
(`TauCeti.KnotTheory.tristramLevineSignature_congr`). Invariance under the two enlargements
`TauCeti.KnotTheory.enlargeColumn` and `TauCeti.KnotTheory.enlargeRow`, which would complete
invariance under S-equivalence, is not proved here.

## Main definitions

* `TauCeti.KnotTheory.tristramLevineForm`: the Hermitian form `(1 - ω) V + (1 - conj ω) Vᵀ`.
* `TauCeti.KnotTheory.tristramLevineSignature`: its signature.

## Main results

* `TauCeti.KnotTheory.isHermitian_tristramLevineForm`: the form is Hermitian.
* `TauCeti.KnotTheory.tristramLevineSignature_neg_one`: at `ω = -1` the classical signature.
* `TauCeti.KnotTheory.tristramLevineSignature_one`: at `ω = 1` the signature vanishes.
* `TauCeti.KnotTheory.tristramLevineSignature_congr`: invariance under congruence.
* `TauCeti.KnotTheory.tristramLevineSignature_conj`: `ω` and `conj ω` give the same signature.
* `TauCeti.KnotTheory.tristramLevineSignature_neg_transpose`: the mirror image, whose Seifert
  matrix is `-Vᵀ`, has the negated signature.
* `TauCeti.KnotTheory.exists_tristramLevineSignature_trefoilSeifertMatrix_ne`: the trefoil's
  signature is not constant on the unit circle.

## References

* A. G. Tristram, *Some cobordism invariants for links*, Proc. Cambridge Philos. Soc. 66
  (1969), 251--264.
* J. Levine, *Invariants of knot cobordism*, Invent. Math. 8 (1969), 98--110.
* C. Livingston, *A survey of classical knot concordance*, in *Handbook of Knot Theory* (2005),
  for the conventions used here.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 8.
-/

public section

open Matrix
open scoped ComplexConjugate

namespace TauCeti.KnotTheory

variable {ι : Type*}

/-- The Tristram--Levine form of a Seifert matrix `V` at `ω`, the Hermitian matrix
`(1 - ω) V + (1 - conj ω) Vᵀ` over `ℂ`. -/
def tristramLevineForm (V : Matrix ι ι ℝ) (ω : ℂ) : Matrix ι ι ℂ :=
  (1 - ω) • V.map ((↑) : ℝ → ℂ) + (1 - conj ω) • (Vᵀ).map ((↑) : ℝ → ℂ)

@[simp]
theorem tristramLevineForm_apply (V : Matrix ι ι ℝ) (ω : ℂ) (i j : ι) :
    tristramLevineForm V ω i j = (1 - ω) * V i j + (1 - conj ω) * V j i := by
  simp [tristramLevineForm]

/-- **The Tristram--Levine form is Hermitian**, for every `ω`: conjugating an entry exchanges
the roles of `ω` and `conj ω`, which is what transposing `V` does. -/
theorem isHermitian_tristramLevineForm (V : Matrix ι ι ℝ) (ω : ℂ) :
    (tristramLevineForm V ω).IsHermitian := by
  ext i j
  simp [Matrix.conjTranspose_apply]
  ring

/-- The Tristram--Levine form vanishes at `ω = 1`. -/
@[simp]
theorem tristramLevineForm_one (V : Matrix ι ι ℝ) : tristramLevineForm V 1 = 0 := by
  simp [tristramLevineForm]

/-- At `ω = -1` the Tristram--Levine form is twice the symmetrised Seifert matrix. -/
@[simp]
theorem tristramLevineForm_neg_one (V : Matrix ι ι ℝ) :
    tristramLevineForm V (-1) = ((2 : ℝ) • (V + Vᵀ)).map ((↑) : ℝ → ℂ) := by
  ext i j
  simp [Matrix.transpose_apply]
  ring

/-- Replacing `ω` by `conj ω` conjugates the Tristram--Levine form entrywise. -/
theorem tristramLevineForm_conj (V : Matrix ι ι ℝ) (ω : ℂ) :
    tristramLevineForm V (conj ω) = (tristramLevineForm V ω).map (starRingEnd ℂ) := by
  ext i j
  simp

/-- The Seifert matrix `-Vᵀ` of the mirror image has the negated form at the conjugate
parameter. -/
theorem tristramLevineForm_neg_transpose (V : Matrix ι ι ℝ) (ω : ℂ) :
    tristramLevineForm (-Vᵀ) ω = -tristramLevineForm V (conj ω) := by
  ext i j
  simp [Matrix.transpose_apply]

/-- Congruence of Seifert matrices becomes `*`-congruence of Tristram--Levine forms. -/
theorem tristramLevineForm_congr [Fintype ι] (P V : Matrix ι ι ℝ) (ω : ℂ) :
    tristramLevineForm (P * V * Pᵀ) ω =
      P.map ((↑) : ℝ → ℂ) * tristramLevineForm V ω * (P.map ((↑) : ℝ → ℂ))ᴴ := by
  have hconj : (P.map ((↑) : ℝ → ℂ))ᴴ = (Pᵀ).map ((↑) : ℝ → ℂ) := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  have hmap : ∀ A B : Matrix ι ι ℝ, (A * B).map ((↑) : ℝ → ℂ)
      = A.map ((↑) : ℝ → ℂ) * B.map ((↑) : ℝ → ℂ) := fun A B =>
    Matrix.map_mul (f := Complex.ofRealHom)
  simp only [tristramLevineForm, hconj, Matrix.transpose_mul, Matrix.transpose_transpose, hmap,
    Matrix.transpose_map, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_assoc]

section Signature

variable [Fintype ι] [DecidableEq ι]

/-- The Tristram--Levine signature of a Seifert matrix `V` at `ω`: the signature of the
Hermitian form `(1 - ω) V + (1 - conj ω) Vᵀ`. -/
noncomputable def tristramLevineSignature (V : Matrix ι ι ℝ) (ω : ℂ) : ℤ :=
  (isHermitian_tristramLevineForm V ω).signature

/-- Twice the Tristram--Levine signature is the real signature of the realified form. This is
the bridge to the real signature API, and is how the computations below proceed. -/
theorem two_mul_tristramLevineSignature (V : Matrix ι ι ℝ) (ω : ℂ) :
    2 * tristramLevineSignature V ω = Matrix.signature (tristramLevineForm V ω).realify :=
  ((isHermitian_tristramLevineForm V ω).signature_realify).symm

/-- **The Tristram--Levine signature read off an explicit diagonalising `*`-congruence.** -/
theorem tristramLevineSignature_eq_of_congr_diagonal (V : Matrix ι ι ℝ) (ω : ℂ)
    {P : Matrix ι ι ℂ} (hP : IsUnit P.det) {d : ι → ℝ}
    (h : P * tristramLevineForm V ω * Pᴴ = (Matrix.diagonal d).map ((↑) : ℝ → ℂ)) :
    tristramLevineSignature V ω = ∑ i, if 0 < d i then (1 : ℤ) else if d i < 0 then -1 else 0 :=
  (isHermitian_tristramLevineForm V ω).signature_eq_of_congr_diagonal hP h

/-- **The Tristram--Levine signature vanishes at `ω = 1`**, where the form itself vanishes. -/
@[simp]
theorem tristramLevineSignature_one (V : Matrix ι ι ℝ) : tristramLevineSignature V 1 = 0 := by
  unfold tristramLevineSignature
  simpa only [tristramLevineForm_one] using
    (Matrix.IsHermitian.signature_zero (ι := ι))

/-- **At `ω = -1` the Tristram--Levine signature is the classical signature** of the Seifert
matrix. -/
@[simp]
theorem tristramLevineSignature_neg_one (V : Matrix ι ι ℝ) :
    tristramLevineSignature V (-1) = Matrix.signature V := by
  have h := two_mul_tristramLevineSignature V (-1)
  rw [tristramLevineForm_neg_one, realify_map_ofReal, Matrix.signature_fromBlocks_zero,
    Matrix.signature_smul_of_pos two_pos, Matrix.signature_add_transpose] at h
  omega

/-- **Congruence invariance of the Tristram--Levine signature.** Replacing `V` by `P * V * Pᵀ`
for a matrix `P` with unit determinant does not change it; over `ℤ` this is a change of basis of
the first homology of the Seifert surface. -/
theorem tristramLevineSignature_congr {P : Matrix ι ι ℝ} (hP : IsUnit P.det) (V : Matrix ι ι ℝ)
    (ω : ℂ) : tristramLevineSignature (P * V * Pᵀ) ω = tristramLevineSignature V ω := by
  -- `P.map (↑)` is `Complex.ofRealHom.mapMatrix P`, so its determinant is `↑P.det`.
  have hP' : IsUnit (P.map ((↑) : ℝ → ℂ)).det :=
    RingHom.map_det Complex.ofRealHom P ▸ hP.map Complex.ofRealHom
  unfold tristramLevineSignature
  simpa only [tristramLevineForm_congr] using
    (isHermitian_tristramLevineForm V ω).signature_congr hP'

/-- **Conjugate parameters give the same Tristram--Levine signature**, so the family is
determined by the upper half of the unit circle. -/
@[simp]
theorem tristramLevineSignature_conj (V : Matrix ι ι ℝ) (ω : ℂ) :
    tristramLevineSignature V (conj ω) = tristramLevineSignature V ω := by
  unfold tristramLevineSignature
  simpa only [tristramLevineForm_conj] using
    (isHermitian_tristramLevineForm V ω).signature_map_starRingEnd

/-- **The mirror image negates the Tristram--Levine signature.** The mirror of a knot has
Seifert matrix `-Vᵀ`. -/
@[simp]
theorem tristramLevineSignature_neg_transpose (V : Matrix ι ι ℝ) (ω : ℂ) :
    tristramLevineSignature (-Vᵀ) ω = -tristramLevineSignature V ω := by
  calc
    tristramLevineSignature (-Vᵀ) ω = -tristramLevineSignature V (conj ω) := by
      unfold tristramLevineSignature
      simpa only [tristramLevineForm_neg_transpose] using
        (isHermitian_tristramLevineForm V (conj ω)).signature_neg
    _ = -tristramLevineSignature V ω := by rw [tristramLevineSignature_conj]

end Signature

section Examples

/-- **The trefoil has Tristram--Levine signature `-2` at `ω = -1`**, its classical signature. -/
theorem tristramLevineSignature_trefoilSeifertMatrix_neg_one :
    tristramLevineSignature (trefoilSeifertMatrix.map ((↑) : ℤ → ℝ)) (-1) = -2 := by
  rw [tristramLevineSignature_neg_one, signature_trefoilSeifertMatrix]

/-- **The figure-eight knot has Tristram--Levine signature `0` at `ω = -1`.** -/
theorem tristramLevineSignature_figureEightSeifertMatrix_neg_one :
    tristramLevineSignature (figureEightSeifertMatrix.map ((↑) : ℤ → ℝ)) (-1) = 0 := by
  rw [tristramLevineSignature_neg_one, signature_figureEightSeifertMatrix]

/-- **The Tristram--Levine signature of the trefoil is not constant on the unit circle.** The
witness is the rational point `(3 + 4i)/5`, where the symmetrised form becomes indefinite and the
signature changes from `-2` to `0`. -/
theorem exists_tristramLevineSignature_trefoilSeifertMatrix_ne :
    ∃ ω : ℂ, ‖ω‖ = 1 ∧
      tristramLevineSignature (trefoilSeifertMatrix.map ((↑) : ℤ → ℝ)) ω ≠
        tristramLevineSignature (trefoilSeifertMatrix.map ((↑) : ℤ → ℝ)) (-1) := by
  refine ⟨(3 + 4 * Complex.I) / 5, ?_, ?_⟩
  · rw [norm_div, Complex.norm_def, Complex.normSq_apply]
    norm_num
    have hsqrt : Real.sqrt (25 : ℝ) = 5 := by
      have hsqrt_sq : (Real.sqrt (25 : ℝ)) ^ 2 = 25 := Real.sq_sqrt (by norm_num)
      nlinarith [Real.sqrt_nonneg (25 : ℝ)]
    rw [hsqrt]
    norm_num
  · have hform : tristramLevineForm (trefoilSeifertMatrix.map ((↑) : ℤ → ℝ))
        ((3 + 4 * Complex.I) / 5) =
        !![-(4 / 5 : ℂ), (2 - 4 * Complex.I) / 5; (2 + 4 * Complex.I) / 5, -(4 / 5 : ℂ)] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [map_trefoilSeifertMatrix, Complex.ext_iff, map_ofNat] <;> norm_num
    have hP : IsUnit (!![(1 : ℂ), 0; (1 + 2 * Complex.I) / 2, 1]).det := by
      rw [Matrix.det_fin_two_of, isUnit_iff_ne_zero]
      norm_num
    have hd : !![(1 : ℂ), 0; (1 + 2 * Complex.I) / 2, 1] *
        tristramLevineForm (trefoilSeifertMatrix.map ((↑) : ℤ → ℝ)) ((3 + 4 * Complex.I) / 5) *
        (!![(1 : ℂ), 0; (1 + 2 * Complex.I) / 2, 1])ᴴ =
          (Matrix.diagonal ![-(4 / 5 : ℝ), 1 / 5]).map ((↑) : ℝ → ℂ) := by
      rw [hform, Matrix.diagonal_fin_two]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.ext_iff,
          map_ofNat] <;> norm_num
    rw [tristramLevineSignature_eq_of_congr_diagonal _ _ hP hd, Fin.sum_univ_two,
      tristramLevineSignature_trefoilSeifertMatrix_neg_one]
    norm_num

end Examples

end TauCeti.KnotTheory
