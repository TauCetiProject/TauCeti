/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Wishart.Bartlett
public import TauCeti.Probability.Distributions.Wishart.Congruence

import TauCeti.Analysis.Matrix.OrthogonalRows
import TauCeti.LinearAlgebra.Matrix.Rank
import TauCeti.LinearAlgebra.Matrix.Triangular
import TauCeti.MeasureTheory.Constructions.Pi

/-!
# Congruence images and marginals of the nonsingular Wishart law

Congruence `A ↦ M * A * Mᵀ` by a `q × p` matrix `M` of full row rank carries the nonsingular
Wishart law of degree `n` and positive-definite scale `S` to the nonsingular Wishart law of the
same degree and scale `M * S * Mᵀ`. Full row rank is what keeps the new scale positive definite,
so that the image is again a law of the density family; congruences of smaller rank leave that
family and belong to the Gaussian-Gram one.

Selecting `q` of the `p` coordinates is the special case in which `M` deletes the last `p - q`
rows of the identity matrix; congruence by that matrix reads off the leading principal `q × q`
submatrix, by `Matrix.submatrix_one_mul_mul_submatrix_one`. So the leading principal `q × q`
submatrix of a Wishart matrix is again Wishart, of the same degree and with the corresponding
submatrix of `S` as its scale: the Wishart family is closed under marginalisation.

The two statements are proved together, by reducing an arbitrary full-row-rank congruence to a
coordinate selection at the standard scale. Write `S = R * Rᵀ` and `M * S * Mᵀ = T * Tᵀ` with `R`
and `T` invertible. Then `M * R` has Gram matrix `T * Tᵀ`, so by its `LQ` decomposition
`Matrix.exists_mul_transpose_eq_one_and_eq_mul_submatrix_castLE` it equals `T * (E * Q)`, where
`Q` is orthogonal and `E` is the row selection. Congruence by an invertible matrix is already
understood, and congruence by `Q` fixes the standard law, which leaves the coordinate selection
at the standard scale. There the Bartlett coordinates make it transparent: the leading block of
the Cholesky factor of `A` is the Cholesky factor of the leading block of `A`, and the Bartlett
coordinate laws in dimension `q` are literally those in dimension `p` at the retained
positions.

## Main results

* `TauCeti.map_symmetricCongruenceLinearMap_nonsingularWishartMeasure` — congruence by a matrix
  of full row rank carries the law of scale `S` to the law of scale `M * S * Mᵀ`;
* `TauCeti.map_symmetricCongruenceLinearMap_submatrix_one_nonsingularWishartMeasure` — the
  leading principal `q × q` submatrix of a nonsingular Wishart matrix has the nonsingular Wishart
  law of the corresponding submatrix of the scale.

## References

* R. J. Muirhead, *Aspects of Multivariate Statistical Theory*, Wiley, 1982, Section 3.2.
* M. L. Eaton, *Multivariate Statistics: A Vector Space Approach*, IMS Lecture Notes 53,
  chapter 8.
-/

public section

noncomputable section

open MeasureTheory

open scoped Matrix

namespace TauCeti

variable {p q : ℕ} {n : ℝ} {S : Matrix (Fin p) (Fin p) ℝ}

/-! ### Selecting coordinates at the standard scale -/

/-- The on-or-below-diagonal positions of a `q × q` matrix sit among those of a `p × p` matrix. -/
private def lowerTriangleCastLE (hqp : q ≤ p) : lowerTriangle q ↪ lowerTriangle p where
  toFun ij := ⟨(Fin.castLE hqp ij.1.1, Fin.castLE hqp ij.1.2), ij.2⟩
  inj' ij kl h := by
    refine Subtype.ext (Prod.ext ?_ ?_)
    · exact Fin.castLE_injective hqp (congrArg (fun x => x.1.1) h)
    · exact Fin.castLE_injective hqp (congrArg (fun x => x.1.2) h)

/-- The leading `q × q` block of a lower-triangular matrix is read off by restricting its
coordinates along `TauCeti.lowerTriangleCastLE`. -/
private theorem submatrix_castLE_lowerTriangleMatrix (hqp : q ≤ p) (x : lowerTriangle p → ℝ) :
    (lowerTriangleMatrix p x).submatrix (Fin.castLE hqp) (Fin.castLE hqp) =
      lowerTriangleMatrix q fun ij => x (lowerTriangleCastLE hqp ij) := by
  ext i j
  by_cases h : j ≤ i
  · rw [Matrix.submatrix_apply,
      lowerTriangleMatrix_apply_of_le (i := Fin.castLE hqp i) (j := Fin.castLE hqp j) x h,
      lowerTriangleMatrix_apply_of_le _ h]
    rfl
  · rw [Matrix.submatrix_apply,
      lowerTriangleMatrix_apply_of_lt (i := Fin.castLE hqp i) (j := Fin.castLE hqp j) x
        (not_le.1 h),
      lowerTriangleMatrix_apply_of_lt _ (not_le.1 h)]

/-- Congruence by the row selection turns the Gram map of the Bartlett coordinates in dimension
`p` into the Gram map of the retained coordinates in dimension `q`. -/
private theorem symmetricCongruenceLinearMap_lowerTriangleGram (hqp : q ≤ p)
    (x : lowerTriangle p → ℝ) :
    Matrix.symmetricCongruenceLinearMap
        ((1 : Matrix (Fin p) (Fin p) ℝ).submatrix (Fin.castLE hqp) id) (lowerTriangleGram p x) =
      lowerTriangleGram q fun ij => x (lowerTriangleCastLE hqp ij) := by
  refine Subtype.ext ?_
  rw [Matrix.coe_symmetricCongruenceLinearMap_apply, coe_lowerTriangleGram, coe_lowerTriangleGram,
    Matrix.transpose_submatrix, Matrix.transpose_one, Matrix.submatrix_one_mul_mul_submatrix_one,
    Matrix.IsLowerTriangular.submatrix_castLE_mul_transpose
      (isLowerTriangular_lowerTriangleMatrix x) hqp,
    submatrix_castLE_lowerTriangleMatrix]

/-- A Bartlett coordinate law depends only on the position, not on the ambient dimension. -/
private theorem bartlettCoordinateMeasure_lowerTriangleCastLE (hqp : q ≤ p) (n : ℝ)
    (ij : lowerTriangle q) :
    bartlettCoordinateMeasure (p := p) n (lowerTriangleCastLE hqp ij) =
      bartlettCoordinateMeasure (p := q) n ij := by
  by_cases h : ij.1.1 = ij.1.2
  · have h' : (lowerTriangleCastLE hqp ij).1.1 = (lowerTriangleCastLE hqp ij).1.2 :=
      congrArg (Fin.castLE hqp) h
    rw [bartlettCoordinateMeasure_of_eq n h', bartlettCoordinateMeasure_of_eq n h]
    rfl
  · have h' : (lowerTriangleCastLE hqp ij).1.1 ≠ (lowerTriangleCastLE hqp ij).1.2 := fun hc =>
      h (Fin.castLE_injective hqp hc)
    rw [bartlettCoordinateMeasure_of_ne n h', bartlettCoordinateMeasure_of_ne n h]

/-- Restricting the Bartlett coordinates of dimension `p` to the positions of a `q × q` block
gives the Bartlett coordinates of dimension `q`. -/
private theorem map_lowerTriangleCastLE_pi_bartlettCoordinateMeasure (hqp : q ≤ p)
    (hn : (p : ℝ) - 1 < n) :
    (Measure.pi (bartlettCoordinateMeasure (p := p) n)).map
        (fun x ij => x (lowerTriangleCastLE hqp ij)) =
      Measure.pi (bartlettCoordinateMeasure (p := q) n) := by
  have : ∀ ij : lowerTriangle p, IsProbabilityMeasure (bartlettCoordinateMeasure n ij) :=
    fun ij => isProbabilityMeasure_bartlettCoordinateMeasure hn ij
  rw [(measurePreserving_pi_comp_embedding _ (lowerTriangleCastLE hqp)).map_eq]
  exact congrArg Measure.pi (funext (bartlettCoordinateMeasure_lowerTriangleCastLE hqp n))

/-- **The leading principal submatrix of a standard Wishart matrix is a standard Wishart matrix**
of the same degree. -/
private theorem map_submatrix_one_nonsingularWishartMeasure_one (hqp : q ≤ p)
    (hn : (p : ℝ) - 1 < n) :
    (nonsingularWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ)).map
        (Matrix.symmetricCongruenceLinearMap
          ((1 : Matrix (Fin p) (Fin p) ℝ).submatrix (Fin.castLE hqp) id)) =
      nonsingularWishartMeasure n (1 : Matrix (Fin q) (Fin q) ℝ) := by
  have hnq : (q : ℝ) - 1 < n := by
    have hcast : (q : ℝ) ≤ (p : ℝ) := Nat.cast_le.2 hqp
    linarith
  have hcong : Measurable (Matrix.symmetricCongruenceLinearMap
      ((1 : Matrix (Fin p) (Fin p) ℝ).submatrix (Fin.castLE hqp) id)) :=
    (LinearMap.continuous_of_finiteDimensional _).measurable
  have hproj : Measurable fun x : lowerTriangle p → ℝ => fun ij => x (lowerTriangleCastLE hqp ij) :=
    measurable_pi_iff.2 fun ij => measurable_pi_apply _
  have hfun : (Matrix.symmetricCongruenceLinearMap
        ((1 : Matrix (Fin p) (Fin p) ℝ).submatrix (Fin.castLE hqp) id)) ∘ lowerTriangleGram p =
      lowerTriangleGram q ∘ fun x => fun ij => x (lowerTriangleCastLE hqp ij) :=
    funext fun x => symmetricCongruenceLinearMap_lowerTriangleGram hqp x
  rw [nonsingularWishartMeasure_one_eq_map_lowerTriangleGram hn,
    nonsingularWishartMeasure_one_eq_map_lowerTriangleGram hnq,
    Measure.map_map hcong (measurable_lowerTriangleGram p), hfun,
    ← Measure.map_map (measurable_lowerTriangleGram q) hproj,
    map_lowerTriangleCastLE_pi_bartlettCoordinateMeasure hqp hn]

/-! ### Congruence by a matrix of full row rank -/

/-- Congruence by an invertible matrix, in the unbundled form in which it composes with the
congruences by rectangular matrices. -/
private theorem map_symmetricCongruenceLinearMap_nonsingularWishartMeasure_of_det_ne_zero (n : ℝ)
    (S : Matrix (Fin p) (Fin p) ℝ) {C : Matrix (Fin p) (Fin p) ℝ} (hC : C.det ≠ 0) :
    (nonsingularWishartMeasure n S).map (Matrix.symmetricCongruenceLinearMap C) =
      nonsingularWishartMeasure n (C * S * Cᵀ) := by
  set G := Matrix.GeneralLinearGroup.mkOfDetNeZero C hC
  have hcoe : (G : Matrix (Fin p) (Fin p) ℝ) = C := rfl
  have hfun : ⇑(Matrix.GeneralLinearGroup.symmetricCongruence G) =
      ⇑(Matrix.symmetricCongruenceLinearMap C) :=
    funext fun A => Subtype.ext (by
      rw [Matrix.GeneralLinearGroup.coe_symmetricCongruence_apply,
        Matrix.coe_symmetricCongruenceLinearMap_apply, hcoe])
  rw [← hfun, map_symmetricCongruence_nonsingularWishartMeasure n S G, hcoe]

/-- **Congruence by a matrix of full row rank carries the nonsingular Wishart law of scale `S` to
the one of scale `M * S * Mᵀ`.** Full row rank keeps the new scale positive definite, so the
image stays inside the density family. -/
theorem map_symmetricCongruenceLinearMap_nonsingularWishartMeasure
    (M : Matrix (Fin q) (Fin p) ℝ) (hM : M.rank = q) (hS : S.PosDef) (hn : (p : ℝ) - 1 < n) :
    (nonsingularWishartMeasure n S).map (Matrix.symmetricCongruenceLinearMap M) =
      nonsingularWishartMeasure n (M * S * Mᵀ) := by
  have hqp : q ≤ p := hM ▸ M.rank_le_width
  have hMS : (M * S * Mᵀ).PosDef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hS.mul_mul_conjTranspose_same
        ((Matrix.rank_eq_card_iff_vecMul_injective M).1 (by simpa using hM))
  obtain ⟨R, hR⟩ := hS.exists_generalLinearGroup_mul_transpose_eq
  obtain ⟨T, hT⟩ := hMS.exists_generalLinearGroup_mul_transpose_eq
  set Rm := (R : Matrix (Fin p) (Fin p) ℝ)
  set Tm := (T : Matrix (Fin q) (Fin q) ℝ)
  set E := (1 : Matrix (Fin p) (Fin p) ℝ).submatrix (Fin.castLE hqp) id with hE
  -- Absorbing the scale, `M * Rm` has Gram matrix `Tm * Tmᵀ`, so it factors as `Tm * (E * Q)`
  -- with `Q` orthogonal.
  have hMRT : Tm * Tmᵀ = M * Rm * (M * Rm)ᵀ := by
    rw [hT, Matrix.transpose_mul,
      show M * Rm * (Rmᵀ * Mᵀ) = M * (Rm * Rmᵀ) * Mᵀ by simp only [Matrix.mul_assoc], hR]
  obtain ⟨Q, hQ, hQfac⟩ := Matrix.exists_mul_transpose_eq_one_and_eq_mul_submatrix_castLE (M * Rm)
    hqp (Matrix.GeneralLinearGroup.det_ne_zero T) hMRT
  have hMR : M * Rm = Tm * (E * Q) := by
    have hsel : (1 : Matrix (Fin p) (Fin p) ℝ).submatrix (Fin.castLE hqp) id * Q =
        Q.submatrix (Fin.castLE hqp) id := by
      simpa using Matrix.one_submatrix_mul (Fin.castLE hqp) (Equiv.refl (Fin p)) Q
    rw [hE, hsel, hQfac]
  have hQdet : Q.det ≠ 0 := by
    have hdet : Q.det * Q.det = 1 := by
      simpa [Matrix.det_transpose] using congrArg Matrix.det hQ
    intro h
    rw [h, mul_zero] at hdet
    exact zero_ne_one hdet
  -- The four congruences: by `Rm`, which builds the scale `S`; by the orthogonal `Q`, which fixes
  -- the standard law; by `E`, which selects coordinates; and by `Tm`, which builds the new scale.
  have hmeas : ∀ {a b : ℕ} (N : Matrix (Fin a) (Fin b) ℝ),
      Measurable (Matrix.symmetricCongruenceLinearMap N) :=
    fun N => (LinearMap.continuous_of_finiteDimensional _).measurable
  have hcomp : ∀ {a b c : ℕ} (N : Matrix (Fin a) (Fin b) ℝ) (P : Matrix (Fin b) (Fin c) ℝ),
      ⇑(Matrix.symmetricCongruenceLinearMap N) ∘ ⇑(Matrix.symmetricCongruenceLinearMap P) =
        ⇑(Matrix.symmetricCongruenceLinearMap (N * P)) := fun N P => by
    rw [Matrix.symmetricCongruenceLinearMap_mul, LinearMap.coe_comp]
  have hstart : nonsingularWishartMeasure n S =
      (nonsingularWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ)).map
        (Matrix.symmetricCongruenceLinearMap Rm) := by
    rw [map_symmetricCongruenceLinearMap_nonsingularWishartMeasure_of_det_ne_zero n 1
      (Matrix.GeneralLinearGroup.det_ne_zero R), Matrix.mul_one, hR]
  have hQfix : (nonsingularWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ)).map
      (Matrix.symmetricCongruenceLinearMap Q) =
      nonsingularWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ) := by
    rw [map_symmetricCongruenceLinearMap_nonsingularWishartMeasure_of_det_ne_zero n 1 hQdet,
      Matrix.mul_one, hQ]
  have hfun : ⇑(Matrix.symmetricCongruenceLinearMap M) ∘
        ⇑(Matrix.symmetricCongruenceLinearMap Rm) =
      ⇑(Matrix.symmetricCongruenceLinearMap Tm) ∘
        (⇑(Matrix.symmetricCongruenceLinearMap E) ∘
          ⇑(Matrix.symmetricCongruenceLinearMap Q)) := by
    rw [hcomp, hcomp, hcomp, hMR]
  rw [hstart, Measure.map_map (hmeas M) (hmeas Rm), hfun,
    ← Measure.map_map (hmeas Tm) ((hmeas E).comp (hmeas Q)),
    ← Measure.map_map (hmeas E) (hmeas Q), hQfix, hE,
    map_submatrix_one_nonsingularWishartMeasure_one hqp hn,
    map_symmetricCongruenceLinearMap_nonsingularWishartMeasure_of_det_ne_zero n 1
      (Matrix.GeneralLinearGroup.det_ne_zero T), Matrix.mul_one, hT]

/-! ### Principal submatrices -/

/-- **The leading principal submatrices of a nonsingular Wishart matrix are Wishart.** Reading the
first `q` coordinates of a Wishart matrix of degree `n` and positive-definite scale `S` gives the
Wishart law of the same degree with the corresponding submatrix of `S` as its scale. The
congruence matrix here is the identity with its last `p - q` rows deleted, so congruence by it is
the leading principal submatrix (`Matrix.submatrix_one_mul_mul_submatrix_one`). -/
theorem map_symmetricCongruenceLinearMap_submatrix_one_nonsingularWishartMeasure (hqp : q ≤ p)
    (hS : S.PosDef) (hn : (p : ℝ) - 1 < n) :
    (nonsingularWishartMeasure n S).map
        (Matrix.symmetricCongruenceLinearMap
          ((1 : Matrix (Fin p) (Fin p) ℝ).submatrix (Fin.castLE hqp) id)) =
      nonsingularWishartMeasure n (S.submatrix (Fin.castLE hqp) (Fin.castLE hqp)) := by
  have hEE : (1 : Matrix (Fin p) (Fin p) ℝ).submatrix (Fin.castLE hqp) id *
      ((1 : Matrix (Fin p) (Fin p) ℝ).submatrix (Fin.castLE hqp) id)ᵀ =
      (1 : Matrix (Fin q) (Fin q) ℝ) := by
    have h := Matrix.submatrix_one_mul_mul_submatrix_one (Fin.castLE hqp)
      (1 : Matrix (Fin p) (Fin p) ℝ)
    rw [Matrix.mul_one] at h
    rw [Matrix.transpose_submatrix, Matrix.transpose_one, h,
      Matrix.submatrix_one _ (Fin.castLE_injective hqp)]
  have hrank : ((1 : Matrix (Fin p) (Fin p) ℝ).submatrix (Fin.castLE hqp) id).rank = q := by
    refine le_antisymm (Matrix.rank_le_height _) ?_
    calc q = ((1 : Matrix (Fin p) (Fin p) ℝ).submatrix (Fin.castLE hqp) id *
                ((1 : Matrix (Fin p) (Fin p) ℝ).submatrix (Fin.castLE hqp) id)ᵀ).rank := by
          rw [hEE, Matrix.rank_one, Fintype.card_fin]
      _ ≤ _ := Matrix.rank_mul_le_left _ _
  rw [map_symmetricCongruenceLinearMap_nonsingularWishartMeasure _ hrank hS hn,
    Matrix.transpose_submatrix, Matrix.transpose_one, Matrix.submatrix_one_mul_mul_submatrix_one]

end TauCeti
