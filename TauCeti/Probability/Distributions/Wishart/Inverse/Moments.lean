/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Probability.Distributions.InverseGamma.Moments
public import TauCeti.Probability.Distributions.Wishart.Inverse.Basic

import TauCeti.Analysis.Matrix.PosSemidef
import TauCeti.Analysis.Matrix.Sqrt
import TauCeti.LinearAlgebra.Matrix.Triangular
import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Integrable
import TauCeti.Probability.Distributions.Wishart.Bartlett
import Mathlib.LinearAlgebra.Matrix.Swap
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# Moments of the inverse-Wishart family

At the standard scale, each diagonal entry has an inverse-gamma law.
The proof uses Cholesky coordinates of the source Wishart matrix.
Orthogonal congruence transports this law to every diagonal entry.
It also makes the off-diagonal means vanish.
Congruence by a square root carries the standard mean to a positive-definite scale.

For a positive-definite scale `S` and degree above the threshold `p + 1`,
the mean is `(n - p - 1)⁻¹ • S`.
This threshold is sharp within the valid family:
for a positive-definite scale in positive dimension,
the matrix is not integrable when `p - 1 < n ≤ p + 1`.

## Main results

* `TauCeti.Probability.map_coe_apply_inverseWishartMeasure_one` identifies each diagonal marginal.
* `TauCeti.Probability.integrable_id_inverseWishartMeasure` gives integrability above the threshold.
* `TauCeti.Probability.integral_id_inverseWishartMeasure` computes the mean above the threshold.
* `TauCeti.Probability.not_integrable_id_inverseWishartMeasure` proves sharpness in positive
  dimension.
* `TauCeti.Probability.integrable_id_inverseWishartMeasure_zero` covers integrability in dimension
  zero.
* `TauCeti.Probability.integral_id_inverseWishartMeasure_zero` computes the mean in dimension zero.

## References

* R. J. Muirhead, *Aspects of Multivariate Statistical Theory*, Wiley, 1982, chapter 3.
* M. L. Eaton, *Multivariate Statistics: A Vector Space Approach*, IMS Lecture Notes 53, chapter 8.
-/

public section

noncomputable section

open MeasureTheory

open scoped ENNReal Matrix MatrixOrder

namespace TauCeti.Probability

variable {p : ℕ} {n : ℝ} {S : Matrix (Fin p) (Fin p) ℝ}

/-! ### The law of a diagonal entry at the standard scale -/

/-- The last diagonal entry of the inverse of the Gram matrix `L * Lᵀ` of a lower-triangular `L`
with positive diagonal is the inverse square of the last diagonal entry of `L`: the inverse of a
lower-triangular matrix is again lower triangular, so a single term of the Gram sum survives at
the last index. -/
private theorem inv_coe_lowerTriangleGram_apply_last {q : ℕ} {x : lowerTriangle (q + 1) → ℝ}
    (hx : x ∈ posDiagLowerRegion (q + 1)) :
    ((lowerTriangleGram (q + 1) x : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ)⁻¹)
        (Fin.last q) (Fin.last q) = (x ⟨(Fin.last q, Fin.last q), le_rfl⟩ ^ 2)⁻¹ := by
  set L := lowerTriangleMatrix (q + 1) x with hLdef
  have htri : L.IsLowerTriangular := isLowerTriangular_lowerTriangleMatrix x
  have hdiag : ∀ i : Fin (q + 1), L i i = x ⟨(i, i), le_rfl⟩ :=
    fun i ↦ lowerTriangleMatrix_apply_of_le x le_rfl
  have hpos : ∀ i : Fin (q + 1), 0 < L i i := by
    intro i
    rw [hdiag i]
    exact (mem_posDiagLowerRegion _).1 hx i
  have hdet : IsUnit L.det := by
    rw [Matrix.det_of_isLowerTriangular L htri, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.2 fun i _ ↦ (hpos i).ne'
  have hinvtri : L⁻¹.IsLowerTriangular := by
    have : Invertible L := Matrix.invertibleOfIsUnitDet L hdet
    exact Matrix.blockTriangular_inv_of_blockTriangular htri
  have hne : L (Fin.last q) (Fin.last q) ≠ 0 := (hpos _).ne'
  have hinvdiag : L⁻¹ (Fin.last q) (Fin.last q) = (L (Fin.last q) (Fin.last q))⁻¹ := by
    have h := congrFun (congrFun (Matrix.nonsing_inv_mul L hdet) (Fin.last q)) (Fin.last q)
    rw [Matrix.mul_apply_diag_of_isLowerTriangular hinvtri htri, Matrix.one_apply_eq] at h
    field_simp
    exact h
  have hgram : (lowerTriangleGram (q + 1) x : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ)⁻¹ =
      L⁻¹ᵀ * L⁻¹ := by
    rw [coe_lowerTriangleGram, ← hLdef, Matrix.mul_inv_rev, ← Matrix.transpose_nonsing_inv]
  rw [hgram, Matrix.mul_apply, Finset.sum_eq_single (Fin.last q)]
  · rw [Matrix.transpose_apply, hinvdiag, hdiag]
    ring
  · intro k _ hk
    have hklt : k < Fin.last q := lt_of_le_of_ne (Fin.le_last k) hk
    rw [hinvtri (by simpa using hklt), mul_zero]
  · exact fun h ↦ absurd (Finset.mem_univ _) h

/-- **The last diagonal entry of an inverse-Wishart matrix of standard scale is inverse gamma.**
In Cholesky coordinates this entry is the inverse square of the last diagonal coordinate, whose
chi law with `n - p + 1` degrees of freedom passes to the inverse-gamma law on inverting its
square. -/
private theorem map_coe_apply_last_inverseWishartMeasure_one {q : ℕ} (hn : (q : ℝ) < n) :
    (inverseWishartMeasure n (1 : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ)).map
        (fun B : selfAdjoint.submodule ℝ (Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ) ↦
          (B : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ) (Fin.last q) (Fin.last q)) =
      Probability.inverseGammaMeasure ((n - (q : ℝ)) / 2) (1 / 2) := by
  have hn' : ((q + 1 : ℕ) : ℝ) - 1 < n := by
    push_cast
    linarith
  have hk : 0 < n - (q : ℝ) := by linarith
  have : ∀ ij : lowerTriangle (q + 1), IsProbabilityMeasure (bartlettCoordinateMeasure n ij) :=
    fun ij ↦ isProbabilityMeasure_bartlettCoordinateMeasure hn' ij
  have hIW : inverseWishartMeasure n (1 : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ) =
      (Measure.pi (bartlettCoordinateMeasure (p := q + 1) n)).map
        (symmetricInv ∘ lowerTriangleGram (q + 1)) := by
    rw [inverseWishartMeasure_def, inv_one,
      nonsingularWishartMeasure_one_eq_map_lowerTriangleGram hn',
      Measure.map_map measurable_symmetricInv (measurable_lowerTriangleGram _)]
  rw [hIW, Measure.map_map (selfAdjoint.measurable_coe_apply _ _)
    (measurable_symmetricInv.comp (measurable_lowerTriangleGram _))]
  have hcongr : (fun B : selfAdjoint.submodule ℝ (Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ) ↦
        (B : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ) (Fin.last q) (Fin.last q)) ∘
        (symmetricInv ∘ lowerTriangleGram (q + 1)) =ᵐ[Measure.pi
          (bartlettCoordinateMeasure (p := q + 1) n)]
      (fun t : ℝ ↦ (t ^ 2)⁻¹) ∘
        Function.eval (⟨(Fin.last q, Fin.last q), le_rfl⟩ : lowerTriangle (q + 1)) := by
    have hpos : ∀ᵐ x ∂(Measure.pi (bartlettCoordinateMeasure (p := q + 1) n)),
        x ∈ posDiagLowerRegion (q + 1) :=
      ae_iff.2 (pi_bartlettCoordinateMeasure_compl_posDiagLowerRegion hn')
    filter_upwards [hpos] with x hx
    simpa using inv_coe_lowerTriangleGram_apply_last hx
  have heval : (Measure.pi (bartlettCoordinateMeasure (p := q + 1) n)).map
      (Function.eval (⟨(Fin.last q, Fin.last q), le_rfl⟩ : lowerTriangle (q + 1))) =
      bartlettCoordinateMeasure n (⟨(Fin.last q, Fin.last q), le_rfl⟩ : lowerTriangle (q + 1)) :=
    (measurePreserving_eval (μ := bartlettCoordinateMeasure (p := q + 1) n) _).map_eq
  have hcomp := Measure.map_map (μ := Measure.pi (bartlettCoordinateMeasure (p := q + 1) n))
    (g := fun t : ℝ ↦ (t ^ 2)⁻¹)
    (f := Function.eval (⟨(Fin.last q, Fin.last q), le_rfl⟩ : lowerTriangle (q + 1)))
    (by fun_prop) (measurable_pi_apply _)
  rw [Measure.map_congr hcongr, ← hcomp, heval, bartlettCoordinateMeasure_of_eq n rfl]
  -- squaring and then inverting, so that the chi law passes through the chi-squared law
  have hsq : (fun t : ℝ ↦ (t ^ 2)⁻¹) = Inv.inv ∘ fun t : ℝ ↦ t ^ 2 := rfl
  rw [hsq, ← Measure.map_map measurable_inv (by fun_prop)]
  simp only [Fin.val_last]
  rw [Probability.map_sq_withDensity_eq_chiSquaredMeasure hk,
    Probability.chiSquaredMeasure_eq_gammaMeasure hk,
    Probability.inverseGammaMeasure_of_pos (by linarith) (by norm_num)]

/-! ### The mean -/

/-- Congruence by an orthogonal matrix leaves the inverse-Wishart law of standard scale
unchanged. -/
private theorem map_symmetricCongruence_inverseWishartMeasure_one
    {C : Matrix.GeneralLinearGroup (Fin p) ℝ}
    (hC : (C : Matrix (Fin p) (Fin p) ℝ) * (C : Matrix (Fin p) (Fin p) ℝ)ᵀ = 1) :
    (inverseWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ)).map
        (Matrix.GeneralLinearGroup.symmetricCongruence C) =
      inverseWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ) := by
  rw [map_symmetricCongruence_inverseWishartMeasure, Matrix.mul_one, hC]

/-- Congruence by a swap matrix permutes the two indices of every entry. -/
private theorem coe_symmetricCongruence_swap_apply (i j a b : Fin p)
    (B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    (Matrix.GeneralLinearGroup.symmetricCongruence (Matrix.GeneralLinearGroup.swap ℝ i j) B :
        Matrix (Fin p) (Fin p) ℝ) a b =
      (B : Matrix (Fin p) (Fin p) ℝ) (Equiv.swap i j a) (Equiv.swap i j b) := by
  rw [Matrix.GeneralLinearGroup.coe_symmetricCongruence_apply,
    Matrix.GeneralLinearGroup.val_swap, Matrix.transpose_swap, Matrix.swap,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  simp

/-- **Every diagonal entry of an inverse-Wishart matrix of standard scale is inverse gamma**, with
shape `(n - p + 1) / 2` and scale `1 / 2`. Equivalently, the reciprocal of a diagonal entry is
chi-squared with `n - p + 1` degrees of freedom. -/
theorem map_coe_apply_inverseWishartMeasure_one (hn : (p : ℝ) - 1 < n) (i : Fin p) :
    (inverseWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ)).map
        (fun B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
          (B : Matrix (Fin p) (Fin p) ℝ) i i) =
      Probability.inverseGammaMeasure ((n - (p : ℝ) + 1) / 2) (1 / 2) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := i.pos; omega⟩
  set C : Matrix.GeneralLinearGroup (Fin (q + 1)) ℝ :=
    Matrix.GeneralLinearGroup.swap ℝ i (Fin.last q) with hC
  have hmeasC : Measurable (Matrix.GeneralLinearGroup.symmetricCongruence C) :=
    (Matrix.GeneralLinearGroup.symmetricCongruence C).continuous.measurable
  have hfun : (fun B : selfAdjoint.submodule ℝ (Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ) ↦
        (B : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ) i i) =
      (fun B : selfAdjoint.submodule ℝ (Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ) ↦
          (B : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ) (Fin.last q) (Fin.last q)) ∘
        (Matrix.GeneralLinearGroup.symmetricCongruence C) := by
    funext B
    rw [Function.comp_apply, hC, coe_symmetricCongruence_swap_apply, Equiv.swap_apply_right]
  have hcomp := Measure.map_map (μ := inverseWishartMeasure n
      (1 : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ))
    (g := fun B : selfAdjoint.submodule ℝ (Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ) ↦
      (B : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ) (Fin.last q) (Fin.last q))
    (f := (Matrix.GeneralLinearGroup.symmetricCongruence C))
    (selfAdjoint.measurable_coe_apply _ _) hmeasC
  have horth : (C : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ) *
      (C : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ)ᵀ = 1 := by
    rw [hC, Matrix.GeneralLinearGroup.val_swap, Matrix.transpose_swap]
    exact Matrix.swap_mul_self i (Fin.last q)
  rw [hfun, ← hcomp, map_symmetricCongruence_inverseWishartMeasure_one horth,
    map_coe_apply_last_inverseWishartMeasure_one (by push_cast at hn; linarith)]
  congr 2
  push_cast
  ring

/-- Congruence by the diagonal sign matrix that flips the index `k` changes the sign of exactly
the entries with one index equal to `k`. -/
private theorem coe_symmetricCongruence_sign_apply {D : Matrix.GeneralLinearGroup (Fin p) ℝ}
    {d : Fin p → ℝ} (hD : (D : Matrix (Fin p) (Fin p) ℝ) = Matrix.diagonal d) (a b : Fin p)
    (B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    (Matrix.GeneralLinearGroup.symmetricCongruence D B : Matrix (Fin p) (Fin p) ℝ) a b =
      d a * (B : Matrix (Fin p) (Fin p) ℝ) a b * d b := by
  rw [Matrix.GeneralLinearGroup.coe_symmetricCongruence_apply, hD, Matrix.diagonal_transpose,
    Matrix.mul_diagonal, Matrix.diagonal_mul]

/-- The diagonal sign matrix flipping the index `k` is an involution. -/
private theorem diagonal_sign_mul_self (k : Fin p) :
    (Matrix.diagonal fun j : Fin p ↦ if j = k then (-1 : ℝ) else 1) *
      (Matrix.diagonal fun j : Fin p ↦ if j = k then (-1 : ℝ) else 1) = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  exact congrArg Matrix.diagonal (by funext j; by_cases h : j = k <;> simp [h])

/-- The diagonal sign matrix flipping the index `k`, as an invertible matrix. -/
private noncomputable def signCongruence (k : Fin p) : Matrix.GeneralLinearGroup (Fin p) ℝ :=
  ⟨Matrix.diagonal fun j ↦ if j = k then -1 else 1,
    Matrix.diagonal fun j ↦ if j = k then -1 else 1,
    diagonal_sign_mul_self k, diagonal_sign_mul_self k⟩

private theorem coe_signCongruence (k : Fin p) :
    (signCongruence k : Matrix (Fin p) (Fin p) ℝ) =
      Matrix.diagonal fun j ↦ if j = k then -1 else 1 := rfl

private theorem signCongruence_mul_transpose (k : Fin p) :
    (signCongruence k : Matrix (Fin p) (Fin p) ℝ) *
      (signCongruence k : Matrix (Fin p) (Fin p) ℝ)ᵀ = 1 := by
  rw [coe_signCongruence, Matrix.diagonal_transpose]
  exact diagonal_sign_mul_self k

/-- An off-diagonal entry of an inverse-Wishart matrix of standard scale has mean zero, by the
sign symmetry of the law: flipping one index is a congruence that preserves the law and reverses
the sign of that entry. -/
private theorem integral_coe_apply_inverseWishartMeasure_one_of_ne {i j : Fin p} (hij : i ≠ j) :
    ∫ B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        (B : Matrix (Fin p) (Fin p) ℝ) i j ∂inverseWishartMeasure n 1 = 0 := by
  have hmeas : Measurable (Matrix.GeneralLinearGroup.symmetricCongruence (signCongruence i)) :=
    (Matrix.GeneralLinearGroup.symmetricCongruence (signCongruence i)).continuous.measurable
  have h := integral_map (μ := inverseWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ))
    (φ := Matrix.GeneralLinearGroup.symmetricCongruence (signCongruence i))
    (f := fun B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      (B : Matrix (Fin p) (Fin p) ℝ) i j)
    hmeas.aemeasurable (selfAdjoint.measurable_coe_apply i j).aestronglyMeasurable
  rw [map_symmetricCongruence_inverseWishartMeasure_one (signCongruence_mul_transpose i)] at h
  have hsign : (fun B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      (Matrix.GeneralLinearGroup.symmetricCongruence (signCongruence i) B :
        Matrix (Fin p) (Fin p) ℝ) i j) =
      fun B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        -((B : Matrix (Fin p) (Fin p) ℝ) i j) := by
    funext B
    rw [coe_symmetricCongruence_sign_apply (coe_signCongruence i)]
    simp [hij.symm]
  rw [hsign, integral_neg] at h
  linarith

/-- Each diagonal entry of an inverse-Wishart matrix of standard scale is integrable above the
degree threshold `p + 1`, its inverse-gamma law then having shape above one. -/
private theorem integrable_coe_apply_diag_inverseWishartMeasure_one (hn : (p : ℝ) + 1 < n)
    (i : Fin p) :
    Integrable (fun B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      (B : Matrix (Fin p) (Fin p) ℝ) i i) (inverseWishartMeasure n 1) := by
  have hmap := map_coe_apply_inverseWishartMeasure_one (by linarith : (p : ℝ) - 1 < n) i
  have hint : Integrable id (Probability.inverseGammaMeasure ((n - (p : ℝ) + 1) / 2) (1 / 2)) :=
    (Probability.integrable_id_inverseGammaMeasure_iff (by linarith) (by norm_num)).2 (by linarith)
  rw [← hmap] at hint
  simpa using (integrable_map_measure aestronglyMeasurable_id
    (selfAdjoint.measurable_coe_apply i i).aemeasurable).1 hint

/-- Every entry of an inverse-Wishart matrix of standard scale is integrable above the degree
threshold `p + 1`: positive semidefiniteness bounds an entry by the mean of the two diagonal
entries in its row and column. -/
private theorem integrable_coe_apply_inverseWishartMeasure_one (hn : (p : ℝ) + 1 < n)
    (i j : Fin p) :
    Integrable (fun B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      (B : Matrix (Fin p) (Fin p) ℝ) i j) (inverseWishartMeasure n 1) := by
  refine Integrable.mono' (((integrable_coe_apply_diag_inverseWishartMeasure_one hn i).add
      (integrable_coe_apply_diag_inverseWishartMeasure_one hn j)).div_const 2)
    (selfAdjoint.measurable_coe_apply i j).aestronglyMeasurable ?_
  filter_upwards [ae_posDef_inverseWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ)] with B hB
  have hsq : ((B : Matrix (Fin p) (Fin p) ℝ) i j) ^ 2 ≤
      (B : Matrix (Fin p) (Fin p) ℝ) i i * (B : Matrix (Fin p) (Fin p) ℝ) j j := by
    simpa [RCLike.normSq_apply, sq] using hB.posSemidef.normSq_le i j
  have hii : 0 ≤ (B : Matrix (Fin p) (Fin p) ℝ) i i := hB.posSemidef.diag_nonneg
  have hjj : 0 ≤ (B : Matrix (Fin p) (Fin p) ℝ) j j := hB.posSemidef.diag_nonneg
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs]
  nlinarith [sq_abs ((B : Matrix (Fin p) (Fin p) ℝ) i j),
    abs_nonneg ((B : Matrix (Fin p) (Fin p) ℝ) i j),
    sq_nonneg ((B : Matrix (Fin p) (Fin p) ℝ) i i - (B : Matrix (Fin p) (Fin p) ℝ) j j)]

/-- The entrywise mean of an inverse-Wishart matrix of standard scale: the diagonal entries have
the common value `(n - p - 1)⁻¹` and the off-diagonal entries vanish. -/
private theorem integral_coe_apply_inverseWishartMeasure_one (hn : (p : ℝ) + 1 < n) (i j : Fin p) :
    ∫ B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        (B : Matrix (Fin p) (Fin p) ℝ) i j ∂inverseWishartMeasure n 1 =
      (n - (p : ℝ) - 1)⁻¹ * (1 : Matrix (Fin p) (Fin p) ℝ) i j := by
  rcases eq_or_ne i j with rfl | hij
  · rw [Matrix.one_apply_eq, mul_one]
    have h := integral_map (μ := inverseWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ))
      (φ := fun B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        (B : Matrix (Fin p) (Fin p) ℝ) i i)
      (f := id) (selfAdjoint.measurable_coe_apply i i).aemeasurable aestronglyMeasurable_id
    rw [map_coe_apply_inverseWishartMeasure_one (by linarith : (p : ℝ) - 1 < n) i] at h
    simp only [id_eq] at h
    have hshape : (n - (p : ℝ) + 1) / 2 - 1 = (n - (p : ℝ) - 1) / 2 := by ring
    rw [← h, Probability.integral_id_inverseGammaMeasure (by norm_num) (by linarith), hshape]
    have hne : n - (p : ℝ) - 1 ≠ 0 := by linarith
    field_simp
  · rw [Matrix.one_apply_ne hij, mul_zero]
    exact integral_coe_apply_inverseWishartMeasure_one_of_ne hij

/-- The mean of an inverse-Wishart matrix of standard scale is `(n - p - 1)⁻¹` times the
identity. -/
private theorem integral_id_inverseWishartMeasure_one (hn : (p : ℝ) + 1 < n) :
    ∫ B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ), B ∂inverseWishartMeasure n 1 =
      (n - (p : ℝ) - 1)⁻¹ •
        (⟨1, Matrix.isHermitian_iff_isSelfAdjoint.1 Matrix.isHermitian_one⟩ :
          selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) := by
  have hcoords : Integrable (fun B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      symmetricCoordinates p B) (inverseWishartMeasure n 1) :=
    (symmetricCoordinates p).toContinuousLinearMap.integrable_comp
      (integrable_iff_integrable_coe_apply.2
        fun i j ↦ integrable_coe_apply_inverseWishartMeasure_one hn i j)
  apply (symmetricCoordinates p).injective
  funext ij
  rw [← (symmetricCoordinates p).integral_comp_comm, eval_integral fun ij ↦ hcoords.eval ij]
  simp only [symmetricCoordinates_apply, Submodule.coe_smul, Matrix.smul_apply]
  rw [integral_coe_apply_inverseWishartMeasure_one hn]
  simp

/-- An inverse-Wishart law of positive-definite scale is the standard one transported by the
congruence with a square root of the scale. -/
private theorem inverseWishartMeasure_eq_map_symmetricCongruence
    {C : Matrix.GeneralLinearGroup (Fin p) ℝ}
    (hC : (C : Matrix (Fin p) (Fin p) ℝ) * (C : Matrix (Fin p) (Fin p) ℝ)ᵀ = S) :
    inverseWishartMeasure n S =
      (inverseWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ)).map
        (Matrix.GeneralLinearGroup.symmetricCongruence C) := by
  rw [map_symmetricCongruence_inverseWishartMeasure, Matrix.mul_one, hC]

/-- **An inverse-Wishart matrix is integrable above the degree threshold `p + 1`.** -/
theorem integrable_id_inverseWishartMeasure (hS : S.PosDef) (hn : (p : ℝ) + 1 < n) :
    Integrable (fun B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦ B)
      (inverseWishartMeasure n S) := by
  obtain ⟨C, hC⟩ := hS.exists_generalLinearGroup_mul_transpose_eq
  have hmeasC : Measurable (Matrix.GeneralLinearGroup.symmetricCongruence C) :=
    (Matrix.GeneralLinearGroup.symmetricCongruence C).continuous.measurable
  have hiff := integrable_map_measure
    (μ := inverseWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ))
    (g := fun B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦ B)
    (f := Matrix.GeneralLinearGroup.symmetricCongruence C)
    aestronglyMeasurable_id hmeasC.aemeasurable
  rw [inverseWishartMeasure_eq_map_symmetricCongruence hC, hiff]
  exact (Matrix.GeneralLinearGroup.symmetricCongruence C).toContinuousLinearMap.integrable_comp
    (integrable_iff_integrable_coe_apply.2
      fun i j ↦ integrable_coe_apply_inverseWishartMeasure_one hn i j)

/-- **The mean of an inverse-Wishart law** of degree `n` and positive-definite scale `S` is
`(n - p - 1)⁻¹ • S`, for a degree above the threshold `p + 1`; in positive dimension, at a valid
degree at or below the threshold the identity is no longer integrable. -/
theorem integral_id_inverseWishartMeasure (hS : S.PosDef) (hn : (p : ℝ) + 1 < n) :
    ∫ B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ), B ∂inverseWishartMeasure n S =
      (n - (p : ℝ) - 1)⁻¹ •
        (⟨S, Matrix.isHermitian_iff_isSelfAdjoint.1 hS.1⟩ :
          selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) := by
  obtain ⟨C, hC⟩ := hS.exists_generalLinearGroup_mul_transpose_eq
  have hmeasC : Measurable (Matrix.GeneralLinearGroup.symmetricCongruence C) :=
    (Matrix.GeneralLinearGroup.symmetricCongruence C).continuous.measurable
  have hint := integral_map (μ := inverseWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ))
    (φ := Matrix.GeneralLinearGroup.symmetricCongruence C)
    (f := fun B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦ B)
    hmeasC.aemeasurable aestronglyMeasurable_id
  rw [inverseWishartMeasure_eq_map_symmetricCongruence hC, hint,
    (Matrix.GeneralLinearGroup.symmetricCongruence C).integral_comp_comm,
    integral_id_inverseWishartMeasure_one hn, map_smul]
  congr 1
  refine Subtype.ext ?_
  rw [Matrix.GeneralLinearGroup.coe_symmetricCongruence_apply]
  simpa using hC

/-- **Below the degree threshold `p + 1` an inverse-Wishart matrix is not integrable**, in every
positive dimension, as long as the degree is that of a genuine member of the family: a diagonal
entry then has an inverse-gamma law of shape at most one. Below the valid range the law is zero
and the statement fails for want of any mass. -/
theorem not_integrable_id_inverseWishartMeasure (hp : 0 < p) (hS : S.PosDef)
    (hn : (p : ℝ) - 1 < n) (hn' : n ≤ (p : ℝ) + 1) :
    ¬ Integrable (fun B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦ B)
      (inverseWishartMeasure n S) := by
  intro hint
  obtain ⟨C, hC⟩ := hS.exists_generalLinearGroup_mul_transpose_eq
  have hmeasC : Measurable (Matrix.GeneralLinearGroup.symmetricCongruence C) :=
    (Matrix.GeneralLinearGroup.symmetricCongruence C).continuous.measurable
  have hiff := integrable_map_measure
    (μ := inverseWishartMeasure n (1 : Matrix (Fin p) (Fin p) ℝ))
    (g := fun B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦ B)
    (f := Matrix.GeneralLinearGroup.symmetricCongruence C)
    aestronglyMeasurable_id hmeasC.aemeasurable
  rw [inverseWishartMeasure_eq_map_symmetricCongruence hC, hiff] at hint
  have hone : Integrable (fun B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦ B)
      (inverseWishartMeasure n 1) :=
    (((Matrix.GeneralLinearGroup.symmetricCongruence C).symm.toContinuousLinearMap).integrable_comp
      hint).congr (Filter.Eventually.of_forall fun x ↦
        (Matrix.GeneralLinearGroup.symmetricCongruence C).symm_apply_apply x)
  have hdiag := integrable_iff_integrable_coe_apply.1 hone ⟨0, hp⟩ ⟨0, hp⟩
  have hgamma : Integrable id
      (Probability.inverseGammaMeasure ((n - (p : ℝ) + 1) / 2) (1 / 2)) := by
    rw [← map_coe_apply_inverseWishartMeasure_one hn ⟨0, hp⟩]
    exact (integrable_map_measure aestronglyMeasurable_id
      (selfAdjoint.measurable_coe_apply (⟨0, hp⟩ : Fin p) ⟨0, hp⟩).aemeasurable).2
      (by simpa using hdiag)
  exact Probability.not_integrable_id_inverseGammaMeasure (by linarith) (by norm_num)
    (by linarith) hgamma

/-- In dimension zero the identity is integrable against every valid inverse-Wishart law, the
whole mass sitting at a single point. -/
theorem integrable_id_inverseWishartMeasure_zero {n : ℝ} (hn : -1 < n)
    (S : Matrix (Fin 0) (Fin 0) ℝ) :
    Integrable id (inverseWishartMeasure n S) := by
  rw [inverseWishartMeasure_zero hn]
  exact integrable_dirac (by simp)

/-- In dimension zero every valid inverse-Wishart law has mean zero, the unique symmetric
matrix. -/
theorem integral_id_inverseWishartMeasure_zero {n : ℝ} (hn : -1 < n)
    (S : Matrix (Fin 0) (Fin 0) ℝ) :
    ∫ B, B ∂inverseWishartMeasure n S = 0 := by
  rw [inverseWishartMeasure_zero hn, integral_dirac]

end TauCeti.Probability
