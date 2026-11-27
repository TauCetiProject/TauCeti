/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.LinearAlgebra.Matrix.ToQuadraticForm
public import TauCeti.Topology.Algebra.Module.BilinearForm
import TauCeti.Analysis.PDE.Ellipticity.Basic

/-!
# Uniform quadratic bounds for compact positive-definite matrix families

For a continuous family `A : X → Matrix ι ι ℝ` of positive-definite matrices, with compact
parameter space `X` and finite index type `ι`, there are constants `a, b > 0` such that
`a * ‖ξ‖² ≤ (A x).toQuadraticForm' ξ ≤ b * ‖ξ‖²` for every parameter `x` and vector `ξ`.
The same constants work across all parameters and vectors, including in dimension zero.
These uniform ellipticity bounds are used for segment-averaged inverse matrices.

For a single matrix, `Matrix.toQuadraticForm'_eq_mul_norm_sq` identifies `A.toQuadraticForm' ξ` on
a one-dimensional index type with `A default default * ‖ξ‖²`, while
`Matrix.toQuadraticForm'_le_sum_abs_mul_sq` gives the general explicit upper bound
`A.toQuadraticForm' ξ ≤ (∑ᵢⱼ |Aᵢⱼ|) ‖ξ‖²`, so a bound on the entries of a coefficient field is an
upper ellipticity bound (`Matrix.toQuadraticForm'_le_of_forall_abs_le`). Conversely, the diagonal
entries are values of the form (`Matrix.toQuadraticForm'_single`), so quadratic bounds
`0 ≤ ξᵀ A ξ ≤ Λ ‖ξ‖²` give `0 ≤ tr A ≤ card ι * Λ`
(`Matrix.trace_nonneg_of_toQuadraticForm'_nonneg`,
`Matrix.trace_le_card_mul_of_toQuadraticForm'_le`). Along the segment from
the identity to a matrix with bounds `λ` and `Λ`, the bounds `min 1 λ` and `max 1 Λ` hold
(`Matrix.min_one_mul_norm_sq_le_toQuadraticForm'_lineMap` and
`Matrix.toQuadraticForm'_lineMap_le_max_one_mul_norm_sq`); this is the ellipticity of the
operators `(1 - t) Δ + t L` of the method of continuity.

The statement is adapted from the
[KLS formalization](https://github.com/human-ai-mathematics/kls-lean/tree/e60bc39b18ef691263c66e2dba8d64726f18060d/formalization/FunctionalInequalities/Analysis/Matrix).
-/

public section

open Set Metric
open scoped Matrix

/-- Over a unique index type, the quadratic form of a real `1 × 1` matrix is its unique entry times
`‖ξ‖²`. -/
theorem Matrix.toQuadraticForm'_eq_mul_norm_sq {ι : Type*} [Unique ι] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (ξ : EuclideanSpace ℝ ι) :
    A.toQuadraticForm' ξ = A default default * ‖ξ‖ ^ 2 := by
  simp only [Matrix.toQuadraticForm'_apply, dotProduct, Matrix.mulVec, Finset.univ_unique,
    Finset.sum_singleton, EuclideanSpace.real_norm_sq_eq]
  ring

/-- The quadratic form of a real matrix is bounded above by the sum of the absolute values of its
entries times `‖ξ‖²`. -/
theorem Matrix.toQuadraticForm'_le_sum_abs_mul_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (ξ : EuclideanSpace ℝ ι) :
    A.toQuadraticForm' ξ ≤ (∑ i, ∑ j, |A i j|) * ‖ξ‖ ^ 2 :=
  (TauCeti.PDE.toQuadraticForm'_le_norm_matrixBilinearForm_mul_sq A ξ).trans
    (mul_le_mul_of_nonneg_right (TauCeti.PDE.norm_matrixBilinearForm_le_sum_abs A) (sq_nonneg _))

/-- A bound `|Aᵢⱼ| ≤ M` on the entries of a real matrix gives the upper quadratic bound
`A.toQuadraticForm' ξ ≤ (∑ᵢⱼ M) ‖ξ‖²`. -/
theorem Matrix.toQuadraticForm'_le_of_forall_abs_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} {M : ℝ} (hA : ∀ i j, |A i j| ≤ M) (ξ : EuclideanSpace ℝ ι) :
    A.toQuadraticForm' ξ ≤ (∑ _i : ι, ∑ _j : ι, M) * ‖ξ‖ ^ 2 :=
  (A.toQuadraticForm'_le_sum_abs_mul_sq ξ).trans (mul_le_mul_of_nonneg_right
    (Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hA i j) (sq_nonneg _))

/-- A lower quadratic bound `λ ‖ξ‖² ≤ ξᵀ A ξ` gives the lower bound `min 1 λ ‖ξ‖²` at every point
`(1 - s) 1 + s A`, `s ∈ [0, 1]`, of the segment from the identity matrix to `A`. -/
theorem Matrix.min_one_mul_norm_sq_le_toQuadraticForm'_lineMap {ι : Type*} [Fintype ι]
    [DecidableEq ι] {A : Matrix ι ι ℝ} {lam s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    {ξ : EuclideanSpace ℝ ι} (hA : lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ) :
    min 1 lam * ‖ξ‖ ^ 2 ≤ (AffineMap.lineMap (1 : Matrix ι ι ℝ) A s).toQuadraticForm' ξ := by
  simp only [AffineMap.lineMap_apply_module, Matrix.toQuadraticForm'_add,
    Matrix.toQuadraticForm'_smul, _root_.add_apply, _root_.smul_apply,
    TauCeti.PDE.toQuadraticForm'_one, smul_eq_mul]
  have hξ := sq_nonneg ‖ξ‖
  have hm₁ : min 1 lam * ‖ξ‖ ^ 2 ≤ ‖ξ‖ ^ 2 := mul_le_of_le_one_left hξ (min_le_left _ _)
  have hm₂ : min 1 lam * ‖ξ‖ ^ 2 ≤ lam * ‖ξ‖ ^ 2 := mul_le_mul_of_nonneg_right (min_le_right _ _) hξ
  nlinarith [mul_le_mul_of_nonneg_left hm₁ (sub_nonneg.2 hs.2),
    mul_le_mul_of_nonneg_left (hm₂.trans hA) hs.1]

/-- An upper quadratic bound `ξᵀ A ξ ≤ Λ ‖ξ‖²` gives the upper bound `max 1 Λ ‖ξ‖²` at every point
`(1 - s) 1 + s A`, `s ∈ [0, 1]`, of the segment from the identity matrix to `A`. -/
theorem Matrix.toQuadraticForm'_lineMap_le_max_one_mul_norm_sq {ι : Type*} [Fintype ι]
    [DecidableEq ι] {A : Matrix ι ι ℝ} {Lam s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    {ξ : EuclideanSpace ℝ ι} (hA : A.toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) :
    (AffineMap.lineMap (1 : Matrix ι ι ℝ) A s).toQuadraticForm' ξ ≤ max 1 Lam * ‖ξ‖ ^ 2 := by
  simp only [AffineMap.lineMap_apply_module, Matrix.toQuadraticForm'_add,
    Matrix.toQuadraticForm'_smul, _root_.add_apply, _root_.smul_apply,
    TauCeti.PDE.toQuadraticForm'_one, smul_eq_mul]
  have hξ := sq_nonneg ‖ξ‖
  have hM₁ : ‖ξ‖ ^ 2 ≤ max 1 Lam * ‖ξ‖ ^ 2 := le_mul_of_one_le_left hξ (le_max_left _ _)
  have hM₂ : Lam * ‖ξ‖ ^ 2 ≤ max 1 Lam * ‖ξ‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hξ
  nlinarith [mul_le_mul_of_nonneg_left hM₁ (sub_nonneg.2 hs.2),
    mul_le_mul_of_nonneg_left (hA.trans hM₂) hs.1]

/-- The quadratic form of a matrix at a standard basis vector is the corresponding diagonal
entry. -/
@[simp]
theorem Matrix.toQuadraticForm'_single {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) (i : ι) :
    A.toQuadraticForm' (Pi.single i 1) = A i i := by
  simp [Matrix.toQuadraticForm'_apply]

/-- A matrix whose quadratic form is nonnegative has nonnegative trace: its diagonal entries are
values of the form. -/
theorem Matrix.trace_nonneg_of_toQuadraticForm'_nonneg {R ι : Type*} [CommRing R] [PartialOrder R]
    [IsOrderedAddMonoid R] [Fintype ι] [DecidableEq ι] {A : Matrix ι ι R}
    (hA : ∀ x, 0 ≤ A.toQuadraticForm' x) : 0 ≤ A.trace :=
  Finset.sum_nonneg fun i _ ↦ by simpa using hA (Pi.single i 1)

/-- An upper quadratic bound `ξᵀ A ξ ≤ Λ ‖ξ‖²` bounds the trace of `A` by `card ι * Λ`: its
diagonal entries are values of the form at unit vectors. -/
theorem Matrix.trace_le_card_mul_of_toQuadraticForm'_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} {Lam : ℝ}
    (hA : ∀ ξ : EuclideanSpace ℝ ι, A.toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) :
    A.trace ≤ Fintype.card ι * Lam := by
  calc A.trace = ∑ i, A i i := rfl
    _ ≤ ∑ _i : ι, Lam := Finset.sum_le_sum fun i _ ↦ by
      simpa using hA (EuclideanSpace.single i 1)
    _ = Fintype.card ι * Lam := by simp

namespace TauCeti

/-- A compact continuous positive-definite matrix family has common positive lower and upper
quadratic bounds, with constants independent of both the family parameter and the vector. -/
theorem exists_uniform_quadratic_bounds {ι X : Type*} [Fintype ι] [DecidableEq ι]
    [TopologicalSpace X] [CompactSpace X]
    (A : X → Matrix ι ι ℝ) (hA : Continuous A) (hpos : ∀ x, (A x).PosDef) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ x (ξ : EuclideanSpace ℝ ι),
      a * ‖ξ‖ ^ 2 ≤ (A x).toQuadraticForm' ξ ∧
        (A x).toQuadraticForm' ξ ≤ b * ‖ξ‖ ^ 2 := by
  -- Supply the bounded-convergence instances used by the general bilinear coercivity API.
  let : ContinuousAdd (EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ) :=
    (inferInstance : IsTopologicalAddGroup
      (EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ)).toContinuousAdd
  let : ContinuousSMul ℝ (EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ) :=
    ContinuousLinearMap.continuousSMul
  let B : X → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ := fun x =>
    PDE.matrixBilinearForm (A x)
  have hB : Continuous B := PDE.continuous_matrixBilinearForm.comp hA
  have hpositive (x : X) (_ : x ∈ (univ : Set X)) (ξ : EuclideanSpace ℝ ι) (hξ : ξ ≠ 0) :
      0 < B x ξ ξ := by
    dsimp only [B]
    rw [PDE.matrixBilinearForm_self, Matrix.toQuadraticForm'_apply]
    apply (hpos x).dotProduct_mulVec_pos
    intro hz
    apply hξ
    ext i
    exact congrFun hz i
  obtain ⟨a, ha, hlo⟩ := isCompact_univ.exists_pos_forall_mul_norm_sq_le
    hB.continuousOn hpositive
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn (f := B) hB.continuousOn
  let b : ℝ := max M 0 + 1
  have hMb : M ≤ b := (le_max_left M 0).trans (le_add_of_nonneg_right zero_le_one)
  refine ⟨a, b, ha, by positivity, fun x ξ => ⟨?_, ?_⟩⟩
  · exact (hlo x (mem_univ x) ξ).trans_eq (PDE.matrixBilinearForm_self (A x) ξ)
  · calc
      (A x).toQuadraticForm' ξ ≤ ‖B x‖ * ‖ξ‖ ^ 2 :=
        PDE.toQuadraticForm'_le_norm_matrixBilinearForm_mul_sq (A x) ξ
      _ ≤ b * ‖ξ‖ ^ 2 :=
        mul_le_mul_of_nonneg_right ((hM x (mem_univ x)).trans hMb) (sq_nonneg _)

end TauCeti
