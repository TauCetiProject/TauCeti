/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import TauCeti.LinearAlgebra.Matrix.PosDef.Sylvester
public import TauCeti.LinearAlgebra.Matrix.Triangular
import TauCeti.Analysis.Matrix.LDL
import TauCeti.Analysis.Matrix.PosSemidef.Hadamard

/-!
# Reduced positive-definite forms and uniform Cholesky bounds

A real `n × n` matrix `b` is **`C`-reduced** in the standard basis (`TauCeti.RealSiegel.IsReduced`)
when `|b i j| < C * b i i` for all `i, j`, `b i i < C * b j j` for `i < j`, and
`∏ i, b i i < C * b.det`. On positive-definite forms, Hadamard's inequality forces `1 < C`, and
reducedness is preserved by positive scaling (`isReduced_smul_iff`), including determinant-one
normalization `b.det ^ (-(n : ℝ)⁻¹) • b`.

## Main definitions and results

* `TauCeti.RealSiegel.IsReduced`, `TauCeti.RealSiegel.reducedSet`,
  `TauCeti.RealSiegel.reducedSetInBasis`: `C`-reduced positive-definite forms, semialgebraicity in
  entry coordinates (`isSemialgebraic_reducedSet`), and `GL (Fin n) ℝ` equivariance.
* `TauCeti.RealSiegel.exists_cholesky_bound_of_isReduced` and
  `TauCeti.RealSiegel.exists_isReduced_of_cholesky_bound`: quantitative equivalence between
  `C`-reducedness of `Nᵀ * Matrix.diagonal d * N` and uniform bounds on upper-unitriangular `N` and
  adjacent ratios `d i / d (i + 1)`.
* `TauCeti.RealSiegel.abs_dotProduct_mulVec_le_of_diag_le` and
  `TauCeti.RealSiegel.exists_perm_isReduced_congr`: transfer of reducedness across an invertible
  change of basis with determinant control after sorting the diagonal via `Tuple.sort`.

## References

* B. Bakker, B. Klingler, and J. Tsimerman, *Tame topology of arithmetic quotients and
  algebraicity of Hodge loci*, J. Amer. Math. Soc. 33 (2020), 917–939, §4.5, Definition 4.11.
* V. Platonov, A. Rapinchuk, and I. Rapinchuk, *Algebraic Groups and Number Theory*, second
  edition, Vol. I, Cambridge University Press, 2023, §4.2.
-/

public section

open scoped Matrix

namespace TauCeti.RealSiegel

section Predicate

variable {n : ℕ}

/-- A real `n × n` matrix `b` is **`C`-reduced** in the standard basis when
`|b i j| < C * b i i` for all `i, j`, `b i i < C * b j j` for `i < j`, and
`∏ i, b i i < C * b.det` (Bakker–Klingler–Tsimerman, Definition 4.11). -/
def IsReduced (C : ℝ) (b : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i j, |b i j| < C * b i i) ∧ (∀ i j, i < j → b i i < C * b j j) ∧ (∏ i, b i i < C * b.det)

/-- Unfolding characterization of `IsReduced`. -/
theorem isReduced_def {C : ℝ} {b : Matrix (Fin n) (Fin n) ℝ} :
    IsReduced C b ↔
      (∀ i j, |b i j| < C * b i i) ∧ (∀ i j, i < j → b i i < C * b j j) ∧
        (∏ i, b i i < C * b.det) :=
  Iff.rfl

/-- Off-diagonal bound of a `C`-reduced matrix: `|b i j| < C * b i i`. -/
theorem IsReduced.abs_apply_lt {C : ℝ} {b : Matrix (Fin n) (Fin n) ℝ} (h : IsReduced C b)
    (i j : Fin n) : |b i j| < C * b i i :=
  h.1 i j

/-- Diagonal growth bound of a `C`-reduced matrix: `b i i < C * b j j` for `i < j`. -/
theorem IsReduced.diag_lt_of_lt {C : ℝ} {b : Matrix (Fin n) (Fin n) ℝ} (h : IsReduced C b)
    {i j : Fin n} (hij : i < j) : b i i < C * b j j :=
  h.2.1 i j hij

/-- Converse Hadamard bound of a `C`-reduced matrix: `∏ i, b i i < C * b.det`. -/
theorem IsReduced.prod_diag_lt {C : ℝ} {b : Matrix (Fin n) (Fin n) ℝ} (h : IsReduced C b) :
    ∏ i, b i i < C * b.det :=
  h.2.2

/-- If a positive-definite matrix is `C`-reduced, then `1 < C` (including in rank zero). -/
theorem IsReduced.one_lt {C : ℝ} {b : Matrix (Fin n) (Fin n) ℝ} (h : IsReduced C b)
    (hb : b.PosDef) : 1 < C :=
  lt_of_mul_lt_mul_right
    ((one_mul b.det).symm ▸ hb.posSemidef.det_le_prod_diag.trans_lt h.prod_diag_lt) hb.det_pos.le

/-- If a positive-definite matrix is `C`-reduced, then `0 < C`. -/
theorem IsReduced.pos {C : ℝ} {b : Matrix (Fin n) (Fin n) ℝ} (h : IsReduced C b)
    (hb : b.PosDef) : 0 < C :=
  zero_lt_one.trans (h.one_lt hb)

/-- Monotonicity of `IsReduced` in the threshold `C` for positive-definite matrices. -/
theorem IsReduced.mono {C C' : ℝ} {b : Matrix (Fin n) (Fin n) ℝ} (hb : b.PosDef)
    (h : IsReduced C b) (hCC' : C ≤ C') : IsReduced C' b :=
  ⟨fun i j ↦ (h.abs_apply_lt i j).trans_le (mul_le_mul_of_nonneg_right hCC' hb.diag_pos.le),
    fun _ _ hij ↦ (h.diag_lt_of_lt hij).trans_le (mul_le_mul_of_nonneg_right hCC' hb.diag_pos.le),
    h.prod_diag_lt.trans_le (mul_le_mul_of_nonneg_right hCC' hb.det_pos.le)⟩

/-- Scaling a `C`-reduced matrix by a positive real scalar preserves `C`-reducedness. -/
theorem IsReduced.smul {C a : ℝ} {b : Matrix (Fin n) (Fin n) ℝ} (ha : 0 < a) (h : IsReduced C b) :
    IsReduced C (a • b) := by
  refine ⟨fun i j ↦ ?_, fun i j hij ↦ ?_, ?_⟩
  · simp only [Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_pos ha]
    linarith [mul_lt_mul_of_pos_left (h.abs_apply_lt i j) ha]
  · simp only [Matrix.smul_apply, smul_eq_mul]
    linarith [mul_lt_mul_of_pos_left (h.diag_lt_of_lt hij) ha]
  · simp only [Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, Matrix.det_smul]
    linarith [mul_lt_mul_of_pos_left h.prod_diag_lt (pow_pos ha n)]

/-- Positive scalar invariance: for `0 < a`, `a • b` is `C`-reduced if and only if `b` is. -/
@[simp]
theorem isReduced_smul_iff {C a : ℝ} {b : Matrix (Fin n) (Fin n) ℝ} (ha : 0 < a) :
    IsReduced C (a • b) ↔ IsReduced C b :=
  ⟨fun h ↦ by simpa [inv_smul_smul₀ ha.ne'] using h.smul (inv_pos.mpr ha), IsReduced.smul ha⟩

/-- Normalizing a positive-definite `n × n` matrix (`n ≠ 0`) by `b.det ^ (-(n : ℝ)⁻¹)` produces a
matrix of determinant `1`. -/
theorem det_det_rpow_neg_inv_smul {b : Matrix (Fin n) (Fin n) ℝ} (hn : n ≠ 0) (hb : b.PosDef) :
    (b.det ^ (-(n : ℝ)⁻¹) • b).det = 1 := by
  rw [Matrix.det_smul, Fintype.card_fin, ← Real.rpow_natCast, ← Real.rpow_mul hb.det_pos.le,
    neg_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn), Real.rpow_neg_one,
    inv_mul_cancel₀ hb.det_pos.ne']

/-- Normalizing a positive-definite matrix by `b.det ^ (-(n : ℝ)⁻¹)` preserves `C`-reducedness. -/
theorem isReduced_det_rpow_neg_inv_smul_iff {C : ℝ} {b : Matrix (Fin n) (Fin n) ℝ} (hb : b.PosDef) :
    IsReduced C (b.det ^ (-(n : ℝ)⁻¹) • b) ↔ IsReduced C b :=
  isReduced_smul_iff (Real.rpow_pos_of_pos hb.det_pos _)

/-- No matrix with a nonpositive diagonal entry can be `C`-reduced for `0 ≤ C`. -/
theorem not_isReduced_of_diag_nonpos {C : ℝ} (hC : 0 ≤ C) {b : Matrix (Fin n) (Fin n) ℝ}
    (i : Fin n) (hi : b i i ≤ 0) : ¬ IsReduced C b := fun h ↦ by
  linarith [h.abs_apply_lt i i, abs_nonneg (b i i), mul_nonpos_of_nonneg_of_nonpos hC hi]

/-- In rank zero, a matrix is `C`-reduced if and only if `1 < C`. -/
@[simp]
theorem isReduced_fin_zero_iff {C : ℝ} {b : Matrix (Fin 0) (Fin 0) ℝ} :
    IsReduced C b ↔ 1 < C := by
  simp [IsReduced]

/-- In dimension one, a positive-definite matrix is `C`-reduced if and only if `1 < C`. -/
theorem isReduced_fin_one_iff {C : ℝ} {b : Matrix (Fin 1) (Fin 1) ℝ} (hb : b.PosDef) :
    IsReduced C b ↔ 1 < C := by
  refine ⟨fun h ↦ h.one_lt hb, fun hC ↦ ⟨fun i j ↦ ?_, fun i j hij ↦ ?_, ?_⟩⟩
  · rw [Subsingleton.elim i 0, Subsingleton.elim j 0, abs_of_pos hb.diag_pos]
    exact lt_mul_of_one_lt_left hb.diag_pos hC
  · exact (lt_irrefl _ (Subsingleton.elim i j ▸ hij)).elim
  · simpa [Fin.prod_univ_one, Matrix.det_fin_one] using lt_mul_of_one_lt_left hb.diag_pos hC

/-- The identity matrix of size `n` is `C`-reduced if and only if `1 < C`. -/
@[simp]
theorem isReduced_one_iff {C : ℝ} :
    IsReduced C (1 : Matrix (Fin n) (Fin n) ℝ) ↔ 1 < C := by
  refine ⟨fun h ↦ h.one_lt Matrix.PosDef.one, fun hC ↦ ⟨fun i j ↦ ?_, fun _ _ _ ↦ ?_, ?_⟩⟩
  · by_cases hij : i = j <;> simp [Matrix.one_apply, hij, hC, zero_lt_one.trans hC]
  · simpa using hC
  · simpa using hC

/-- In nonzero dimension, the zero matrix is never `C`-reduced. -/
theorem not_isReduced_zero [NeZero n] (C : ℝ) :
    ¬ IsReduced C (0 : Matrix (Fin n) (Fin n) ℝ) :=
  fun h ↦ by simpa using h.abs_apply_lt (0 : Fin n) 0

/-- For `0 ≤ C` and `n ≠ 0`, `-1` is not `C`-reduced. -/
theorem not_isReduced_neg_one [NeZero n] {C : ℝ} (hC : 0 ≤ C) :
    ¬ IsReduced C (-1 : Matrix (Fin n) (Fin n) ℝ) :=
  not_isReduced_of_diag_nonpos hC 0 (by simp)

/-- Concrete check: `diag(1, 4)` is `2`-reduced. -/
theorem isReduced_two_diagonal_one_four :
    IsReduced 2 (Matrix.diagonal ![1, (4 : ℝ)]) := by
  refine ⟨fun i j ↦ by fin_cases i <;> fin_cases j <;> norm_num,
    fun i j hij ↦ by fin_cases i <;> fin_cases j <;> simp at hij ⊢; norm_num, ?_⟩
  norm_num [Fin.prod_univ_two, Matrix.det_diagonal]

/-- Concrete check: `diag(4, 1)` is not `2`-reduced because `4 < 2 * 1` fails. -/
theorem not_isReduced_two_diagonal_four_one :
    ¬ IsReduced 2 (Matrix.diagonal ![(4 : ℝ), 1]) := fun h ↦ by
  have h01 : (0 : Fin 2) < 1 := by decide
  have hlt := h.diag_lt_of_lt h01
  norm_num at hlt

/-- Concrete check: `(diag(1, 4))⁻¹ = diag(1, 1/4)` is not `2`-reduced, so reducedness is not
preserved by matrix inversion. -/
theorem not_isReduced_two_diagonal_one_inv_four :
    ¬ IsReduced 2 (Matrix.diagonal ![1, (4⁻¹ : ℝ)]) := fun h ↦ by
  have h01 : (0 : Fin 2) < 1 := by decide
  have hlt := h.diag_lt_of_lt h01
  norm_num at hlt

end Predicate

section ReducedSet

/-- The set `T_{std, C}` of positive-definite `C`-reduced `n × n` real matrices. -/
def reducedSet (n : ℕ) (C : ℝ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {b | b.PosDef ∧ IsReduced C b}

/-- Membership in `reducedSet n C` means positive definiteness together with `IsReduced C`. -/
@[simp]
theorem mem_reducedSet_iff {n : ℕ} {C : ℝ} {b : Matrix (Fin n) (Fin n) ℝ} :
    b ∈ reducedSet n C ↔ b.PosDef ∧ IsReduced C b :=
  Iff.rfl

/-- The reduced set `reducedSet n C` is monotone in `C`. -/
theorem reducedSet_mono {n : ℕ} {C C' : ℝ} (hCC' : C ≤ C') :
    reducedSet n C ⊆ reducedSet n C' :=
  fun _ ⟨hb, hred⟩ ↦ ⟨hb, hred.mono hb hCC'⟩

/-- The identity matrix belongs to `reducedSet n C` if and only if `1 < C`. -/
theorem one_mem_reducedSet_iff {n : ℕ} {C : ℝ} :
    (1 : Matrix (Fin n) (Fin n) ℝ) ∈ reducedSet n C ↔ 1 < C := by
  simp [Matrix.PosDef.one]

/-- For `1 < C`, the one-dimensional reduced set is the entire positive-definite cone. -/
theorem reducedSet_fin_one {C : ℝ} (hC : 1 < C) :
    reducedSet 1 C = {b : Matrix (Fin 1) (Fin 1) ℝ | b.PosDef} :=
  Set.ext fun _ ↦ ⟨And.left, fun hb ↦ ⟨hb, (isReduced_fin_one_iff hb).mpr hC⟩⟩

/-- **The set of `C`-reduced positive-definite matrices is semialgebraic** in matrix-entry
coordinates `Fin n × Fin n → ℝ`. -/
theorem isSemialgebraic_reducedSet (n : ℕ) (C : ℝ) :
    TauCeti.IsSemialgebraic {s : Fin n × Fin n → ℝ |
      Matrix.of (Function.curry s) ∈ reducedSet n C} := by
  have hdet (s : Fin n × Fin n → ℝ) :
      (Matrix.of (Function.curry s)).det =
        MvPolynomial.eval s (Matrix.mvPolynomialX (Fin n) (Fin n) ℝ).det := by
    rw [RingHom.map_det]; congr 1; ext i j; simp [Matrix.mvPolynomialX_apply, Function.curry]
  have heq : {s : Fin n × Fin n → ℝ | Matrix.of (Function.curry s) ∈ reducedSet n C} =
      {s | (Matrix.of (Function.curry s)).PosDef} ∩
      ((⋂ p : Fin n × Fin n,
          {s | 0 < MvPolynomial.eval s
            (MvPolynomial.C C * MvPolynomial.X (p.1, p.1) - MvPolynomial.X p)} ∩
          {s | 0 < MvPolynomial.eval s
            (MvPolynomial.C C * MvPolynomial.X (p.1, p.1) + MvPolynomial.X p)}) ∩
        ((⋂ q : {p : Fin n × Fin n // p.1 < p.2},
            {s | 0 < MvPolynomial.eval s (MvPolynomial.C C * MvPolynomial.X (q.1.2, q.1.2) -
              MvPolynomial.X (q.1.1, q.1.1))}) ∩
          {s | 0 < MvPolynomial.eval s
            (MvPolynomial.C C * (Matrix.mvPolynomialX (Fin n) (Fin n) ℝ).det -
              ∏ i : Fin n, MvPolynomial.X (i, i))})) := by
    ext s
    simp only [mem_reducedSet_iff, IsReduced, Set.mem_ofPred_eq, Set.mem_inter_iff,
      Set.mem_iInter, Prod.forall, Subtype.forall, map_sub, map_add, map_mul, MvPolynomial.eval_C,
      MvPolynomial.eval_X, map_prod, sub_pos, Matrix.of_apply, Function.curry_apply, ← hdet, abs_lt]
    exact and_congr_right fun _ ↦ and_congr
      (forall₂_congr fun _ _ ↦ ⟨fun ⟨_, h2⟩ ↦ ⟨h2, by linarith⟩, fun ⟨h1, _⟩ ↦ ⟨by linarith, h1⟩⟩)
      Iff.rfl
  rw [heq]
  exact (TauCeti.isSemialgebraic_setOf_posDef n).inter
    (((TauCeti.IsSemialgebraic.iInter fun _ ↦
      (TauCeti.isSemialgebraic_eval_pos _).inter (TauCeti.isSemialgebraic_eval_pos _))).inter
      ((TauCeti.IsSemialgebraic.iInter fun _ ↦ TauCeti.isSemialgebraic_eval_pos _).inter
        (TauCeti.isSemialgebraic_eval_pos _)))

/-- The set `T_{P, C}` of positive-definite forms whose Gram matrix `Pᵀ * b * P` in the ordered
basis formed by the columns of `P : GL (Fin n) ℝ` belongs to `reducedSet n C`. -/
def reducedSetInBasis {n : ℕ} (P : GL (Fin n) ℝ) (C : ℝ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {b | ((P : Matrix (Fin n) (Fin n) ℝ)ᵀ * b * (P : Matrix (Fin n) (Fin n) ℝ)) ∈ reducedSet n C}

/-- In the standard basis `1 : GL (Fin n) ℝ`, `reducedSetInBasis` is `reducedSet`. -/
@[simp]
theorem reducedSetInBasis_one (n : ℕ) (C : ℝ) :
    reducedSetInBasis (1 : GL (Fin n) ℝ) C = reducedSet n C := by
  ext b; simp [reducedSetInBasis]

/-- Equivariance of `T_{P, C}` under the left action `b ↦ (g⁻¹)ᵀ * b * g⁻¹` of `g : GL (Fin n) ℝ`:
`g · T_{P, C} = T_{g * P, C}`. -/
theorem image_inv_transpose_mul_reducedSetInBasis {n : ℕ} (g P : GL (Fin n) ℝ) (C : ℝ) :
    (fun b ↦ ((g⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)ᵀ * b *
      ((g⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)) '' reducedSetInBasis P C =
      reducedSetInBasis (g * P) C := by
  let G : Matrix (Fin n) (Fin n) ℝ := g
  let Gi : Matrix (Fin n) (Fin n) ℝ := (g⁻¹ : GL (Fin n) ℝ)
  let PM : Matrix (Fin n) (Fin n) ℝ := P
  have hGiG : Gi * G = 1 := Units.inv_mul g
  have hGGi : G * Gi = 1 := Units.mul_inv g
  have hGTGiT : Gᵀ * Giᵀ = 1 := by rw [← Matrix.transpose_mul, hGiG, Matrix.transpose_one]
  have hGiTGT : Giᵀ * Gᵀ = 1 := by rw [← Matrix.transpose_mul, hGGi, Matrix.transpose_one]
  ext b
  constructor
  · rintro ⟨b₀, hb₀, rfl⟩
    simp only [reducedSetInBasis, Set.mem_ofPred_eq, Units.val_mul, Matrix.transpose_mul] at hb₀ ⊢
    have hmul : PMᵀ * Gᵀ * (Giᵀ * b₀ * Gi) * (G * PM) = PMᵀ * b₀ * PM := by
      calc PMᵀ * Gᵀ * (Giᵀ * b₀ * Gi) * (G * PM)
          = PMᵀ * (Gᵀ * Giᵀ) * b₀ * (Gi * G) * PM := by simp only [Matrix.mul_assoc]
        _ = PMᵀ * b₀ * PM := by rw [hGTGiT, hGiG, Matrix.mul_one, Matrix.mul_one]
    rwa [hmul]
  · intro hb
    refine ⟨Gᵀ * b * G, ?_, ?_⟩
    · simpa only [reducedSetInBasis, Set.mem_ofPred_eq, Units.val_mul, Matrix.transpose_mul,
        Matrix.mul_assoc] using hb
    · calc Giᵀ * (Gᵀ * b * G) * Gi = (Giᵀ * Gᵀ) * b * (G * Gi) := by simp only [Matrix.mul_assoc]
        _ = b := by rw [hGiTGT, hGGi, Matrix.one_mul, Matrix.mul_one]

end ReducedSet

section CholeskyBounds

/-- Every positive-definite real `n × n` matrix decomposes as `Nᵀ * Matrix.diagonal d * N` with
`N` upper unitriangular and `0 < d i` for all `i`, given by Mathlib's `LDL` decomposition. -/
theorem exists_isUpperUnitriangular_transpose_mul_diagonal_mul_eq {n : ℕ}
    {b : Matrix (Fin n) (Fin n) ℝ} (hb : b.PosDef) :
    ∃ (N : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ),
      N.IsUpperUnitriangular ∧ (∀ i, 0 < d i) ∧ b = Nᵀ * Matrix.diagonal d * N := by
  refine ⟨(LDL.lower hb)ᵀ, LDL.diagEntries hb,
    (Matrix.isUpperUnitriangular_def _).mpr
      ⟨(LDL.isLowerTriangular_lower hb).transpose, fun i ↦ LDL.lower_apply_diag hb i⟩,
    fun i ↦ LDL.diagEntries_pos hb i, ?_⟩
  have h := (LDL.lower_conj_diag hb).symm
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial, LDL.diag,
    ← Matrix.transpose_transpose (LDL.lower hb)] at h

private theorem transpose_mul_diagonal_mul_apply {n : ℕ} (N : Matrix (Fin n) (Fin n) ℝ)
    (d : Fin n → ℝ) (i j : Fin n) :
    (Nᵀ * Matrix.diagonal d * N) i j = ∑ k : Fin n, d k * N k i * N k j := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal_apply]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Finset.sum_mul, Finset.sum_eq_single k (fun _ _ hlk ↦ by simp [hlk]) (by simp)]
  simp [mul_comm, mul_left_comm]

private theorem transpose_mul_diagonal_mul_apply_of_isUpperUnitriangular {n : ℕ}
    {N : Matrix (Fin n) (Fin n) ℝ} (hN : N.IsUpperUnitriangular) (d : Fin n → ℝ) (i j : Fin n) :
    (Nᵀ * Matrix.diagonal d * N) i j =
      d i * N i j + ∑ k ∈ Finset.univ.filter (· < i), d k * N k i * N k j := by
  rw [transpose_mul_diagonal_mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    hN.apply_diag i, mul_one]
  congr 1
  refine (Finset.sum_subset (fun k hk ↦ Finset.mem_erase.mpr
    ⟨(Finset.mem_filter.mp hk).2.ne, Finset.mem_univ k⟩) fun k hk hnot ↦ ?_).symm
  have hik : i < k := lt_of_le_of_ne
    (le_of_not_gt fun hlt ↦ hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hlt⟩))
    (Finset.mem_erase.mp hk).1.symm
  simp [hN.isUpperTriangular hik]

private theorem diag_le_transpose_mul_diagonal_mul_self {n : ℕ} {N : Matrix (Fin n) (Fin n) ℝ}
    (hN : N.IsUpperUnitriangular) {d : Fin n → ℝ} (hd : ∀ i, 0 ≤ d i) (i : Fin n) :
    d i ≤ (Nᵀ * Matrix.diagonal d * N) i i := by
  rw [transpose_mul_diagonal_mul_apply_of_isUpperUnitriangular hN d i i, hN.apply_diag i, mul_one]
  exact le_add_of_nonneg_right
    (Finset.sum_nonneg fun k _ ↦ by nlinarith [hd k, mul_self_nonneg (N k i)])

private theorem det_transpose_mul_diagonal_mul {n : ℕ} {N : Matrix (Fin n) (Fin n) ℝ}
    (hN : N.IsUpperUnitriangular) (d : Fin n → ℝ) :
    (Nᵀ * Matrix.diagonal d * N).det = ∏ i, d i := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hN.det_eq_one, Matrix.det_diagonal,
    one_mul, mul_one]

private def choleskySeqBound (n : ℕ) (C : ℝ) : ℕ → ℝ
  | 0 => C ^ 2
  | m + 1 => choleskySeqBound n C m + C ^ 2 * (1 + (n : ℝ) * choleskySeqBound n C m ^ 2)

private theorem choleskySeqBound_nonneg (n : ℕ) (C : ℝ) (m : ℕ) : 0 ≤ choleskySeqBound n C m := by
  induction m with
  | zero => exact sq_nonneg C
  | succ m ih => simp only [choleskySeqBound]; positivity

private theorem sq_le_choleskySeqBound (n : ℕ) (C : ℝ) (m : ℕ) :
    C ^ 2 ≤ choleskySeqBound n C m := by
  induction m with
  | zero => exact le_rfl
  | succ m ih =>
    simp only [choleskySeqBound]
    exact ih.trans (le_add_of_nonneg_right (by positivity))

private theorem abs_apply_le_choleskySeqBound {n : ℕ} {C : ℝ} {b N : Matrix (Fin n) (Fin n) ℝ}
    {d : Fin n → ℝ} (hb : b.PosDef) (hred : IsReduced C b) (hN : N.IsUpperUnitriangular)
    (hd : ∀ i, 0 < d i) (hfac : b = Nᵀ * Matrix.diagonal d * N) (hb_lt_Cd : ∀ i, b i i < C * d i) :
    ∀ m : ℕ, ∀ i j : Fin n, i.1 < m → i < j → |N i j| ≤ choleskySeqBound n C m := by
  have hC_pos : 0 < C := hred.pos hb
  have hd_le_b (i : Fin n) : d i ≤ b i i :=
    hfac ▸ diag_le_transpose_mul_diagonal_mul_self hN (fun k ↦ (hd k).le) i
  intro m
  induction m with
  | zero => intro i _ hi; exact (Nat.not_lt_zero i.1 hi).elim
  | succ m ih =>
    intro i j him hij
    rcases Nat.lt_succ_iff_lt_or_eq.mp him with hlt | heq
    · simp only [choleskySeqBound]
      exact (ih i j hlt hij).trans (le_add_of_nonneg_right (by positivity))
    · have hbij : d i * N i j =
          b i j - ∑ k ∈ Finset.univ.filter (· < i), d k * N k i * N k j := by
        linarith [hfac ▸ transpose_mul_diagonal_mul_apply_of_isUpperUnitriangular hN d i j]
      have hdi_abs : d i * |N i j| ≤
          |b i j| + ∑ k ∈ Finset.univ.filter (· < i), d k * |N k i| * |N k j| := by
        calc d i * |N i j| = |d i * N i j| := by rw [abs_mul, abs_of_pos (hd i)]
          _ ≤ |b i j| + ∑ k ∈ Finset.univ.filter (· < i), |d k * N k i * N k j| := by
              rw [hbij]
              exact (abs_sub _ _).trans (add_le_add_right (Finset.abs_sum_le_sum_abs _ _) _)
          _ = |b i j| + ∑ k ∈ Finset.univ.filter (· < i), d k * |N k i| * |N k j| := by
              congr 2 with k; rw [abs_mul, abs_mul, abs_of_pos (hd k)]
      have hbii_pos : 0 < b i i := hb.diag_pos
      have hterm (k : Fin n) (hk : k ∈ Finset.univ.filter (· < i)) :
          d k * |N k i| * |N k j| ≤ C * b i i * choleskySeqBound n C m ^ 2 := by
        have hki : k < i := (Finset.mem_filter.mp hk).2
        have hkm : k.1 < m := heq ▸ hki
        have hprodN : |N k i| * |N k j| ≤ choleskySeqBound n C m ^ 2 := by
          rw [sq]
          exact mul_le_mul (ih k i hkm hki) (ih k j hkm (hki.trans hij))
            (abs_nonneg _) (choleskySeqBound_nonneg n C m)
        nlinarith [hd_le_b k, hred.diag_lt_of_lt hki, mul_nonneg (abs_nonneg (N k i))
          (abs_nonneg (N k j)), mul_nonneg hC_pos.le hbii_pos.le,
          mul_le_mul ((hd_le_b k).trans (hred.diag_lt_of_lt hki).le) hprodN
            (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (mul_nonneg hC_pos.le hbii_pos.le)]
      have hcard : ((Finset.univ.filter (· < i)).card : ℝ) ≤ n := by
        exact_mod_cast (Finset.card_filter_le _ _).trans_eq (Fintype.card_fin n)
      have hsum_le : ∑ k ∈ Finset.univ.filter (· < i), d k * |N k i| * |N k j| ≤
          (n : ℝ) * (C * b i i * choleskySeqBound n C m ^ 2) :=
        (Finset.sum_le_sum hterm).trans (by
          simp only [Finset.sum_const, nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right hcard (by positivity))
      have hmul_le : d i * |N i j| ≤
          d i * (C ^ 2 * (1 + (n : ℝ) * choleskySeqBound n C m ^ 2)) := by
        have h1 : d i * |N i j| ≤ C * b i i * (1 + (n : ℝ) * choleskySeqBound n C m ^ 2) := by
          linarith [hdi_abs, hred.abs_apply_lt i j, hsum_le]
        exact h1.trans (by
          nlinarith [hb_lt_Cd i,
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hb_lt_Cd i).le hC_pos.le)
              (by positivity : 0 ≤ 1 + (n : ℝ) * choleskySeqBound n C m ^ 2)])
      simp only [choleskySeqBound]
      linarith [le_of_mul_le_mul_left hmul_le (hd i), choleskySeqBound_nonneg n C m]

/-- **Uniform Cholesky bounds for reduced forms.** For fixed `n` and `C`, there is a constant
`R > 0` such that every positive-definite `C`-reduced matrix `b = Nᵀ * Matrix.diagonal d * N`
with `N` upper unitriangular and `0 < d i` satisfies `|N i j| ≤ R` and `d i ≤ R * d j` whenever
`i < j`. -/
theorem exists_cholesky_bound_of_isReduced (n : ℕ) (C : ℝ) :
    ∃ R : ℝ, 0 < R ∧ ∀ {b N : Matrix (Fin n) (Fin n) ℝ} {d : Fin n → ℝ},
      b.PosDef → IsReduced C b → N.IsUpperUnitriangular → (∀ i, 0 < d i) →
        b = Nᵀ * Matrix.diagonal d * N →
        (∀ i j, i < j → |N i j| ≤ R) ∧ (∀ i j, i < j → d i ≤ R * d j) := by
  refine ⟨max 1 (choleskySeqBound n C n), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro b N d hb hred hN hd hfac
  have hC_pos : 0 < C := hred.pos hb
  have hd_le_b (i : Fin n) : d i ≤ b i i :=
    hfac ▸ diag_le_transpose_mul_diagonal_mul_self hN (fun k ↦ (hd k).le) i
  have hb_det : b.det = ∏ i, d i := hfac ▸ det_transpose_mul_diagonal_mul hN d
  have hb_lt_Cd (i : Fin n) : b i i < C * d i := by
    have hrest_pos : 0 < ∏ j ∈ Finset.univ.erase i, d j := Finset.prod_pos fun j _ ↦ hd j
    refine lt_of_mul_lt_mul_right ?_ hrest_pos.le
    calc b i i * (∏ j ∈ Finset.univ.erase i, d j)
        ≤ b i i * (∏ j ∈ Finset.univ.erase i, b j j) :=
          mul_le_mul_of_nonneg_left
            (Finset.prod_le_prod₀ (fun j _ ↦ (hd j).le) fun j _ ↦ hd_le_b j) hb.diag_pos.le
      _ < C * (d i * ∏ j ∈ Finset.univ.erase i, d j) := by
          rw [Finset.mul_prod_erase Finset.univ (fun j ↦ b j j) (Finset.mem_univ i),
            Finset.mul_prod_erase Finset.univ d (Finset.mem_univ i), ← hb_det]
          exact hred.prod_diag_lt
      _ = (C * d i) * (∏ j ∈ Finset.univ.erase i, d j) := by ring
  refine ⟨fun i j hij ↦ (abs_apply_le_choleskySeqBound hb hred hN hd hfac hb_lt_Cd n i j
      i.isLt hij).trans (le_max_right _ _), fun i j hij ↦ ?_⟩
  have h1 : d i ≤ C ^ 2 * d j := by
    nlinarith [hd_le_b i, hred.diag_lt_of_lt hij, hb_lt_Cd j,
      mul_le_mul_of_nonneg_left (hb_lt_Cd j).le hC_pos.le]
  exact h1.trans (mul_le_mul_of_nonneg_right
    ((sq_le_choleskySeqBound n C n).trans (le_max_right _ _)) (hd j).le)

private theorem pivot_le_pow_mul {n : ℕ} {d : Fin n → ℝ} {R R₁ : ℝ} (hd : ∀ i, 0 < d i)
    (hR₁ : 1 ≤ R₁) (hR : R ≤ R₁)
    (hd_step : ∀ (i : Fin n) (h : i.1 + 1 < n), d i ≤ R * d ⟨i.1 + 1, h⟩) :
    ∀ {k i : Fin n}, k ≤ i → d k ≤ R₁ ^ n * d i := by
  have haux : ∀ m : ℕ, ∀ {k i : Fin n}, i.1 - k.1 = m → k ≤ i → d k ≤ R₁ ^ m * d i := by
    intro m
    induction m with
    | zero =>
      intro k i hdiff hki
      obtain rfl : k = i := Fin.ext (by omega)
      simp
    | succ m ih =>
      intro k i hdiff hki
      have hk1 : k.1 + 1 < n := by omega
      let k' : Fin n := ⟨k.1 + 1, hk1⟩
      calc d k ≤ R₁ * d k' := (hd_step k hk1).trans (mul_le_mul_of_nonneg_right hR (hd k').le)
        _ ≤ R₁ * (R₁ ^ m * d i) := mul_le_mul_of_nonneg_left
            (ih (by dsimp [k']; omega) (Fin.le_def.mpr (by dsimp [k']; omega)))
            (zero_le_one.trans hR₁)
        _ = R₁ ^ (m + 1) * d i := by ring
  intro k i hki
  exact (haux (i.1 - k.1) rfl hki).trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hR₁ (by omega)) (hd i).le)

/-- **Converse Cholesky bound.** For fixed `n` and `R`, there is `C > 1` such that whenever `N` is
upper unitriangular with `|N i j| ≤ R` above the diagonal and `d` has positive entries satisfying
`d i ≤ R * d (i + 1)`, the matrix `Nᵀ * Matrix.diagonal d * N` is positive definite and
`C`-reduced. -/
theorem exists_isReduced_of_cholesky_bound (n : ℕ) (R : ℝ) :
    ∃ C : ℝ, 1 < C ∧ ∀ {N : Matrix (Fin n) (Fin n) ℝ} {d : Fin n → ℝ},
      N.IsUpperUnitriangular → (∀ i, 0 < d i) →
        (∀ i j, i < j → |N i j| ≤ R) →
        (∀ (i : Fin n) (h : i.1 + 1 < n), d i ≤ R * d ⟨i.1 + 1, h⟩) →
        (Nᵀ * Matrix.diagonal d * N).PosDef ∧ IsReduced C (Nᵀ * Matrix.diagonal d * N) := by
  set R₁ : ℝ := max R 1
  have hR₁_one : 1 ≤ R₁ := le_max_right R 1
  have hR₁_pos : 0 < R₁ := zero_lt_one.trans_le hR₁_one
  set M : ℝ := (n : ℝ) * R₁ ^ (n + 2) + 1
  have hM_one : 1 ≤ M := le_add_of_nonneg_left (by positivity)
  set C : ℝ := max (M * R₁ ^ n) (M ^ n + 1)
  have hC_gt : 1 < C := (by linarith [one_le_pow₀ (n := n) hM_one] : 1 < M ^ n + 1).trans_le
    (le_max_right _ _)
  refine ⟨C, hC_gt, fun {N d} hN hd hN_le hd_step ↦ ?_⟩
  set b : Matrix (Fin n) (Fin n) ℝ := Nᵀ * Matrix.diagonal d * N
  have hb_posDef : b.PosDef := by
    simpa [b, Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.posDef_diagonal_iff.mpr hd).conjTranspose_mul_mul_same
        (Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det N).mpr hN.isUnit_det))
  have hd_ratio {k i : Fin n} (hki : k ≤ i) : d k ≤ R₁ ^ n * d i :=
    pivot_le_pow_mul hd hR₁_one (le_max_left R 1) hd_step hki
  have hN_all (i j : Fin n) : |N i j| ≤ R₁ := by
    rcases lt_trichotomy i j with hij | rfl | hji
    · exact (hN_le i j hij).trans (le_max_left R 1)
    · simpa [hN.apply_diag i] using hR₁_one
    · simpa [hN.isUpperTriangular hji] using hR₁_pos.le
  have habs_bij (i j : Fin n) : |b i j| < M * d i := by
    have hdi_pos : 0 < d i := hd i
    have hterm (k : Fin n) : |d k * N k i * N k j| ≤ R₁ ^ (n + 2) * d i := by
      by_cases hki : k ≤ i
      · rw [abs_mul, abs_mul, abs_of_pos (hd k)]
        calc d k * |N k i| * |N k j| = d k * (|N k i| * |N k j|) := by ring
          _ ≤ (R₁ ^ n * d i) * (R₁ * R₁) := mul_le_mul (hd_ratio hki)
              (mul_le_mul (hN_all k i) (hN_all k j) (abs_nonneg _) hR₁_pos.le)
              (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (by positivity)
          _ = R₁ ^ (n + 2) * d i := by ring
      · rw [hN.isUpperTriangular (lt_of_not_ge hki), mul_zero, zero_mul, abs_zero]; positivity
    have hle : |b i j| ≤ (n : ℝ) * (R₁ ^ (n + 2) * d i) := by
      dsimp only [b]
      rw [transpose_mul_diagonal_mul_apply N d i j]
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        ((Finset.sum_le_sum fun k _ ↦ hterm k).trans (by simp))
    linarith
  have hd_le_b (i : Fin n) : d i ≤ b i i :=
    diag_le_transpose_mul_diagonal_mul_self hN (fun k ↦ (hd k).le) i
  have hM_le_C : M ≤ C :=
    (le_mul_of_one_le_right (zero_le_one.trans hM_one) (one_le_pow₀ hR₁_one)).trans
      (le_max_left _ _)
  refine ⟨hb_posDef, ⟨fun i j ↦ ?_, fun i j hij ↦ ?_, ?_⟩⟩
  · exact (habs_bij i j).trans_le ((mul_le_mul_of_nonneg_left (hd_le_b i)
      (zero_le_one.trans hM_one)).trans (mul_le_mul_of_nonneg_right hM_le_C hb_posDef.diag_pos.le))
  · calc b i i < M * d i := (le_abs_self _).trans_lt (habs_bij i i)
      _ ≤ (M * R₁ ^ n) * b j j := by
          nlinarith [hd_ratio hij.le, hd_le_b j,
            mul_le_mul_of_nonneg_left (hd_ratio hij.le) (zero_le_one.trans hM_one),
            mul_le_mul_of_nonneg_left (hd_le_b j) (by positivity : 0 ≤ M * R₁ ^ n)]
      _ ≤ C * b j j := mul_le_mul_of_nonneg_right (le_max_left _ _) hb_posDef.diag_pos.le
  · calc ∏ i, b i i ≤ ∏ i, M * d i := Finset.prod_le_prod₀ (fun _ _ ↦ hb_posDef.diag_pos.le)
          fun i _ ↦ ((le_abs_self _).trans_lt (habs_bij i i)).le
      _ = M ^ n * b.det := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
            det_transpose_mul_diagonal_mul hN d]
      _ < (M ^ n + 1) * b.det := by linarith [hb_posDef.det_pos]
      _ ≤ C * b.det := mul_le_mul_of_nonneg_right (le_max_right _ _) hb_posDef.det_pos.le

end CholeskyBounds

section BasisChange

/-- **Transferring off-diagonal bounds across a basis.** If a positive-definite matrix `B`
satisfies weak `C'`-reducedness inequalities (`C' ≥ 1`) and `v : Fin n → ℝ` has top nonzero
coordinate `k`, then
`|v ⬝ᵥ B *ᵥ w| ≤ C' ^ 3 * (∑ a, |v a|) * (∑ b, |w b|) / v k ^ 2 * (v ⬝ᵥ B *ᵥ v)`
for every vector `w`. -/
theorem abs_dotProduct_mulVec_le_of_diag_le {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.PosDef)
    {C' : ℝ} (hC'1 : 1 ≤ C') (hOff : ∀ a b, |B a b| ≤ C' * B a a)
    (hDiag : ∀ a b, a < b → B a a ≤ C' * B b b) (hDet : ∏ a, B a a ≤ C' * B.det)
    {v : Fin n → ℝ} (w : Fin n → ℝ) {k : Fin n} (hvk : v k ≠ 0) (hsupp : ∀ a, k < a → v a = 0) :
    |v ⬝ᵥ B *ᵥ w| ≤
      C' ^ 3 * (∑ a, |v a|) * (∑ b, |w b|) / v k ^ 2 * (v ⬝ᵥ B *ᵥ v) := by
  have hC'_pos : 0 < C' := zero_lt_one.trans_le hC'1
  have hBab_le {a : Fin n} (hak : a ≤ k) (b : Fin n) : |B a b| ≤ C' ^ 2 * B k k := by
    have hBaa : B a a ≤ C' * B k k := by
      rcases lt_or_eq_of_le hak with hlt | rfl
      · exact hDiag a k hlt
      · simpa using mul_le_mul_of_nonneg_right hC'1 hB.diag_pos.le
    calc |B a b| ≤ C' * B a a := hOff a b
      _ ≤ C' * (C' * B k k) := mul_le_mul_of_nonneg_left hBaa hC'_pos.le
      _ = C' ^ 2 * B k k := by ring
  have hterm (a b : Fin n) : |v a * (B a b * w b)| ≤ C' ^ 2 * B k k * |v a| * |w b| := by
    by_cases hak : a ≤ k
    · rw [abs_mul, abs_mul]
      nlinarith [hBab_le hak b, mul_nonneg (abs_nonneg (v a)) (abs_nonneg (w b)),
        mul_le_mul_of_nonneg_right (hBab_le hak b)
          (mul_nonneg (abs_nonneg (v a)) (abs_nonneg (w b)))]
    · simp [hsupp a (lt_of_not_ge hak)]
  have hsum_le : |v ⬝ᵥ B *ᵥ w| ≤ B k k * (C' ^ 2 * (∑ a, |v a|) * (∑ b, |w b|)) := by
    have hdot : v ⬝ᵥ B *ᵥ w = ∑ a, ∑ b, v a * (B a b * w b) := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    rw [hdot]
    calc |∑ a, ∑ b, v a * (B a b * w b)|
        ≤ ∑ a, ∑ b, |v a * (B a b * w b)| := (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun _ _ ↦ Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ a, ∑ b, C' ^ 2 * B k k * |v a| * |w b| :=
          Finset.sum_le_sum fun a _ ↦ Finset.sum_le_sum fun b _ ↦ hterm a b
      _ = B k k * (C' ^ 2 * (∑ a, |v a|) * (∑ b, |w b|)) := by
          simp only [← Finset.mul_sum, ← Finset.sum_mul]; ring
  have hlower := (div_le_iff₀ hC'_pos).mp (hB.sq_mul_apply_self_div_le_dotProduct_mulVec hDet v k)
  have hBkk_le : B k k ≤ C' / v k ^ 2 * (v ⬝ᵥ B *ᵥ v) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (sq_pos_of_ne_zero hvk)]; linarith
  calc |v ⬝ᵥ B *ᵥ w|
      ≤ (C' / v k ^ 2 * (v ⬝ᵥ B *ᵥ v)) * (C' ^ 2 * (∑ a, |v a|) * (∑ b, |w b|)) :=
        hsum_le.trans (mul_le_mul_of_nonneg_right hBkk_le (by positivity))
    _ = C' ^ 3 * (∑ a, |v a|) * (∑ b, |w b|) / v k ^ 2 * (v ⬝ᵥ B *ᵥ v) := by ring

private theorem exists_topIdx_col {n : ℕ} (A : GL (Fin n) ℝ) (i : Fin n) :
    ∃ k : Fin n, (A : Matrix (Fin n) (Fin n) ℝ) k i ≠ 0 ∧
      ∀ a : Fin n, k < a → (A : Matrix (Fin n) (Fin n) ℝ) a i = 0 := by
  classical
  have hcol_ne : (fun a ↦ (A : Matrix (Fin n) (Fin n) ℝ) a i) ≠ 0 := fun h0 ↦ by
    have hmul : (A : Matrix (Fin n) (Fin n) ℝ) *ᵥ Pi.single i 1 = 0 :=
      funext fun a ↦ by simpa [Matrix.mulVec_single_one, Matrix.col_apply] using congrFun h0 a
    have h10 := Matrix.mulVec_injective_of_isUnit A.isUnit (hmul.trans (Matrix.mulVec_zero _).symm)
    simpa using congrFun h10 i
  let supp : Finset (Fin n) := Finset.univ.filter fun a ↦ (A : Matrix (Fin n) (Fin n) ℝ) a i ≠ 0
  obtain ⟨a₀, ha₀⟩ := Function.ne_iff.mp hcol_ne
  have hne : supp.Nonempty := ⟨a₀, Finset.mem_filter.mpr ⟨Finset.mem_univ a₀, ha₀⟩⟩
  refine ⟨supp.max' hne, (Finset.mem_filter.mp (supp.max'_mem hne)).2, fun a ha ↦ ?_⟩
  by_contra hne'
  exact not_le_of_gt ha (supp.le_max' a (Finset.mem_filter.mpr ⟨Finset.mem_univ a, hne'⟩))

/-- **Basis change with determinant control.** Given `A : GL (Fin n) ℝ` and thresholds `C, C'`,
there is `C'' > 1` depending only on `C`, `C'`, and `A` such that for every positive-definite
`C'`-reduced matrix `B` whose transformed Gram matrix `B_A = Aᵀ * B * A` satisfies
`∏ i, B_A i i ≤ C * B_A.det`, sorting the diagonal of `B_A` by `σ = Tuple.sort (fun i ↦ B_A i i)`
produces a `C''`-reduced matrix `B_A.submatrix σ σ` with monotone diagonal. -/
theorem exists_perm_isReduced_congr {n : ℕ} (A : GL (Fin n) ℝ) (C C' : ℝ) :
    ∃ C'' : ℝ, 1 < C'' ∧ ∀ {B : Matrix (Fin n) (Fin n) ℝ},
      B.PosDef → IsReduced C' B →
        (∏ i, ((A : Matrix (Fin n) (Fin n) ℝ)ᵀ * B * (A : Matrix (Fin n) (Fin n) ℝ)) i i ≤
          C * ((A : Matrix (Fin n) (Fin n) ℝ)ᵀ * B * (A : Matrix (Fin n) (Fin n) ℝ)).det) →
        let B_A := (A : Matrix (Fin n) (Fin n) ℝ)ᵀ * B * (A : Matrix (Fin n) (Fin n) ℝ)
        let σ := Tuple.sort (fun i ↦ B_A i i)
        Monotone (fun i ↦ B_A (σ i) (σ i)) ∧ IsReduced C'' (B_A.submatrix σ σ) := by
  classical
  let colA (i : Fin n) : Fin n → ℝ := fun a ↦ (A : Matrix (Fin n) (Fin n) ℝ) a i
  choose topIdx htop_ne htop_vanish using exists_topIdx_col A
  set C₁ : ℝ := max C 1
  set C'₁ : ℝ := max C' 1
  let K (i j : Fin n) : ℝ :=
    C'₁ ^ 3 * (∑ a, |colA i a|) * (∑ b, |colA j b|) / (colA i (topIdx i)) ^ 2
  have hK_nonneg (i j : Fin n) : 0 ≤ K i j := by dsimp [K]; positivity
  set C'' : ℝ := max 2 (max (C₁ + 1) ((∑ i : Fin n, ∑ j : Fin n, K i j) + 1))
  have hC''_gt : 1 < C'' := (by norm_num : (1 : ℝ) < 2).trans_le (le_max_left _ _)
  refine ⟨C'', hC''_gt, fun {B} hB hRed hDet ↦ ?_⟩
  intro B_A σ
  have hmono : Monotone (fun i ↦ B_A (σ i) (σ i)) := Tuple.monotone_sort (fun i ↦ B_A i i)
  have hRed₁ : IsReduced C'₁ B := hRed.mono hB (le_max_left C' 1)
  have hB_A_posDef : B_A.PosDef := by
    simpa [B_A, Matrix.conjTranspose_eq_transpose_of_trivial] using
      hB.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit A.isUnit)
  have hB_A_apply (i j : Fin n) : B_A i j = colA i ⬝ᵥ B *ᵥ colA j := by
    simp only [B_A, colA, Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec,
      Finset.mul_sum, mul_assoc]
  set B' : Matrix (Fin n) (Fin n) ℝ := B_A.submatrix σ σ
  have hB'_posDef : B'.PosDef := hB_A_posDef.submatrix σ.injective
  refine ⟨hmono, ⟨fun i j ↦ ?_, fun i j hij ↦ ?_, ?_⟩⟩
  · have hbij : |B' i j| ≤ K (σ i) (σ j) * B' i i := by
      simpa [B', Matrix.submatrix_apply, hB_A_apply, K] using
        abs_dotProduct_mulVec_le_of_diag_le hB (le_max_right C' 1)
          (fun a b ↦ (hRed₁.abs_apply_lt a b).le) (fun _ _ hab ↦ (hRed₁.diag_lt_of_lt hab).le)
          hRed₁.prod_diag_lt.le (v := colA (σ i)) (colA (σ j)) (k := topIdx (σ i))
          (htop_ne (σ i)) (htop_vanish (σ i))
    have hK_le : K (σ i) (σ j) ≤ ∑ a : Fin n, ∑ b : Fin n, K a b :=
      (Finset.single_le_sum (fun b _ ↦ hK_nonneg (σ i) b) (Finset.mem_univ (σ j))).trans
        (Finset.single_le_sum (fun a _ ↦ Finset.sum_nonneg fun b _ ↦ hK_nonneg a b)
          (Finset.mem_univ (σ i)))
    have hdiag_pos : 0 < B' i i := hB'_posDef.diag_pos
    calc |B' i j| ≤ (∑ a : Fin n, ∑ b : Fin n, K a b) * B' i i :=
          hbij.trans (mul_le_mul_of_nonneg_right hK_le hdiag_pos.le)
      _ < ((∑ a : Fin n, ∑ b : Fin n, K a b) + 1) * B' i i := by linarith
      _ ≤ C'' * B' i i :=
          mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) hdiag_pos.le
  · calc B' i i ≤ B' j j := hmono hij.le
      _ = 1 * B' j j := (one_mul _).symm
      _ < C'' * B' j j := mul_lt_mul_of_pos_right hC''_gt hB'_posDef.diag_pos
  · simp only [B', Matrix.submatrix_apply, Equiv.prod_comp σ (fun i ↦ B_A i i),
      Matrix.det_submatrix_equiv_self σ B_A]
    have hdet_pos : 0 < B_A.det := hB_A_posDef.det_pos
    calc ∏ i, B_A i i ≤ C₁ * B_A.det :=
          hDet.trans (mul_le_mul_of_nonneg_right (le_max_left C 1) hdet_pos.le)
      _ < (C₁ + 1) * B_A.det := by linarith
      _ ≤ C'' * B_A.det :=
          mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) hdet_pos.le

/-- **Necessity of the sorting permutation in `exists_perm_isReduced_congr`.** For the fixed swap
permutation `σ = Equiv.swap 0 1` on `Fin 2` and any proposed threshold `C''`, there exists `N ≥ 2`
such that `B = diag(1, N)` is positive definite and `2`-reduced, its swapped Gram matrix
`B' = diag(N, 1)` satisfies `∏ i, B' i i ≤ 2 * B'.det`, yet `B'` is not `C''`-reduced. -/
theorem exists_posDef_isReduced_and_not_isReduced_swap (C'' : ℝ) :
    ∃ N : ℝ, 2 ≤ N ∧
      let B : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![1, N]
      let σ : Equiv.Perm (Fin 2) := Equiv.swap 0 1
      B.PosDef ∧ IsReduced 2 B ∧
        (∏ i, (B.submatrix σ σ) i i ≤ 2 * (B.submatrix σ σ).det) ∧
        ¬ IsReduced C'' (B.submatrix σ σ) := by
  set N : ℝ := max 2 (max C'' 0 + 1)
  have hN2 : 2 ≤ N := le_max_left _ _
  have hNC'' : C'' < N := by linarith [le_max_left C'' 0, le_max_right 2 (max C'' 0 + 1)]
  refine ⟨N, hN2, Matrix.posDef_diagonal_iff.mpr fun i ↦ by fin_cases i <;> simp; linarith,
    ⟨fun i j ↦ by
        fin_cases i <;> fin_cases j <;> simp <;> linarith [abs_of_pos (by linarith : 0 < N)],
      fun i j hij ↦ by fin_cases i <;> fin_cases j <;> simp at hij ⊢; linarith,
      by simp [Fin.prod_univ_two, Matrix.det_diagonal]; linarith⟩,
    by simp [Fin.prod_univ_two, Matrix.det_diagonal]; linarith, fun hRed ↦ ?_⟩
  have h01 : (0 : Fin 2) < 1 := by decide
  have hlt := hRed.diag_lt_of_lt h01
  simp at hlt
  linarith

end BasisChange

end TauCeti.RealSiegel
