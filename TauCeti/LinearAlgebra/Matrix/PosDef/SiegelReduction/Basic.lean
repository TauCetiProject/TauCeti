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
when

1. `|b i j| < C * b i i` for all `i, j`,
2. `b i i < C * b j j` whenever `i < j`, and
3. `∏ i, b i i < C * b.det`.

When `b` is positive definite, Hadamard's determinant inequality `b.det ≤ ∏ i, b i i` forces
`1 < C`. Reducedness is invariant under positive real scaling (`isReduced_smul_iff`), and in
particular under normalizing a positive-definite matrix of nonzero size to determinant one via
`b.det ^ (-(n : ℝ)⁻¹) • b`.

## Main definitions and results

* `TauCeti.RealSiegel.IsReduced`: the `C`-reducedness predicate on `Matrix (Fin n) (Fin n) ℝ`.
* `TauCeti.RealSiegel.IsReduced.one_lt`, `TauCeti.RealSiegel.IsReduced.mono`,
  `TauCeti.RealSiegel.isReduced_smul_iff`: basic order and scaling properties on positive-definite
  forms, together with low-rank characterizations and explicit `2 × 2` checks.
* `TauCeti.RealSiegel.reducedSet` and `TauCeti.RealSiegel.reducedSetInBasis`: the set of
  `C`-reduced positive-definite matrices, its semialgebraicity in entry coordinates
  (`isSemialgebraic_reducedSet`), and its equivariance under `GL (Fin n) ℝ` basis changes.
* `TauCeti.RealSiegel.exists_cholesky_bound_of_isReduced` and
  `TauCeti.RealSiegel.exists_isReduced_of_cholesky_bound`: quantitative equivalence between
  `C`-reducedness of `Nᵀ * Matrix.diagonal d * N` (for upper-unitriangular `N` and positive `d`)
  and uniform bounds on the off-diagonal entries of `N` and adjacent ratios `d i / d (i + 1)`.
* `TauCeti.RealSiegel.abs_dotProduct_mulVec_le_of_diag_le` and
  `TauCeti.RealSiegel.exists_perm_isReduced_congr`: quantitative transfer of reducedness across an
  invertible change of basis with determinant control, after sorting the new diagonal entries via
  `Tuple.sort`.

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
    (hb : b.PosDef) : 1 < C := by
  have hdet_pos : 0 < b.det := hb.det_pos
  have hlt : 1 * b.det < C * b.det := by
    rw [one_mul]
    exact hb.posSemidef.det_le_prod_diag.trans_lt h.prod_diag_lt
  exact lt_of_mul_lt_mul_right hlt hdet_pos.le

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
    calc a * |b i j| < a * (C * b i i) := mul_lt_mul_of_pos_left (h.abs_apply_lt i j) ha
      _ = C * (a * b i i) := by ring
  · simp only [Matrix.smul_apply, smul_eq_mul]
    calc a * b i i < a * (C * b j j) := mul_lt_mul_of_pos_left (h.diag_lt_of_lt hij) ha
      _ = C * (a * b j j) := by ring
  · simp only [Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, Matrix.det_smul]
    have han : 0 < a ^ n := pow_pos ha n
    calc a ^ n * ∏ i, b i i < a ^ n * (C * b.det) := mul_lt_mul_of_pos_left h.prod_diag_lt han
      _ = C * (a ^ n * b.det) := by ring

/-- Positive scalar invariance: for `0 < a`, `a • b` is `C`-reduced if and only if `b` is. -/
@[simp]
theorem isReduced_smul_iff {C a : ℝ} {b : Matrix (Fin n) (Fin n) ℝ} (ha : 0 < a) :
    IsReduced C (a • b) ↔ IsReduced C b :=
  ⟨fun h ↦ by simpa [inv_smul_smul₀ ha.ne'] using h.smul (inv_pos.mpr ha), IsReduced.smul ha⟩

/-- Normalizing a positive-definite `n × n` matrix (`n ≠ 0`) by `b.det ^ (-(n : ℝ)⁻¹)` produces a
matrix of determinant `1`. -/
theorem det_det_rpow_neg_inv_smul {b : Matrix (Fin n) (Fin n) ℝ} (hn : n ≠ 0) (hb : b.PosDef) :
    (b.det ^ (-(n : ℝ)⁻¹) • b).det = 1 := by
  have hdet_pos : 0 < b.det := hb.det_pos
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [Matrix.det_smul, Fintype.card_fin, ← Real.rpow_natCast,
    ← Real.rpow_mul hdet_pos.le, neg_mul, inv_mul_cancel₀ hnR, Real.rpow_neg_one,
    inv_mul_cancel₀ hdet_pos.ne']

/-- Normalizing a positive-definite matrix by `b.det ^ (-(n : ℝ)⁻¹)` preserves `C`-reducedness. -/
theorem isReduced_det_rpow_neg_inv_smul_iff {C : ℝ} {b : Matrix (Fin n) (Fin n) ℝ} (hb : b.PosDef) :
    IsReduced C (b.det ^ (-(n : ℝ)⁻¹) • b) ↔ IsReduced C b :=
  isReduced_smul_iff (Real.rpow_pos_of_pos hb.det_pos _)

/-- No matrix with a nonpositive diagonal entry can be `C`-reduced for `0 ≤ C`. -/
theorem not_isReduced_of_diag_nonpos {C : ℝ} (hC : 0 ≤ C) {b : Matrix (Fin n) (Fin n) ℝ}
    (i : Fin n) (hi : b i i ≤ 0) : ¬ IsReduced C b := by
  intro h
  have hlt := h.abs_apply_lt i i
  have hnonpos : C * b i i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hC hi
  linarith [abs_nonneg (b i i)]

/-- In rank zero, a matrix is `C`-reduced if and only if `1 < C`. -/
@[simp]
theorem isReduced_fin_zero_iff {C : ℝ} {b : Matrix (Fin 0) (Fin 0) ℝ} :
    IsReduced C b ↔ 1 < C := by
  simp [IsReduced]

/-- In dimension one, a positive-definite matrix is `C`-reduced if and only if `1 < C`. -/
theorem isReduced_fin_one_iff {C : ℝ} {b : Matrix (Fin 1) (Fin 1) ℝ} (hb : b.PosDef) :
    IsReduced C b ↔ 1 < C := by
  refine ⟨fun h ↦ h.one_lt hb, fun hC ↦ ⟨fun i j ↦ ?_, fun i j hij ↦ ?_, ?_⟩⟩
  · rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    have h0 : 0 < b 0 0 := hb.diag_pos
    rw [abs_of_pos h0]
    exact lt_mul_of_one_lt_left h0 hC
  · exact (lt_irrefl _ (Subsingleton.elim i j ▸ hij)).elim
  · have h0 : 0 < b 0 0 := hb.diag_pos
    simp only [Fin.prod_univ_one, Matrix.det_fin_one]
    exact lt_mul_of_one_lt_left h0 hC

/-- The identity matrix of size `n` is `C`-reduced if and only if `1 < C`. -/
@[simp]
theorem isReduced_one_iff {C : ℝ} :
    IsReduced C (1 : Matrix (Fin n) (Fin n) ℝ) ↔ 1 < C := by
  refine ⟨fun h ↦ h.one_lt Matrix.PosDef.one, fun hC ↦ ⟨fun i j ↦ ?_, fun i j _ ↦ ?_, ?_⟩⟩
  · by_cases hij : i = j
    · subst hij
      simpa using hC
    · simpa [Matrix.one_apply_ne hij] using zero_lt_one.trans hC
  · simpa using hC
  · simpa using hC

/-- In nonzero dimension, the zero matrix is never `C`-reduced. -/
theorem not_isReduced_zero [NeZero n] (C : ℝ) :
    ¬ IsReduced C (0 : Matrix (Fin n) (Fin n) ℝ) := by
  intro h
  simpa using h.abs_apply_lt (0 : Fin n) 0

/-- For `0 ≤ C` and `n ≠ 0`, `-1` is not `C`-reduced. -/
theorem not_isReduced_neg_one [NeZero n] {C : ℝ} (hC : 0 ≤ C) :
    ¬ IsReduced C (-1 : Matrix (Fin n) (Fin n) ℝ) :=
  not_isReduced_of_diag_nonpos hC 0 (by simp)

/-- Concrete check: `diag(1, 4)` is `2`-reduced. -/
theorem isReduced_two_diagonal_one_four :
    IsReduced 2 (Matrix.diagonal ![1, (4 : ℝ)]) := by
  refine ⟨fun i j ↦ ?_, fun i j hij ↦ ?_, ?_⟩
  · fin_cases i <;> fin_cases j <;> norm_num
  · fin_cases i <;> fin_cases j <;> simp at hij ⊢; norm_num
  · norm_num [Fin.prod_univ_two, Matrix.det_diagonal]

/-- Concrete check: `diag(4, 1)` is not `2`-reduced because `4 < 2 * 1` fails. -/
theorem not_isReduced_two_diagonal_four_one :
    ¬ IsReduced 2 (Matrix.diagonal ![(4 : ℝ), 1]) := by
  intro h
  have h01 := h.diag_lt_of_lt (show (0 : Fin 2) < 1 by decide)
  norm_num at h01

/-- Concrete check: `(diag(1, 4))⁻¹ = diag(1, 1/4)` is not `2`-reduced, so reducedness is not
preserved by matrix inversion. -/
theorem not_isReduced_two_diagonal_one_inv_four :
    ¬ IsReduced 2 (Matrix.diagonal ![1, (4⁻¹ : ℝ)]) := by
  intro h
  have h01 := h.diag_lt_of_lt (show (0 : Fin 2) < 1 by decide)
  norm_num at h01

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
    reducedSet 1 C = {b : Matrix (Fin 1) (Fin 1) ℝ | b.PosDef} := by
  ext b
  exact ⟨fun h ↦ h.1, fun hb ↦ ⟨hb, (isReduced_fin_one_iff hb).mpr hC⟩⟩

/-- **The set of `C`-reduced positive-definite matrices is semialgebraic** in matrix-entry
coordinates `Fin n × Fin n → ℝ`. -/
theorem isSemialgebraic_reducedSet (n : ℕ) (C : ℝ) :
    TauCeti.IsSemialgebraic {s : Fin n × Fin n → ℝ |
      Matrix.of (Function.curry s) ∈ reducedSet n C} := by
  have hdet (s : Fin n × Fin n → ℝ) :
      (Matrix.of (Function.curry s)).det =
        MvPolynomial.eval s (Matrix.mvPolynomialX (Fin n) (Fin n) ℝ).det := by
    have hsub : (MvPolynomial.eval s).mapMatrix (Matrix.mvPolynomialX (Fin n) (Fin n) ℝ) =
        Matrix.of (Function.curry s) := by
      ext i j
      simp [Matrix.mvPolynomialX_apply, Function.curry]
    rw [← hsub, RingHom.map_det]
  have heq : {s : Fin n × Fin n → ℝ | Matrix.of (Function.curry s) ∈ reducedSet n C} =
      {s | (Matrix.of (Function.curry s)).PosDef} ∩
      ((⋂ p : Fin n × Fin n,
          {s | 0 < MvPolynomial.eval s
            (MvPolynomial.C C * MvPolynomial.X (p.1, p.1) - MvPolynomial.X p)} ∩
          {s | 0 < MvPolynomial.eval s
            (MvPolynomial.C C * MvPolynomial.X (p.1, p.1) + MvPolynomial.X p)}) ∩
        ((⋂ q : {p : Fin n × Fin n // p.1 < p.2},
            {s | 0 < MvPolynomial.eval s
              (MvPolynomial.C C * MvPolynomial.X (q.1.2, q.1.2) -
                MvPolynomial.X (q.1.1, q.1.1))}) ∩
          {s | 0 < MvPolynomial.eval s
            (MvPolynomial.C C * (Matrix.mvPolynomialX (Fin n) (Fin n) ℝ).det -
              ∏ i : Fin n, MvPolynomial.X (i, i))})) := by
    ext s
    simp only [mem_reducedSet_iff, IsReduced, Set.mem_ofPred_eq, Set.mem_inter_iff,
      Set.mem_iInter, Prod.forall, Subtype.forall, map_sub, map_add, map_mul, MvPolynomial.eval_C,
      MvPolynomial.eval_X, map_prod, sub_pos, Matrix.of_apply, Function.curry_apply, ← hdet, abs_lt]
    refine and_congr_right fun _ ↦ and_congr ?_ (and_congr Iff.rfl Iff.rfl)
    refine forall₂_congr fun i j ↦ ?_
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2, by linarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, h1⟩
  rw [heq]
  refine (TauCeti.isSemialgebraic_setOf_posDef n).inter ?_
  refine (TauCeti.IsSemialgebraic.iInter fun _ ↦
    (TauCeti.isSemialgebraic_eval_pos _).inter (TauCeti.isSemialgebraic_eval_pos _)).inter ?_
  exact (TauCeti.IsSemialgebraic.iInter fun _ ↦ TauCeti.isSemialgebraic_eval_pos _).inter
    (TauCeti.isSemialgebraic_eval_pos _)

/-- The set `T_{P, C}` of positive-definite forms whose Gram matrix `Pᵀ * b * P` in the ordered
basis formed by the columns of `P : GL (Fin n) ℝ` belongs to `reducedSet n C`. -/
def reducedSetInBasis {n : ℕ} (P : GL (Fin n) ℝ) (C : ℝ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {b | ((P : Matrix (Fin n) (Fin n) ℝ)ᵀ * b * (P : Matrix (Fin n) (Fin n) ℝ)) ∈ reducedSet n C}

/-- In the standard basis `1 : GL (Fin n) ℝ`, `reducedSetInBasis` is `reducedSet`. -/
@[simp]
theorem reducedSetInBasis_one (n : ℕ) (C : ℝ) :
    reducedSetInBasis (1 : GL (Fin n) ℝ) C = reducedSet n C := by
  ext b
  simp [reducedSetInBasis]

/-- Equivariance of `T_{P, C}` under the left action `b ↦ (g⁻¹)ᵀ * b * g⁻¹` of `g : GL (Fin n) ℝ`:
`g · T_{P, C} = T_{g * P, C}`. -/
theorem image_inv_transpose_mul_reducedSetInBasis {n : ℕ} (g P : GL (Fin n) ℝ) (C : ℝ) :
    (fun b ↦ ((g⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)ᵀ * b *
      ((g⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)) '' reducedSetInBasis P C =
      reducedSetInBasis (g * P) C := by
  ext b
  constructor
  · rintro ⟨b₀, hb₀, rfl⟩
    simp only [reducedSetInBasis, Set.mem_ofPred_eq] at hb₀ ⊢
    have hmul : ((g * P : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)ᵀ *
        (((g⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)ᵀ * b₀ *
          ((g⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)) *
        ((g * P : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) =
        (P : Matrix (Fin n) (Fin n) ℝ)ᵀ * b₀ * (P : Matrix (Fin n) (Fin n) ℝ) := by
      have hgg : ((g⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) *
          (g : Matrix (Fin n) (Fin n) ℝ) = 1 := Units.inv_mul g
      have hggt : (g : Matrix (Fin n) (Fin n) ℝ)ᵀ *
          ((g⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)ᵀ = 1 := by
        rw [← Matrix.transpose_mul, hgg, Matrix.transpose_one]
      calc ((g * P : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)ᵀ *
            (((g⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)ᵀ * b₀ *
              ((g⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)) *
            ((g * P : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)
          = (P : Matrix (Fin n) (Fin n) ℝ)ᵀ *
              ((g : Matrix (Fin n) (Fin n) ℝ)ᵀ *
                ((g⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)ᵀ) * b₀ *
              (((g⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) *
                (g : Matrix (Fin n) (Fin n) ℝ)) *
              (P : Matrix (Fin n) (Fin n) ℝ) := by
            simp only [Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]
        _ = (P : Matrix (Fin n) (Fin n) ℝ)ᵀ * b₀ * (P : Matrix (Fin n) (Fin n) ℝ) := by
            rw [hggt, hgg, Matrix.mul_one, Matrix.mul_one]
    rwa [hmul]
  · intro hb
    refine ⟨(g : Matrix (Fin n) (Fin n) ℝ)ᵀ * b * (g : Matrix (Fin n) (Fin n) ℝ), ?_, ?_⟩
    · simp only [reducedSetInBasis, Set.mem_ofPred_eq] at hb ⊢
      have hmul : (P : Matrix (Fin n) (Fin n) ℝ)ᵀ *
          ((g : Matrix (Fin n) (Fin n) ℝ)ᵀ * b * (g : Matrix (Fin n) (Fin n) ℝ)) *
          (P : Matrix (Fin n) (Fin n) ℝ) =
          ((g * P : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)ᵀ * b *
            ((g * P : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) := by
        simp only [Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]
      rwa [hmul]
    · have hggt : ((g⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)ᵀ *
          (g : Matrix (Fin n) (Fin n) ℝ)ᵀ = 1 := by
        rw [← Matrix.transpose_mul, Units.mul_inv g, Matrix.transpose_one]
      calc ((g⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)ᵀ *
            ((g : Matrix (Fin n) (Fin n) ℝ)ᵀ * b * (g : Matrix (Fin n) (Fin n) ℝ)) *
            ((g⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)
          = (((g⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)ᵀ *
              (g : Matrix (Fin n) (Fin n) ℝ)ᵀ) * b *
            ((g : Matrix (Fin n) (Fin n) ℝ) *
              ((g⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)) := by
            simp only [Matrix.mul_assoc]
        _ = b := by rw [hggt, Units.mul_inv g, Matrix.one_mul, Matrix.mul_one]

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
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial, LDL.diag, ← Matrix.transpose_transpose
    (LDL.lower hb)] at h

private theorem transpose_mul_diagonal_mul_apply {n : ℕ} (N : Matrix (Fin n) (Fin n) ℝ)
    (d : Fin n → ℝ) (i j : Fin n) :
    (Nᵀ * Matrix.diagonal d * N) i j = ∑ k : Fin n, d k * N k i * N k j := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal_apply]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Finset.sum_mul, Finset.sum_eq_single k]
  · simp [mul_comm, mul_left_comm]
  · intro l _ hlk
    simp [hlk]
  · simp

private theorem transpose_mul_diagonal_mul_apply_of_isUpperUnitriangular {n : ℕ}
    {N : Matrix (Fin n) (Fin n) ℝ} (hN : N.IsUpperUnitriangular) (d : Fin n → ℝ) (i j : Fin n) :
    (Nᵀ * Matrix.diagonal d * N) i j =
      d i * N i j + ∑ k ∈ Finset.univ.filter (· < i), d k * N k i * N k j := by
  rw [transpose_mul_diagonal_mul_apply]
  have hsplit : ∑ k : Fin n, d k * N k i * N k j =
      d i * N i i * N i j + ∑ k ∈ Finset.univ.erase i, d k * N k i * N k j :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
  rw [hsplit, hN.apply_diag i, mul_one]
  congr 1
  rw [← Finset.sum_subset (s₁ := Finset.univ.filter (· < i)) (s₂ := Finset.univ.erase i)]
  · intro k hk
    exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hk).2.ne, Finset.mem_univ k⟩
  · intro k hk hnot
    have hki_ne : k ≠ i := (Finset.mem_erase.mp hk).1
    have hik : i < k := lt_of_le_of_ne (le_of_not_gt fun hlt ↦
      hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hlt⟩)) hki_ne.symm
    simp [hN.isUpperTriangular hik]

private theorem diag_le_transpose_mul_diagonal_mul_self {n : ℕ} {N : Matrix (Fin n) (Fin n) ℝ}
    (hN : N.IsUpperUnitriangular) {d : Fin n → ℝ} (hd : ∀ i, 0 ≤ d i) (i : Fin n) :
    d i ≤ (Nᵀ * Matrix.diagonal d * N) i i := by
  rw [transpose_mul_diagonal_mul_apply_of_isUpperUnitriangular hN d i i, hN.apply_diag i, mul_one]
  have hsum : 0 ≤ ∑ k ∈ Finset.univ.filter (· < i), d k * N k i * N k i :=
    Finset.sum_nonneg fun k _ ↦ by
      have : 0 ≤ N k i * N k i := mul_self_nonneg _
      nlinarith [hd k]
  linarith

private theorem det_transpose_mul_diagonal_mul {n : ℕ} {N : Matrix (Fin n) (Fin n) ℝ}
    (hN : N.IsUpperUnitriangular) (d : Fin n → ℝ) :
    (Nᵀ * Matrix.diagonal d * N).det = ∏ i, d i := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hN.det_eq_one, Matrix.det_diagonal,
    one_mul, mul_one]

private def choleskySeqBound (C : ℝ) : ℕ → ℝ
  | 0 => C ^ 2
  | m + 1 => choleskySeqBound C m + C ^ 2 * (1 + (m : ℝ) * choleskySeqBound C m ^ 2)

private theorem choleskySeqBound_nonneg (C : ℝ) (m : ℕ) : 0 ≤ choleskySeqBound C m := by
  induction m with
  | zero => exact sq_nonneg C
  | succ m ih =>
    simp only [choleskySeqBound]
    positivity

private theorem sq_le_choleskySeqBound (C : ℝ) (m : ℕ) : C ^ 2 ≤ choleskySeqBound C m := by
  induction m with
  | zero => exact le_rfl
  | succ m ih =>
    simp only [choleskySeqBound]
    have hadd : 0 ≤ C ^ 2 * (1 + (m : ℝ) * choleskySeqBound C m ^ 2) := by positivity
    linarith

/-- **Uniform Cholesky bounds for reduced forms.** For fixed `n` and `C`, there is a constant
`R > 0` such that every positive-definite `C`-reduced matrix `b = Nᵀ * Matrix.diagonal d * N`
with `N` upper unitriangular and `0 < d i` satisfies `|N i j| ≤ R` and `d i ≤ R * d j` whenever
`i < j`. -/
theorem exists_cholesky_bound_of_isReduced (n : ℕ) (C : ℝ) :
    ∃ R : ℝ, 0 < R ∧ ∀ {b N : Matrix (Fin n) (Fin n) ℝ} {d : Fin n → ℝ},
      b.PosDef → IsReduced C b → N.IsUpperUnitriangular → (∀ i, 0 < d i) →
        b = Nᵀ * Matrix.diagonal d * N →
        (∀ i j, i < j → |N i j| ≤ R) ∧ (∀ i j, i < j → d i ≤ R * d j) := by
  refine ⟨max 1 (choleskySeqBound C n), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro b N d hb hred hN hd hfac
  have hC_pos : 0 < C := hred.pos hb
  have hd_le_b (i : Fin n) : d i ≤ b i i := by
    rw [hfac]
    exact diag_le_transpose_mul_diagonal_mul_self hN (fun k ↦ (hd k).le) i
  have hb_det : b.det = ∏ i, d i := by
    rw [hfac]
    exact det_transpose_mul_diagonal_mul hN d
  have hb_lt_Cd (i : Fin n) : b i i < C * d i := by
    have hrest_pos : 0 < ∏ j ∈ Finset.univ.erase i, d j :=
      Finset.prod_pos fun j _ ↦ hd j
    have hrest_le : (∏ j ∈ Finset.univ.erase i, d j) ≤ ∏ j ∈ Finset.univ.erase i, b j j :=
      Finset.prod_le_prod₀ (fun j _ ↦ (hd j).le) fun j _ ↦ hd_le_b j
    have hmul : b i i * (∏ j ∈ Finset.univ.erase i, d j) <
        (C * d i) * (∏ j ∈ Finset.univ.erase i, d j) := by
      calc b i i * (∏ j ∈ Finset.univ.erase i, d j)
          ≤ b i i * (∏ j ∈ Finset.univ.erase i, b j j) :=
            mul_le_mul_of_nonneg_left hrest_le hb.diag_pos.le
        _ = ∏ j, b j j := Finset.mul_prod_erase Finset.univ (fun j ↦ b j j) (Finset.mem_univ i)
        _ < C * b.det := hred.prod_diag_lt
        _ = C * (d i * ∏ j ∈ Finset.univ.erase i, d j) := by
            rw [hb_det, ← Finset.mul_prod_erase Finset.univ d (Finset.mem_univ i)]
        _ = (C * d i) * (∏ j ∈ Finset.univ.erase i, d j) := by ring
    exact lt_of_mul_lt_mul_right hmul hrest_pos.le
  have hstep : ∀ m : ℕ, ∀ i j : Fin n, i.1 < m → i < j → |N i j| ≤ choleskySeqBound C m := by
    intro m
    induction m with
    | zero =>
      intro i _ hi
      exact (Nat.not_lt_zero i.1 hi).elim
    | succ m ih =>
      intro i j him hij
      rcases Nat.lt_succ_iff_lt_or_eq.mp him with hlt | heq
      · have hprev := ih i j hlt hij
        simp only [choleskySeqBound]
        have hadd : 0 ≤ C ^ 2 * (1 + (m : ℝ) * choleskySeqBound C m ^ 2) := by positivity
        linarith
      · have hbij : b i j =
            d i * N i j + ∑ k ∈ Finset.univ.filter (· < i), d k * N k i * N k j := by
          rw [hfac]
          exact transpose_mul_diagonal_mul_apply_of_isUpperUnitriangular hN d i j
        have hdi_abs : d i * |N i j| ≤
            |b i j| + ∑ k ∈ Finset.univ.filter (· < i), d k * |N k i| * |N k j| := by
          have heq' : d i * N i j =
              b i j - ∑ k ∈ Finset.univ.filter (· < i), d k * N k i * N k j := by linarith
          calc d i * |N i j| = |d i * N i j| := by rw [abs_mul, abs_of_pos (hd i)]
            _ = |b i j - ∑ k ∈ Finset.univ.filter (· < i), d k * N k i * N k j| := by rw [heq']
            _ ≤ |b i j| + |∑ k ∈ Finset.univ.filter (· < i), d k * N k i * N k j| := abs_sub _ _
            _ ≤ |b i j| + ∑ k ∈ Finset.univ.filter (· < i), |d k * N k i * N k j| :=
                  add_le_add_right (Finset.abs_sum_le_sum_abs _ _) _
            _ = |b i j| + ∑ k ∈ Finset.univ.filter (· < i), d k * |N k i| * |N k j| := by
                  congr 2 with k
                  rw [abs_mul, abs_mul, abs_of_pos (hd k)]
        have hterm (k : Fin n) (hk : k ∈ Finset.univ.filter (· < i)) :
            d k * |N k i| * |N k j| ≤ C * b i i * choleskySeqBound C m ^ 2 := by
          have hki : k < i := (Finset.mem_filter.mp hk).2
          have hkm : k.1 < m := heq ▸ hki
          have hNki : |N k i| ≤ choleskySeqBound C m := ih k i hkm hki
          have hNkj : |N k j| ≤ choleskySeqBound C m := ih k j hkm (hki.trans hij)
          have hdk_le : d k ≤ C * b i i := (hd_le_b k).trans (hred.diag_lt_of_lt hki).le
          have hprodN : |N k i| * |N k j| ≤ choleskySeqBound C m ^ 2 := by
            rw [sq]
            exact mul_le_mul hNki hNkj (abs_nonneg _) (choleskySeqBound_nonneg C m)
          calc d k * |N k i| * |N k j| = d k * (|N k i| * |N k j|) := by ring
            _ ≤ (C * b i i) * choleskySeqBound C m ^ 2 :=
                mul_le_mul hdk_le hprodN (mul_nonneg (abs_nonneg _) (abs_nonneg _))
                  (mul_nonneg hC_pos.le hb.diag_pos.le)
            _ = C * b i i * choleskySeqBound C m ^ 2 := by ring
        have hcard : (Finset.univ.filter (· < i)).card ≤ m := by
          have hsub : (Finset.univ.filter (· < i)).map ⟨Fin.val, Fin.val_injective⟩ ⊆
              Finset.range m := by
            intro x hx
            obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hx
            exact Finset.mem_range.mpr (heq ▸ (Finset.mem_filter.mp hk).2)
          simpa using Finset.card_le_card hsub
        have hcardR : ((Finset.univ.filter (· < i)).card : ℝ) ≤ m := Nat.cast_le.mpr hcard
        have hsum_le : ∑ k ∈ Finset.univ.filter (· < i), d k * |N k i| * |N k j| ≤
            (m : ℝ) * (C * b i i * choleskySeqBound C m ^ 2) := by
          calc ∑ k ∈ Finset.univ.filter (· < i), d k * |N k i| * |N k j|
              ≤ ∑ _k ∈ Finset.univ.filter (· < i), C * b i i * choleskySeqBound C m ^ 2 :=
                Finset.sum_le_sum hterm
            _ = ((Finset.univ.filter (· < i)).card : ℝ) *
                  (C * b i i * choleskySeqBound C m ^ 2) := by simp
            _ ≤ (m : ℝ) * (C * b i i * choleskySeqBound C m ^ 2) :=
                mul_le_mul_of_nonneg_right hcardR
                  (mul_nonneg (mul_nonneg hC_pos.le hb.diag_pos.le) (sq_nonneg _))
        have hmul_le : d i * |N i j| ≤
            d i * (C ^ 2 * (1 + (m : ℝ) * choleskySeqBound C m ^ 2)) := by
          have hfactor_nonneg : 0 ≤ 1 + (m : ℝ) * choleskySeqBound C m ^ 2 := by positivity
          calc d i * |N i j|
              ≤ C * b i i + (m : ℝ) * (C * b i i * choleskySeqBound C m ^ 2) :=
                hdi_abs.trans (add_le_add (hred.abs_apply_lt i j).le hsum_le)
            _ = C * b i i * (1 + (m : ℝ) * choleskySeqBound C m ^ 2) := by ring
            _ ≤ C * (C * d i) * (1 + (m : ℝ) * choleskySeqBound C m ^ 2) :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left (hb_lt_Cd i).le hC_pos.le) hfactor_nonneg
            _ = d i * (C ^ 2 * (1 + (m : ℝ) * choleskySeqBound C m ^ 2)) := by ring
        have hNij : |N i j| ≤ C ^ 2 * (1 + (m : ℝ) * choleskySeqBound C m ^ 2) :=
          le_of_mul_le_mul_left hmul_le (hd i)
        simp only [choleskySeqBound]
        linarith [choleskySeqBound_nonneg C m]
  refine ⟨fun i j hij ↦ (hstep n i j i.isLt hij).trans (le_max_right _ _), fun i j hij ↦ ?_⟩
  have h1 : d i ≤ C ^ 2 * d j := by
    calc d i ≤ b i i := hd_le_b i
      _ ≤ C * b j j := (hred.diag_lt_of_lt hij).le
      _ ≤ C * (C * d j) := mul_le_mul_of_nonneg_left (hb_lt_Cd j).le hC_pos.le
      _ = C ^ 2 * d j := by ring
  exact h1.trans (mul_le_mul_of_nonneg_right
    ((sq_le_choleskySeqBound C n).trans (le_max_right _ _)) (hd j).le)

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
  have hR_le : R ≤ R₁ := le_max_left R 1
  set M : ℝ := (n : ℝ) * R₁ ^ (n + 2) + 1
  have hM_one : 1 ≤ M := by
    have : 0 ≤ (n : ℝ) * R₁ ^ (n + 2) := by positivity
    linarith
  set C : ℝ := max (M * R₁ ^ n) (M ^ n + 1)
  have hC_gt : 1 < C := by
    have hpow : 1 ≤ M ^ n := one_le_pow₀ hM_one
    exact (by linarith : 1 < M ^ n + 1).trans_le (le_max_right _ _)
  refine ⟨C, hC_gt, ?_⟩
  intro N d hN hd hN_le hd_step
  set b : Matrix (Fin n) (Fin n) ℝ := Nᵀ * Matrix.diagonal d * N
  have hb_posDef : b.PosDef := by
    have hdiag : (Matrix.diagonal d).PosDef := Matrix.posDef_diagonal_iff.mpr hd
    have hinj : Function.Injective N.mulVec :=
      Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det N).mpr hN.isUnit_det)
    simpa [b, Matrix.conjTranspose_eq_transpose_of_trivial] using
      hdiag.conjTranspose_mul_mul_same hinj
  have hd_ratio : ∀ (k i : Fin n), k ≤ i → d k ≤ R₁ ^ n * d i := by
    have haux : ∀ m : ℕ, ∀ (k i : Fin n), i.1 - k.1 = m → k ≤ i → d k ≤ R₁ ^ m * d i := by
      intro m
      induction m with
      | zero =>
        intro k i hdiff hki
        have hkeq : k = i := Fin.ext (by omega)
        subst hkeq
        simp
      | succ m ih =>
        intro k i hdiff hki
        have hlt : k.1 < i.1 := by omega
        have hk1 : k.1 + 1 < n := Nat.lt_of_le_of_lt hlt i.isLt
        let k' : Fin n := ⟨k.1 + 1, hk1⟩
        have hk'_le : k' ≤ i := Fin.le_def.mpr hlt
        have hdiff' : i.1 - k'.1 = m := by
          dsimp [k']
          omega
        calc d k ≤ R * d k' := hd_step k hk1
          _ ≤ R₁ * d k' := mul_le_mul_of_nonneg_right hR_le (hd k').le
          _ ≤ R₁ * (R₁ ^ m * d i) :=
              mul_le_mul_of_nonneg_left (ih k' i hdiff' hk'_le) hR₁_pos.le
          _ = R₁ ^ (m + 1) * d i := by ring
    intro k i hki
    have hm_le : i.1 - k.1 ≤ n := by omega
    calc d k ≤ R₁ ^ (i.1 - k.1) * d i := haux (i.1 - k.1) k i rfl hki
      _ ≤ R₁ ^ n * d i :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hR₁_one hm_le) (hd i).le
  have hN_all (i j : Fin n) : |N i j| ≤ R₁ := by
    rcases lt_trichotomy i j with hij | rfl | hji
    · exact (hN_le i j hij).trans hR_le
    · simpa [hN.apply_diag i] using hR₁_one
    · simpa [hN.isUpperTriangular hji] using hR₁_pos.le
  have habs_bij (i j : Fin n) : |b i j| < M * d i := by
    have hdi_pos : 0 < d i := hd i
    have hterm (k : Fin n) : |d k * N k i * N k j| ≤ R₁ ^ (n + 2) * d i := by
      by_cases hki : k ≤ i
      · rw [abs_mul, abs_mul, abs_of_pos (hd k)]
        have hN2 : |N k i| * |N k j| ≤ R₁ * R₁ :=
          mul_le_mul (hN_all k i) (hN_all k j) (abs_nonneg _) hR₁_pos.le
        calc d k * |N k i| * |N k j| = d k * (|N k i| * |N k j|) := by ring
          _ ≤ (R₁ ^ n * d i) * (R₁ * R₁) :=
              mul_le_mul (hd_ratio k i hki) hN2
                (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (by positivity)
          _ = R₁ ^ (n + 2) * d i := by ring
      · have hik : i < k := lt_of_not_ge hki
        rw [hN.isUpperTriangular hik, mul_zero, zero_mul, abs_zero]
        positivity
    have hle : |b i j| ≤ (n : ℝ) * (R₁ ^ (n + 2) * d i) := by
      have hb_eq : b i j = ∑ k : Fin n, d k * N k i * N k j :=
        transpose_mul_diagonal_mul_apply N d i j
      rw [hb_eq]
      calc |∑ k : Fin n, d k * N k i * N k j|
          ≤ ∑ k : Fin n, |d k * N k i * N k j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _k : Fin n, R₁ ^ (n + 2) * d i := Finset.sum_le_sum fun k _ ↦ hterm k
        _ = (n : ℝ) * (R₁ ^ (n + 2) * d i) := by simp
    calc |b i j| ≤ (n : ℝ) * R₁ ^ (n + 2) * d i := by linarith
      _ < ((n : ℝ) * R₁ ^ (n + 2) + 1) * d i := by linarith
  have hd_le_b (i : Fin n) : d i ≤ b i i :=
    diag_le_transpose_mul_diagonal_mul_self hN (fun k ↦ (hd k).le) i
  have hM_le_C : M ≤ C := by
    have hpow : 1 ≤ R₁ ^ n := one_le_pow₀ hR₁_one
    exact (le_mul_of_one_le_right (zero_le_one.trans hM_one) hpow).trans (le_max_left _ _)
  refine ⟨hb_posDef, ⟨fun i j ↦ ?_, fun i j hij ↦ ?_, ?_⟩⟩
  · calc |b i j| < M * d i := habs_bij i j
      _ ≤ M * b i i := mul_le_mul_of_nonneg_left (hd_le_b i) (zero_le_one.trans hM_one)
      _ ≤ C * b i i := mul_le_mul_of_nonneg_right hM_le_C hb_posDef.diag_pos.le
  · have hbii : b i i < M * d i := (le_abs_self _).trans_lt (habs_bij i i)
    have hM_pos : 0 < M := zero_lt_one.trans_le hM_one
    calc b i i < M * d i := hbii
      _ ≤ M * (R₁ ^ n * d j) :=
          mul_le_mul_of_nonneg_left (hd_ratio i j hij.le) hM_pos.le
      _ = (M * R₁ ^ n) * d j := by ring
      _ ≤ (M * R₁ ^ n) * b j j := mul_le_mul_of_nonneg_left (hd_le_b j) (by positivity)
      _ ≤ C * b j j := mul_le_mul_of_nonneg_right (le_max_left _ _) hb_posDef.diag_pos.le
  · have hb_det : b.det = ∏ i, d i := det_transpose_mul_diagonal_mul hN d
    have hprod_le : (∏ i, b i i) ≤ ∏ i, M * d i :=
      Finset.prod_le_prod₀ (fun i _ ↦ hb_posDef.diag_pos.le) fun i _ ↦
        ((le_abs_self _).trans_lt (habs_bij i i)).le
    have hdet_pos : 0 < b.det := hb_posDef.det_pos
    calc ∏ i, b i i
        ≤ ∏ i, M * d i := hprod_le
      _ = M ^ n * b.det := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
            hb_det]
      _ < (M ^ n + 1) * b.det := by linarith
      _ ≤ C * b.det := mul_le_mul_of_nonneg_right (le_max_right _ _) hdet_pos.le

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
  have hBkk_pos : 0 < B k k := hB.diag_pos
  have hterm (a b : Fin n) : |v a * (B a b * w b)| ≤ C' ^ 2 * B k k * |v a| * |w b| := by
    rw [abs_mul, abs_mul]
    rcases lt_trichotomy a k with hak | rfl | hka
    · have hBab : |B a b| ≤ C' ^ 2 * B k k := by
        calc |B a b| ≤ C' * B a a := hOff a b
          _ ≤ C' * (C' * B k k) := mul_le_mul_of_nonneg_left (hDiag a k hak) hC'_pos.le
          _ = C' ^ 2 * B k k := by ring
      calc |v a| * (|B a b| * |w b|) = |B a b| * (|v a| * |w b|) := by ring
        _ ≤ (C' ^ 2 * B k k) * (|v a| * |w b|) :=
            mul_le_mul_of_nonneg_right hBab (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        _ = C' ^ 2 * B k k * |v a| * |w b| := by ring
    · have hBkb : |B a b| ≤ C' ^ 2 * B a a := by
        calc |B a b| ≤ C' * B a a := hOff a b
          _ = C' * 1 * B a a := by ring
          _ ≤ C' * C' * B a a :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC'1 hC'_pos.le) hB.diag_pos.le
          _ = C' ^ 2 * B a a := by ring
      calc |v a| * (|B a b| * |w b|) = |B a b| * (|v a| * |w b|) := by ring
        _ ≤ (C' ^ 2 * B a a) * (|v a| * |w b|) :=
            mul_le_mul_of_nonneg_right hBkb (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        _ = C' ^ 2 * B a a * |v a| * |w b| := by ring
    · rw [hsupp a hka, abs_zero, zero_mul, mul_zero, zero_mul]
  have hsum_le : |v ⬝ᵥ B *ᵥ w| ≤ C' ^ 2 * B k k * (∑ a, |v a|) * (∑ b, |w b|) := by
    have hdot : v ⬝ᵥ B *ᵥ w = ∑ a, ∑ b, v a * (B a b * w b) := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    rw [hdot]
    calc |∑ a, ∑ b, v a * (B a b * w b)|
        ≤ ∑ a, |∑ b, v a * (B a b * w b)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a, ∑ b, |v a * (B a b * w b)| :=
          Finset.sum_le_sum fun a _ ↦ Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a, ∑ b, C' ^ 2 * B k k * |v a| * |w b| :=
          Finset.sum_le_sum fun a _ ↦ Finset.sum_le_sum fun b _ ↦ hterm a b
      _ = C' ^ 2 * B k k * (∑ a, |v a|) * (∑ b, |w b|) := by
          simp only [← Finset.mul_sum, ← Finset.sum_mul, mul_assoc]
  have hlower := hB.sq_mul_apply_self_div_le_dotProduct_mulVec hDet v k
  have hvk_sq : 0 < v k ^ 2 := sq_pos_of_ne_zero hvk
  have hBkk_le : B k k ≤ C' / v k ^ 2 * (v ⬝ᵥ B *ᵥ v) := by
    rw [div_le_iff₀ hC'_pos] at hlower
    rw [div_mul_eq_mul_div, le_div_iff₀ hvk_sq]
    linarith
  have hnonneg : 0 ≤ C' ^ 2 * (∑ a, |v a|) * (∑ b, |w b|) := by positivity
  calc |v ⬝ᵥ B *ᵥ w|
      ≤ B k k * (C' ^ 2 * (∑ a, |v a|) * (∑ b, |w b|)) := by linarith
    _ ≤ (C' / v k ^ 2 * (v ⬝ᵥ B *ᵥ v)) * (C' ^ 2 * (∑ a, |v a|) * (∑ b, |w b|)) :=
        mul_le_mul_of_nonneg_right hBkk_le hnonneg
    _ = C' ^ 3 * (∑ a, |v a|) * (∑ b, |w b|) / v k ^ 2 * (v ⬝ᵥ B *ᵥ v) := by ring

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
  have hcol_ne (i : Fin n) : colA i ≠ 0 := by
    intro h0
    have hinj := Matrix.mulVec_injective_of_isUnit A.isUnit
    have hmul : (A : Matrix (Fin n) (Fin n) ℝ) *ᵥ Pi.single i 1 = 0 := by
      ext a
      simpa [Matrix.mulVec_single_one, Matrix.col_apply, colA] using congrFun h0 a
    have h10 : (Pi.single i 1 : Fin n → ℝ) = 0 := hinj (hmul.trans (Matrix.mulVec_zero _).symm)
    simpa using congrFun h10 i
  let supp (i : Fin n) : Finset (Fin n) := Finset.univ.filter (fun a ↦ colA i a ≠ 0)
  have hsupp_ne (i : Fin n) : (supp i).Nonempty := by
    obtain ⟨a, ha⟩ := Function.ne_iff.mp (hcol_ne i)
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩
  let topIdx (i : Fin n) : Fin n := (supp i).max' (hsupp_ne i)
  have htop_ne (i : Fin n) : colA i (topIdx i) ≠ 0 :=
    (Finset.mem_filter.mp ((supp i).max'_mem (hsupp_ne i))).2
  have htop_vanish (i : Fin n) (a : Fin n) (ha : topIdx i < a) : colA i a = 0 := by
    by_contra hne
    exact not_le_of_gt ha ((supp i).le_max' a (Finset.mem_filter.mpr ⟨Finset.mem_univ a, hne⟩))
  set C₁ : ℝ := max C 1
  set C'₁ : ℝ := max C' 1
  have hC'₁_one : 1 ≤ C'₁ := le_max_right C' 1
  let K (i j : Fin n) : ℝ :=
    C'₁ ^ 3 * (∑ a, |colA i a|) * (∑ b, |colA j b|) / (colA i (topIdx i)) ^ 2
  have hK_nonneg (i j : Fin n) : 0 ≤ K i j := by
    dsimp [K]
    positivity
  set C'' : ℝ := max 2 (max (C₁ + 1) ((∑ i : Fin n, ∑ j : Fin n, K i j) + 1))
  have hC''_gt : 1 < C'' := (by norm_num : (1 : ℝ) < 2).trans_le (le_max_left _ _)
  refine ⟨C'', hC''_gt, ?_⟩
  intro B hB hRed hDet
  set B_A : Matrix (Fin n) (Fin n) ℝ :=
    (A : Matrix (Fin n) (Fin n) ℝ)ᵀ * B * (A : Matrix (Fin n) (Fin n) ℝ)
  set σ : Equiv.Perm (Fin n) := Tuple.sort (fun i ↦ B_A i i)
  have hmono : Monotone (fun i ↦ B_A (σ i) (σ i)) := Tuple.monotone_sort (fun i ↦ B_A i i)
  refine ⟨hmono, ?_⟩
  have hRed₁ : IsReduced C'₁ B := hRed.mono hB (le_max_left C' 1)
  have hB_A_posDef : B_A.PosDef := by
    have hinj := Matrix.mulVec_injective_of_isUnit A.isUnit
    simpa [B_A, Matrix.conjTranspose_eq_transpose_of_trivial] using
      hB.conjTranspose_mul_mul_same hinj
  have hB_A_apply (i j : Fin n) : B_A i j = colA i ⬝ᵥ B *ᵥ colA j := by
    simp only [B_A, colA, Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec,
      Finset.mul_sum, mul_assoc]
  set B' : Matrix (Fin n) (Fin n) ℝ := B_A.submatrix σ σ
  have hB'_posDef : B'.PosDef := hB_A_posDef.submatrix σ.injective
  refine ⟨fun i j ↦ ?_, fun i j hij ↦ ?_, ?_⟩
  · have hbij : |B' i j| ≤ K (σ i) (σ j) * B' i i := by
      simpa [B', Matrix.submatrix_apply, hB_A_apply, K] using
        abs_dotProduct_mulVec_le_of_diag_le hB hC'₁_one
          (fun a b ↦ (hRed₁.abs_apply_lt a b).le)
          (fun a b hab ↦ (hRed₁.diag_lt_of_lt hab).le)
          hRed₁.prod_diag_lt.le
          (colA (σ j)) (htop_ne (σ i)) (htop_vanish (σ i))
    have hK_le : K (σ i) (σ j) ≤ ∑ a : Fin n, ∑ b : Fin n, K a b := by
      refine le_trans (Finset.single_le_sum (fun b _ ↦ hK_nonneg (σ i) b) (Finset.mem_univ (σ j)))
        ?_
      exact Finset.single_le_sum
        (fun a _ ↦ Finset.sum_nonneg fun b _ ↦ hK_nonneg a b) (Finset.mem_univ (σ i))
    have hdiag_pos : 0 < B' i i := hB'_posDef.diag_pos
    have hsum_le_C'' : (∑ a : Fin n, ∑ b : Fin n, K a b) + 1 ≤ C'' :=
      (le_max_right _ _).trans (le_max_right _ _)
    calc |B' i j| ≤ K (σ i) (σ j) * B' i i := hbij
      _ ≤ (∑ a : Fin n, ∑ b : Fin n, K a b) * B' i i :=
          mul_le_mul_of_nonneg_right hK_le hdiag_pos.le
      _ < ((∑ a : Fin n, ∑ b : Fin n, K a b) + 1) * B' i i := by linarith
      _ ≤ C'' * B' i i := mul_le_mul_of_nonneg_right hsum_le_C'' hdiag_pos.le
  · have hle : B' i i ≤ B' j j := hmono hij.le
    have hdiag_pos : 0 < B' j j := hB'_posDef.diag_pos
    calc B' i i ≤ 1 * B' j j := by simpa using hle
      _ < C'' * B' j j := mul_lt_mul_of_pos_right hC''_gt hdiag_pos
  · have hprod_eq : (∏ i, B' i i) = ∏ i, B_A i i := Equiv.prod_comp σ (fun i ↦ B_A i i)
    have hdet_eq : B'.det = B_A.det := Matrix.det_submatrix_equiv_self σ B_A
    have hdet_pos : 0 < B_A.det := hB_A_posDef.det_pos
    have hC₁_le_C'' : C₁ + 1 ≤ C'' := (le_max_left _ _).trans (le_max_right _ _)
    rw [hprod_eq, hdet_eq]
    calc ∏ i, B_A i i ≤ C * B_A.det := hDet
      _ ≤ C₁ * B_A.det := mul_le_mul_of_nonneg_right (le_max_left C 1) hdet_pos.le
      _ < (C₁ + 1) * B_A.det := by linarith
      _ ≤ C'' * B_A.det := mul_le_mul_of_nonneg_right hC₁_le_C'' hdet_pos.le

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
  refine ⟨max 2 (max C'' 0 + 1), le_max_left _ _, ?_⟩
  set N : ℝ := max 2 (max C'' 0 + 1)
  have hN2 : 2 ≤ N := le_max_left _ _
  have hNC'' : C'' < N := by
    have h1 : C'' ≤ max C'' 0 := le_max_left _ _
    have h2 : max C'' 0 + 1 ≤ N := le_max_right _ _
    linarith
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine Matrix.posDef_diagonal_iff.mpr fun i ↦ ?_
    fin_cases i <;> simp; linarith
  · refine ⟨fun i j ↦ ?_, fun i j hij ↦ ?_, ?_⟩
    · fin_cases i <;> fin_cases j <;> simp <;> linarith [abs_of_pos (by linarith : 0 < N)]
    · fin_cases i <;> fin_cases j <;> simp at hij ⊢; linarith
    · simp [Fin.prod_univ_two, Matrix.det_diagonal]
      linarith
  · simp [Fin.prod_univ_two, Matrix.det_diagonal]
    linarith
  · intro hRed
    have h01 := hRed.diag_lt_of_lt (show (0 : Fin 2) < 1 by decide)
    simp at h01
    linarith

end BasisChange

end TauCeti.RealSiegel
