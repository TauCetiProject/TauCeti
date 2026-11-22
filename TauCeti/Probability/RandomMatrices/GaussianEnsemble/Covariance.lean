/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.RandomMatrices.GaussianEnsemble.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Matrix.Hermitian

/-!
# Covariance identities for the coordinate directions of the Gaussian ensembles

The Gaussian ensemble `gaussianEnsemble β n g` is real-linear in the array `g`, so it is the
combination `∑ ab, g ab • E ab` of the coordinate directions `E ab = gaussianEnsemble β n
(Pi.single ab 1)` (`gaussianEnsemble_eq_sum_smul_single`). With independent standard Gaussian
coordinates, or with independent standard Brownian coordinates as in matrix Brownian motion
`H(t) = H₀ + ∑ ab, B ab t • E ab`, every covariance and every quadratic covariation of linear
functionals of the matrix is therefore a sum over `ab` of products of the values of these
functionals on the directions `E ab`. This file evaluates those sums.

The basic identities are the entry covariances. Summed over `ab`, the products
`E ab k l * E ab k' l'` equal `n⁻¹` when `(k, l) = (l', k')` and vanish otherwise for `β ≠ 1`
(`sum_gaussianEnsemble_single_apply_mul_apply_of_ne_one`). For `β = 1` they equal `n⁻¹` times the
number of the two conditions `(k, l) = (l', k')` and `(k, l) = (k', l')` that hold
(`sum_gaussianEnsemble_one_single_apply_mul_apply`). Contracting against arbitrary complex
matrices `X` and `Y` gives the trace identities

* `∑ ab, tr (X E ab) * tr (Y E ab) = n⁻¹ tr (X Y)` for `β ≠ 1`,
* `∑ ab, tr (X E ab) * tr (Y E ab) = n⁻¹ (tr (X Y) + tr (X Yᵀ))` for `β = 1`,

which for Hermitian `X`, `Y` (real symmetric when `β = 1`) give the coefficient
`(2 / (β n)) Re tr (X Y)` of the bracket formula
`[tr (X H), tr (Y H)]_t = (2 / (β n)) Re tr (X Y) t` of matrix Brownian motion
(Anderson–Guionnet–Zeitouni, Definition 4.3.1). Taking rank-one matrices `X = vecMulVec v w`
gives the same identities for the bilinear expressions `w ⬝ᵥ E ab *ᵥ v`.

Write `⟪u, w⟫ = star u ⬝ᵥ w`. In the Itô computation for the eigenvalues of matrix Brownian motion
(the proof of Anderson–Guionnet–Zeitouni, Theorem 4.3.2), the eigenvalue `λᵢ` has first derivative
`Re ⟪uᵢ, E uᵢ⟫` in the direction `E` and second derivative `2 ∑_{j ≠ i} ‖⟪uⱼ, E uᵢ⟫‖² / (λᵢ - λⱼ)`,
for an orthonormal eigenbasis `u`. The last four theorems evaluate the two sums over the directions
that this computation needs. For `β ≠ 1` and unit vectors `u`, `v`, the sum of `‖⟪u, E ab v⟫‖²` is
`n⁻¹`, which turns the second derivatives into the drift `n⁻¹ ∑_{j ≠ i} (λᵢ - λⱼ)⁻¹`. The sum of
`Re ⟪u, E ab u⟫ * Re ⟪v, E ab v⟫` is `n⁻¹ ‖⟪u, v⟫‖²` for `β ≠ 1`, so the martingale parts of
distinct eigenvalues have zero bracket and each has bracket `2 / (β n)` per unit time. For `β = 1`
both sums carry the extra term `n⁻¹ ‖u ⬝ᵥ v‖²`, which vanishes for real orthogonal vectors.

## Main results

* `TauCeti.Probability.gaussianEnsemble_eq_sum_smul_single`: the expansion in the directions.
* `TauCeti.Probability.sum_gaussianEnsemble_single_apply_mul_apply_of_ne_one` and
  `TauCeti.Probability.sum_gaussianEnsemble_one_single_apply_mul_apply`: entry covariances.
* `TauCeti.Probability.sum_trace_mul_gaussianEnsemble_single_mul_trace_mul_of_ne_one` and
  `TauCeti.Probability.sum_trace_mul_gaussianEnsemble_one_single_mul_trace_mul`: trace identities.
* `TauCeti.Probability.sum_dotProduct_mulVec_gaussianEnsemble_single_mul_of_ne_one` and
  `TauCeti.Probability.sum_dotProduct_mulVec_gaussianEnsemble_one_single_mul`: bilinear forms.
* `TauCeti.Probability.sum_norm_star_dotProduct_mulVec_gaussianEnsemble_single_sq_of_ne_one`,
  `TauCeti.Probability.sum_norm_star_dotProduct_mulVec_gaussianEnsemble_one_single_sq`,
  `TauCeti.Probability.sum_re_star_dotProduct_mulVec_gaussianEnsemble_single_mul_re_of_ne_one`
  and `TauCeti.Probability.sum_re_star_dotProduct_mulVec_gaussianEnsemble_one_single_mul_re`: the
  sums entering the eigenvalue equation.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), Definition 4.3.1 and the proof of Theorem 4.3.2.
* T. Tao, *Topics in Random Matrix Theory*, Graduate Studies in Mathematics 132, AMS (2012),
  §3.1.
-/

public section

noncomputable section

open Matrix
open scoped ComplexOrder

namespace TauCeti

namespace Probability

variable {β n : ℕ}

/-- The Gaussian ensemble of an array `g` is the combination, with coefficients `g ab`, of the
ensembles of the unit arrays `Pi.single ab 1`. -/
theorem gaussianEnsemble_eq_sum_smul_single (β n : ℕ) (g : Fin n × Fin n → ℝ) :
    gaussianEnsemble β n g = ∑ ab, g ab • gaussianEnsemble β n (Pi.single ab 1) := by
  let L : (Fin n × Fin n → ℝ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun := gaussianEnsemble β n
      map_add' := gaussianEnsemble_add
      map_smul' := gaussianEnsemble_smul }
  have hg : ∑ ab, g ab • Pi.single ab (1 : ℝ) = g := by
    simp_rw [← Pi.single_smul', smul_eq_mul, mul_one]
    exact Finset.univ_sum_single g
  calc gaussianEnsemble β n g = L (∑ ab, g ab • Pi.single ab 1) := by simp [L, hg]
    _ = _ := by simp [L]

/-- **Entry covariances of the complex Hermitian ensemble.** For `β ≠ 1`, summing the products
`E ab k l * E ab k' l'` of entries of the directions `E ab = gaussianEnsemble β n (Pi.single ab 1)`
over all `ab` gives `n⁻¹` when `k = l'` and `l = k'`, and `0` otherwise. Equivalently, since
`E ab l' k'` is the conjugate of `E ab k' l'`, the sum of `E ab k l * conj (E ab k' l')` is `n⁻¹`
exactly when `(k, l) = (k', l')`. -/
theorem sum_gaussianEnsemble_single_apply_mul_apply_of_ne_one (hβ : β ≠ 1) (k l k' l' : Fin n) :
    ∑ ab, gaussianEnsemble β n (Pi.single ab 1) k l *
        gaussianEnsemble β n (Pi.single ab 1) k' l' =
      if k = l' ∧ l = k' then (n : ℂ)⁻¹ else 0 := by
  have hs : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ ^ 2 = 1 / 2 := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_pow, inv_pow, Real.sq_sqrt (by norm_num)]
    simp
  have hn : ((Real.sqrt n : ℝ) : ℂ)⁻¹ ^ 2 = (n : ℂ)⁻¹ := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_pow, inv_pow, Real.sq_sqrt (by positivity)]
    simp
  have hI := Complex.I_sq
  simp only [gaussianEnsemble_apply, hβ, ite_false, Pi.single_apply]
  -- Split on the position of `(k, l)` and of `(k', l')` relative to the diagonal, evaluate the sum
  -- over `ab` of products of indicators, and close each case by the order relations of the
  -- indices or by arithmetic in `ℂ`.
  split_ifs <;>
    simp only [apply_ite Complex.ofReal, Complex.ofReal_one, Complex.ofReal_zero, mul_add,
      add_mul, mul_sub, sub_mul, div_eq_mul_inv, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ite_mul, mul_ite, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
      Prod.mk.injEq, mul_one] <;>
    split_ifs <;> simp only [Fin.ext_iff, Fin.lt_def] at * <;> first | omega | grind

/-- **Entry covariances of the real symmetric ensemble.** For `β = 1`, summing the products
`E ab k l * E ab k' l'` of entries of the directions `E ab = gaussianEnsemble 1 n (Pi.single ab 1)`
over all `ab` gives `n⁻¹` times the number of the conditions `(k, l) = (l', k')` and
`(k, l) = (k', l')` that hold. In particular the diagonal entries have variance `2 / n` and the
off-diagonal ones `1 / n`. -/
theorem sum_gaussianEnsemble_one_single_apply_mul_apply (k l k' l' : Fin n) :
    ∑ ab, gaussianEnsemble 1 n (Pi.single ab 1) k l *
        gaussianEnsemble 1 n (Pi.single ab 1) k' l' =
      (n : ℂ)⁻¹ * ((if k = l' ∧ l = k' then 1 else 0) + if k = k' ∧ l = l' then 1 else 0) := by
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    simp
  have hn : ((Real.sqrt n : ℝ) : ℂ)⁻¹ ^ 2 = (n : ℂ)⁻¹ := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_pow, inv_pow, Real.sq_sqrt (by positivity)]
    simp
  simp only [gaussianEnsemble_apply, ite_true, Pi.single_apply]
  -- The same case analysis as for `β ≠ 1`, with real entries.
  split_ifs <;>
    simp only [apply_ite Complex.ofReal, Complex.ofReal_one, Complex.ofReal_zero, mul_add,
      ite_mul, mul_ite, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
      Prod.mk.injEq, mul_one] <;>
    split_ifs <;> simp only [Fin.ext_iff, Fin.lt_def] at * <;> first | omega | grind

/-- The sum over the directions of products of traces, expanded in the entries of `X` and `Y`. -/
private theorem sum_trace_mul_gaussianEnsemble_single_mul_trace_mul_eq_sum (β n : ℕ)
    (X Y : Matrix (Fin n) (Fin n) ℂ) :
    ∑ ab, (X * gaussianEnsemble β n (Pi.single ab 1)).trace *
        (Y * gaussianEnsemble β n (Pi.single ab 1)).trace =
      ∑ i, ∑ j, ∑ k, ∑ l, X k l * Y i j * ∑ ab, gaussianEnsemble β n (Pi.single ab 1) l k *
        gaussianEnsemble β n (Pi.single ab 1) j i := by
  simp only [trace, diag, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  -- Move the sum over the directions `ab` inside the four sums over the entries.
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun l _ ↦ ?_
  exact Finset.sum_congr rfl fun ab _ ↦ by ring

/-- **Trace identity for the complex Hermitian ensemble.** For `β ≠ 1` and all complex matrices
`X` and `Y`, the sum over the directions `E ab = gaussianEnsemble β n (Pi.single ab 1)` of
`tr (X E ab) * tr (Y E ab)` is `n⁻¹ tr (X Y)`. For Hermitian `X` and `Y` both traces on the left
are real, and this is the covariance `n⁻¹ Re tr (X Y)` of `tr (X H)` and `tr (Y H)` for the GUE
`H`. -/
theorem sum_trace_mul_gaussianEnsemble_single_mul_trace_mul_of_ne_one (hβ : β ≠ 1)
    (X Y : Matrix (Fin n) (Fin n) ℂ) :
    ∑ ab, (X * gaussianEnsemble β n (Pi.single ab 1)).trace *
        (Y * gaussianEnsemble β n (Pi.single ab 1)).trace =
      (n : ℂ)⁻¹ * (X * Y).trace := by
  rw [sum_trace_mul_gaussianEnsemble_single_mul_trace_mul_eq_sum]
  simp only [sum_gaussianEnsemble_single_apply_mul_apply_of_ne_one hβ, mul_ite, mul_zero, ite_and,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, trace, diag, Matrix.mul_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

/-- **Trace identity for the real symmetric ensemble.** For `β = 1` and all complex matrices `X`
and `Y`, the sum over the directions `E ab = gaussianEnsemble 1 n (Pi.single ab 1)` of
`tr (X E ab) * tr (Y E ab)` is `n⁻¹ (tr (X Y) + tr (X Yᵀ))`. For real symmetric `X` and `Y` this
is the covariance `(2 / n) tr (X Y)` of `tr (X H)` and `tr (Y H)` for the GOE `H`. -/
theorem sum_trace_mul_gaussianEnsemble_one_single_mul_trace_mul (X Y : Matrix (Fin n) (Fin n) ℂ) :
    ∑ ab, (X * gaussianEnsemble 1 n (Pi.single ab 1)).trace *
        (Y * gaussianEnsemble 1 n (Pi.single ab 1)).trace =
      (n : ℂ)⁻¹ * ((X * Y).trace + (X * Yᵀ).trace) := by
  rw [sum_trace_mul_gaussianEnsemble_single_mul_trace_mul_eq_sum]
  simp only [sum_gaussianEnsemble_one_single_apply_mul_apply, mul_add, mul_ite, mul_one, mul_zero,
    Finset.sum_add_distrib, ite_and, Finset.sum_ite_eq', Finset.mem_univ, ite_true, trace,
    diag, Matrix.mul_apply, transpose_apply, Finset.mul_sum]
  congr 1
  · rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
  · exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

/-- **Bilinear forms of the complex Hermitian directions.** For `β ≠ 1` and all vectors, the sum
over the directions `E ab = gaussianEnsemble β n (Pi.single ab 1)` of
`(w ⬝ᵥ E ab *ᵥ v) * (w' ⬝ᵥ E ab *ᵥ v')` is `n⁻¹ (w ⬝ᵥ v') (w' ⬝ᵥ v)`. -/
theorem sum_dotProduct_mulVec_gaussianEnsemble_single_mul_of_ne_one (hβ : β ≠ 1)
    (w v w' v' : Fin n → ℂ) :
    ∑ ab, (w ⬝ᵥ gaussianEnsemble β n (Pi.single ab 1) *ᵥ v) *
        (w' ⬝ᵥ gaussianEnsemble β n (Pi.single ab 1) *ᵥ v') =
      (n : ℂ)⁻¹ * ((w ⬝ᵥ v') * (w' ⬝ᵥ v)) := by
  -- Each bilinear form is the trace of a rank-one matrix times the direction.
  have h (v w : Fin n → ℂ) (M : Matrix (Fin n) (Fin n) ℂ) :
      w ⬝ᵥ M *ᵥ v = (vecMulVec v w * M).trace := by
    rw [vecMulVec_mul, trace_vecMulVec, dotProduct_mulVec, dotProduct_comm]
  simp_rw [h]
  rw [sum_trace_mul_gaussianEnsemble_single_mul_trace_mul_of_ne_one hβ, vecMulVec_mul_vecMulVec,
    trace_vecMulVec, dotProduct_smul, smul_eq_mul, dotProduct_comm v w']

/-- **Bilinear forms of the real symmetric directions.** For `β = 1` and all vectors, the sum
over the directions `E ab = gaussianEnsemble 1 n (Pi.single ab 1)` of
`(w ⬝ᵥ E ab *ᵥ v) * (w' ⬝ᵥ E ab *ᵥ v')` is `n⁻¹ ((w ⬝ᵥ v') (w' ⬝ᵥ v) + (w ⬝ᵥ w') (v ⬝ᵥ v'))`. -/
theorem sum_dotProduct_mulVec_gaussianEnsemble_one_single_mul (w v w' v' : Fin n → ℂ) :
    ∑ ab, (w ⬝ᵥ gaussianEnsemble 1 n (Pi.single ab 1) *ᵥ v) *
        (w' ⬝ᵥ gaussianEnsemble 1 n (Pi.single ab 1) *ᵥ v') =
      (n : ℂ)⁻¹ * ((w ⬝ᵥ v') * (w' ⬝ᵥ v) + (w ⬝ᵥ w') * (v ⬝ᵥ v')) := by
  -- Each bilinear form is the trace of a rank-one matrix times the direction.
  have h (v w : Fin n → ℂ) (M : Matrix (Fin n) (Fin n) ℂ) :
      w ⬝ᵥ M *ᵥ v = (vecMulVec v w * M).trace := by
    rw [vecMulVec_mul, trace_vecMulVec, dotProduct_mulVec, dotProduct_comm]
  simp_rw [h]
  rw [sum_trace_mul_gaussianEnsemble_one_single_mul_trace_mul, transpose_vecMulVec,
    vecMulVec_mul_vecMulVec, vecMulVec_mul_vecMulVec, trace_vecMulVec, trace_vecMulVec,
    dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, dotProduct_comm v w',
    dotProduct_comm v v']

/-- A sum of squared norms of the bilinear forms `star u ⬝ᵥ E ab *ᵥ v` of Hermitian directions,
written as the sum of the products `(star u ⬝ᵥ E ab *ᵥ v) * (star v ⬝ᵥ E ab *ᵥ u)` in `ℂ`. -/
private theorem ofReal_sum_norm_star_dotProduct_mulVec_gaussianEnsemble_single_sq (β n : ℕ)
    (u v : Fin n → ℂ) :
    ((∑ ab, ‖star u ⬝ᵥ gaussianEnsemble β n (Pi.single ab 1) *ᵥ v‖ ^ 2 : ℝ) : ℂ) =
      ∑ ab, (star u ⬝ᵥ gaussianEnsemble β n (Pi.single ab 1) *ᵥ v) *
        (star v ⬝ᵥ gaussianEnsemble β n (Pi.single ab 1) *ᵥ u) := by
  push_cast
  refine Finset.sum_congr rfl fun ab _ ↦ ?_
  rw [← Complex.mul_conj', ← Complex.star_def,
    (isHermitian_gaussianEnsemble β n _).star_dotProduct_mulVec_comm]

/-- **The drift sum for the complex Hermitian ensemble.** For `β ≠ 1`, the sum over the directions
`E ab = gaussianEnsemble β n (Pi.single ab 1)` of `‖star u ⬝ᵥ E ab *ᵥ v‖²` is
`n⁻¹ (star u ⬝ᵥ u) (star v ⬝ᵥ v)`, so it is `n⁻¹` for unit vectors. -/
theorem sum_norm_star_dotProduct_mulVec_gaussianEnsemble_single_sq_of_ne_one (hβ : β ≠ 1)
    (u v : Fin n → ℂ) :
    ∑ ab, ‖star u ⬝ᵥ gaussianEnsemble β n (Pi.single ab 1) *ᵥ v‖ ^ 2 =
      (n : ℝ)⁻¹ * (star u ⬝ᵥ u).re * (star v ⬝ᵥ v).re := by
  have h := ofReal_sum_norm_star_dotProduct_mulVec_gaussianEnsemble_single_sq β n u v
  rw [sum_dotProduct_mulVec_gaussianEnsemble_single_mul_of_ne_one hβ,
    Complex.eq_re_of_ofReal_le (r := 0) (z := star u ⬝ᵥ u)
      (by rw [Complex.ofReal_zero]; exact dotProduct_star_self_nonneg u),
    Complex.eq_re_of_ofReal_le (r := 0) (z := star v ⬝ᵥ v)
      (by rw [Complex.ofReal_zero]; exact dotProduct_star_self_nonneg v),
    ← mul_assoc] at h
  exact Complex.ofReal_injective (by rw [h]; push_cast; rfl)

/-- **The drift sum for the real symmetric ensemble.** For `β = 1`, the sum over the directions
`E ab = gaussianEnsemble 1 n (Pi.single ab 1)` of `‖star u ⬝ᵥ E ab *ᵥ v‖²` is
`n⁻¹ ((star u ⬝ᵥ u) (star v ⬝ᵥ v) + ‖u ⬝ᵥ v‖²)`, so it is `n⁻¹` for unit vectors with
`u ⬝ᵥ v = 0`, for instance real orthogonal unit vectors. -/
theorem sum_norm_star_dotProduct_mulVec_gaussianEnsemble_one_single_sq (u v : Fin n → ℂ) :
    ∑ ab, ‖star u ⬝ᵥ gaussianEnsemble 1 n (Pi.single ab 1) *ᵥ v‖ ^ 2 =
      (n : ℝ)⁻¹ * ((star u ⬝ᵥ u).re * (star v ⬝ᵥ v).re + ‖u ⬝ᵥ v‖ ^ 2) := by
  have h := ofReal_sum_norm_star_dotProduct_mulVec_gaussianEnsemble_single_sq 1 n u v
  rw [sum_dotProduct_mulVec_gaussianEnsemble_one_single_mul, star_dotProduct_star,
    dotProduct_comm v u, Complex.star_def, Complex.conj_mul'] at h
  rw [Complex.eq_re_of_ofReal_le (r := 0) (z := star u ⬝ᵥ u)
      (by rw [Complex.ofReal_zero]; exact dotProduct_star_self_nonneg u),
    Complex.eq_re_of_ofReal_le (r := 0) (z := star v ⬝ᵥ v)
      (by rw [Complex.ofReal_zero]; exact dotProduct_star_self_nonneg v)] at h
  exact Complex.ofReal_injective (by rw [h]; push_cast; rfl)

/-- For Hermitian directions, the sum of products of the real parts of the quadratic forms
`star u ⬝ᵥ E ab *ᵥ u` and `star v ⬝ᵥ E ab *ᵥ v` is the real part of the sum of their products. -/
private theorem sum_re_mul_re_star_dotProduct_mulVec_gaussianEnsemble_single (β n : ℕ)
    (u v : Fin n → ℂ) :
    ∑ ab, (star u ⬝ᵥ gaussianEnsemble β n (Pi.single ab 1) *ᵥ u).re *
        (star v ⬝ᵥ gaussianEnsemble β n (Pi.single ab 1) *ᵥ v).re =
      (∑ ab, (star u ⬝ᵥ gaussianEnsemble β n (Pi.single ab 1) *ᵥ u) *
        (star v ⬝ᵥ gaussianEnsemble β n (Pi.single ab 1) *ᵥ v)).re := by
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun ab _ ↦ ?_
  have hu := (isHermitian_gaussianEnsemble β n (Pi.single ab 1)).im_star_dotProduct_mulVec_self u
  rw [RCLike.im_to_complex] at hu
  rw [Complex.mul_re, hu, zero_mul, sub_zero]

/-- **The bracket sum for the complex Hermitian ensemble.** For `β ≠ 1`, the sum over the
directions `E ab = gaussianEnsemble β n (Pi.single ab 1)` of the products of the real parts of
`star u ⬝ᵥ E ab *ᵥ u` and `star v ⬝ᵥ E ab *ᵥ v` is `n⁻¹ ‖star u ⬝ᵥ v‖²`: it is `n⁻¹` for a unit
vector `u = v` and vanishes for orthogonal `u` and `v`. -/
theorem sum_re_star_dotProduct_mulVec_gaussianEnsemble_single_mul_re_of_ne_one (hβ : β ≠ 1)
    (u v : Fin n → ℂ) :
    ∑ ab, (star u ⬝ᵥ gaussianEnsemble β n (Pi.single ab 1) *ᵥ u).re *
        (star v ⬝ᵥ gaussianEnsemble β n (Pi.single ab 1) *ᵥ v).re =
      (n : ℝ)⁻¹ * ‖star u ⬝ᵥ v‖ ^ 2 := by
  rw [sum_re_mul_re_star_dotProduct_mulVec_gaussianEnsemble_single,
    sum_dotProduct_mulVec_gaussianEnsemble_single_mul_of_ne_one hβ, star_dotProduct v u,
    Complex.star_def, Complex.mul_conj']
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.re_ofReal_mul]
  norm_cast

/-- **The bracket sum for the real symmetric ensemble.** For `β = 1`, the sum over the
directions `E ab = gaussianEnsemble 1 n (Pi.single ab 1)` of the products of the real parts of
`star u ⬝ᵥ E ab *ᵥ u` and `star v ⬝ᵥ E ab *ᵥ v` is `n⁻¹ (‖star u ⬝ᵥ v‖² + ‖u ⬝ᵥ v‖²)`: it is
`2 / n` for a real unit vector `u = v` and vanishes for real orthogonal `u` and `v`. -/
theorem sum_re_star_dotProduct_mulVec_gaussianEnsemble_one_single_mul_re (u v : Fin n → ℂ) :
    ∑ ab, (star u ⬝ᵥ gaussianEnsemble 1 n (Pi.single ab 1) *ᵥ u).re *
        (star v ⬝ᵥ gaussianEnsemble 1 n (Pi.single ab 1) *ᵥ v).re =
      (n : ℝ)⁻¹ * (‖star u ⬝ᵥ v‖ ^ 2 + ‖u ⬝ᵥ v‖ ^ 2) := by
  rw [sum_re_mul_re_star_dotProduct_mulVec_gaussianEnsemble_single,
    sum_dotProduct_mulVec_gaussianEnsemble_one_single_mul, star_dotProduct v u,
    star_dotProduct_star, dotProduct_comm v u, Complex.star_def, Complex.mul_conj',
    Complex.conj_mul']
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.re_ofReal_mul]
  norm_cast

end Probability

end TauCeti
