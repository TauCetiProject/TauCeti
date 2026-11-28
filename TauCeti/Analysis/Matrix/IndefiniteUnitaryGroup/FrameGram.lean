/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import TauCeti.LinearAlgebra.Matrix.Determinant.FrameGram
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import TauCeti.Analysis.Matrix.Eigenvalues.Inertia
import TauCeti.Analysis.Matrix.IndefiniteUnitaryGroup
import TauCeti.LinearAlgebra.Matrix.DotProduct

/-!
# The Gram determinant of two frames in `U(p, q)` has sign `(-1) ^ (n + 1)`

Let `J = diag(1, …, 1, -1, …, -1)` be the Gram matrix of the Hermitian form of signature
`(p, q)` on `𝕜^(p ⊕ q)`, over `ℝ` or `ℂ`. Let `F` and `F'` be frames of `n + 1` vectors of norms
`-T` and `-T'` (`Matrix.det_conjTranspose_fromCols_mul_mul_fromCols_of_frame`): the first `n`
vectors of each are isotropic and orthogonal to the whole frame, and the last has norm `-T`,
respectively `-T'`. Let `Z = Fᴴ * J * F'` be the matrix of the products `⟨F_a, F'_b⟩` and `D` its
leading principal minor of order `n`. If `q ≤ n + 1` and `T ≥ 0`, then

`T T' |D|² ≤ |det Z|²`

(`Matrix.mul_mul_norm_det_submatrix_castSucc_sq_le_of_frame`). For `n = 0` this is the
reverse Cauchy–Schwarz inequality `T T' ≤ |⟨z, z'⟩|²` for two vectors `z`, `z'` of norms `-T`,
`-T'` in a space of signature `(p, 1)`.

The Gram determinant of the `2n + 2` vectors `F ∪ F'` is `(-1) ^ (n + 1) * (|det Z|² - T T' |D|²)`.
On the span of the first frame the form is `-T |c_n|² ≤ 0`, and on the vectors whose image has
vanishing `q` coordinates it is nonnegative. These two subspaces have dimensions `n + 1` and at
least `2n + 2 - q ≥ n + 1`, so by the count of the indices of inertia of the Gram matrix
(`Matrix.IsHermitian.neg_one_pow_finrank_mul_re_det_nonneg`) the sign of the Gram determinant is
`(-1) ^ (n + 1)` unless it vanishes.

## Main results

* `Matrix.mul_mul_norm_det_submatrix_castSucc_sq_le_of_frame`: the inequality for two frames.
* `TauCeti.Matrix.indefiniteUnitaryGroup.mul_mul_norm_det_submatrix_castSucc_sq_le_of_frame`:
  the inequality for a frame and the image of a frame under an element of `U(p, q)`.

## References

The statement is the sign of the function `Gr` of the big cell of `U(p, q)` relative to a Bessel
subgroup, used in the analysis of Bessel models of discrete series. The Gram determinant identity
it rests on is adapted from grh-lean, see `TauCeti.LinearAlgebra.Matrix.Determinant.FrameGram`.
-/

public section

open Fin LieAlgebra.Orthogonal Module

namespace Matrix

variable {p q 𝕜 : Type*} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q] [RCLike 𝕜]
  {n : ℕ} {F F' : Matrix (p ⊕ q) (Fin (n + 1)) 𝕜} {T T' : ℝ}

/-- The form of the Gram matrix of `fromCols F F'` is nonpositive on the span of the first
frame `F`, the image of `fromRows 1 0`: at `fromRows 1 0 *ᵥ c` it is `-T * ‖c (last n)‖ ^ 2`. -/
private theorem re_star_dotProduct_fromCols_mulVec_fromRows_one_zero_nonpos (hT : 0 ≤ T)
    (hF : Fᴴ * indefiniteDiagonal p q 𝕜 * F = single (last n) (last n) (-(T : 𝕜)))
    (c : Fin (n + 1) → 𝕜) :
    RCLike.re (star (fromRows 1 0 *ᵥ c) ⬝ᵥ
      ((fromCols F F')ᴴ * indefiniteDiagonal p q 𝕜 * fromCols F F') *ᵥ (fromRows 1 0 *ᵥ c)) ≤
      0 := by
  set J := indefiniteDiagonal p q 𝕜
  set P := fromCols F F'
  set E : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1)) 𝕜 := fromRows 1 0
  have hPE : P * E = F := by simp [P, E, fromCols_mul_fromRows]
  rw [← star_dotProduct_conjTranspose_mul_mul_mulVec,
    show Eᴴ * (Pᴴ * J * P) * E = (P * E)ᴴ * J * (P * E) by
      simp only [conjTranspose_mul, Matrix.mul_assoc], hPE, hF]
  -- the form of `single (last n) (last n) (-T)` at `c` is `-T * ‖c (last n)‖ ^ 2`
  have h_val : star c ⬝ᵥ single (last n) (last n) (-(T : 𝕜)) *ᵥ c =
      ((-T * ‖c (last n)‖ ^ 2 : ℝ) : 𝕜) := by
    suffices h : star (c (last n)) * (-(T : 𝕜) * c (last n)) =
        ((-T * ‖c (last n)‖ ^ 2 : ℝ) : 𝕜) by
      simpa [dotProduct, single_mulVec, Function.update_apply] using h
    rw [RCLike.star_def, mul_left_comm, RCLike.conj_mul]
    push_cast
    ring
  rw [h_val, RCLike.ofReal_re, neg_mul, neg_nonpos]
  positivity

/-- The form of the Gram matrix `Pᴴ * J * P` is nonnegative at the vectors `v` whose image
`P v` has vanishing `q` coordinates. -/
private theorem re_star_dotProduct_gram_mulVec_nonneg_of_mem_ker {m : Type*} [Fintype m]
    {P : Matrix (p ⊕ q) m 𝕜} {v : m → 𝕜}
    (hv : v ∈ LinearMap.ker (P.submatrix Sum.inr id).mulVecLin) :
    0 ≤ RCLike.re (star v ⬝ᵥ (Pᴴ * indefiniteDiagonal p q 𝕜 * P) *ᵥ v) := by
  have h_q (j : q) : (P *ᵥ v) (Sum.inr j) = 0 := congrFun (LinearMap.mem_ker.1 hv) j
  rw [star_dotProduct_conjTranspose_mul_mul_mulVec,
    star_dotProduct_indefiniteDiagonal_mulVec_self, RCLike.ofReal_re]
  simp only [h_q, norm_zero, zero_pow two_ne_zero, Finset.sum_const_zero, sub_zero]
  positivity

/-- The real part of `(-1) ^ (n + 1) * (a * star a - T * T' * (b * star b))` is
`(-1) ^ (n + 1) * (‖a‖ ^ 2 - T * T' * ‖b‖ ^ 2)`. -/
private theorem re_neg_one_pow_mul_sub_mul_mul (a b : 𝕜) :
    RCLike.re ((-1 : 𝕜) ^ (n + 1) * (a * star a - (T : 𝕜) * T' * (b * star b))) =
      (-1) ^ (n + 1) * (‖a‖ ^ 2 - T * T' * ‖b‖ ^ 2) := by
  have h_real (z : 𝕜) : z * star z = ((‖z‖ ^ 2 : ℝ) : 𝕜) := by
    rw [RCLike.star_def, RCLike.mul_conj, RCLike.ofReal_pow]
  have h : (-1 : 𝕜) ^ (n + 1) * (a * star a - (T : 𝕜) * T' * (b * star b)) =
      (((-1) ^ (n + 1) * (‖a‖ ^ 2 - T * T' * ‖b‖ ^ 2) : ℝ) : 𝕜) := by
    rw [h_real, h_real]
    push_cast
    ring
  rw [h, RCLike.ofReal_re]

/-- **The Gram determinant of two frames in `U(p, q)`.** Let `F` and `F'` be frames of norms
`-T` and `-T'` for the form `J` of signature `(p, q)`, with `q ≤ n + 1` and `T ≥ 0`. With
`Z = Fᴴ * J * F'` the matrix of the products `⟨F_a, F'_b⟩` and `D` its leading principal minor of
order `n`, `T T' |D|² ≤ |det Z|²`: the Gram determinant of `F ∪ F'`, which is
`(-1) ^ (n + 1) * (|det Z|² - T T' |D|²)`, has the sign `(-1) ^ (n + 1)` or vanishes. -/
theorem mul_mul_norm_det_submatrix_castSucc_sq_le_of_frame (hq : Fintype.card q ≤ n + 1)
    (hT : 0 ≤ T)
    (hF : Fᴴ * indefiniteDiagonal p q 𝕜 * F = single (last n) (last n) (-(T : 𝕜)))
    (hF' : F'ᴴ * indefiniteDiagonal p q 𝕜 * F' = single (last n) (last n) (-(T' : 𝕜))) :
    T * T' * ‖((Fᴴ * indefiniteDiagonal p q 𝕜 * F').submatrix castSucc castSucc).det‖ ^ 2 ≤
      ‖(Fᴴ * indefiniteDiagonal p q 𝕜 * F').det‖ ^ 2 := by
  set J := indefiniteDiagonal p q 𝕜
  set P := fromCols F F'
  have hG : (Pᴴ * J * P).IsHermitian :=
    isHermitian_conjTranspose_mul_mul P isHermitian_indefiniteDiagonal
  -- The form is nonpositive on the span `W` of the first frame, of dimension `n + 1`.
  set E : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1)) 𝕜 := fromRows 1 0
  have hE : Function.Injective E.mulVecLin := fun c c' h => funext fun i => by
    simpa [E, fromRows_mulVec] using congrFun h (Sum.inl i)
  have hW : ∀ v ∈ LinearMap.range E.mulVecLin, RCLike.re (star v ⬝ᵥ (Pᴴ * J * P) *ᵥ v) ≤ 0 := by
    rintro _ ⟨c, rfl⟩
    exact re_star_dotProduct_fromCols_mulVec_fromRows_one_zero_nonpos hT hF c
  -- The form is nonnegative on the vectors `v` whose image `P v` has vanishing `q` coordinates,
  -- a subspace of dimension at least `2 * (n + 1) - q`.
  set K := (P.submatrix Sum.inr id).mulVecLin
  have h_ker : 2 * (n + 1) ≤ Fintype.card q + finrank 𝕜 (LinearMap.ker K) := by
    have h := LinearMap.finrank_range_add_finrank_ker K
    have h_range := Submodule.finrank_le (LinearMap.range K)
    simp only [finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin] at h h_range
    omega
  have h_sign := hG.neg_one_pow_finrank_mul_re_det_nonneg hW
    (W' := LinearMap.ker K) (fun _ hv => re_star_dotProduct_gram_mulVec_nonneg_of_mem_ker hv) (by
      rw [LinearMap.finrank_range_of_inj hE]
      simp only [finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
      omega)
  rw [LinearMap.finrank_range_of_inj hE, finrank_fintype_fun_eq_card, Fintype.card_fin,
    det_conjTranspose_fromCols_mul_mul_fromCols_of_frame isHermitian_indefiniteDiagonal hF hF']
    at h_sign
  -- The Gram determinant is `(-1) ^ (n + 1)` times the real number `|det Z|² - T T' |D|²`.
  have h_sq : ((-1 : ℝ) ^ (n + 1)) ^ 2 = 1 := by
    rw [← pow_mul]
    exact Even.neg_one_pow ⟨n + 1, by ring⟩
  rwa [re_neg_one_pow_mul_sub_mul_mul, ← mul_assoc, ← sq, h_sq, one_mul, sub_nonneg] at h_sign

end Matrix

namespace TauCeti.Matrix.indefiniteUnitaryGroup

open _root_.Matrix

variable {p q 𝕜 : Type*} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q] [RCLike 𝕜]
  {n : ℕ} {F F' : _root_.Matrix (p ⊕ q) (Fin (n + 1)) 𝕜} {T T' : ℝ}

/-- **The Gram determinant of a frame and the image of a frame under `U(p, q)`.** Let `F` and
`F'` be frames of norms `-T` and `-T'` for the form `J` of signature `(p, q)`, with `q ≤ n + 1`
and `T ≥ 0`, and let `x ∈ U(p, q)`. With `Z` the matrix of the products `⟨F_a, x F'_b⟩` and `D`
its leading principal minor of order `n`, `T T' |D|² ≤ |det Z|²`. -/
theorem mul_mul_norm_det_submatrix_castSucc_sq_le_of_frame (hq : Fintype.card q ≤ n + 1)
    (hT : 0 ≤ T)
    {x : GL (p ⊕ q) 𝕜} (hx : x ∈ indefiniteUnitaryGroup p q 𝕜)
    (hF : Fᴴ * indefiniteDiagonal p q 𝕜 * F = single (last n) (last n) (-(T : 𝕜)))
    (hF' : F'ᴴ * indefiniteDiagonal p q 𝕜 * F' = single (last n) (last n) (-(T' : 𝕜))) :
    T * T' *
        ‖((Fᴴ * indefiniteDiagonal p q 𝕜 * (x.val * F')).submatrix castSucc castSucc).det‖ ^ 2 ≤
      ‖(Fᴴ * indefiniteDiagonal p q 𝕜 * (x.val * F')).det‖ ^ 2 :=
  _root_.Matrix.mul_mul_norm_det_submatrix_castSucc_sq_le_of_frame hq hT hF (by
    rw [conjTranspose_mul_mul_mul_of_star_mul_mul_eq (R := 𝕜) (mem_unitaryGroupOf_iff.1 hx), hF'])

end TauCeti.Matrix.indefiniteUnitaryGroup
