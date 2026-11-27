/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import TauCeti.NumberTheory.Height.FamilyOverPairs
import TauCeti.Analysis.InnerProductSpace.Gram.ChangeOfFamily
import TauCeti.Analysis.Matrix.Ultra
import TauCeti.Data.Matrix.Block

/-!
# Prime-adic bounds for scaled Gram determinants

To bound a complex Gram determinant at a prime-adic embedding, one may change the two families
in the inner products independently. The determinant pays for the two changes separately: the
first determinant is measured at the conjugate embedding, and the second at the original one.

For a family completed by auxiliary vectors, scaling just those vectors by `γ` contributes
`‖γ‖ ^ (2 * n)` to the original Gram determinant, where `n` is the number of auxiliary vectors.
A common budget at each prime for the two changes then gives a height bound for the family of
scaled Gram determinants.

## References

* lsernau/grh-lean, commit `72fead102f663d5c7a407964a13dc0cf9d977207`,
  `grh/src/New/Reduction/Lattices/TwistedLattice.lean`
  (`New.TwistedLattice.norm_pow_mul_det_gram_le`, `New.TwistedLattice.heightLe_pow_mul_det_gram`).
-/

public section

open Matrix Finset
open scoped InnerProductSpace

namespace TauCeti.PrimePadicIso

/-- Independent changes that make all mixed pairings integral bound the original Gram
determinant by the product of the inverse determinant budgets. The change on the first
argument of the inner product is measured after complex conjugation. -/
theorem norm_map_det_gram_le_of_norm_inner_sum_smul_le_one
    (ι : PrimePadicIso) {m E : Type*} [Fintype m] [DecidableEq m]
    [SeminormedAddCommGroup E] [InnerProductSpace ℂ E] (x : m → E)
    (U V : Matrix m m ℂ) {a b : ℝ}
    (hU : (ι.prime : ℝ) ^ (-a) ≤ ‖ι.iso (star U.det)‖)
    (hV : (ι.prime : ℝ) ^ (-b) ≤ ‖ι.iso V.det‖)
    (hpair : ∀ i j, ‖ι.iso ⟪∑ k, U i k • x k, ∑ k, V j k • x k⟫_ℂ‖ ≤ 1) :
    ‖ι.iso (Matrix.gram ℂ x).det‖ ≤ (ι.prime : ℝ) ^ (a + b) := by
  let P : Matrix m m ℂ := of fun i j ↦ ⟪∑ k, U i k • x k, ∑ k, V j k • x k⟫_ℂ
  have hdet : P.det = star U.det * (Matrix.gram ℂ x).det * V.det := by
    have hconj : (U.map (starRingEnd ℂ)).det = star U.det :=
      (det_transpose Uᴴ).trans (det_conjTranspose U)
    simp only [P, inner_sum_smul_matrix, det_mul, det_transpose, hconj, Matrix.gram]
  have hnorm : ‖ι.iso P.det‖ ≤ 1 := by
    rw [ι.iso.map_det, RingEquiv.mapMatrix_apply]
    simpa only [prod_const_one] using
      (norm_det_le_prod_of_norm_le (A := P.map ι.iso) (c := fun _ ↦ 1) hpair)
  rw [hdet, map_mul, map_mul, norm_mul, norm_mul, mul_right_comm] at hnorm
  have hp : 0 < (ι.prime : ℝ) := by exact_mod_cast ι.fact_prime.out.pos
  have h : (ι.prime : ℝ) ^ (-(a + b)) * ‖ι.iso (Matrix.gram ℂ x).det‖ ≤ 1 := by
    rw [neg_add, Real.rpow_add hp]
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul hU hV (Real.rpow_nonneg hp.le _) (norm_nonneg _)) (norm_nonneg _)).trans hnorm
  calc
    ‖ι.iso (Matrix.gram ℂ x).det‖ ≤ 1 / (ι.prime : ℝ) ^ (-(a + b)) :=
      (le_div_iff₀ (Real.rpow_pos_of_pos hp _)).2 (by simpa [mul_comm] using h)
    _ = (ι.prime : ℝ) ^ (a + b) := by rw [one_div, Real.rpow_neg hp.le, inv_inv]

/-- If changing the original vectors on the two sides and rescaling each auxiliary vector
by `γ` makes all pairings integral, the norm of the scaled Gram determinant at `ι` is bounded
by `ℓ ^ (a + b)`, where `a` and `b` control the conjugate and ordinary change determinants. -/
theorem norm_map_scaled_det_gram_le (ι : PrimePadicIso) {m n E : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
    (x : m → E) (y : n → E) (γ : ℂ) (U V : Matrix m m ℂ) {a b : ℝ}
    (hU : (ι.prime : ℝ) ^ (-a) ≤ ‖ι.iso (star U.det)‖)
    (hV : (ι.prime : ℝ) ^ (-b) ≤ ‖ι.iso V.det‖)
    (hpair : ∀ i j, ‖ι.iso
      ⟪Sum.elim (fun i ↦ ∑ k, U i k • x k) (fun i ↦ γ • y i) i,
       Sum.elim (fun j ↦ ∑ k, V j k • x k) (fun j ↦ γ • y j) j⟫_ℂ‖ ≤ 1) :
    ‖ι.iso ((↑(‖γ‖ ^ (2 * Fintype.card n)) : ℂ) * (gram ℂ (Sum.elim x y)).det)‖ ≤
      (ι.prime : ℝ) ^ (a + b) := by
  have h := ι.norm_map_det_gram_le_of_norm_inner_sum_smul_le_one
    (Sum.elim x (fun j ↦ γ • y j)) (fromBlocks U 0 0 1) (fromBlocks V 0 0 1)
    (by simpa [det_fromBlocks_zero₂₁] using hU) (by simpa [det_fromBlocks_zero₂₁] using hV)
    (by simpa [sum_smul_fromBlocks_zero₁₂_zero₂₁, Matrix.one_apply, ite_smul] using hpair)
  have hscale := det_gram_smul (Sum.elim (fun _ : m ↦ 1) (fun _ : n ↦ γ)) (Sum.elim x y)
  have hv : (fun i ↦ Sum.elim (fun _ : m ↦ (1 : ℂ)) (fun _ : n ↦ γ) i • Sum.elim x y i) =
      Sum.elim x (fun j ↦ γ • y j) := by
    funext i
    cases i <;> simp
  rw [hv] at hscale
  simpa [hscale, Fintype.prod_sum_type, ← pow_mul] using h

/-- If the changes in a completed family cost at most `h ℓ` on each side at each prime `ℓ`,
then the scaled Gram determinants have height at most twice the total prime-log budget. The
space containing the vectors may vary with the prime-adic embedding. -/
theorem heightLe_scaled_gram_det {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] {E : PrimePadicIso → Type*}
    [∀ ι, SeminormedAddCommGroup (E ι)] [∀ ι, InnerProductSpace ℂ (E ι)]
    (x : ∀ ι, m → E ι) (y : ∀ ι, n → E ι) (γ : PrimePadicIso → ℂ) {h : ℕ → ℝ} {δ : ℝ}
    (hbudget : ∀ S : Finset ℕ, (∀ ℓ ∈ S, ℓ.Prime) → ∑ ℓ ∈ S, h ℓ * Real.log ℓ ≤ δ)
    (hintegral : ∀ ι : PrimePadicIso, ∃ U V : Matrix m m ℂ,
      (ι.prime : ℝ) ^ (-h ι.prime) ≤ ‖ι.iso (star U.det)‖ ∧
      (ι.prime : ℝ) ^ (-h ι.prime) ≤ ‖ι.iso V.det‖ ∧
      ∀ i j, ‖ι.iso
        ⟪Sum.elim (fun i ↦ ∑ k, U i k • x ι k) (fun i ↦ γ ι • y ι i) i,
         Sum.elim (fun j ↦ ∑ k, V j k • x ι k) (fun j ↦ γ ι • y ι j) j⟫_ℂ‖ ≤ 1) :
    HeightLe (fun ι ↦ (↑(‖γ ι‖ ^ (2 * Fintype.card n)) : ℂ) *
      (gram ℂ (Sum.elim (x ι) (y ι))).det) (2 * δ) := by
  refine HeightLe.of_mul_le (H := 1) one_ne_zero (α := 0) (by simp)
    (fun ℓ ↦ 2 * (h ℓ * Real.log ℓ)) ?_ ?_
  · intro ι
    obtain ⟨U, V, hU, hV, hpair⟩ := hintegral ι
    have hp : 0 < (ι.prime : ℝ) := by exact_mod_cast ι.fact_prime.out.pos
    have hlocal := ι.norm_map_scaled_det_gram_le (x ι) (y ι) (γ ι) U V hU hV hpair
    have hexp : (ι.prime : ℝ) ^ (h ι.prime + h ι.prime) =
        Real.exp (2 * (h ι.prime * Real.log ι.prime)) := by
      rw [Real.rpow_def_of_pos hp]
      congr 1
      ring
    simpa only [one_mul, hexp] using hlocal
  · intro S hS
    rw [zero_add, ← mul_sum]
    exact mul_le_mul_of_nonneg_left (hbudget S hS) (by norm_num)

end TauCeti.PrimePadicIso
