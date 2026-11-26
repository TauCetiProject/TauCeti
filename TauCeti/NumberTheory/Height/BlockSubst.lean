/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.Matrix
public import TauCeti.NumberTheory.Height.MvPolynomial
public import TauCeti.RingTheory.MvPolynomial.Abv.LinearSubst

/-!
# Projective coefficient heights under linear and block-linear substitutions

Over a field `K` with admissible absolute values, applying `MvPolynomial.linearSubst M` to a
homogeneous polynomial `p` of degree `n` multiplies the local sup norm at each archimedean place by
at most `(card σ ^ 2 * max_{i, j} v (M i j)) ^ n` and at each nonarchimedean place by at most
`(max_{i, j} v (M i j)) ^ n`. Combining the `n`-th power of the matrix entry tuple with the nonzero
coefficient tuple of `p` via `MvPolynomial.mulHeight_le_of_abv_coeff_le` gives
`H(linearSubst M p) ≤ ((card σ ^ 2) ^ n) ^ totalWeight K * H(M) ^ n * H(p)`.

For a multihomogeneous polynomial `P` of multidegree `d : κ → ℕ` under `MvPolynomial.blockSubst A`,
each variable expands within its own block of size `card ι`, so the archimedean factor depends on
`card ι` rather than on `card (κ × ι)`:
`H(blockSubst A P) ≤ ((card ι ^ 2) ^ ∑ h, d h) ^ totalWeight K * H(A) ^ (∑ h, d h) * H(P)`.
Composing with `MvPolynomial.mulHeight_hasseDeriv_le` bounds the projective height of
`blockSubst A (hasseDeriv I P)` uniformly in the derivative order `I`, with archimedean constant
`(2 * card ι ^ 2) ^ ∑ h, d h`.

The multiplicative bounds require the variable block to be nonempty (`0 ^ 1 = 0 < 1 = H(0)` over
`ℚ` when `σ = Fin 0`), whereas the logarithmic bounds hold unconditionally since `Real.log 0 = 0`
and every polynomial in zero variables is constant of logarithmic height zero.

## Main results

* `MvPolynomial.mulHeight_linearSubst_le` and `MvPolynomial.logHeight_linearSubst_le`: height of a
  homogeneous polynomial under `linearSubst`.
* `MvPolynomial.mulHeight_blockSubst_le` and `MvPolynomial.logHeight_blockSubst_le`: height of a
  multihomogeneous polynomial under `blockSubst`.
* `MvPolynomial.mulHeight_blockSubst_hasseDeriv_le` and
  `MvPolynomial.logHeight_blockSubst_hasseDeriv_le`: height of a Hasse derivative of a
  multihomogeneous polynomial under `blockSubst`, uniform in the derivative order.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  Lemma 1.6.11 and Lemma 7.5.15.
-/

public section

namespace MvPolynomial

open Finset Height AdmissibleAbsValues

section General

variable {K σ κ ι : Type*} [Field K] [AdmissibleAbsValues K]

private theorem logHeight_le_of_mulHeight_matrix_le [Fintype ι]
    {P : MvPolynomial σ K} {Q : MvPolynomial τ K} (hEmpty : IsEmpty ι → IsEmpty τ)
    (A : Matrix ι ι K) {D : ℕ} {a : ℝ} (ha : 1 ≤ a)
    (hmul : Nonempty ι →
      Q.mulHeight ≤ ((a * Fintype.card ι ^ 2) ^ D) ^ totalWeight K *
        A.mulHeight ^ D * P.mulHeight) :
    Q.logHeight ≤
      P.logHeight + D * A.logHeight +
        totalWeight K * D * Real.log (a * Fintype.card ι ^ 2) := by
  have h := logHeight_le_of_mulHeight_le (x := fun q : ι × ι ↦ A q.1 q.2)
    (c := a * (Fintype.card ι : ℝ) ^ 2)
    (fun h ↦ hEmpty ((isEmpty_prod.mp h).elim id id))
    (fun ⟨q⟩ ↦ have : Nonempty ι := ⟨q.1⟩; by positivity)
    (fun h ↦ have : IsEmpty ι := (isEmpty_prod.mp h).elim id id; by simp)
    (fun ⟨q⟩ ↦ by simpa only [← Matrix.mulHeight_def] using hmul ⟨q.1⟩)
  simpa only [← Matrix.logHeight_def] using h

/-- **The multiplicative height of a homogeneous polynomial under `linearSubst`.** For a
homogeneous polynomial `p` of degree `n` in a nonempty finite variable type `σ`,
`H(linearSubst M p) ≤ ((card σ ^ 2) ^ n) ^ totalWeight K * H(M) ^ n * H(p)`. -/
theorem mulHeight_linearSubst_le [Fintype σ] [Nonempty σ] {p : MvPolynomial σ K} {n : ℕ}
    (hp : p.IsHomogeneous n) (M : Matrix σ σ K) :
    (linearSubst M p).mulHeight ≤
      ((Fintype.card σ ^ 2 : ℝ) ^ n) ^ totalWeight K * M.mulHeight ^ n * p.mulHeight := by
  have hc : (1 : ℝ) ≤ (Fintype.card σ ^ 2 : ℝ) := by
    exact_mod_cast Nat.pow_le_pow_left Fintype.card_pos 2
  rw [Matrix.mulHeight_def]
  exact mulHeight_le_of_abv_coeff_le hc (fun hp0 ↦ by rw [hp0, map_zero])
    (fun hM0 hn ↦ by
      have hM : M = 0 := Matrix.ext fun i j ↦ congrFun hM0 (i, j)
      rw [hM, linearSubst_zero, hp.coeff_eq_zero (by simpa using hn.symm), map_zero])
    (fun v _ {B C} hMB hpC t ↦ by
      simpa only [Nat.cast_pow] using
        abv_coeff_linearSubst_le_of_isHomogeneous hp (fun i j ↦ hMB (i, j)) hpC t)
    (fun v hv {B C} hB0 hMB hpC t ↦
      abv_coeff_linearSubst_le_of_isHomogeneous_of_isNonarchimedean
        (isNonarchimedean v hv) hp hB0 (fun i j ↦ hMB (i, j)) hpC t)

/-- **The logarithmic height of a homogeneous polynomial under `linearSubst`:**
`h(linearSubst M p) ≤ h(p) + n h(M) + 2 * totalWeight K * n * log (card σ)`. -/
theorem logHeight_linearSubst_le [Fintype σ] {p : MvPolynomial σ K} {n : ℕ}
    (hp : p.IsHomogeneous n) (M : Matrix σ σ K) :
    (linearSubst M p).logHeight ≤
      p.logHeight + n * M.logHeight + 2 * totalWeight K * n * Real.log (Fintype.card σ) :=
  (logHeight_le_of_mulHeight_matrix_le id M (a := 1) le_rfl
    fun _ ↦ by simpa only [one_mul] using mulHeight_linearSubst_le hp M).trans_eq
    (by rw [one_mul, Real.log_pow, Nat.cast_ofNat]; ring)

/-- **The multiplicative height of a multihomogeneous polynomial under `blockSubst`.** For a
multihomogeneous polynomial `P` of multidegree `d` over a nonempty block variable type `ι`,
`H(blockSubst A P) ≤ ((card ι ^ 2) ^ ∑ h, d h) ^ totalWeight K * H(A) ^ (∑ h, d h) * H(P)`. -/
theorem mulHeight_blockSubst_le [Fintype κ] [DecidableEq κ] [Fintype ι] [Nonempty ι]
    {P : MvPolynomial (κ × ι) K} {d : κ → ℕ} (hP : IsMultiHomogeneous d P) (A : Matrix ι ι K) :
    (blockSubst A P).mulHeight ≤
      ((Fintype.card ι ^ 2 : ℝ) ^ ∑ h, d h) ^ totalWeight K *
        A.mulHeight ^ (∑ h, d h) * P.mulHeight := by
  have hc : (1 : ℝ) ≤ (Fintype.card ι ^ 2 : ℝ) := by
    exact_mod_cast Nat.pow_le_pow_left Fintype.card_pos 2
  rw [Matrix.mulHeight_def]
  exact mulHeight_le_of_abv_coeff_le hc (fun hP0 ↦ by rw [hP0, map_zero])
    (fun hA0 hD ↦ by
      have hA : A = 0 := Matrix.ext fun i j ↦ congrFun hA0 (i, j)
      rw [hA, blockSubst_zero, hP.isHomogeneous.coeff_eq_zero (by simpa using hD.symm), map_zero])
    (fun v _ {B C} hAB hPC t ↦ by
      simpa only [Nat.cast_pow] using
        abv_coeff_blockSubst_le_of_isMultiHomogeneous hP (fun i j ↦ hAB (i, j)) hPC t)
    (fun v hv {B C} hB0 hAB hPC t ↦
      abv_coeff_blockSubst_le_of_isHomogeneous_of_isNonarchimedean
        (isNonarchimedean v hv) hP.isHomogeneous hB0 (fun i j ↦ hAB (i, j)) hPC t)

/-- **The logarithmic height of a multihomogeneous polynomial under `blockSubst`:**
`h(blockSubst A P) ≤ h(P) + (∑ h, d h) h(A) + 2 * totalWeight K * (∑ h, d h) * log (card ι)`. -/
theorem logHeight_blockSubst_le [Fintype κ] [DecidableEq κ] [Fintype ι]
    {P : MvPolynomial (κ × ι) K} {d : κ → ℕ} (hP : IsMultiHomogeneous d P) (A : Matrix ι ι K) :
    (blockSubst A P).logHeight ≤
      P.logHeight + (∑ h, d h) * A.logHeight +
        2 * totalWeight K * (∑ h, d h) * Real.log (Fintype.card ι) :=
  (logHeight_le_of_mulHeight_matrix_le (@Prod.isEmpty_right _ _) A (a := 1) le_rfl
    fun _ ↦ by simpa only [one_mul] using mulHeight_blockSubst_le hP A).trans_eq
    (by rw [one_mul, Real.log_pow, Nat.cast_ofNat]; ring)

/-- **The multiplicative height of a Hasse derivative under `blockSubst`.** For a multihomogeneous
polynomial `P` of multidegree `d` over a nonempty block variable type `ι` and any derivative order
`I`, `H(blockSubst A (∂^I P))` is at most
`((2 * card ι ^ 2) ^ ∑ h, d h) ^ totalWeight K * H(A) ^ (∑ h, d h) * H(P)`. -/
theorem mulHeight_blockSubst_hasseDeriv_le [Fintype κ] [DecidableEq κ] [Fintype ι] [Nonempty ι]
    {P : MvPolynomial (κ × ι) K} {d : κ → ℕ} (hP : IsMultiHomogeneous d P)
    (A : Matrix ι ι K) (I : κ × ι →₀ ℕ) :
    (blockSubst A (hasseDeriv I P)).mulHeight ≤
      ((2 * Fintype.card ι ^ 2 : ℝ) ^ ∑ h, d h) ^ totalWeight K *
        A.mulHeight ^ (∑ h, d h) * P.mulHeight := by
  have hD' : (∑ h, (d h - ∑ i, I (h, i))) ≤ ∑ h, d h := sum_le_sum fun h _ ↦ Nat.sub_le _ _
  have hdeg : P.totalDegree ≤ ∑ h, d h := hP.isHomogeneous.totalDegree_le
  have hc1 : (1 : ℝ) ≤ Fintype.card ι ^ 2 := by
    exact_mod_cast Nat.pow_le_pow_left Fintype.card_pos 2
  have h1 : ((Fintype.card ι ^ 2 : ℝ) ^ ∑ h, (d h - ∑ i, I (h, i))) ^ totalWeight K ≤
      ((Fintype.card ι ^ 2 : ℝ) ^ ∑ h, d h) ^ totalWeight K :=
    pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ hc1 hD') _
  have h2 : A.mulHeight ^ (∑ h, (d h - ∑ i, I (h, i))) ≤ A.mulHeight ^ (∑ h, d h) :=
    pow_le_pow_right₀ A.one_le_mulHeight hD'
  have h3 : (hasseDeriv I P).mulHeight ≤
      ((2 : ℝ) ^ ∑ h, d h) ^ totalWeight K * P.mulHeight :=
    (mulHeight_hasseDeriv_le I P).trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (one_le_two : (1 : ℝ) ≤ 2) hdeg) _)
      (mulHeight_pos P).le)
  calc (blockSubst A (hasseDeriv I P)).mulHeight
      ≤ ((Fintype.card ι ^ 2 : ℝ) ^ ∑ h, (d h - ∑ i, I (h, i))) ^ totalWeight K *
          A.mulHeight ^ (∑ h, (d h - ∑ i, I (h, i))) * (hasseDeriv I P).mulHeight :=
        mulHeight_blockSubst_le (hP.hasseDeriv I) A
    _ ≤ ((Fintype.card ι ^ 2 : ℝ) ^ ∑ h, d h) ^ totalWeight K * A.mulHeight ^ (∑ h, d h) *
          (((2 : ℝ) ^ ∑ h, d h) ^ totalWeight K * P.mulHeight) :=
        mul_le_mul (mul_le_mul h1 h2 (pow_pos A.mulHeight_pos _).le (by positivity)) h3
          (mulHeight_pos _).le (mul_nonneg (by positivity) (pow_pos A.mulHeight_pos _).le)
    _ = ((2 * Fintype.card ι ^ 2 : ℝ) ^ ∑ h, d h) ^ totalWeight K *
          A.mulHeight ^ (∑ h, d h) * P.mulHeight := by
        rw [← mul_assoc, mul_right_comm _ (A.mulHeight ^ _), ← mul_pow, ← mul_pow,
          mul_comm (Fintype.card ι ^ 2 : ℝ) 2]

/-- **The logarithmic height of a Hasse derivative under `blockSubst`:** `h(blockSubst A (∂^I P))`
is at most `h(P) + (∑ h, d h) h(A) + totalWeight K * (∑ h, d h) * log (2 * card ι ^ 2)`, uniformly
in the derivative order `I`. -/
theorem logHeight_blockSubst_hasseDeriv_le [Fintype κ] [DecidableEq κ] [Fintype ι]
    {P : MvPolynomial (κ × ι) K} {d : κ → ℕ} (hP : IsMultiHomogeneous d P)
    (A : Matrix ι ι K) (I : κ × ι →₀ ℕ) :
    (blockSubst A (hasseDeriv I P)).logHeight ≤
      P.logHeight + (∑ h, d h) * A.logHeight +
        totalWeight K * (∑ h, d h) * Real.log (2 * Fintype.card ι ^ 2) :=
  logHeight_le_of_mulHeight_matrix_le (@Prod.isEmpty_right _ _) A (a := 2) one_le_two
    fun _ ↦ mulHeight_blockSubst_hasseDeriv_le hP A I

end General

/-- `[Nonempty σ]` cannot be dropped in `mulHeight_linearSubst_le`: over `ℚ` and `σ = Fin 0`, taking
`n = 1` and `p = 0` gives `H(linearSubst 0 0) = 1`, whereas the right-hand side is `0 ^ 1 = 0`. -/
example :
    (0 : MvPolynomial (Fin 0) ℚ).IsHomogeneous 1 ∧
      ¬ (linearSubst (0 : Matrix (Fin 0) (Fin 0) ℚ) 0).mulHeight ≤
        ((Fintype.card (Fin 0) ^ 2 : ℝ) ^ 1) ^ totalWeight ℚ *
          (0 : Matrix (Fin 0) (Fin 0) ℚ).mulHeight ^ 1 *
          (0 : MvPolynomial (Fin 0) ℚ).mulHeight := by
  refine ⟨isHomogeneous_zero _ _ 1, ?_⟩
  simp [NumberField.totalWeight_eq_finrank]

end MvPolynomial
