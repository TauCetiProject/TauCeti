/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.Matrix
public import TauCeti.NumberTheory.Height.MvPolynomial
public import TauCeti.RingTheory.MvPolynomial.Abv.LinearSubst
import TauCeti.NumberTheory.Height.Basic

/-!
# Projective coefficient heights under linear and block-linear substitutions

Over a field `K` with admissible absolute values, applying `MvPolynomial.linearSubst M` to a
homogeneous polynomial `p` of degree `n` multiplies the local sup norm at each archimedean place by
at most `(card σ ^ 2 * max_{i, j} v (M i j)) ^ n` and at each nonarchimedean place by at most
`(max_{i, j} v (M i j)) ^ n`. Combining the `n`-th power of the matrix entry tuple with the nonzero
coefficient tuple of `p` via the Segre multiplication table `Height.mulHeight_fun_mul_eq` gives
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

variable {K σ τ κ ι : Type*} [Field K] [AdmissibleAbsValues K]

private lemma mulHeight_le_of_abv_coeff_le [Finite ι] [Nonempty ι] {A : Matrix ι ι K}
    {P : MvPolynomial σ K} {Q : MvPolynomial τ K} {D k : ℕ} (hk : 1 ≤ k)
    (h0P : P = 0 → Q = 0) (h0A : A = 0 → D ≠ 0 → Q = 0)
    (harch : ∀ (v : AbsoluteValue K ℝ) {B C : ℝ}, (∀ i j, v (A i j) ≤ B) →
      (∀ a, v (P.coeff a) ≤ C) → ∀ t, v (Q.coeff t) ≤ (k * B) ^ D * C)
    (hnon : ∀ (v : AbsoluteValue K ℝ), IsNonarchimedean v → ∀ {B C : ℝ}, 0 ≤ B →
      (∀ i j, v (A i j) ≤ B) → (∀ a, v (P.coeff a) ≤ C) → ∀ t, v (Q.coeff t) ≤ B ^ D * C) :
    Q.mulHeight ≤ ((k : ℝ) ^ D) ^ totalWeight K * A.mulHeight ^ D * P.mulHeight := by
  cases nonempty_fintype ι
  have hC : (1 : ℝ) ≤ (k : ℝ) ^ D := one_le_pow₀ (by exact_mod_cast hk)
  rcases eq_or_ne P 0 with rfl | hP0
  · rw [h0P rfl, MvPolynomial.mulHeight_zero, MvPolynomial.mulHeight_zero, mul_one]
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hC) (one_le_pow₀ A.one_le_mulHeight)
  by_cases hAD : A = 0 ∧ D ≠ 0
  · rw [h0A hAD.1 hAD.2, MvPolynomial.mulHeight_zero]
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hC)
      (one_le_pow₀ A.one_le_mulHeight)) P.one_le_mulHeight
  let y : ι × ι → K := fun q ↦ A q.1 q.2
  let x : P.support → K := fun c ↦ P.coeff c
  obtain ⟨c₁, hc₁⟩ := support_nonempty.mpr hP0
  have hx : x ≠ 0 := Function.ne_iff.mpr ⟨⟨c₁, hc₁⟩, mem_support_iff.mp hc₁⟩
  have hyD : y ^ D ≠ 0 := by
    rcases eq_or_ne D 0 with rfl | hD
    · exact Function.ne_iff.mpr ⟨(Classical.arbitrary ι, Classical.arbitrary ι), by simp⟩
    · obtain ⟨i, j, hij⟩ : ∃ i j, A i j ≠ 0 := by contrapose! hAD; exact ⟨Matrix.ext hAD, hD⟩
      exact Function.ne_iff.mpr ⟨(i, j), pow_ne_zero D hij⟩
  let w : (ι × ι) × P.support → K := fun a ↦ (y ^ D) a.1 * x a.2
  have hwH : Height.mulHeight w = A.mulHeight ^ D * P.mulHeight := by
    rw [Height.mulHeight_fun_mul_eq hyD hx, Height.mulHeight_pow, ← Matrix.mulHeight_def,
      ← mulHeight_eq_support]
  have hlocal (v : AbsoluteValue K ℝ) : ∃ B C, 0 ≤ B ∧ (∀ i j, v (A i j) ≤ B) ∧
      (∀ a, v (P.coeff a) ≤ C) ∧ B ^ D * C ≤ ⨆ a, v (w a) := by
    obtain ⟨q₀, -, hqmax⟩ := exists_max_image univ (fun q : ι × ι ↦ v (y q)) univ_nonempty
    obtain ⟨c₀, hc₀, hcmax⟩ := exists_max_image P.support (v ∘ P.coeff) (support_nonempty.mpr hP0)
    refine ⟨v (y q₀), v (P.coeff c₀), v.nonneg _, fun i j ↦ hqmax (i, j) (mem_univ _),
      fun a ↦ by
        by_cases ha : a ∈ P.support
        · exact hcmax a ha
        · rw [notMem_support_iff.mp ha, map_zero]; exact v.nonneg _,
      (by simp [w, x, Pi.pow_apply] : v (y q₀) ^ D * v (P.coeff c₀) = v (w (q₀, ⟨c₀, hc₀⟩))) ▸
        Finite.le_ciSup_of_le (q₀, ⟨c₀, hc₀⟩) le_rfl⟩
  have hw0 (v : AbsoluteValue K ℝ) : 0 ≤ ⨆ a, v (w a) := Real.iSup_nonneg fun _ ↦ v.nonneg _
  rw [mul_assoc, ← hwH, mulHeight_eq_support]
  refine (Height.mulHeight_le_of_forall_iSup_le w _ hC (p := 1)
    (fun v _ ↦ Real.iSup_le (fun t ↦ ?_) (mul_nonneg (zero_le_one.trans hC) (by simpa using hw0 v)))
    fun v hv ↦ Real.iSup_le (fun t ↦ ?_) (by simpa using hw0 v)).trans_eq (by rw [pow_one])
  · obtain ⟨B, C, -, hAB, hPC, hBC⟩ := hlocal v
    rw [pow_one]
    exact (harch v hAB hPC t.val).trans
      ((by rw [mul_pow, mul_assoc] : (k * B : ℝ) ^ D * C = (k : ℝ) ^ D * (B ^ D * C)).trans_le
        (mul_le_mul_of_nonneg_left hBC (zero_le_one.trans hC)))
  · obtain ⟨B, C, hB0, hAB, hPC, hBC⟩ := hlocal v
    simpa only [pow_one] using (hnon v (isNonarchimedean v hv) hB0 hAB hPC t.val).trans hBC

private lemma logHeight_le_of_mulHeight_le [Finite ι] {A : Matrix ι ι K}
    {P : MvPolynomial σ K} {Q : MvPolynomial τ K} {D : ℕ} {c : ℝ}
    (hEmpty : IsEmpty ι → IsEmpty τ) (hc_pos : Nonempty ι → 0 < c) (hc_zero : IsEmpty ι → c = 0)
    (hmul : Nonempty ι → Q.mulHeight ≤ (c ^ D) ^ totalWeight K * A.mulHeight ^ D * P.mulHeight) :
    Q.logHeight ≤ P.logHeight + D * A.logHeight + totalWeight K * D * Real.log c := by
  by_cases hι : Nonempty ι
  · have hc : 0 < c := hc_pos hι
    have hApos : 0 < A.mulHeight ^ D := pow_pos A.mulHeight_pos D
    have h := Real.log_le_log (mulHeight_pos Q) (hmul hι)
    rw [Real.log_mul (mul_pos (by positivity) hApos).ne' (mulHeight_pos P).ne',
      Real.log_mul (by positivity) hApos.ne', Real.log_pow, Real.log_pow,
      Real.log_pow A.mulHeight] at h
    rw [logHeight_eq_log_mulHeight, logHeight_eq_log_mulHeight, Matrix.logHeight_eq_log_mulHeight]
    linarith
  · have : IsEmpty ι := not_nonempty_iff.mp hι
    have : IsEmpty τ := hEmpty ‹_›
    simp [hc_zero ‹_›, P.logHeight_nonneg]

/-- **The multiplicative height of a homogeneous polynomial under `linearSubst`.** For a
homogeneous polynomial `p` of degree `n` in a nonempty finite variable type `σ`,
`H(linearSubst M p) ≤ ((card σ ^ 2) ^ n) ^ totalWeight K * H(M) ^ n * H(p)`. -/
theorem mulHeight_linearSubst_le [Fintype σ] [Nonempty σ] {p : MvPolynomial σ K} {n : ℕ}
    (hp : p.IsHomogeneous n) (M : Matrix σ σ K) :
    (linearSubst M p).mulHeight ≤
      ((Fintype.card σ ^ 2 : ℝ) ^ n) ^ totalWeight K * M.mulHeight ^ n * p.mulHeight := by
  have hk : 1 ≤ Fintype.card σ ^ 2 := Nat.pow_le_pow_left Fintype.card_pos 2
  refine (mulHeight_le_of_abv_coeff_le hk (fun hp0 ↦ by rw [hp0, map_zero])
    (fun hM0 hn ↦ by
      rw [hM0, linearSubst_zero, hp.coeff_eq_zero (by simpa using hn.symm), map_zero])
    (fun v {B C} hMB hpC t ↦ by
      simpa only [Nat.cast_pow] using abv_coeff_linearSubst_le_of_isHomogeneous hp hMB hpC t)
    (fun v hv {B C} hB0 hMB hpC t ↦
      abv_coeff_linearSubst_le_of_isHomogeneous_of_isNonarchimedean hv hp hB0 hMB hpC t)).trans_eq
    (by norm_cast)

/-- **The logarithmic height of a homogeneous polynomial under `linearSubst`:**
`h(linearSubst M p) ≤ h(p) + n h(M) + 2 * totalWeight K * n * log (card σ)`. -/
theorem logHeight_linearSubst_le [Fintype σ] {p : MvPolynomial σ K} {n : ℕ}
    (hp : p.IsHomogeneous n) (M : Matrix σ σ K) :
    (linearSubst M p).logHeight ≤
      p.logHeight + n * M.logHeight + 2 * totalWeight K * n * Real.log (Fintype.card σ) := by
  have h := logHeight_le_of_mulHeight_le id
    (fun h ↦ by have := @Fintype.card_pos σ _ h; positivity) (fun _ ↦ by simp)
    fun _ ↦ mulHeight_linearSubst_le hp M
  simp only [Real.log_pow, Nat.cast_ofNat] at h
  linarith

/-- **The multiplicative height of a multihomogeneous polynomial under `blockSubst`.** For a
multihomogeneous polynomial `P` of multidegree `d` over a nonempty block variable type `ι`,
`H(blockSubst A P) ≤ ((card ι ^ 2) ^ ∑ h, d h) ^ totalWeight K * H(A) ^ (∑ h, d h) * H(P)`. -/
theorem mulHeight_blockSubst_le [Fintype κ] [DecidableEq κ] [Fintype ι] [Nonempty ι]
    {P : MvPolynomial (κ × ι) K} {d : κ → ℕ} (hP : IsMultiHomogeneous d P) (A : Matrix ι ι K) :
    (blockSubst A P).mulHeight ≤
      ((Fintype.card ι ^ 2 : ℝ) ^ ∑ h, d h) ^ totalWeight K *
        A.mulHeight ^ (∑ h, d h) * P.mulHeight := by
  have hk : 1 ≤ Fintype.card ι ^ 2 := Nat.pow_le_pow_left Fintype.card_pos 2
  refine (mulHeight_le_of_abv_coeff_le hk (fun hP0 ↦ by rw [hP0, map_zero])
    (fun hA0 hD ↦ by
      rw [hA0, blockSubst_zero, hP.isHomogeneous.coeff_eq_zero (by simpa using hD.symm), map_zero])
    (fun v {B C} hAB hPC t ↦ by
      simpa only [Nat.cast_pow] using abv_coeff_blockSubst_le_of_isMultiHomogeneous hP hAB hPC t)
    (fun v hv {B C} hB0 hAB hPC t ↦
      abv_coeff_blockSubst_le_of_isHomogeneous_of_isNonarchimedean
        hv hP.isHomogeneous hB0 hAB hPC t)).trans_eq (by norm_cast)

/-- **The logarithmic height of a multihomogeneous polynomial under `blockSubst`:**
`h(blockSubst A P) ≤ h(P) + (∑ h, d h) h(A) + 2 * totalWeight K * (∑ h, d h) * log (card ι)`. -/
theorem logHeight_blockSubst_le [Fintype κ] [DecidableEq κ] [Fintype ι]
    {P : MvPolynomial (κ × ι) K} {d : κ → ℕ} (hP : IsMultiHomogeneous d P) (A : Matrix ι ι K) :
    (blockSubst A P).logHeight ≤
      P.logHeight + (∑ h, d h) * A.logHeight +
        2 * totalWeight K * (∑ h, d h) * Real.log (Fintype.card ι) := by
  have h := logHeight_le_of_mulHeight_le (fun _ ↦ inferInstance)
    (fun h ↦ by have := @Fintype.card_pos ι _ h; positivity) (fun _ ↦ by simp)
    fun _ ↦ mulHeight_blockSubst_le hP A
  simp only [Real.log_pow, Nat.cast_ofNat] at h
  linarith

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
  logHeight_le_of_mulHeight_le (fun _ ↦ inferInstance)
    (fun h ↦ by have := @Fintype.card_pos ι _ h; positivity) (fun _ ↦ by simp)
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
