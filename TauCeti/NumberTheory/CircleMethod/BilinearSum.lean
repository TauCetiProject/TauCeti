/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.CircleMethod.TypeISum
import Mathlib.Data.Nat.Dist

/-!
# Type II sums for additive twists

For `α` close to a reduced fraction, `|α - c / q| ≤ q⁻²` with `gcd(c, q) = 1`, this file proves
the type II (bilinear) bound of the circle method: for all complex coefficients `a`, `b` on `ℕ`,
the sum `∑_{M < m ≤ 2M} ∑_{n ≤ N / m} a(m) b(n) e(αmn)` has absolute value at most

`6 ‖a‖₂ ‖b‖₂ ((N / M + M + N / q + q) log (2Nq))^(1/2)`

(`TauCeti.norm_typeII_le`), where `n ≤ N / m` means `0 < n ≤ ⌊N / m⌋`,
`‖a‖₂² = ∑_{M < m ≤ 2M} |a(m)|²` and `‖b‖₂² = ∑_{0 < n ≤ N / M} |b(n)|²`. Together with the type I
bound `TauCeti.sum_min_inv_distInt_le` it is the input for Vinogradov's bound on exponential
sums over primes, after Vaughan's identity splits `∑ Λ(n) e(nα)` into sums of type I and type II.

The proof is the standard one (Davenport, Chapter 25). Write `T(m) = ∑_{n ≤ N / m} b(n) e(αmn)`.

* Cauchy–Schwarz in `m` bounds the square of the left side by `‖a‖₂² ∑_m |T(m)|²`.
* Expanding `|T(m)|²` and summing over `m` first gives
  `∑_m |T(m)|² = ∑_{n, n'} b(n) conj(b(n')) ∑_m e(mα(n - n'))`, where `m` runs over the integers
  of `(M, 2M]` with `mn ≤ N` and `mn' ≤ N`, an interval of length at most `M`. The geometric-sum
  bound `TauCeti.norm_sum_Ioc_expTwoPiI_le` bounds the inner sum by `min(M, 1 / ‖α(n - n')‖)`.
* With `|b(n) b(n')| ≤ (|b(n)|² + |b(n')|²) / 2` and the symmetry of the weight in `n, n'`,
  `∑_m |T(m)|² ≤ ‖b‖₂² (2M + 2 ∑_{1 ≤ h ≤ N / M} min(M, 1 / ‖hα‖))`, since each value
  `h = |n - n'|` occurs for at most two `n'`.
* For `h ≤ N / M`, `M ≤ N / h`, so the type I bound with `X = N` bounds the last sum by
  `16 (N / q + N / M + q) log (2Nq)`.

As in `TauCeti.norm_sum_expTwoPiI_le`, the minimum `min(M, 1 / ‖x‖)` takes the value `M` when
`‖x‖ = 0`.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., GTM 74, Springer, 2000, Chapter 25.
* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, AMS Colloquium Publications 53, 2004,
  §13.5.
-/

public section

noncomputable section

open Finset

namespace TauCeti

/-- The sum of `e(mα(n - n'))` over the `m ∈ (M, 2M]` with `mn ≤ N` and `mn' ≤ N` is at most
`min(M, 1 / ‖|n - n'| α‖)`, with the value `M` when `‖|n - n'| α‖ = 0`. -/
private theorem norm_sum_filter_Ioc_expTwoPiI_le (M N : ℕ) {n n' : ℕ} (hn : 0 < n) (hn' : 0 < n')
    (α : ℝ) :
    ‖∑ m ∈ Ioc M (2 * M) with m * n ≤ N ∧ m * n' ≤ N,
        expTwoPiI (m * (α * ((n : ℝ) - n')))‖ ≤
      if distInt (Nat.dist n n' * α) = 0 then (M : ℝ)
      else min (M : ℝ) (distInt (Nat.dist n n' * α))⁻¹ := by
  have hI : {m ∈ Ioc M (2 * M) | m * n ≤ N ∧ m * n' ≤ N} =
      Ioc M (min (2 * M) (min (N / n) (N / n'))) := by
    ext m
    simp only [mem_filter, mem_Ioc, le_min_iff, Nat.le_div_iff_mul_le hn,
      Nat.le_div_iff_mul_le hn']
    tauto
  have hdist : distInt (α * ((n : ℝ) - n')) = distInt (Nat.dist n n' * α) := by
    rcases le_total n' n with h | h
    · rw [Nat.dist_eq_sub_of_le_right h, Nat.cast_sub h, mul_comm]
    · rw [Nat.dist_eq_sub_of_le h, Nat.cast_sub h, ← distInt_neg]
      ring_nf
  have hlen : ((min (2 * M) (min (N / n) (N / n')) - M : ℕ) : ℝ) ≤ M := by
    exact_mod_cast (by omega : min (2 * M) (min (N / n) (N / n')) - M ≤ M)
  rw [hI]
  refine (norm_sum_Ioc_expTwoPiI_le _ _ _).trans ?_
  rw [hdist]
  split_ifs with h0
  · exact hlen
  · have hpos : 0 < distInt (Nat.dist n n' * α) := lt_of_le_of_ne (distInt_nonneg _) (Ne.symm h0)
    refine min_le_min hlen ?_
    rw [one_div, mul_inv]
    exact mul_le_of_le_one_left (inv_nonneg.2 hpos.le) (by norm_num)

/-- For `0 < n ≤ H`, the values `|n - n'|` with `0 < n' ≤ H` lie in `[0, H)` and each is taken at
most twice, so `∑_{0 < n' ≤ H} w(|n - n'|) ≤ 2 w(0) + 2 ∑_{1 ≤ h ≤ H} w(h)` for `w ≥ 0`. -/
private theorem sum_Ioc_dist_le {w : ℕ → ℝ} (hw : ∀ k, 0 ≤ w k) {n H : ℕ} (hn : n ∈ Ioc 0 H) :
    ∑ n' ∈ Ioc 0 H, w (Nat.dist n n') ≤ 2 * w 0 + 2 * ∑ k ∈ Icc 1 H, w k := by
  have hmaps : ∀ n' ∈ Ioc 0 H, Nat.dist n n' ∈ insert 0 (Icc 1 H) := by
    intro n' hn'
    simp only [mem_Ioc] at hn hn'
    simp only [mem_insert, mem_Icc, Nat.dist]
    omega
  rw [← sum_fiberwise_of_maps_to hmaps, ← mul_add, ← sum_insert (by simp), mul_sum]
  refine sum_le_sum fun k _ ↦ ?_
  rw [sum_congr rfl fun n' hn' ↦ by rw [(mem_filter.1 hn').2], sum_const, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ (hw k)
  have hcard : {n' ∈ Ioc 0 H | Nat.dist n n' = k}.card ≤ ({n + k, n - k} : Finset ℕ).card :=
    card_le_card fun n' hn' ↦ by
      obtain ⟨-, hk⟩ := mem_filter.1 hn'
      unfold Nat.dist at hk
      simp only [mem_insert, mem_singleton]
      omega
  exact_mod_cast hcard.trans card_le_two

/-- The symmetric weight step: for `w(n, n') = v(|n - n'|)` with `v ≥ 0`,
`∑_{n, n'} x(n) x(n') w(n, n') ≤ ∑_n x(n)² ∑_{n'} w(n, n')`, from
`x(n) x(n') ≤ (x(n)² + x(n')²) / 2`. -/
private theorem sum_sum_mul_mul_dist_le (s : Finset ℕ) (x v : ℕ → ℝ) (hv : ∀ k, 0 ≤ v k) :
    ∑ n ∈ s, ∑ n' ∈ s, x n * x n' * v (Nat.dist n n') ≤
      ∑ n ∈ s, x n ^ 2 * ∑ n' ∈ s, v (Nat.dist n n') := by
  have h : ∀ n n', x n * x n' * v (Nat.dist n n') ≤
      (x n ^ 2 * v (Nat.dist n n') + x n' ^ 2 * v (Nat.dist n' n)) / 2 := fun n n' ↦ by
    rw [Nat.dist_comm n' n]
    nlinarith [mul_nonneg (sq_nonneg (x n - x n')) (hv (Nat.dist n n'))]
  refine (sum_le_sum fun n _ ↦ sum_le_sum fun n' _ ↦ h n n').trans_eq ?_
  simp only [← sum_div, sum_add_distrib, mul_sum]
  rw [sum_comm (f := fun n n' ↦ x n' ^ 2 * v (Nat.dist n' n))]
  ring

/-- For `M ≤ m`, the inner sum over `n ≤ N / m` is the sum over `n ≤ N / M` cut off at
`mn ≤ N`. -/
private theorem sum_Ioc_div_eq_sum_ite (b : ℕ → ℂ) (α : ℝ) {M N m : ℕ} (hM : 0 < M)
    (hMm : M ≤ m) :
    ∑ n ∈ Ioc 0 (N / m), b n * expTwoPiI (α * m * n) =
      ∑ n ∈ Ioc 0 (N / M), if m * n ≤ N then b n * expTwoPiI (α * m * n) else 0 := by
  rw [← sum_filter]
  refine sum_congr ?_ fun _ _ ↦ rfl
  ext n
  simp only [mem_filter, mem_Ioc, Nat.le_div_iff_mul_le (hM.trans_le hMm),
    Nat.le_div_iff_mul_le hM, mul_comm m n]
  exact ⟨fun h ↦ ⟨⟨h.1, (Nat.mul_le_mul_left n hMm).trans h.2⟩, h.2⟩,
    fun h ↦ ⟨h.1.1, h.2⟩⟩

/-- Expanding `|T(m)|²` and summing over `m` first:
`∑_m |T(m)|² = ∑_{n, n'} b(n) conj(b(n')) ∑_{m : mn ≤ N, mn' ≤ N} e(mα(n - n'))`. -/
private theorem ofReal_sum_norm_sq_eq (M N : ℕ) (b : ℕ → ℂ) (α : ℝ) :
    ((∑ m ∈ Ioc M (2 * M), ‖∑ n ∈ Ioc 0 (N / m), b n * expTwoPiI (α * m * n)‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ Ioc 0 (N / M), ∑ n' ∈ Ioc 0 (N / M), b n * (starRingEnd ℂ) (b n') *
        ∑ m ∈ Ioc M (2 * M) with m * n ≤ N ∧ m * n' ≤ N,
          expTwoPiI (m * (α * ((n : ℝ) - n'))) := by
  push_cast
  rw [sum_congr rfl fun m hm ↦ by
    have hm := mem_Ioc.1 hm
    rw [← Complex.mul_conj', sum_Ioc_div_eq_sum_ite b α (by omega : 0 < M) hm.1.le, map_sum,
      sum_mul_sum]]
  rw [sum_comm]
  refine sum_congr rfl fun n _ ↦ ?_
  rw [sum_comm]
  refine sum_congr rfl fun n' _ ↦ ?_
  rw [sum_filter, mul_sum]
  refine sum_congr rfl fun m _ ↦ ?_
  have he : expTwoPiI (m * (α * ((n : ℝ) - n'))) =
      expTwoPiI (α * m * n) * (starRingEnd ℂ) (expTwoPiI (α * m * n')) := by
    rw [conj_expTwoPiI, ← expTwoPiI_add]
    ring_nf
  by_cases h : m * n ≤ N <;> by_cases h' : m * n' ≤ N <;>
    simp only [h, h', and_self, and_false, false_and, ↓reduceIte, map_zero, zero_mul, mul_zero]
  rw [he, map_mul]
  ring

/-- The mean square of the inner sums against the weight `min(M, 1 / ‖hα‖)`: for
`T(m) = ∑_{n ≤ N / m} b(n) e(αmn)`,
`∑_{M < m ≤ 2M} |T(m)|² ≤ ‖b‖₂² (2M + 2 ∑_{1 ≤ h ≤ N / M} min(M, 1 / ‖hα‖))`. -/
private theorem sum_norm_sq_le_mul_sum_ite (M N : ℕ) (b : ℕ → ℂ) (α : ℝ) :
    ∑ m ∈ Ioc M (2 * M), ‖∑ n ∈ Ioc 0 (N / m), b n * expTwoPiI (α * m * n)‖ ^ 2 ≤
      (∑ n ∈ Ioc 0 (N / M), ‖b n‖ ^ 2) *
        (2 * M + 2 * ∑ k ∈ Icc 1 (N / M),
          if distInt (k * α) = 0 then (M : ℝ) else min (M : ℝ) (distInt (k * α))⁻¹) := by
  set w : ℕ → ℝ := fun k ↦
    if distInt (k * α) = 0 then (M : ℝ) else min (M : ℝ) (distInt (k * α))⁻¹ with hw_def
  have hw : ∀ k, 0 ≤ w k := fun k ↦ by
    simp only [hw_def]
    split_ifs
    · positivity
    · exact le_min (by positivity) (inv_nonneg.2 (distInt_nonneg _))
  calc ∑ m ∈ Ioc M (2 * M), ‖∑ n ∈ Ioc 0 (N / m), b n * expTwoPiI (α * m * n)‖ ^ 2
      = ‖((∑ m ∈ Ioc M (2 * M),
          ‖∑ n ∈ Ioc 0 (N / m), b n * expTwoPiI (α * m * n)‖ ^ 2 : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    _ ≤ ∑ n ∈ Ioc 0 (N / M), ∑ n' ∈ Ioc 0 (N / M), ‖b n‖ * ‖b n'‖ * w (Nat.dist n n') := by
        rw [ofReal_sum_norm_sq_eq]
        refine (norm_sum_le _ _).trans (sum_le_sum fun n hn ↦
          (norm_sum_le _ _).trans (sum_le_sum fun n' hn' ↦ ?_))
        rw [norm_mul, norm_mul, Complex.norm_conj]
        gcongr
        exact norm_sum_filter_Ioc_expTwoPiI_le M N (mem_Ioc.1 hn).1 (mem_Ioc.1 hn').1 α
    _ ≤ ∑ n ∈ Ioc 0 (N / M), ‖b n‖ ^ 2 * ∑ n' ∈ Ioc 0 (N / M), w (Nat.dist n n') :=
        sum_sum_mul_mul_dist_le _ _ _ hw
    _ ≤ ∑ n ∈ Ioc 0 (N / M), ‖b n‖ ^ 2 * (2 * w 0 + 2 * ∑ k ∈ Icc 1 (N / M), w k) :=
        sum_le_sum fun n hn ↦ mul_le_mul_of_nonneg_left (sum_Ioc_dist_le hw hn) (sq_nonneg _)
    _ = (∑ n ∈ Ioc 0 (N / M), ‖b n‖ ^ 2) * (2 * M + 2 * ∑ k ∈ Icc 1 (N / M), w k) := by
        rw [← sum_mul]
        simp [hw_def]

/-- For `h ≤ N / M` the cap `M` is at most `N / h`, so the sum of `min(M, 1 / ‖hα‖)` over
`1 ≤ h ≤ N / M` is a type I sum with `X = N`, at most `16 (N / q + N / M + q) log (2Nq)`. -/
private theorem sum_Icc_ite_min_inv_distInt_le {α : ℝ} {c : ℤ} {q : ℕ} (hq : 0 < q)
    (hc : Int.gcd c q = 1) (hα : |α - c / q| ≤ 1 / (q : ℝ) ^ 2) (M N : ℕ) :
    ∑ k ∈ Icc 1 (N / M),
        (if distInt (k * α) = 0 then (M : ℝ) else min (M : ℝ) (distInt (k * α))⁻¹) ≤
      16 * ((N : ℝ) / q + N / M + q) * Real.log (2 * N * q) := by
  rcases Nat.eq_zero_or_pos (N / M) with hH | hH
  · rw [hH, Icc_eq_empty_of_lt one_pos, sum_empty]
    exact mul_nonneg (by positivity) (by exact_mod_cast Real.log_natCast_nonneg (2 * N * q))
  have hM : 0 < M := Nat.pos_of_ne_zero fun h ↦ by simp [h] at hH
  have hlog0 : 0 ≤ Real.log (2 * (N / M : ℕ) * q) := Real.log_nonneg (by
    have : (1 : ℝ) ≤ (N / M : ℕ) * q :=
      one_le_mul_of_one_le_of_one_le (by exact_mod_cast hH) (by exact_mod_cast hq)
    linarith)
  calc ∑ k ∈ Icc 1 (N / M),
        (if distInt (k * α) = 0 then (M : ℝ) else min (M : ℝ) (distInt (k * α))⁻¹)
      ≤ ∑ k ∈ Icc 1 (N / M),
        (if distInt (k * α) = 0 then (N : ℝ) / k else min ((N : ℝ) / k) (distInt (k * α))⁻¹) :=
        sum_le_sum fun k hk ↦ ite_min_inv_distInt_le_of_le (by
          have hk := mem_Icc.1 hk
          rw [le_div_iff₀ (by exact_mod_cast hk.1), mul_comm]
          exact_mod_cast (Nat.le_div_iff_mul_le hM).1 hk.2)
    _ ≤ 16 * ((N : ℝ) / q + (N / M : ℕ) + q) * Real.log (2 * (N / M : ℕ) * q) :=
        sum_min_inv_distInt_le hq hc hα (N / M) (Nat.cast_nonneg N)
    _ ≤ 16 * ((N : ℝ) / q + N / M + q) * Real.log (2 * N * q) := by
        have hHN : ((N / M : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.div_le_self N M
        gcongr
        exact Nat.cast_div_le

/-- **The mean-square bound** dual to the type II bound: for `α` as in `norm_typeII_le` and
`T(m) = ∑_{n ≤ N / m} b(n) e(αmn)`,
`∑_{M < m ≤ 2M} |T(m)|² ≤ 36 ‖b‖₂² (N / M + M + N / q + q) log (2Nq)`. -/
private theorem sum_norm_sq_sum_expTwoPiI_le {α : ℝ} {c : ℤ} {q : ℕ} (hq : 0 < q)
    (hc : Int.gcd c q = 1) (hα : |α - c / q| ≤ 1 / (q : ℝ) ^ 2) (M : ℕ) {N : ℕ} (hN : 0 < N)
    (b : ℕ → ℂ) :
    ∑ m ∈ Ioc M (2 * M), ‖∑ n ∈ Ioc 0 (N / m), b n * expTwoPiI (α * m * n)‖ ^ 2 ≤
      36 * (∑ n ∈ Ioc 0 (N / M), ‖b n‖ ^ 2) *
        (((N : ℝ) / M + M + (N : ℝ) / q + q) * Real.log (2 * N * q)) := by
  have hL : 1 / 2 ≤ Real.log (2 * N * q) := by
    have h2 : (2 : ℝ) ≤ 2 * N * q := by
      have : (1 : ℝ) ≤ N * q :=
        one_le_mul_of_one_le_of_one_le (by exact_mod_cast hN) (by exact_mod_cast hq)
      linarith
    linarith [Real.log_le_log (by norm_num) h2,
      Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)]
  refine (sum_norm_sq_le_mul_sum_ite M N b α).trans ?_
  rw [mul_comm 36, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hI := sum_Icc_ite_min_inv_distInt_le hq hc hα M N
  have hP : 0 ≤ (N : ℝ) / q + N / M + q := by positivity
  nlinarith [mul_nonneg hP (by linarith : (0 : ℝ) ≤ Real.log (2 * N * q)),
    mul_nonneg (Nat.cast_nonneg M : (0 : ℝ) ≤ M)
      (by linarith : (0 : ℝ) ≤ 36 * Real.log (2 * N * q) - 2)]

/-- **The type II bound** for additive twists. If `|α - c / q| ≤ q⁻²` with `gcd(c, q) = 1`, then
for all complex coefficients `a`, `b` and natural numbers `M`, `N`,
`|∑_{M < m ≤ 2M} ∑_{n ≤ N / m} a(m) b(n) e(αmn)|` is at most
`6 ‖a‖₂ ‖b‖₂ ((N / M + M + N / q + q) log (2Nq))^(1/2)`, where
`‖a‖₂² = ∑_{M < m ≤ 2M} |a(m)|²` and `‖b‖₂² = ∑_{0 < n ≤ N / M} |b(n)|²`. -/
theorem norm_typeII_le {α : ℝ} {c : ℤ} {q : ℕ} (hq : 0 < q) (hc : Int.gcd c q = 1)
    (hα : |α - c / q| ≤ 1 / (q : ℝ) ^ 2) (M N : ℕ) (a b : ℕ → ℂ) :
    ‖∑ m ∈ Ioc M (2 * M), ∑ n ∈ Ioc 0 (N / m), a m * b n * expTwoPiI (α * m * n)‖ ≤
      6 * √(∑ m ∈ Ioc M (2 * M), ‖a m‖ ^ 2) * √(∑ n ∈ Ioc 0 (N / M), ‖b n‖ ^ 2) *
        √(((N : ℝ) / M + M + (N : ℝ) / q + q) * Real.log (2 * N * q)) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  set A := ∑ m ∈ Ioc M (2 * M), ‖a m‖ ^ 2
  set B := ∑ n ∈ Ioc 0 (N / M), ‖b n‖ ^ 2
  set KL := ((N : ℝ) / M + M + (N : ℝ) / q + q) * Real.log (2 * N * q)
  set T : ℕ → ℂ := fun m ↦ ∑ n ∈ Ioc 0 (N / m), b n * expTwoPiI (α * m * n)
  have hA : 0 ≤ A := by positivity
  have hB : 0 ≤ B := by positivity
  -- Cauchy–Schwarz in `m`, then the mean-square bound.
  have hS : ‖∑ m ∈ Ioc M (2 * M), ∑ n ∈ Ioc 0 (N / m), a m * b n * expTwoPiI (α * m * n)‖ ≤
      ∑ m ∈ Ioc M (2 * M), ‖a m‖ * ‖T m‖ := by
    refine (norm_sum_le _ _).trans_eq (sum_congr rfl fun m _ ↦ ?_)
    simp only [T, mul_assoc, ← mul_sum, norm_mul]
  have hsq : 6 * √A * √B * √KL = √(36 * A * B * KL) := by
    have h36 : √(36 : ℝ) = 6 := by
      rw [show (36 : ℝ) = 6 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [Real.sqrt_mul (mul_nonneg (mul_nonneg (by norm_num) hA) hB) KL,
      Real.sqrt_mul (mul_nonneg (by norm_num) hA) B, Real.sqrt_mul (by norm_num) A, h36]
  rw [hsq]
  refine hS.trans ((le_abs_self _).trans (Real.abs_le_sqrt ?_))
  calc (∑ m ∈ Ioc M (2 * M), ‖a m‖ * ‖T m‖) ^ 2 ≤ A * ∑ m ∈ Ioc M (2 * M), ‖T m‖ ^ 2 :=
        sum_mul_sq_le_sq_mul_sq _ _ _
    _ ≤ A * (36 * B * KL) :=
        mul_le_mul_of_nonneg_left (sum_norm_sq_sum_expTwoPiI_le hq hc hα M hN b) hA
    _ = 36 * A * B * KL := by ring

/-! ### Checks -/

/-- For `M = N` the inner sums over `n ≤ N / m` with `m > N` are empty, and the type II sum
is `0`. -/
example (N : ℕ) (a b : ℕ → ℂ) (α : ℝ) :
    ∑ m ∈ Ioc N (2 * N), ∑ n ∈ Ioc 0 (N / m), a m * b n * expTwoPiI (α * m * n) = 0 :=
  sum_eq_zero fun m hm ↦ by
    rw [Nat.div_eq_of_lt (mem_Ioc.1 hm).1, Ioc_self, sum_empty]

end TauCeti
