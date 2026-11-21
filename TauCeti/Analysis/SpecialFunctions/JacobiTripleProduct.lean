/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.QPochhammer
import TauCeti.Data.Int.MulPred

/-!
# Jacobi's triple product identity

For `‖q‖ < 1` and `w ≠ 0` in a complete normed field, **Jacobi's triple product identity** is
`(w; q)_∞ (q / w; q)_∞ (q; q)_∞ = ∑_{k ∈ ℤ} (-1)ᵏ q^{k(k-1)/2} wᵏ`,
where `(x; q)_∞ = ∏_{n ≥ 0} (1 - x qⁿ)`. In terms of the theta product
`θ_q(w) = (w; q)_∞ (q / w; q)_∞` (`TauCeti.qTheta`) and the Euler function
`∏_{n ≥ 1} (1 - qⁿ) = (q; q)_∞`, it reads
`θ_q(w) ∏_{n ≥ 1} (1 - qⁿ) = ∑_{k ∈ ℤ} (-1)ᵏ q^{k(k-1)/2} wᵏ`.
With `q = e^{2π i τ}` it is the source of the product formulas of the Jacobi theta functions.

The proof is Andrews' derivation from Euler's two expansions
`(z; q)_∞ = ∑_{k ≥ 0} (-1)ᵏ q^{k(k-1)/2} zᵏ / (q; q)_k` and `1 / (z; q)_∞ = ∑_{k ≥ 0} zᵏ / (q; q)_k`
(`TauCeti.hasSum_tprod_one_sub_mul_pow`, `TauCeti.hasSum_inv_tprod_one_sub_mul_pow`). For
`‖q‖ < ‖w‖`, the product of the bilateral series with `1 / (q / w; q)_∞` is a double series whose
inner sums are, by the first expansion, the products `(q^{m+1}; q)_∞`; these vanish for `m < 0`,
and the remaining series is `(q; q)_∞ (w; q)_∞` by the first expansion again. Both sides satisfy
`f(q w) = -w⁻¹ f(w)`, which extends the identity to every `w ≠ 0`.

## Main results

* `TauCeti.hasSum_qTheta_mul_tprod_one_sub_pow`: Jacobi's triple product identity,
  `θ_q(w) ∏_{n ≥ 1} (1 - qⁿ) = ∑_{k ∈ ℤ} (-1)ᵏ q^{k(k-1)/2} wᵏ` for `‖q‖ < 1` and `w ≠ 0`.

## References

* G. E. Andrews, *A simple proof of Jacobi's triple product identity*, Proc. Amer. Math. Soc. 16
  (1965), 333–334.
* G. Gasper, M. Rahman, *Basic Hypergeometric Series*, 2nd ed., Encyclopedia of Mathematics and
  its Applications 96, Cambridge University Press, 2004, §1.6.
-/

public section

open Filter Topology

namespace TauCeti

variable {𝕜 : Type*} [NormedField 𝕜]

/-- The terms `t(k) = (-1)ᵏ q^{k(k-1)/2} wᵏ` of the bilateral series in Jacobi's triple
product. -/
private noncomputable def tripleTerm (q w : 𝕜) (k : ℤ) : 𝕜 :=
  (-1) ^ k * q ^ (k * (k - 1) / 2) * w ^ k

/-- For `q ≠ 0` and `w ≠ 0` no term of the bilateral series vanishes. -/
private theorem tripleTerm_ne_zero {q w : 𝕜} (hq₀ : q ≠ 0) (hw : w ≠ 0) (k : ℤ) :
    tripleTerm q w k ≠ 0 := by
  unfold tripleTerm
  exact mul_ne_zero (mul_ne_zero (zpow_ne_zero _ (by norm_num)) (zpow_ne_zero _ hq₀))
    (zpow_ne_zero _ hw)

/-- Consecutive terms: `t(k + 1) = -(qᵏ w) t(k)`. -/
private theorem tripleTerm_add_one {q w : 𝕜} (hq₀ : q ≠ 0) (hw : w ≠ 0) (k : ℤ) :
    tripleTerm q w (k + 1) = -(q ^ k * w) * tripleTerm q w k := by
  unfold tripleTerm
  rw [Int.add_mul_add_sub_one_ediv_two]
  simp [zpow_add₀, hq₀, hw]
  ring

/-- Replacing `w` by `q w` multiplies the `k`-th term by `qᵏ`. -/
private theorem tripleTerm_mul_left (q w : 𝕜) (k : ℤ) :
    tripleTerm q (q * w) k = q ^ k * tripleTerm q w k := by
  unfold tripleTerm
  rw [mul_zpow]
  ring

/-- The terms `t(m + r) (q / w)ʳ / (q; q)_r` of the double series factor as `t(m)` times the
`r`-th term of Euler's expansion of `(q^{m+1}; q)_∞`. -/
private theorem tripleTerm_add_mul {q w : 𝕜} (hq₀ : q ≠ 0) (hw : w ≠ 0) (m : ℤ) (r : ℕ) :
    tripleTerm q w (m + r) * ((q * w⁻¹) ^ r / qPochhammer q q r) =
      tripleTerm q w m *
        ((-1) ^ r * q ^ r.choose 2 * (q ^ (m + 1)) ^ r / qPochhammer q q r) := by
  unfold tripleTerm
  rw [Int.add_mul_add_sub_one_ediv_two, ← Int.natCast_choose_two]
  simp [zpow_add₀, zpow_mul, hq₀, hw, mul_pow]
  field_simp

/-- Norms of consecutive terms: `‖t(k + 1)‖ = ‖q‖ᵏ ‖w‖ ‖t(k)‖`. -/
private theorem norm_tripleTerm_add_one {q w : 𝕜} (hq₀ : q ≠ 0) (hw : w ≠ 0) (k : ℤ) :
    ‖tripleTerm q w (k + 1)‖ = ‖q‖ ^ k * ‖w‖ * ‖tripleTerm q w k‖ := by
  simp [tripleTerm_add_one hq₀ hw]

/-- The bilateral series `∑_{k ∈ ℤ} (-1)ᵏ q^{k(k-1)/2} wᵏ` converges absolutely for `‖q‖ < 1`. -/
private theorem summable_norm_tripleTerm {q w : 𝕜} (hq : ‖q‖ < 1) (hq₀ : q ≠ 0) (hw : w ≠ 0) :
    Summable fun k : ℤ ↦ ‖tripleTerm q w k‖ := by
  have hpos : ∀ k, 0 < ‖tripleTerm q w k‖ := fun k ↦ norm_pos_iff.2 (tripleTerm_ne_zero hq₀ hw k)
  have hgeom := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · -- `‖t(n + 1)‖ = ‖q‖ⁿ ‖w‖ ‖t(n)‖`
    refine summable_of_ratio_test_tendsto_lt_one zero_lt_one
      (.of_forall fun n ↦ (hpos n).ne') ?_
    have h (n : ℕ) : ‖‖tripleTerm q w ↑(n + 1)‖‖ / ‖‖tripleTerm q w n‖‖ = ‖q‖ ^ n * ‖w‖ := by
      have := (hpos n).ne'
      rw [norm_norm, norm_norm, Nat.cast_succ, norm_tripleTerm_add_one hq₀ hw, zpow_natCast]
      field_simp
    exact (tendsto_congr h).mpr (by simpa using hgeom.mul_const ‖w‖)
  · -- `‖t(-(n + 1))‖ = ‖q‖^{-(n + 2)} ‖w‖ ‖t(-(n + 2))‖`
    refine summable_of_ratio_test_tendsto_lt_one zero_lt_one
      (.of_forall fun n ↦ (hpos _).ne') ?_
    have h (n : ℕ) : ‖‖tripleTerm q w (-(↑(n + 1) + 1))‖‖ / ‖‖tripleTerm q w (-(↑n + 1))‖‖ =
        ‖q‖ ^ 2 * ‖w‖⁻¹ * ‖q‖ ^ n := by
      have e := norm_tripleTerm_add_one hq₀ hw (-(↑(n + 1) + 1))
      have hq' : ‖q‖ ^ (-((↑(n + 1) : ℤ) + 1)) = (‖q‖ ^ (n + 2))⁻¹ := by
        rw [show -((↑(n + 1) : ℤ) + 1) = -↑(n + 2) by push_cast; ring, zpow_neg, zpow_natCast]
      rw [show -((↑(n + 1) : ℤ) + 1) + 1 = -(↑n + 1) by push_cast; ring, hq'] at e
      have := (hpos (-(↑(n + 1) + 1))).ne'
      have := norm_ne_zero_iff.2 hq₀
      have := norm_ne_zero_iff.2 hw
      rw [norm_norm, norm_norm, e]
      field_simp
      ring
    exact (tendsto_congr h).mpr (by simpa using hgeom.const_mul (‖q‖ ^ 2 * ‖w‖⁻¹))

/-- For `n : ℕ` the product `(q^{-n}; q)_∞` vanishes: its factor `1 - q^{-n} qⁿ` is zero. -/
private theorem tprod_one_sub_zpow_neg_mul_pow {q : 𝕜} (hq₀ : q ≠ 0) (n : ℕ) :
    ∏' i : ℕ, (1 - q ^ (-(n : ℤ)) * q ^ i) = 0 :=
  tprod_of_exists_eq_zero ⟨n, by rw [zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero n hq₀),
    sub_self]⟩

variable [CompleteSpace 𝕜]

/-- The Euler function splits as `(q; q)_∞ = (q; q)_n (q^{n+1}; q)_∞`. -/
private theorem tprod_one_sub_pow_succ_eq {q : 𝕜} (hq : ‖q‖ < 1) (n : ℕ) :
    ∏' i : ℕ, (1 - q ^ (i + 1)) = qPochhammer q q n * ∏' i : ℕ, (1 - q ^ (n + 1) * q ^ i) := by
  rw [pow_succ', ← tprod_one_sub_mul_pow_eq_qPochhammer_mul hq]
  exact tprod_congr fun i ↦ by ring

/-- For `‖q‖ < ‖w‖`, the product of the bilateral series with Euler's expansion of
`1 / (q / w; q)_∞`, summed first over the index of the latter: the inner sums are
`t(m) (q^{m+1}; q)_∞` by Euler's expansion of `(q^{m+1}; q)_∞`. -/
private theorem hasSum_tripleTerm_mul_tprod_of_norm_lt {q w : 𝕜} (hq : ‖q‖ < 1) (hq₀ : q ≠ 0)
    (hw : w ≠ 0) (hz : ‖q * w⁻¹‖ < 1) :
    HasSum (fun m : ℤ ↦ tripleTerm q w m * ∏' n : ℕ, (1 - q ^ (m + 1) * q ^ n))
      ((∑' k, tripleTerm q w k) * (∏' n : ℕ, (1 - q * w⁻¹ * q ^ n))⁻¹) := by
  have hS := summable_norm_tripleTerm hq hq₀ hw
  have hB := summable_norm_pow_div_qPochhammer hq hz
  -- The product of the two series as a double series over `(k, r) ∈ ℤ × ℕ`.
  have h : HasSum (fun p : ℤ × ℕ ↦
      tripleTerm q w p.1 * ((q * w⁻¹) ^ p.2 / qPochhammer q q p.2))
      ((∑' k, tripleTerm q w k) * (∏' n : ℕ, (1 - q * w⁻¹ * q ^ n))⁻¹) := by
    rw [← (hasSum_inv_tprod_one_sub_mul_pow hq hz).tsum_eq, tsum_mul_tsum_of_summable_norm hS hB]
    exact (summable_mul_of_summable_norm hS hB).hasSum
  -- Reindex by `k = m + r` and sum over `r` for each `m`.
  let e : ℤ × ℕ ≃ ℤ × ℕ :=
    { toFun := fun p ↦ (p.1 + p.2, p.2)
      invFun := fun p ↦ (p.1 - p.2, p.2)
      left_inv := fun p ↦ by simp
      right_inv := fun p ↦ by simp }
  refine (e.hasSum_iff.mpr h).prod_fiberwise fun m ↦ ?_
  convert (hasSum_tprod_one_sub_mul_pow hq (q ^ (m + 1))).mul_left (tripleTerm q w m) using 1
  funext r
  exact tripleTerm_add_mul hq₀ hw m r

/-- The series `∑_{m ∈ ℤ} t(m) (q^{m+1}; q)_∞` is `(q; q)_∞ (w; q)_∞`: its terms with `m < 0`
vanish, and for `m ≥ 0`, `t(m) (q^{m+1}; q)_∞ = (q; q)_∞ (-1)ᵐ q^{m(m-1)/2} wᵐ / (q; q)_m` is a
term of Euler's expansion of `(w; q)_∞`, times `(q; q)_∞`. -/
private theorem hasSum_tripleTerm_mul_tprod {q : 𝕜} (hq : ‖q‖ < 1) (hq₀ : q ≠ 0) (w : 𝕜) :
    HasSum (fun m : ℤ ↦ tripleTerm q w m * ∏' n : ℕ, (1 - q ^ (m + 1) * q ^ n))
      ((∏' n : ℕ, (1 - q ^ (n + 1))) * ∏' n : ℕ, (1 - w * q ^ n)) := by
  rw [← add_zero (_ * _)]
  refine HasSum.of_nat_of_neg_add_one ?_ ?_
  · convert (hasSum_tprod_one_sub_mul_pow hq w).mul_left (∏' n : ℕ, (1 - q ^ (n + 1))) using 1
    funext m
    have hD := qPochhammer_ne_zero_of_norm_lt_one hq hq.le m
    rw [tprod_one_sub_pow_succ_eq hq m, show q ^ ((m : ℤ) + 1) = q ^ (m + 1) by
      exact_mod_cast zpow_natCast q (m + 1)]
    unfold tripleTerm
    rw [← Int.natCast_choose_two, zpow_natCast, zpow_natCast, zpow_natCast]
    field_simp
  · convert hasSum_zero using 1
    funext n
    rw [show -((n : ℤ) + 1) + 1 = -(n : ℤ) by ring, tprod_one_sub_zpow_neg_mul_pow hq₀ n,
      mul_zero]

/-- Jacobi's triple product identity in the range `‖q‖ < ‖w‖`, where Euler's expansion of
`1 / (q / w; q)_∞` converges. -/
private theorem hasSum_tripleTerm_of_norm_lt {q w : 𝕜} (hq : ‖q‖ < 1) (hq₀ : q ≠ 0)
    (hqw : ‖q‖ < ‖w‖) :
    HasSum (tripleTerm q w) (qTheta q w * ∏' n : ℕ, (1 - q ^ (n + 1))) := by
  have hw : w ≠ 0 := norm_pos_iff.1 ((norm_nonneg q).trans_lt hqw)
  have hz : ‖q * w⁻¹‖ < 1 := by
    rw [norm_mul, norm_inv, ← div_eq_mul_inv, div_lt_one (norm_pos_iff.2 hw)]
    exact hqw
  -- `(q / w; q)_∞ = ∏_{n ≥ 1} (1 - qⁿ w⁻¹)` does not vanish.
  have hP : ∏' n : ℕ, (1 - q * w⁻¹ * q ^ n) = ∏' n : ℕ, (1 - q ^ (n + 1) * w⁻¹) :=
    tprod_congr fun n ↦ by ring
  have hP₀ : ∏' n : ℕ, (1 - q ^ (n + 1) * w⁻¹) ≠ 0 := by
    refine tprod_one_sub_pow_mul_ne_zero hq fun n h ↦ ?_
    have h₁ : ‖q ^ (n + 1) * w⁻¹‖ < 1 := by
      rw [norm_mul, norm_pow]
      calc ‖q‖ ^ (n + 1) * ‖w⁻¹‖ ≤ ‖q‖ * ‖w⁻¹‖ := by
            gcongr
            exact pow_le_of_le_one (norm_nonneg q) hq.le n.succ_ne_zero
        _ = ‖q * w⁻¹‖ := (norm_mul _ _).symm
        _ < 1 := hz
    exact one_sub_ne_zero_of_norm_lt_one h₁ h
  -- `(w; q)_∞ = (1 - w) ∏_{n ≥ 1} (1 - qⁿ w)`.
  have hW : ∏' n : ℕ, (1 - w * q ^ n) = (1 - w) * ∏' n : ℕ, (1 - q ^ (n + 1) * w) := by
    rw [tprod_one_sub_mul_pow_eq_qPochhammer_mul hq w 1, qPochhammer_one]
    exact congrArg _ (tprod_congr fun n ↦ by ring)
  have h := (hasSum_tripleTerm_mul_tprod_of_norm_lt hq hq₀ hw hz).unique
    (hasSum_tripleTerm_mul_tprod hq hq₀ w)
  rw [hP, mul_inv_eq_iff_eq_mul₀ hP₀] at h
  convert (summable_norm_tripleTerm hq hq₀ hw).of_norm.hasSum using 1
  rw [h, hW, qTheta_eq_mul_tprod_mul_tprod hq]
  ring

/-- **Jacobi's triple product identity**: for `‖q‖ < 1` and `w ≠ 0`,
`θ_q(w) ∏_{n ≥ 1} (1 - qⁿ) = (w; q)_∞ (q / w; q)_∞ (q; q)_∞ = ∑_{k ∈ ℤ} (-1)ᵏ q^{k(k-1)/2} wᵏ`,
where `θ_q(w) = (1 - w) ∏_{n ≥ 1} (1 - qⁿ w) (1 - qⁿ w⁻¹)` is the theta product `TauCeti.qTheta`.
The exponent `k(k-1)/2` is an exact integer quotient. -/
theorem hasSum_qTheta_mul_tprod_one_sub_pow {q w : 𝕜} (hq : ‖q‖ < 1) (hw : w ≠ 0) :
    HasSum (fun k : ℤ ↦ (-1) ^ k * q ^ (k * (k - 1) / 2) * w ^ k)
      (qTheta q w * ∏' n : ℕ, (1 - q ^ (n + 1))) := by
  rcases eq_or_ne q 0 with rfl | hq₀
  · -- For `q = 0` only the terms `k = 0` and `k = 1` survive.
    have h : ∀ k ∉ ({0, 1} : Finset ℤ),
        (-1) ^ k * (0 : 𝕜) ^ (k * (k - 1) / 2) * w ^ k = 0 := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
      simp [zero_zpow _ (Int.mul_sub_one_ediv_two_ne_zero hk.1 hk.2)]
    convert hasSum_sum_of_ne_finset_zero (L := .unconditional ℤ) h using 1
    simp [qTheta_def, sub_eq_add_neg]
  set E := ∏' n : ℕ, (1 - q ^ (n + 1))
  -- Both sides satisfy `f(q u) = -u⁻¹ f(u)`.
  have hstep : ∀ u : 𝕜, u ≠ 0 → HasSum (tripleTerm q u) (qTheta q u * E) →
      HasSum (tripleTerm q (q * u)) (qTheta q (q * u) * E) := by
    intro u hu h
    rw [qTheta_mul_left hq hq₀ hu, mul_assoc]
    convert ((Equiv.addRight (1 : ℤ)).hasSum_iff.mpr h).mul_left (-u⁻¹) using 1
    funext k
    rw [Function.comp_apply, Equiv.coe_addRight, tripleTerm_mul_left, tripleTerm_add_one hq₀ hu]
    field_simp
  -- `v = w / q^N` lies in the range `‖q‖ < ‖v‖`, and `w = q^N v`.
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.2 hw) hq
  have hqN : q ^ N ≠ 0 := pow_ne_zero N hq₀
  have hv : ‖q‖ < ‖w / q ^ N‖ := by
    rw [norm_div, norm_pow, lt_div_iff₀ (pow_pos (norm_pos_iff.2 hq₀) N), ← pow_succ']
    exact (pow_le_pow_of_le_one (norm_nonneg q) hq.le N.le_succ).trans_lt hN
  have hiter : ∀ n : ℕ, HasSum (tripleTerm q (q ^ n * (w / q ^ N)))
      (qTheta q (q ^ n * (w / q ^ N)) * E) := by
    intro n
    induction n with
    | zero => simpa using hasSum_tripleTerm_of_norm_lt hq hq₀ hv
    | succ n ih =>
      rw [pow_succ', mul_assoc]
      exact hstep _ (mul_ne_zero (pow_ne_zero n hq₀) (div_ne_zero hw hqN)) ih
  have h := hiter N
  rwa [show q ^ N * (w / q ^ N) = w by field_simp] at h

end TauCeti
