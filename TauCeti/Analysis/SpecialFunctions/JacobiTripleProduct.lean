/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.QPochhammer
import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.Theta.Basic
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

For `q ≠ 0` the bilateral series is the theta series `TauCeti.tateTheta` of the Tate curve, whose
absolute convergence (`TauCeti.summable_norm_tateTheta`) and quasi-periodicity
(`TauCeti.tateTheta_self_mul`) are used here.

## Main results

* `TauCeti.hasSum_qTheta_mul_tprod_one_sub_pow`: Jacobi's triple product identity,
  `θ_q(w) ∏_{n ≥ 1} (1 - qⁿ) = ∑_{k ∈ ℤ} (-1)ᵏ q^{k(k-1)/2} wᵏ` for `‖q‖ < 1` and `w ≠ 0`.
* `TauCeti.hasSum_neg_one_pow_mul_zpow_sq`, `TauCeti.tsum_neg_one_pow_mul_zpow_sq`,
  `TauCeti.hasSum_neg_one_pow_mul_zpow_sq_tprod_div`,
  `TauCeti.tsum_neg_one_pow_mul_zpow_sq_eq_tprod_div`,
  `TauCeti.tsum_neg_one_pow_mul_zpow_sq_ne_zero`: Gauss's and Jacobi's product identities and
  nonvanishing for `∑_{k ∈ ℤ} (-1)ᵏ q^{k²}` when `‖q‖ < 1`.
* `TauCeti.hasSum_zpow_sq`, `TauCeti.tsum_zpow_sq`, `TauCeti.tsum_zpow_sq_ne_zero`: Gauss's
  product identity and nonvanishing for `∑_{k ∈ ℤ} q^{k²}` when `‖q‖ < 1`.

## References

* G. E. Andrews, *A simple proof of Jacobi's triple product identity*, Proc. Amer. Math. Soc. 16
  (1965), 333–334.
* G. Gasper, M. Rahman, *Basic Hypergeometric Series*, 2nd ed., Encyclopedia of Mathematics and
  its Applications 96, Cambridge University Press, 2004, §1.6.
* C. G. J. Jacobi, *Fundamenta Nova Theoriae Functionum Ellipticarum* (1829), §61.
-/

public section

open Filter Topology

namespace TauCeti

variable {𝕜 : Type*} [NormedField 𝕜]

/-- The terms `t(m + r) (q / w)ʳ / (q; q)_r` of the double series, where
`t(k) = (-1)ᵏ q^{k(k-1)/2} wᵏ` is the `k`-th term of the theta series `TauCeti.tateTheta`, factor
as `t(m)` times the `r`-th term of Euler's expansion of `(q^{m+1}; q)_∞`. -/
private theorem tateTheta_term_add_mul {q w : 𝕜} (hq₀ : q ≠ 0) (hw : w ≠ 0) (m : ℤ) (r : ℕ) :
    (-1) ^ (m + r) * q ^ ((m + r) * (m + r - 1) / 2) * w ^ (m + r) *
        ((q * w⁻¹) ^ r / qPochhammer q q r) =
      (-1) ^ m * q ^ (m * (m - 1) / 2) * w ^ m *
        ((-1) ^ r * q ^ r.choose 2 * (q ^ (m + 1)) ^ r / qPochhammer q q r) := by
  rw [Int.add_mul_add_sub_one_ediv_two, ← Int.natCast_choose_two]
  simp [zpow_add₀, zpow_mul, hq₀, hw, mul_pow]
  field_simp

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

/-- For `‖q‖ < ‖w‖`, the product of the theta series with Euler's expansion of
`1 / (q / w; q)_∞`, summed first over the index of the latter: the inner sums are
`t(m) (q^{m+1}; q)_∞` by Euler's expansion of `(q^{m+1}; q)_∞`. -/
private theorem hasSum_tateTheta_term_mul_tprod_of_norm_lt {q w : 𝕜} (hq : ‖q‖ < 1)
    (hq₀ : q ≠ 0) (hw : w ≠ 0) (hz : ‖q * w⁻¹‖ < 1) :
    HasSum (fun m : ℤ ↦
        (-1) ^ m * q ^ (m * (m - 1) / 2) * w ^ m * ∏' n : ℕ, (1 - q ^ (m + 1) * q ^ n))
      (tateTheta (Units.mk0 q hq₀) (Units.mk0 w hw) * (∏' n : ℕ, (1 - q * w⁻¹ * q ^ n))⁻¹) := by
  have hS := summable_norm_tateTheta (Units.mk0 q hq₀) (Units.mk0 w hw) hq
  simp only [Units.val_mk0] at hS
  have hB := summable_norm_pow_div_qPochhammer hq hz
  -- The product of the two series as a double series over `(k, r) ∈ ℤ × ℕ`.
  have h : HasSum (fun p : ℤ × ℕ ↦ (-1) ^ p.1 * q ^ (p.1 * (p.1 - 1) / 2) * w ^ p.1 *
      ((q * w⁻¹) ^ p.2 / qPochhammer q q p.2))
      (tateTheta (Units.mk0 q hq₀) (Units.mk0 w hw) * (∏' n : ℕ, (1 - q * w⁻¹ * q ^ n))⁻¹) := by
    rw [← (hasSum_inv_tprod_one_sub_mul_pow hq hz).tsum_eq, tateTheta_def, Units.val_mk0,
      Units.val_mk0, tsum_mul_tsum_of_summable_norm hS hB]
    exact (summable_mul_of_summable_norm hS hB).hasSum
  -- Reindex by `k = m + r` and sum over `r` for each `m`.
  let e : ℤ × ℕ ≃ ℤ × ℕ :=
    { toFun := fun p ↦ (p.1 + p.2, p.2)
      invFun := fun p ↦ (p.1 - p.2, p.2)
      left_inv := fun p ↦ by simp
      right_inv := fun p ↦ by simp }
  refine (e.hasSum_iff.mpr h).prod_fiberwise fun m ↦ ?_
  convert (hasSum_tprod_one_sub_mul_pow hq (q ^ (m + 1))).mul_left
    ((-1) ^ m * q ^ (m * (m - 1) / 2) * w ^ m) using 1
  funext r
  exact tateTheta_term_add_mul hq₀ hw m r

/-- The series `∑_{m ∈ ℤ} t(m) (q^{m+1}; q)_∞` is `(q; q)_∞ (w; q)_∞`: its terms with `m < 0`
vanish, and for `m ≥ 0`, `t(m) (q^{m+1}; q)_∞ = (q; q)_∞ (-1)ᵐ q^{m(m-1)/2} wᵐ / (q; q)_m` is a
term of Euler's expansion of `(w; q)_∞`, times `(q; q)_∞`. -/
private theorem hasSum_tateTheta_term_mul_tprod {q : 𝕜} (hq : ‖q‖ < 1) (hq₀ : q ≠ 0) (w : 𝕜) :
    HasSum (fun m : ℤ ↦
        (-1) ^ m * q ^ (m * (m - 1) / 2) * w ^ m * ∏' n : ℕ, (1 - q ^ (m + 1) * q ^ n))
      ((∏' n : ℕ, (1 - q ^ (n + 1))) * ∏' n : ℕ, (1 - w * q ^ n)) := by
  rw [← add_zero (_ * _)]
  refine HasSum.of_nat_of_neg_add_one ?_ ?_
  · convert (hasSum_tprod_one_sub_mul_pow hq w).mul_left (∏' n : ℕ, (1 - q ^ (n + 1))) using 1
    funext m
    have hD := qPochhammer_ne_zero_of_norm_lt_one hq hq.le m
    rw [tprod_one_sub_pow_succ_eq hq m, show q ^ ((m : ℤ) + 1) = q ^ (m + 1) by
      exact_mod_cast zpow_natCast q (m + 1)]
    rw [← Int.natCast_choose_two, zpow_natCast, zpow_natCast, zpow_natCast]
    field_simp
  · convert hasSum_zero using 1
    funext n
    rw [show -((n : ℤ) + 1) + 1 = -(n : ℤ) by ring, tprod_one_sub_zpow_neg_mul_pow hq₀ n,
      mul_zero]

/-- Jacobi's triple product identity in the range `‖q‖ < ‖w‖`, where Euler's expansion of
`1 / (q / w; q)_∞` converges. -/
private theorem tateTheta_eq_qTheta_mul_tprod_of_norm_lt {q w : 𝕜} (hq : ‖q‖ < 1) (hq₀ : q ≠ 0)
    (hw : w ≠ 0) (hqw : ‖q‖ < ‖w‖) :
    tateTheta (Units.mk0 q hq₀) (Units.mk0 w hw) = qTheta q w * ∏' n : ℕ, (1 - q ^ (n + 1)) := by
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
  have h := (hasSum_tateTheta_term_mul_tprod_of_norm_lt hq hq₀ hw hz).unique
    (hasSum_tateTheta_term_mul_tprod hq hq₀ w)
  rw [hP, mul_inv_eq_iff_eq_mul₀ hP₀] at h
  rw [h, hW, qTheta_eq_mul_tprod_mul_tprod hq]
  ring

/-- **Jacobi's triple product identity**: for `‖q‖ < 1` and `w ≠ 0`,
`θ_q(w) ∏_{n ≥ 1} (1 - qⁿ) = (w; q)_∞ (q / w; q)_∞ (q; q)_∞ = ∑_{k ∈ ℤ} (-1)ᵏ q^{k(k-1)/2} wᵏ`,
where `θ_q(w) = (1 - w) ∏_{n ≥ 1} (1 - qⁿ w) (1 - qⁿ w⁻¹)` is the theta product `TauCeti.qTheta`.
The exponent `k(k-1)/2` is an exact integer quotient. For `q ≠ 0` the sum is the theta series
`TauCeti.tateTheta` of the Tate curve. -/
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
  set Q := Units.mk0 q hq₀
  set E := ∏' n : ℕ, (1 - q ^ (n + 1))
  -- Both sides satisfy `f(q u) = -u⁻¹ f(u)`.
  have hstep (u : 𝕜ˣ) (h : tateTheta Q u = qTheta q u * E) :
      tateTheta Q (Q * u) = qTheta q ((Q * u : 𝕜ˣ) : 𝕜) * E := by
    rw [tateTheta_self_mul, h, Units.val_mul, Units.val_mk0, qTheta_mul_left hq hq₀ u.ne_zero]
    ring
  -- `v = w / q^N` lies in the range `‖q‖ < ‖v‖`, and `w = q^N v`.
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.2 hw) hq
  have hqN : q ^ N ≠ 0 := pow_ne_zero N hq₀
  have hv : ‖q‖ < ‖w / q ^ N‖ := by
    rw [norm_div, norm_pow, lt_div_iff₀ (pow_pos (norm_pos_iff.2 hq₀) N), ← pow_succ']
    exact (pow_le_pow_of_le_one (norm_nonneg q) hq.le N.le_succ).trans_lt hN
  set V := Units.mk0 (w / q ^ N) (div_ne_zero hw hqN)
  have hiter (n : ℕ) : tateTheta Q (Q ^ n * V) = qTheta q ((Q ^ n * V : 𝕜ˣ) : 𝕜) * E := by
    induction n with
    | zero =>
      rw [pow_zero, one_mul]
      exact tateTheta_eq_qTheta_mul_tprod_of_norm_lt hq hq₀ (div_ne_zero hw hqN) hv
    | succ n ih =>
      rw [pow_succ', mul_assoc]
      exact hstep _ ih
  have hw' : Q ^ N * V = Units.mk0 w hw := Units.ext (by simp [Q, V, mul_div_cancel₀ _ hqN])
  have h := hasSum_tateTheta Q (Units.mk0 w hw) hq
  rw [← hw', hiter, hw'] at h
  simpa [Q] using h

/-! ### Specializations to quadratic theta series -/

/-- **Gauss's product identity** for the alternating theta series over any complete normed field:
for `‖q‖ < 1`,
`∑_{k ∈ ℤ} (-1)ᵏ q^{k²} = (∏_{n ≥ 0} (1 - q^{2n+1}))² ∏_{n ≥ 1} (1 - q^{2n})`. -/
theorem hasSum_neg_one_pow_mul_zpow_sq {q : 𝕜} (hq : ‖q‖ < 1) :
    HasSum (fun k : ℤ ↦ (-1) ^ k * q ^ (k ^ 2))
      ((∏' n : ℕ, (1 - q ^ (2 * n + 1))) ^ 2 * ∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1))) := by
  rcases eq_or_ne q 0 with rfl | hq₀
  · have h1 : (fun n : ℕ ↦ (1 : 𝕜) - 0 ^ (2 * n + 1)) = fun _ ↦ 1 := by
      ext n
      simp
    have h2 : (fun n : ℕ ↦ (1 : 𝕜) - ((0 : 𝕜) ^ 2) ^ (n + 1)) = fun _ ↦ 1 := by
      ext n
      simp
    rw [h1, h2, tprod_one, one_pow, one_mul]
    have hsum : HasSum (fun k : ℤ ↦ (-1 : 𝕜) ^ k * (0 : 𝕜) ^ (k ^ 2))
        ((-1 : 𝕜) ^ (0 : ℤ) * (0 : 𝕜) ^ ((0 : ℤ) ^ 2)) :=
      hasSum_single (0 : ℤ) fun k hk ↦ mul_eq_zero_of_right _ (zero_zpow _ (pow_ne_zero 2 hk))
    simpa using hsum
  have h := hasSum_qTheta_mul_tprod_one_sub_pow (norm_pow_lt_one hq two_ne_zero) hq₀
  rw [qTheta_sq_self hq] at h
  refine h.congr_fun fun k ↦ ?_
  have hmul : (q ^ 2) ^ (k * (k - 1) / 2) * q ^ k = q ^ (k ^ 2) := by
    rw [← zpow_natCast, ← zpow_mul, ← zpow_add₀ hq₀, Nat.cast_ofNat,
      Int.two_mul_mul_sub_one_ediv_two]
    congr 1
    ring
  rw [mul_assoc, hmul]

/-- **Gauss's product identity** for the alternating theta series in `tsum` form: for `‖q‖ < 1`,
`∑' k : ℤ, (-1) ^ k * q ^ (k ^ 2) =`
`(∏' n : ℕ, (1 - q ^ (2 * n + 1))) ^ 2 * ∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1))`. -/
theorem tsum_neg_one_pow_mul_zpow_sq {q : 𝕜} (hq : ‖q‖ < 1) :
    ∑' k : ℤ, (-1) ^ k * q ^ (k ^ 2) =
      (∏' n : ℕ, (1 - q ^ (2 * n + 1))) ^ 2 * ∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1)) :=
  (hasSum_neg_one_pow_mul_zpow_sq hq).tsum_eq

/-- **Jacobi's product formula** in `HasSum` form: for `‖q‖ < 1`, the series
`∑_{k ∈ ℤ} (-1)ᵏ q^{k²}` has sum `∏_{n ≥ 1} (1 - qⁿ) / (1 + qⁿ)`. -/
theorem hasSum_neg_one_pow_mul_zpow_sq_tprod_div {q : 𝕜} (hq : ‖q‖ < 1) :
    HasSum (fun k : ℤ ↦ (-1) ^ k * q ^ (k ^ 2))
      (∏' n : ℕ, (1 - q ^ (n + 1)) / (1 + q ^ (n + 1))) := by
  rw [tprod_one_sub_div_one_add_pow_eq_tprod_one_sub_pow_odd_sq_mul hq]
  exact hasSum_neg_one_pow_mul_zpow_sq hq

/-- **Jacobi's product formula**: for `‖q‖ < 1` in a complete normed field,
`∑' k : ℤ, (-1) ^ k * q ^ (k ^ 2) = ∏' n : ℕ, (1 - q ^ (n + 1)) / (1 + q ^ (n + 1))`. -/
theorem tsum_neg_one_pow_mul_zpow_sq_eq_tprod_div {q : 𝕜} (hq : ‖q‖ < 1) :
    ∑' k : ℤ, (-1) ^ k * q ^ (k ^ 2) = ∏' n : ℕ, (1 - q ^ (n + 1)) / (1 + q ^ (n + 1)) :=
  (hasSum_neg_one_pow_mul_zpow_sq_tprod_div hq).tsum_eq

/-- For `‖q‖ < 1`, the alternating quadratic theta series `∑_{k ∈ ℤ} (-1)ᵏ q^{k²}`
does not vanish. -/
theorem tsum_neg_one_pow_mul_zpow_sq_ne_zero {q : 𝕜} (hq : ‖q‖ < 1) :
    ∑' k : ℤ, (-1) ^ k * q ^ (k ^ 2) ≠ 0 := by
  rw [tsum_neg_one_pow_mul_zpow_sq hq]
  exact mul_ne_zero (pow_ne_zero 2 (tprod_one_sub_pow_odd_ne_zero hq))
    (tprod_one_sub_pow_ne_zero (norm_pow_lt_one hq two_ne_zero))

/-- **Gauss's product identity** for the theta series `∑_{k ∈ ℤ} q^{k²}`: for `‖q‖ < 1`,
`∑_{k ∈ ℤ} q^{k²}` has sum `(∏_{n ≥ 0} (1 + q^{2n+1}))² ∏_{n ≥ 1} (1 - q^{2n})`. -/
theorem hasSum_zpow_sq {q : 𝕜} (hq : ‖q‖ < 1) :
    HasSum (fun k : ℤ ↦ q ^ (k ^ 2))
      ((∏' n : ℕ, (1 + q ^ (2 * n + 1))) ^ 2 * ∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1))) := by
  have h := hasSum_neg_one_pow_mul_zpow_sq (q := -q) (by rwa [norm_neg])
  simp only [one_sub_neg_pow_odd, neg_sq] at h
  refine h.congr_fun fun k ↦ ?_
  obtain ⟨m, hm⟩ := Int.even_mul_pred_self (-k)
  have hpow : k ^ 2 = ((k.natAbs ^ 2 : ℕ) : ℤ) := by
    rw [Int.natCast_pow, Int.natCast_natAbs, sq_abs]
  rw [hpow, zpow_natCast, zpow_natCast, neg_pow, ← mul_assoc, ← zpow_natCast (-1 : 𝕜),
    ← zpow_add₀ (by norm_num : (-1 : 𝕜) ≠ 0), ← hpow]
  have heven : k + k ^ 2 = 2 * m := by linear_combination hm
  rw [heven, zpow_mul, zpow_ofNat, neg_one_sq, one_zpow, one_mul]

/-- For `‖q‖ < 1`,
`∑' k : ℤ, q ^ (k ^ 2) =`
`(∏' n : ℕ, (1 + q ^ (2 * n + 1))) ^ 2 * ∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1))`. -/
theorem tsum_zpow_sq {q : 𝕜} (hq : ‖q‖ < 1) :
    ∑' k : ℤ, q ^ (k ^ 2) =
      (∏' n : ℕ, (1 + q ^ (2 * n + 1))) ^ 2 * ∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1)) :=
  (hasSum_zpow_sq hq).tsum_eq

/-- For `‖q‖ < 1` in a complete normed field, the quadratic theta series
`∑' k : ℤ, q ^ (k ^ 2)` does not vanish. -/
theorem tsum_zpow_sq_ne_zero {q : 𝕜} (hq : ‖q‖ < 1) :
    ∑' k : ℤ, q ^ (k ^ 2) ≠ 0 := by
  rw [tsum_zpow_sq hq]
  have hodd : ∏' n : ℕ, (1 + q ^ (2 * n + 1)) ≠ 0 := by
    simpa only [one_sub_neg_pow_odd] using
      tprod_one_sub_pow_odd_ne_zero (q := -q) (by rwa [norm_neg])
  exact mul_ne_zero (pow_ne_zero 2 hodd)
    (tprod_one_sub_pow_ne_zero (norm_pow_lt_one hq two_ne_zero))

end TauCeti
