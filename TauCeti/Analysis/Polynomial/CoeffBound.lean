/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Polynomial
public import TauCeti.Analysis.Polynomial.L1Norm

/-!
# Coefficient bounds in terms of root bounds

Mathlib's `Polynomial.coeff_le_of_roots_le` bounds every coefficient of a monic polynomial by
`B ^ (p.natDegree - i)` times a binomial coefficient, where `B` bounds all its roots. This file
adds the estimate for the constant coefficient that keeps the factor of a distinguished root `w`
separate:

  `‖p.coeff 0‖ ≤ ‖w‖ * B ^ (p.natDegree - 1)`

for a monic `p` with a root `w` and all roots in the closed disc of radius `B`.

It also bounds an explicit finite product `∏ₖ (X - zₖ)` over a seminormed commutative ring with
`‖1‖ = 1`. If `‖zₖ‖ ≤ Mₖ`, every coefficient has norm at most `∏ₖ (1 + Mₖ)`; the bounds `Mₖ`
may differ from root to root. If the roots are moved to `wₖ` with `‖zₖ‖ ≤ M` and
`‖wₖ - zₖ‖ ≤ δ`, every coefficient moves by at most `h δ (1 + M + δ) ^ (h - 1)`, where `h` is
the number of factors; in particular it moves by less than `1 / 4` once
`4 h (2 + M) ^ (h - 1) δ < 1`. These are the estimates used to recover a polynomial with integer
coefficients, such as a Hilbert class polynomial, from sufficiently precise approximations to
its roots.

## Main results

* `Polynomial.norm_coeff_zero_le_norm_mul_pow_of_roots_le`: the constant coefficient of a monic
  polynomial with bounded roots is at most `‖w‖ * B ^ (p.natDegree - 1)` at each root `w`.
* `Polynomial.norm_coeff_le_of_roots_erase_le`: the coefficients of a monic polynomial with a
  distinguished root of norm at most `B` and all other roots of norm at most `1`.
* `Polynomial.l1Norm_prod_X_sub_C_le`, `Polynomial.norm_coeff_prod_X_sub_C_le`: the coefficients
  of `∏ₖ (X - zₖ)` with `‖zₖ‖ ≤ Mₖ` are bounded by `∏ₖ (1 + Mₖ)`.
* `Polynomial.l1Norm_prod_X_sub_C_sub_prod_X_sub_C_le`,
  `Polynomial.norm_coeff_prod_X_sub_C_sub_prod_X_sub_C_le`: perturbing every root by at most `δ`
  changes each coefficient by at most `h δ (1 + M + δ) ^ (h - 1)`.
* `Polynomial.norm_coeff_prod_X_sub_C_sub_prod_X_sub_C_lt_one_div_four`: the perturbation is
  below `1 / 4` once `4 h (2 + M) ^ (h - 1) δ < 1`.

## References

* A. V. Sutherland, *Computing Hilbert class polynomials with the Chinese Remainder Theorem*,
  Math. Comp. 80 (2011), Appendix 1, Lemma 8.
-/

public section

open Polynomial

namespace Polynomial

variable {K : Type*} [NormedField K]

/-- **The constant coefficient against a distinguished root.** A monic polynomial `p` that splits
over a normed field, all of whose roots are bounded by `B`, has constant coefficient at most
`‖w‖ * B ^ (p.natDegree - 1)` at each root `w`: it is `±w` times the product of the remaining
roots, each of modulus at most `B`. -/
theorem norm_coeff_zero_le_norm_mul_pow_of_roots_le {p : K[X]} {B : ℝ} (hp : p.Monic)
    (hs : Splits p) (hB : ∀ z ∈ p.roots, ‖z‖ ≤ B) {w : K} (hw : p.IsRoot w) :
    ‖p.coeff 0‖ ≤ ‖w‖ * B ^ (p.natDegree - 1) := by
  set q := p /ₘ (X - C w)
  have hfac : (X - C w) * q = p := mul_divByMonic_eq_iff_isRoot.mpr hw
  have hqmono : q.Monic := by
    have h := congrArg leadingCoeff hfac
    rw [leadingCoeff_mul, (monic_X_sub_C w).leadingCoeff, one_mul, hp.leadingCoeff] at h
    exact h
  have hq0 : q ≠ 0 := hqmono.ne_zero
  have hqdeg : q.natDegree = p.natDegree - 1 := by
    have h := congrArg natDegree hfac
    rw [natDegree_mul (monic_X_sub_C w).ne_zero hq0, natDegree_X_sub_C] at h
    omega
  -- every root of the quotient is a root of `p`
  have hqr : ∀ z ∈ q.roots, ‖z‖ ≤ B := by
    intro z hz
    refine hB z ((mem_roots hp.ne_zero).mpr ?_)
    rw [Polynomial.IsRoot.def, ← hfac, eval_mul, eval_sub, eval_X, eval_C]
    exact mul_eq_zero_of_right _ ((mem_roots hq0).mp hz)
  have hcoeff : ‖q.coeff 0‖ ≤ B ^ q.natDegree := by
    have hqp : q ∣ p := ⟨X - C w, by rw [← hfac, mul_comm]⟩
    have h := coeff_le_of_roots_le (p := q) (f := RingHom.id K) (B := B) 0 hqmono
      (by simpa using hs.of_dvd hp.ne_zero hqp) (by simpa using hqr)
    simpa only [map_id, tsub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one] using h
  -- the constant term of `p` is `-w` times that of the quotient
  have hconst : p.coeff 0 = -w * q.coeff 0 := by
    rw [coeff_zero_eq_eval_zero, ← hfac, eval_mul, eval_sub, eval_X, eval_C, zero_sub,
      coeff_zero_eq_eval_zero]
  rw [hconst, norm_mul, norm_neg, ← hqdeg]
  exact mul_le_mul_of_nonneg_left hcoeff (norm_nonneg w)

/-- **The coefficients against a distinguished root.** A monic polynomial `p` that splits over a
normed field, with a root `w` of norm at most `B` whose remaining roots have norm at most `1`,
has its coefficient of `X ^ (n - k)`, for `k < n = p.natDegree`, bounded in norm by
`C(n-1, k-1) * B + C(n-1, k)`: it is `q_(n-k-1) - w * q_(n-k)` for the cofactor `q` of `X - w`,
whose coefficients are bounded by Mathlib's `coeff_le_of_roots_le`. -/
theorem norm_coeff_le_of_roots_erase_le [DecidableEq K] {p : K[X]} {B : ℝ} (hp : p.Monic)
    (hs : Splits p) {w : K} (hw : p.IsRoot w) (hwB : ‖w‖ ≤ B)
    (hB : ∀ z ∈ p.roots.erase w, ‖z‖ ≤ 1) {k : ℕ} (hkn : k < p.natDegree) :
    ‖p.coeff (p.natDegree - k)‖ ≤
      (p.natDegree - 1).choose (k - 1) * B + (p.natDegree - 1).choose k := by
  rcases k.eq_zero_or_pos with rfl | hk
  · have hB0 : 0 ≤ B := (norm_nonneg w).trans hwB
    simp only [Nat.sub_zero, hp.coeff_natDegree, norm_one, zero_tsub, Nat.choose_zero_right,
      Nat.cast_one, one_mul]
    linarith
  set q := p /ₘ (X - C w)
  have hfac : (X - C w) * q = p := mul_divByMonic_eq_iff_isRoot.mpr hw
  have hqmono : q.Monic := (monic_X_sub_C w).of_mul_monic_left (by rw [hfac]; exact hp)
  have hqdeg : q.natDegree = p.natDegree - 1 := by
    simpa [q] using natDegree_divByMonic p (monic_X_sub_C w)
  have hqroots : q.roots = p.roots.erase w := by
    rw [← hfac, roots_mul (hfac ▸ hp.ne_zero), roots_X_sub_C]
    simp
  have hqcoeff : ∀ j, ‖q.coeff j‖ ≤ (p.natDegree - 1).choose j := fun j => by
    have hqp : q ∣ p := ⟨X - C w, by rw [← hfac, mul_comm]⟩
    have h := coeff_le_of_roots_le (p := q) (f := RingHom.id K) (B := 1) j hqmono
      (by simpa using hs.of_dvd hp.ne_zero hqp) (by simpa [hqroots] using hB)
    simpa [hqdeg] using h
  have hsplit : p.coeff (p.natDegree - k) =
      q.coeff (p.natDegree - k - 1) - w * q.coeff (p.natDegree - k) := by
    have h := coeff_X_sub_C_mul (p := q) (r := w) (a := p.natDegree - k - 1)
    rwa [hfac, show p.natDegree - k - 1 + 1 = p.natDegree - k by omega] at h
  have hsym1 : (p.natDegree - 1).choose (p.natDegree - k - 1) = (p.natDegree - 1).choose k := by
    rw [show p.natDegree - k - 1 = p.natDegree - 1 - k by omega,
      Nat.choose_symm (Nat.le_sub_one_of_lt hkn)]
  have hsym2 : (p.natDegree - 1).choose (p.natDegree - k) =
      (p.natDegree - 1).choose (k - 1) := by
    rw [show p.natDegree - k = p.natDegree - 1 - (k - 1) by omega,
      Nat.choose_symm (Nat.sub_le_sub_right hkn.le 1)]
  rw [hsplit]
  calc ‖q.coeff (p.natDegree - k - 1) - w * q.coeff (p.natDegree - k)‖
      ≤ ‖q.coeff (p.natDegree - k - 1)‖ + ‖w‖ * ‖q.coeff (p.natDegree - k)‖ := by
        rw [← norm_mul]; exact norm_sub_le _ _
    _ ≤ (p.natDegree - 1).choose k + B * (p.natDegree - 1).choose (k - 1) := by
        refine add_le_add (by rw [← hsym1]; exact hqcoeff _) (mul_le_mul hwB
          (by rw [← hsym2]; exact hqcoeff _) (norm_nonneg _) (hwB.trans' (norm_nonneg w)))
    _ = (p.natDegree - 1).choose (k - 1) * B + (p.natDegree - 1).choose k := by ring

section RootProduct

open scoped Finset

variable {R : Type*} [SeminormedCommRing R] [NormOneClass R] {ι : Type*}

/-- **Coefficient length of a root product.** If `‖z i‖ ≤ M i` for every `i ∈ s`, the
coefficient l¹-norm of `∏ i ∈ s, (X - C (z i))` is at most `∏ i ∈ s, (1 + M i)`. -/
theorem l1Norm_prod_X_sub_C_le (s : Finset ι) (z : ι → R) {M : ι → ℝ}
    (hz : ∀ i ∈ s, ‖z i‖ ≤ M i) :
    (∏ i ∈ s, (X - C (z i))).l1Norm ≤ ∏ i ∈ s, (1 + M i) :=
  (l1Norm_prod_le s _).trans <| Finset.prod_le_prod₀ (fun _ _ ↦ l1Norm_nonneg _) fun i hi ↦ by
    simpa only [l1Norm_X_sub_C, add_le_add_iff_left] using hz i hi

/-- **Coefficients of a root product.** If `‖z i‖ ≤ M i` for every `i ∈ s`, every coefficient
of `∏ i ∈ s, (X - C (z i))` has norm at most `∏ i ∈ s, (1 + M i)`. -/
theorem norm_coeff_prod_X_sub_C_le (s : Finset ι) (z : ι → R) {M : ι → ℝ}
    (hz : ∀ i ∈ s, ‖z i‖ ≤ M i) (n : ℕ) :
    ‖(∏ i ∈ s, (X - C (z i))).coeff n‖ ≤ ∏ i ∈ s, (1 + M i) :=
  (norm_coeff_le_l1Norm _ n).trans (l1Norm_prod_X_sub_C_le s z hz)

/-- **Perturbing the roots of a product.** Let `s` have `h` elements, `‖z i‖ ≤ M` and
`‖w i - z i‖ ≤ δ` for every `i ∈ s`. Then the coefficient l¹-norm of
`∏ i ∈ s, (X - C (w i)) - ∏ i ∈ s, (X - C (z i))` is at most `h δ (1 + M + δ) ^ (h - 1)`. -/
theorem l1Norm_prod_X_sub_C_sub_prod_X_sub_C_le (s : Finset ι) (z w : ι → R) {M δ : ℝ}
    (hz : ∀ i ∈ s, ‖z i‖ ≤ M) (hw : ∀ i ∈ s, ‖w i - z i‖ ≤ δ) :
    (∏ i ∈ s, (X - C (w i)) - ∏ i ∈ s, (X - C (z i))).l1Norm ≤
      #s * δ * (1 + M + δ) ^ (#s - 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hza := hz a (Finset.mem_insert_self a s)
    have hwa := hw a (Finset.mem_insert_self a s)
    have hδ : 0 ≤ δ := (norm_nonneg _).trans hwa
    have hM : 0 ≤ 1 + M := by linarith [(norm_nonneg _).trans hza]
    have ih := ih (fun i hi ↦ hz i (Finset.mem_insert_of_mem hi))
      (fun i hi ↦ hw i (Finset.mem_insert_of_mem hi))
    have hprod := l1Norm_prod_X_sub_C_le s z (M := fun _ ↦ M)
      fun i hi ↦ hz i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_const] at hprod
    -- the new factor contributes `(X - w a) (∏ (X - w) - ∏ (X - z)) + (z a - w a) ∏ (X - z)`
    have hsplit : ∏ i ∈ insert a s, (X - C (w i)) - ∏ i ∈ insert a s, (X - C (z i)) =
        (X - C (w a)) * (∏ i ∈ s, (X - C (w i)) - ∏ i ∈ s, (X - C (z i))) +
          C (z a - w a) * ∏ i ∈ s, (X - C (z i)) := by
      rw [Finset.prod_insert ha, Finset.prod_insert ha, C_sub]
      ring
    have hwa' : 1 + ‖w a‖ ≤ 1 + M + δ := by
      have := (norm_add_le (w a - z a) (z a)).trans (add_le_add hwa hza)
      rw [sub_add_cancel] at this
      linarith
    -- `(1 + M + δ) * (#s * δ * (1 + M + δ) ^ (#s - 1)) = #s * δ * (1 + M + δ) ^ #s`
    have hpow : (1 + M + δ) * (#s * δ * (1 + M + δ) ^ (#s - 1)) =
        #s * δ * (1 + M + δ) ^ #s := by
      rcases Nat.eq_zero_or_pos #s with h | h
      · simp [h]
      · rw [← Nat.sub_add_cancel h, pow_succ, Nat.add_sub_cancel]
        ring
    rw [hsplit, Finset.card_insert_of_notMem ha, Nat.add_sub_cancel, Nat.cast_add_one]
    calc _ ≤ (1 + ‖w a‖) * (#s * δ * (1 + M + δ) ^ (#s - 1)) + ‖z a - w a‖ * (1 + M) ^ #s := by
          refine (l1Norm_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [← l1Norm_X_sub_C]
            exact (l1Norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ih (l1Norm_nonneg _))
          · rw [← l1Norm_C]
            exact (l1Norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hprod (l1Norm_nonneg _))
      _ ≤ (1 + M + δ) * (#s * δ * (1 + M + δ) ^ (#s - 1)) + δ * (1 + M + δ) ^ #s := by
          have hza' : ‖z a - w a‖ ≤ δ := by rwa [norm_sub_rev]
          have h1M : (1 + M) ^ #s ≤ (1 + M + δ) ^ #s := pow_le_pow_left₀ hM (by linarith) _
          gcongr
      _ = (#s + 1) * δ * (1 + M + δ) ^ #s := by
          rw [hpow]
          ring

/-- **Perturbing the roots of a product, coefficientwise.** Let `s` have `h` elements,
`‖z i‖ ≤ M` and `‖w i - z i‖ ≤ δ` for every `i ∈ s`. Then every coefficient of
`∏ i ∈ s, (X - C (w i)) - ∏ i ∈ s, (X - C (z i))` has norm at most
`h δ (1 + M + δ) ^ (h - 1)`. -/
theorem norm_coeff_prod_X_sub_C_sub_prod_X_sub_C_le (s : Finset ι) (z w : ι → R) {M δ : ℝ}
    (hz : ∀ i ∈ s, ‖z i‖ ≤ M) (hw : ∀ i ∈ s, ‖w i - z i‖ ≤ δ) (n : ℕ) :
    ‖(∏ i ∈ s, (X - C (w i)) - ∏ i ∈ s, (X - C (z i))).coeff n‖ ≤
      #s * δ * (1 + M + δ) ^ (#s - 1) :=
  (norm_coeff_le_l1Norm _ n).trans (l1Norm_prod_X_sub_C_sub_prod_X_sub_C_le s z w hz hw)

/-- **A safe precision for the roots of a product.** Let `s` have `h` elements, `‖z i‖ ≤ M` and
`‖w i - z i‖ ≤ δ` for every `i ∈ s`. If `4 h (2 + M) ^ (h - 1) δ < 1`, every coefficient of
`∏ i ∈ s, (X - C (w i))` differs from the corresponding coefficient of
`∏ i ∈ s, (X - C (z i))` by less than `1 / 4`. -/
theorem norm_coeff_prod_X_sub_C_sub_prod_X_sub_C_lt_one_div_four (s : Finset ι) (z w : ι → R)
    {M δ : ℝ} (hz : ∀ i ∈ s, ‖z i‖ ≤ M) (hw : ∀ i ∈ s, ‖w i - z i‖ ≤ δ)
    (hδ : 4 * #s * (2 + M) ^ (#s - 1) * δ < 1) (n : ℕ) :
    ‖(∏ i ∈ s, (X - C (w i)) - ∏ i ∈ s, (X - C (z i))).coeff n‖ < 1 / 4 := by
  refine (norm_coeff_prod_X_sub_C_sub_prod_X_sub_C_le s z w hz hw n).trans_lt ?_
  obtain rfl | ⟨a, ha⟩ := s.eq_empty_or_nonempty
  · norm_num
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans (hw a ha)
  have hM : 0 ≤ M := (norm_nonneg _).trans (hz a ha)
  have hs : (1 : ℝ) ≤ #s := by exact_mod_cast Finset.card_pos.2 ⟨a, ha⟩
  -- the hypothesis forces `δ ≤ 1`, so `1 + M + δ ≤ 2 + M`
  have hδ1 : δ ≤ 1 := by
    have : 1 ≤ 4 * #s * (2 + M) ^ (#s - 1) := by
      have := one_le_pow₀ (n := #s - 1) (by linarith : (1 : ℝ) ≤ 2 + M)
      nlinarith
    nlinarith
  have : (1 + M + δ) ^ (#s - 1) ≤ (2 + M) ^ (#s - 1) :=
    pow_le_pow_left₀ (by linarith) (by linarith) _
  nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) #s) hδ0]

end RootProduct

end Polynomial
