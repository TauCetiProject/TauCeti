/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Height.NumberField
public import TauCeti.Data.Finsupp.Interval
public import TauCeti.RingTheory.MvPolynomial.WeightedIndex

/-!
# Upper and lower bounds for the value of an auxiliary polynomial at a rational point

In the proof of Roth's theorem, an auxiliary polynomial `Q` in `n` variables with partial degrees
`degreeOf i Q ≤ r i` is evaluated at a point `β ∈ ℚⁿ` whose coordinates are very good rational
approximations of an algebraic number `α`. Two estimates for `|Q(β)|` then contradict each other.

* **Lower bound.** If `Q` has integer coefficients and `Q(β) ≠ 0`, then `∏ᵢ den(βᵢ) ^ rᵢ • Q(β)` is
  a nonzero integer, so `log |Q(β)| ≥ -∑ᵢ rᵢ log den(βᵢ)`.
* **Upper bound.** Expand `Q(β) = ∑_d (∂^d Q)(a) (β - a)^d` by Taylor's formula at a point `a`
  where `Q` has weighted index at least `t` with respect to the weights `r`. The terms of
  weight `∑ᵢ dᵢ / rᵢ < t` vanish. If `|βᵢ - aᵢ| ≤ H(βᵢ) ^ (-κ)` and `rᵢ h(βᵢ) ≥ D`, each of the
  remaining terms has `∏ᵢ |βᵢ - aᵢ| ^ dᵢ ≤ exp(-κ D t)`, while the Hasse jets `(∂^d Q)(a)` are
  bounded in terms of the coefficients of `Q`. For coefficients bounded by `B` this gives
  `|Q(β)| ≤ B (∏ᵢ (rᵢ + 1))² ∏ᵢ (2 max(1, |aᵢ|)) ^ rᵢ exp(-κ D t)`.

Here `H` and `h` are Mathlib's multiplicative and logarithmic heights `Height.mulHeight₁` and
`Height.logHeight₁` on `ℚ`. In Roth's theorem `a` is the diagonal point `(α, …, α)`.

## Main results

* `TauCeti.one_le_prod_den_pow_mul_abs_eval`: `1 ≤ ∏ᵢ den(βᵢ) ^ rᵢ * |Q(β)|` for `Q ∈ ℤ[X]` with
  `Q(β) ≠ 0`.
* `TauCeti.neg_sum_mul_log_den_le_log_abs_eval`: its logarithmic form
  `-∑ᵢ rᵢ log den(βᵢ) ≤ log |Q(β)|`.
* `TauCeti.prod_abs_sub_pow_le_exp`: `∏ᵢ |βᵢ - aᵢ| ^ dᵢ ≤ exp(-κ D t)` for a multi-index `d ≤ r`
  of weight at least `t`.
* `TauCeti.abs_eval_le_of_le_weightedIndex`: the upper bound for a real polynomial of weighted
  index at least `t` at `a`.
* `TauCeti.log_abs_eval_le_of_le_weightedIndex`: its logarithmic form
  `log |Q(β)| ≤ log B + ∑ᵢ rᵢ (log 2 + log max(1, |aᵢ|)) + 2 ∑ᵢ log(rᵢ + 1) - κ D t`.

## References

* L. Pottmeyer, [*Diophantine Approximation*](https://esaga.uni-due.de/f/lukas.pottmeyer/DioApp.pdf)
  (2022), §3.5.3 and Exercise 3.10.
-/

public section

open Finset MvPolynomial Height

namespace TauCeti

variable {σ : Type*} [Fintype σ]

/-! ### The lower bound -/

/-- **Lower bound for an integer polynomial at a rational point.** If `Q ∈ ℤ[X]` has partial
degrees `degreeOf i Q ≤ r i` and does not vanish at `β ∈ ℚ^σ`, then
`1 ≤ ∏ᵢ den(βᵢ) ^ rᵢ * |Q(β)|`: clearing denominators turns `Q(β)` into a nonzero integer. -/
theorem one_le_prod_den_pow_mul_abs_eval {Q : MvPolynomial σ ℤ} {r : σ → ℕ}
    (hdeg : ∀ i, Q.degreeOf i ≤ r i) (β : σ → ℚ)
    (hQ : eval β (map (Int.castRingHom ℚ) Q) ≠ 0) :
    1 ≤ (∏ i, ((β i).den : ℚ) ^ r i) * |eval β (map (Int.castRingHom ℚ) Q)| := by
  set c : ℚ := ∏ i, ((β i).den : ℚ) ^ r i
  have hc : 0 < c := by positivity
  -- Each monomial `∏ᵢ βᵢ ^ μᵢ` of `Q(β)` has `μᵢ ≤ rᵢ`, so `c ∏ᵢ βᵢ ^ μᵢ` is an integer.
  obtain ⟨z, hz⟩ : c * eval β (map (Int.castRingHom ℚ) Q) ∈ (Int.castRingHom ℚ).range := by
    rw [eval_eq', mul_sum]
    refine Subring.sum_mem _ fun μ hμ ↦ ?_
    rw [coeff_map, mul_left_comm, ← prod_mul_distrib]
    refine Subring.mul_mem _ ⟨_, rfl⟩ (Subring.prod_mem _ fun i _ ↦ ?_)
    have hμi : μ i ≤ r i :=
      (monomial_le_degreeOf i (support_map_subset _ _ hμ)).trans (hdeg i)
    refine ⟨(β i).num ^ μ i * (β i).den ^ (r i - μ i), ?_⟩
    rw [← pow_mul_pow_sub ((β i).den : ℚ) hμi, eq_intCast]
    push_cast [← Rat.den_mul_eq_num]
    ring
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact hQ (by simpa [hc.ne'] using hz.symm)
  calc (1 : ℚ) ≤ |(z : ℚ)| := by exact_mod_cast Int.one_le_abs hz0
    _ = c * |eval β (map (Int.castRingHom ℚ) Q)| := by
      rw [eq_intCast] at hz
      rw [hz, abs_mul, abs_of_pos hc]

/-- **Lower bound for an integer polynomial at a rational point**, logarithmic form: if
`Q ∈ ℤ[X]` has partial degrees `degreeOf i Q ≤ r i` and `Q(β) ≠ 0` for `β ∈ ℚ^σ`, then
`-∑ᵢ rᵢ log den(βᵢ) ≤ log |Q(β)|`. -/
theorem neg_sum_mul_log_den_le_log_abs_eval {Q : MvPolynomial σ ℤ} {r : σ → ℕ}
    (hdeg : ∀ i, Q.degreeOf i ≤ r i) (β : σ → ℚ)
    (hQ : eval (fun i ↦ (β i : ℝ)) (map (Int.castRingHom ℝ) Q) ≠ 0) :
    -∑ i, (r i : ℝ) * Real.log (β i).den ≤
      Real.log |eval (fun i ↦ (β i : ℝ)) (map (Int.castRingHom ℝ) Q)| := by
  have hcast : eval (fun i ↦ (β i : ℝ)) (map (Int.castRingHom ℝ) Q) =
      ((eval β (map (Int.castRingHom ℚ) Q) : ℚ) : ℝ) := by
    simp [eval_map, eval₂_eq']
  rw [hcast] at hQ ⊢
  have h1 : (1 : ℝ) ≤
      (∏ i, ((β i).den : ℝ) ^ r i) * |(eval β (map (Int.castRingHom ℚ) Q) : ℝ)| := by
    exact_mod_cast one_le_prod_den_pow_mul_abs_eval hdeg β (by exact_mod_cast hQ)
  have hlog := Real.log_nonneg h1
  simp (disch := first | positivity | intro i _; positivity) only [Real.log_mul,
    Real.log_prod, Real.log_pow] at hlog
  linarith

/-! ### The upper bound -/

/-- **Smallness of a high-weight monomial in the approximation errors.** If `β ∈ ℚ^σ` satisfies
`|βᵢ - aᵢ| ≤ H(βᵢ) ^ (-κ)` and `D ≤ rᵢ h(βᵢ)` for all `i`, with `κ, D ≥ 0`, then every
multi-index `d ≤ r` of weight `∑ᵢ dᵢ / rᵢ ≥ t` has `∏ᵢ |βᵢ - aᵢ| ^ dᵢ ≤ exp(-κ D t)`. -/
theorem prod_abs_sub_pow_le_exp {r : σ → ℕ} {a : σ → ℝ} {β : σ → ℚ} {κ D t : ℝ}
    (hκ : 0 ≤ κ) (hD : 0 ≤ D) (hβ : ∀ i, |(β i : ℝ) - a i| ≤ mulHeight₁ (β i) ^ (-κ))
    (hr : ∀ i, D ≤ r i * logHeight₁ (β i)) {d : σ →₀ ℕ} (hdr : ∀ i, d i ≤ r i)
    (ht : t ≤ ∑ i, (d i : ℝ) / r i) :
    ∏ i, |(β i : ℝ) - a i| ^ d i ≤ Real.exp (-(κ * D * t)) := by
  have hpow (i : σ) : mulHeight₁ (β i) ^ (-κ) = Real.exp (-(κ * logHeight₁ (β i))) := by
    rw [Real.rpow_def_of_pos (mulHeight₁_pos _), logHeight₁_eq_log_mulHeight₁]
    ring_nf
  -- `D t ≤ ∑ᵢ dᵢ D / rᵢ ≤ ∑ᵢ dᵢ h(βᵢ)`, using `dᵢ = 0` whenever `rᵢ = 0`.
  have hsum : D * t ≤ ∑ i, (d i : ℝ) * logHeight₁ (β i) := by
    refine (mul_le_mul_of_nonneg_left ht hD).trans ?_
    rw [mul_sum]
    refine sum_le_sum fun i _ ↦ ?_
    rcases Nat.eq_zero_or_pos (r i) with h | h
    · have : d i = 0 := Nat.le_zero.1 (h ▸ hdr i)
      simp [this]
    · have hri : (0 : ℝ) < r i := Nat.cast_pos.2 h
      rw [mul_div_assoc', div_le_iff₀ hri, mul_comm D, mul_assoc]
      exact mul_le_mul_of_nonneg_left (by linarith [hr i]) (Nat.cast_nonneg _)
  calc ∏ i, |(β i : ℝ) - a i| ^ d i
      ≤ ∏ i, Real.exp (-(κ * logHeight₁ (β i))) ^ d i :=
        prod_le_prod₀ (fun i _ ↦ by positivity) fun i _ ↦
          pow_le_pow_left₀ (abs_nonneg _) (hpow i ▸ hβ i) _
    _ = Real.exp (-(κ * ∑ i, (d i : ℝ) * logHeight₁ (β i))) := by
        simp only [← Real.exp_nat_mul, ← Real.exp_sum, mul_sum]
        congr 1
        rw [← sum_neg_distrib]
        exact sum_congr rfl fun i _ ↦ by ring
    _ ≤ Real.exp (-(κ * D * t)) := by
        rw [Real.exp_le_exp, mul_assoc]
        exact neg_le_neg (mul_le_mul_of_nonneg_left hsum hκ)

/-- **Upper bound for an auxiliary polynomial at a rational point.** Let `P` be a real polynomial
with partial degrees `degreeOf i P ≤ r i`, coefficients bounded by `B`, and weighted index at
least `t` at `a` with respect to the weights `r`. If `β ∈ ℚ^σ` satisfies
`|βᵢ - aᵢ| ≤ H(βᵢ) ^ (-κ)` and `D ≤ rᵢ h(βᵢ)` for all `i`, with `κ, D ≥ 0`, then
`|P(β)| ≤ B (∏ᵢ (rᵢ + 1))² ∏ᵢ (2 max(1, |aᵢ|)) ^ rᵢ exp(-κ D t)`. -/
theorem abs_eval_le_of_le_weightedIndex {P : MvPolynomial σ ℝ} {r : σ → ℕ}
    (hdeg : ∀ i, P.degreeOf i ≤ r i) {B : ℝ} (hB : ∀ μ, |P.coeff μ| ≤ B) {a : σ → ℝ} {t : ℝ}
    (ht : ENNReal.ofReal t ≤ weightedIndex r a P) {β : σ → ℚ} {κ D : ℝ} (hκ : 0 ≤ κ)
    (hD : 0 ≤ D) (hβ : ∀ i, |(β i : ℝ) - a i| ≤ mulHeight₁ (β i) ^ (-κ))
    (hr : ∀ i, D ≤ r i * logHeight₁ (β i)) :
    |eval (fun i ↦ (β i : ℝ)) P| ≤
      B * (∏ i, ((r i : ℝ) + 1)) ^ 2 * (∏ i, (2 * max 1 |a i|) ^ r i) *
        Real.exp (-(κ * D * t)) := by
  set T := taylor a P
  set C := B * (∏ i, ((r i : ℝ) + 1)) * ∏ i, (2 * max 1 |a i|) ^ r i
  have hC : 0 ≤ C := by
    have := (abs_nonneg _).trans (hB 0)
    positivity
  -- Every Taylor coefficient `[Y^d] P(a + Y) = (∂^d P)(a)` that is nonzero has `d ≤ r` and
  -- weight at least `t`.
  have hT (d) (hd : d ∈ T.support) :
      (∀ i, d i ≤ r i) ∧ t ≤ ∑ i, (d i : ℝ) / r i := by
    rw [mem_support_iff, coeff_taylor] at hd
    exact le_sum_div_of_le_weightedIndex hdeg ht hd
  have hβa : (fun i ↦ (β i : ℝ)) = (fun i ↦ (β i : ℝ) - a i) + a := by
    ext i
    simp
  rw [hβa, ← eval_taylor, eval_eq']
  refine (abs_sum_le_sum_abs _ _).trans <|
    (Finsupp.sum_le_prod_mul_of_forall_le (C := C * Real.exp (-(κ * D * t)))
      (fun d hd ↦ (hT d hd).1) (fun d hd ↦ ?_) (mul_nonneg hC (Real.exp_pos _).le)).trans_eq
      (by ring)
  rw [abs_mul, abs_prod]
  simp only [abs_pow]
  rw [coeff_taylor]
  exact mul_le_mul (abs_eval_hasseDeriv_le hdeg hB a d)
    (prod_abs_sub_pow_le_exp hκ hD hβ hr (hT d hd).1 (hT d hd).2) (by positivity) hC

/-- **Upper bound for an auxiliary polynomial at a rational point**, logarithmic form: under the
hypotheses of `TauCeti.abs_eval_le_of_le_weightedIndex`, if moreover `P(β) ≠ 0`, then
`log |P(β)| ≤ log B + ∑ᵢ rᵢ (log 2 + log max(1, |aᵢ|)) + 2 ∑ᵢ log(rᵢ + 1) - κ D t`. -/
theorem log_abs_eval_le_of_le_weightedIndex {P : MvPolynomial σ ℝ} {r : σ → ℕ}
    (hdeg : ∀ i, P.degreeOf i ≤ r i) {B : ℝ} (hB : ∀ μ, |P.coeff μ| ≤ B) {a : σ → ℝ} {t : ℝ}
    (ht : ENNReal.ofReal t ≤ weightedIndex r a P) {β : σ → ℚ} {κ D : ℝ} (hκ : 0 ≤ κ)
    (hD : 0 ≤ D) (hβ : ∀ i, |(β i : ℝ) - a i| ≤ mulHeight₁ (β i) ^ (-κ))
    (hr : ∀ i, D ≤ r i * logHeight₁ (β i)) (hP : eval (fun i ↦ (β i : ℝ)) P ≠ 0) :
    Real.log |eval (fun i ↦ (β i : ℝ)) P| ≤
      Real.log B + ∑ i, (r i : ℝ) * (Real.log 2 + Real.log (max 1 |a i|)) +
        2 * ∑ i, Real.log ((r i : ℝ) + 1) - κ * D * t := by
  have h := abs_eval_le_of_le_weightedIndex hdeg hB ht hκ hD hβ hr
  have hB0 : 0 < B := by
    by_contra! hB0
    have hK : 0 ≤ (∏ i, ((r i : ℝ) + 1)) ^ 2 * (∏ i, (2 * max 1 |a i|) ^ r i) *
        Real.exp (-(κ * D * t)) := by positivity
    linarith [abs_pos.2 hP, mul_nonpos_of_nonpos_of_nonneg hB0 hK]
  refine (Real.log_le_log (abs_pos.2 hP) h).trans_eq ?_
  simp (disch := first | positivity | intro i _; positivity) only [Real.log_mul, Real.log_exp,
    Real.log_pow, Real.log_prod]
  push_cast
  ring

end TauCeti
