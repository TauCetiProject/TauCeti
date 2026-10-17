/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Data.Finsupp.Interval
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
open scoped ENNReal

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
  have hc : 0 < c := prod_pos fun i _ ↦ pow_pos (Nat.cast_pos.2 (β i).den_pos) _
  -- Each monomial `∏ᵢ βᵢ ^ μᵢ` of `Q(β)` has `μᵢ ≤ rᵢ`, so `c ∏ᵢ βᵢ ^ μᵢ` is an integer.
  obtain ⟨z, hz⟩ : c * eval β (map (Int.castRingHom ℚ) Q) ∈ (Int.castRingHom ℚ).range := by
    rw [eval_eq', mul_sum]
    refine Subring.sum_mem _ fun μ hμ ↦ ?_
    rw [coeff_map, mul_left_comm, ← prod_mul_distrib]
    refine Subring.mul_mem _ ⟨_, rfl⟩ (Subring.prod_mem _ fun i _ ↦ ?_)
    have hμi : μ i ≤ r i :=
      (monomial_le_degreeOf i (support_map_subset _ _ hμ)).trans (hdeg i)
    refine ⟨(β i).num ^ μ i * (β i).den ^ (r i - μ i), ?_⟩
    rw [← pow_mul_pow_sub ((β i).den : ℚ) hμi, map_mul, map_pow, map_pow, eq_intCast,
      eq_intCast, Int.cast_natCast, ← Rat.den_mul_eq_num]
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
    rw [eval_map, eval_map, ← Rat.coe_castHom, eval₂_comp_left]
    congr 1
  rw [hcast] at hQ ⊢
  have h1 : (1 : ℝ) ≤
      (∏ i, ((β i).den : ℝ) ^ r i) * |(eval β (map (Int.castRingHom ℚ) Q) : ℝ)| := by
    exact_mod_cast one_le_prod_den_pow_mul_abs_eval hdeg β (by exact_mod_cast hQ)
  have hc : 0 < ∏ i, ((β i).den : ℝ) ^ r i :=
    prod_pos fun i _ ↦ pow_pos (Nat.cast_pos.2 (β i).den_pos) _
  have hlog := Real.log_nonneg h1
  rw [Real.log_mul hc.ne' (abs_pos.2 hQ).ne', Real.log_prod fun i _ ↦ (pow_pos
    (Nat.cast_pos.2 (β i).den_pos) _).ne'] at hlog
  simp only [Real.log_pow] at hlog
  linarith

/-! ### The upper bound -/

/-- A finite set of multi-indices bounded coordinatewise by `r` has at most `∏ᵢ (rᵢ + 1)`
elements. -/
private theorem card_le_prod_of_forall_le {s : Finset (σ →₀ ℕ)} {r : σ → ℕ}
    (h : ∀ m ∈ s, ∀ i, m i ≤ r i) : (#s : ℝ) ≤ ∏ i, ((r i : ℝ) + 1) := by
  classical
  set f : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm r
  have hs : s ⊆ Iic f := fun m hm ↦ mem_Iic.2 fun i ↦ by simpa [f] using h m hm i
  have hf : #(Iic f) = ∏ i, (r i + 1) := by
    rw [Finsupp.card_Iic, prod_subset (subset_univ _) fun i _ hi ↦ by
      simp [f, Finsupp.notMem_support_iff.1 hi]]
    simp [f]
  exact_mod_cast (card_le_card hs).trans hf.le

/-- The jets of a real polynomial with partial degrees `degreeOf i P ≤ r i` and coefficients
bounded by `B` are bounded at every point `a`:
`|(∂^d P)(a)| ≤ B ∏ᵢ (rᵢ + 1) ∏ᵢ (2 max(1, |aᵢ|)) ^ rᵢ`. -/
private theorem abs_eval_hasseDeriv_le {P : MvPolynomial σ ℝ} {r : σ → ℕ}
    (hdeg : ∀ i, P.degreeOf i ≤ r i) {B : ℝ} (hB : ∀ μ, |P.coeff μ| ≤ B) (a : σ → ℝ)
    (d : σ →₀ ℕ) :
    |eval a (hasseDeriv d P)| ≤
      B * (∏ i, ((r i : ℝ) + 1)) * ∏ i, (2 * max 1 |a i|) ^ r i := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  -- A monomial `X^m` of `∂^d P` comes from the monomial `X^(m + d)` of `P`.
  have hsupp (m) (hm : m ∈ (hasseDeriv d P).support) (i : σ) : (m + d) i ≤ r i := by
    rw [mem_support_iff, hasseDeriv_coeff] at hm
    exact (monomial_le_degreeOf i (mem_support_iff.2 (right_ne_zero_of_mul hm))).trans (hdeg i)
  have hle (m) (hm : m ∈ (hasseDeriv d P).support) (i : σ) : m i ≤ r i :=
    (Nat.le_add_right _ _).trans (by simpa using hsupp m hm i)
  have hterm (m) (hm : m ∈ (hasseDeriv d P).support) :
      |(hasseDeriv d P).coeff m * ∏ i, a i ^ m i| ≤ B * ∏ i, (2 * max 1 |a i|) ^ r i := by
    have h2 : (2 : ℝ) ^ (m + d).degree ≤ ∏ i, (2 : ℝ) ^ r i := by
      rw [prod_pow_eq_pow_sum, Finsupp.degree_eq_sum]
      exact pow_le_pow_right₀ one_le_two (sum_le_sum fun i _ ↦ hsupp m hm i)
    have ha : ∏ i, |a i| ^ m i ≤ ∏ i, max 1 |a i| ^ r i :=
      prod_le_prod₀ (fun i _ ↦ by positivity) fun i _ ↦
        (pow_le_pow_left₀ (abs_nonneg _) (le_max_right _ _) _).trans <|
          pow_le_pow_right₀ (le_max_left _ _) (hle m hm i)
    rw [abs_mul, abs_prod]
    simp only [abs_pow]
    calc |(hasseDeriv d P).coeff m| * ∏ i, |a i| ^ m i
        ≤ (2 ^ (m + d).degree * |P.coeff (m + d)|) * ∏ i, max 1 |a i| ^ r i :=
          mul_le_mul (abv_coeff_hasseDeriv_le AbsoluteValue.abs d m P) ha
            (prod_nonneg fun i _ ↦ by positivity) (by positivity)
      _ ≤ ((∏ i, (2 : ℝ) ^ r i) * B) * ∏ i, max 1 |a i| ^ r i := by
          gcongr
          exact hB _
      _ = B * ∏ i, (2 * max 1 |a i|) ^ r i := by
          simp only [mul_pow, prod_mul_distrib]
          ring
  have hcard := card_le_prod_of_forall_le hle
  rw [eval_eq']
  calc |∑ m ∈ (hasseDeriv d P).support, (hasseDeriv d P).coeff m * ∏ i, a i ^ m i|
      ≤ ∑ m ∈ (hasseDeriv d P).support, B * ∏ i, (2 * max 1 |a i|) ^ r i :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum hterm)
    _ = #(hasseDeriv d P).support * (B * ∏ i, (2 * max 1 |a i|) ^ r i) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ (∏ i, ((r i : ℝ) + 1)) * (B * ∏ i, (2 * max 1 |a i|) ^ r i) := by
        gcongr
    _ = B * (∏ i, ((r i : ℝ) + 1)) * ∏ i, (2 * max 1 |a i|) ^ r i := by ring

/-- A nonzero jet of a polynomial with partial degrees `degreeOf i P ≤ r i` and weighted index at
least `t` has weight `t ≤ ∑ᵢ dᵢ / rᵢ`, computed in `ℝ`. -/
private theorem le_sum_div_of_le_weightedIndex {R : Type*} [CommSemiring R]
    {P : MvPolynomial σ R} {r : σ → ℕ} (hdeg : ∀ i, P.degreeOf i ≤ r i) {a : σ → R} {t : ℝ}
    (ht : ENNReal.ofReal t ≤ weightedIndex r a P) {d : σ →₀ ℕ}
    (hd : eval a (hasseDeriv d P) ≠ 0) :
    (∀ i, d i ≤ r i) ∧ t ≤ ∑ i, (d i : ℝ) / r i := by
  have hdr (i : σ) : d i ≤ r i := by
    by_contra h
    exact hd (by rw [hasseDeriv_eq_zero_of_degreeOf_lt (i := i) (by have := hdeg i; omega),
      map_zero])
  refine ⟨hdr, ?_⟩
  have hw : d.weight (fun j ↦ (r j : ℝ≥0∞)⁻¹) = ENNReal.ofReal (∑ i, (d i : ℝ) / r i) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun i _ ↦ by positivity, Finsupp.weight_apply,
      Finsupp.sum_fintype _ _ (by simp)]
    refine sum_congr rfl fun i _ ↦ ?_
    rcases Nat.eq_zero_or_pos (d i) with h | h
    · simp [h]
    · rw [ENNReal.ofReal_div_of_pos (Nat.cast_pos.2 (h.trans_le (hdr i))),
        ENNReal.ofReal_natCast, ENNReal.ofReal_natCast, nsmul_eq_mul, div_eq_mul_inv]
  exact (ENNReal.ofReal_le_ofReal_iff (sum_nonneg fun i _ ↦ by positivity)).1
    (ht.trans ((weightedIndex_le hd).trans_eq hw))

/-- A jet of weight at least `t`, paired with the differences `βᵢ - aᵢ` of rational
approximations, is exponentially small: `∏ᵢ |βᵢ - aᵢ| ^ dᵢ ≤ exp(-κ D t)`. -/
private theorem prod_abs_sub_pow_le_exp {r : σ → ℕ} {a : σ → ℝ} {β : σ → ℚ} {κ D t : ℝ}
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
  have hcard : (#T.support : ℝ) ≤ ∏ i, ((r i : ℝ) + 1) :=
    card_le_prod_of_forall_le fun d hd ↦ (hT d hd).1
  have hβa : (fun i ↦ (β i : ℝ)) = (fun i ↦ (β i : ℝ) - a i) + a := by
    ext i
    simp
  rw [hβa, ← eval_taylor, eval_eq']
  calc |∑ d ∈ T.support, T.coeff d * ∏ i, ((β i : ℝ) - a i) ^ d i|
      ≤ ∑ d ∈ T.support, C * Real.exp (-(κ * D * t)) := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d hd ↦ ?_)
        rw [abs_mul, abs_prod]
        simp only [abs_pow]
        rw [coeff_taylor]
        exact mul_le_mul (abs_eval_hasseDeriv_le hdeg hB a d)
          (prod_abs_sub_pow_le_exp hκ hD hβ hr (hT d hd).1 (hT d hd).2)
          (prod_nonneg fun i _ ↦ by positivity) hC
    _ = #T.support * (C * Real.exp (-(κ * D * t))) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (∏ i, ((r i : ℝ) + 1)) * (C * Real.exp (-(κ * D * t))) := by gcongr
    _ = _ := by ring

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
  have hX : 0 < ∏ i, ((r i : ℝ) + 1) := prod_pos fun i _ ↦ by positivity
  have hY : 0 < ∏ i, (2 * max 1 |a i|) ^ r i :=
    prod_pos fun i _ ↦ pow_pos (mul_pos two_pos (one_pos.trans_le (le_max_left _ _))) _
  have hB0 : 0 < B := by
    by_contra hB0
    have : B * (∏ i, ((r i : ℝ) + 1)) ^ 2 * (∏ i, (2 * max 1 |a i|) ^ r i) *
        Real.exp (-(κ * D * t)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hB0) (by positivity)) hY.le) (by positivity)
    exact (abs_pos.2 hP).not_ge (h.trans this)
  refine (Real.log_le_log (abs_pos.2 hP) h).trans_eq ?_
  rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp,
    Real.log_mul (by positivity) hY.ne', Real.log_mul hB0.ne' (by positivity), Real.log_pow,
    Real.log_prod fun i _ ↦ by positivity, Real.log_prod fun i _ ↦ (pow_pos (mul_pos two_pos
      (one_pos.trans_le (le_max_left _ _))) _).ne']
  simp only [Real.log_pow, Real.log_mul two_ne_zero
    (one_pos.trans_le (le_max_left 1 _)).ne']
  push_cast
  ring

end TauCeti
