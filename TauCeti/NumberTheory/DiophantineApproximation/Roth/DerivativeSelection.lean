/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import TauCeti.RingTheory.MvPolynomial.WeightedIndex

/-!
# Choosing a Hasse derivative of Roth's auxiliary polynomial

In the proof of Roth's theorem, an integer auxiliary polynomial `P` vanishes to a high index at
the diagonal point `(α, …, α)`, while Roth's index estimate shows that its index at a tuple `β` of
good rational approximations of `α` is small. The final step needs a polynomial that does not
vanish at `β` at all. It is obtained as a Hasse derivative `Q = ∂^d P`, where `d` is a jet of `P`
at `β` of minimal weight. Since `∂^d` lowers indices by at most the weight of `d`, the index of
`Q` at the diagonal point is still large, and the coefficients of `Q` are at most `2 ^ ∑ᵢ rᵢ`
times those of `P`, where the `rᵢ` bound the partial degrees of `P`.

The value `Q(β)` is then a nonzero rational number which is bounded from above using the large
index of `Q` at the diagonal point, and from below by the denominators of `β`. Comparing the two
bounds yields the contradiction which proves Roth's theorem.

## Main results

* `TauCeti.exists_hasseDeriv_eval_ne_zero`: if `P` has finite index at `b`, some Hasse
  derivative `Q = ∂^d P` satisfies `Q(b) ≠ 0` and `Ind_a(P) - Ind_b(P) ≤ Ind_a(Q)` at every
  other point `a`, and has the same partial degree bounds and coefficients at most
  `2 ^ ∑ᵢ rᵢ` times as large.
* `TauCeti.exists_roth_hasseDeriv`: the same choice with the parameters of the proof of Roth's
  theorem. An index at least `(n / 2) (1 - ε)` at `a` and an index at most `5 n ε / 2` at `b`
  leave the derivative an index at least `(1 / 2 - 3 ε) n` at `a`, and coefficients at most
  `exp (C₁ ∑ᵢ rᵢ)` with `∑ᵢ rᵢ ≤ 2 D / L` become coefficients at most `exp (4 C₁ D / L)`.

## References

* L. Pottmeyer, [*Diophantine Approximation*](https://esaga.uni-due.de/f/lukas.pottmeyer/DioApp.pdf)
  (2022), §3.5, Lemma 3.5.7.
-/

public section

namespace TauCeti

open MvPolynomial Finset
open scoped ENNReal

variable {σ F K : Type*} [Fintype σ] [CommRing F] [CommRing K]

/-- **Choice of a nonvanishing Hasse derivative.** Let `P` be an integer polynomial with partial
degrees `degreeOf i P ≤ r i` and coefficients of absolute value at most `B`. If the index of `P`
at a point `b` is finite, then some Hasse derivative `Q = ∂^d P` does not vanish at `b`, loses at
most the index of `P` at `b` from its index at every other point `a`, still has partial degrees at
most `r i`, and has coefficients of absolute value at most `2 ^ ∑ᵢ rᵢ * B`. -/
theorem exists_hasseDeriv_eval_ne_zero {P : MvPolynomial σ ℤ} {r : σ → ℕ}
    (hdeg : ∀ i, P.degreeOf i ≤ r i) {B : ℝ} (hB : ∀ μ, |(P.coeff μ : ℝ)| ≤ B) (a : σ → F)
    {b : σ → K} (hb : weightedIndex r b (P.map (Int.castRingHom K)) ≠ ⊤) :
    ∃ d : σ →₀ ℕ, eval b ((hasseDeriv d P).map (Int.castRingHom K)) ≠ 0 ∧
      weightedIndex r a (P.map (Int.castRingHom F)) -
          weightedIndex r b (P.map (Int.castRingHom K)) ≤
        weightedIndex r a ((hasseDeriv d P).map (Int.castRingHom F)) ∧
      (∀ i, (hasseDeriv d P).degreeOf i ≤ r i) ∧
      ∀ μ, |((hasseDeriv d P).coeff μ : ℝ)| ≤ 2 ^ (∑ i, r i) * B := by
  -- A jet of minimal weight at `b` is nonzero, and its weight is the index at `b`.
  obtain ⟨d, hd, hbd⟩ := exists_weightedIndex_eq_weight (r := r)
    (mt (weightedIndex_eq_top_of_taylor_eq_zero r) hb)
  rw [hasseDeriv_map] at hd
  refine ⟨d, hd, ?_, fun i ↦ (degreeOf_hasseDeriv_le d P i).trans ((Nat.sub_le _ _).trans (hdeg i)),
    fun μ ↦ ?_⟩
  · rw [hbd, tsub_le_iff_right, ← hasseDeriv_map]
    exact weightedIndex_le_weightedIndex_hasseDeriv_add r a d _
  -- The coefficient `[X^μ] ∂^d P` is `∏ⱼ (μⱼ + dⱼ choose dⱼ) [X^(μ + d)] P`, and each binomial
  -- coefficient is at most `2 ^ (μⱼ + dⱼ) ≤ 2 ^ rⱼ` when `[X^(μ + d)] P ≠ 0`.
  have hB₀ : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  rw [hasseDeriv_coeff, Int.cast_mul, abs_mul, Int.cast_natCast, Nat.abs_cast]
  by_cases hμ : P.coeff (μ + d) = 0
  · simp [hμ, hB₀]
  have hle (j : σ) : μ j + d j ≤ r j := by
    simpa using (monomial_le_degreeOf j (mem_support_iff.2 hμ)).trans (hdeg j)
  have hprod : (d.prod fun j k ↦ (μ j + k).choose k) ≤ 2 ^ ∑ i, r i := calc
    (d.prod fun j k ↦ (μ j + k).choose k) ≤ ∏ j ∈ d.support, 2 ^ r j :=
      prod_le_prod fun j _ ↦
        (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right two_pos (hle j))
    _ ≤ ∏ j, 2 ^ r j :=
      prod_le_prod_of_subset_of_one_le (subset_univ _) fun _ _ _ ↦ Nat.one_le_two_pow
    _ = 2 ^ ∑ i, r i := prod_pow_eq_pow_sum _ _ _
  exact mul_le_mul (by exact_mod_cast hprod) (hB _) (abs_nonneg _) (by positivity)

/-- **Pottmeyer, Lemma 3.5.7.** The choice of a nonvanishing Hasse derivative of Roth's
auxiliary polynomial. Let `P` be an integer polynomial in `n` variables with partial degrees
`degreeOf i P ≤ r i`, where `∑ᵢ rᵢ ≤ 2 D / L`, and with coefficients of absolute value at most
`exp (C₁ ∑ᵢ rᵢ)`, where `C₁ ≥ log 2`. Let `0 ≤ ε`. If the index of `P` is at least
`(n / 2) (1 - ε)` at `a` and at most `5 n ε / 2` at `b`, then some Hasse derivative
`Q = ∂^d P` does not vanish at `b`, has index at least `(1 / 2 - 3 ε) n` at `a`, has partial
degrees at most `r i`, and has coefficients of absolute value at most `exp (4 C₁ D / L)`. -/
theorem exists_roth_hasseDeriv {P : MvPolynomial σ ℤ} {r : σ → ℕ}
    (hdeg : ∀ i, P.degreeOf i ≤ r i) {ε C₁ D L : ℝ} (hε : 0 ≤ ε) (hC₁ : Real.log 2 ≤ C₁)
    (hr : ∑ i, (r i : ℝ) ≤ 2 * D / L)
    (hP : ∀ μ, |(P.coeff μ : ℝ)| ≤ Real.exp (C₁ * ∑ i, (r i : ℝ))) {a : σ → F} {b : σ → K}
    (ha : ENNReal.ofReal (Fintype.card σ / 2 * (1 - ε)) ≤
      weightedIndex r a (P.map (Int.castRingHom F)))
    (hb : weightedIndex r b (P.map (Int.castRingHom K)) ≤
      ENNReal.ofReal (5 * Fintype.card σ * ε / 2)) :
    ∃ d : σ →₀ ℕ, eval b ((hasseDeriv d P).map (Int.castRingHom K)) ≠ 0 ∧
      ENNReal.ofReal ((1 / 2 - 3 * ε) * Fintype.card σ) ≤
        weightedIndex r a ((hasseDeriv d P).map (Int.castRingHom F)) ∧
      (∀ i, (hasseDeriv d P).degreeOf i ≤ r i) ∧
      ∀ μ, |((hasseDeriv d P).coeff μ : ℝ)| ≤ Real.exp (4 * C₁ * D / L) := by
  obtain ⟨d, hd, hind, hdeg', hcoeff⟩ :=
    exists_hasseDeriv_eval_ne_zero hdeg hP a (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb)
  refine ⟨d, hd, le_trans ?_ (le_trans (tsub_le_tsub ha hb) hind), hdeg', fun μ ↦ ?_⟩
  · rw [← ENNReal.ofReal_sub _ (by positivity)]
    exact le_of_eq (congrArg ENNReal.ofReal (by ring))
  -- `2 ^ ∑ᵢ rᵢ * exp (C₁ ∑ᵢ rᵢ) = exp ((log 2 + C₁) ∑ᵢ rᵢ) ≤ exp (2 C₁ ∑ᵢ rᵢ)`.
  have hC₀ : 0 ≤ C₁ := (Real.log_nonneg one_le_two).trans hC₁
  have hr₀ : 0 ≤ ∑ i, (r i : ℝ) := by positivity
  refine (hcoeff μ).trans ?_
  rw [← Real.exp_log (two_pos (α := ℝ)), ← Real.exp_nat_mul, ← Real.exp_add, Nat.cast_sum]
  gcongr
  calc (∑ i, (r i : ℝ)) * Real.log 2 + C₁ * ∑ i, (r i : ℝ) ≤ 2 * C₁ * ∑ i, (r i : ℝ) := by
        nlinarith
    _ ≤ 2 * C₁ * (2 * D / L) := by gcongr
    _ = 4 * C₁ * D / L := by ring

end TauCeti
