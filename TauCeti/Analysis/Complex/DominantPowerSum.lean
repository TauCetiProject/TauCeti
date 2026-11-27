/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Field.GeomSum
import TauCeti.Analysis.Complex.Basic
import TauCeti.Analysis.SpecialFunctions.Trigonometric.FejerSum

/-!
# Power sums with a dominant term

Let `y_1, …, y_N` be complex numbers, `N ≤ L`, one of which has modulus at least `1/(1 + x)`.
If the real parts of their power sums are small for every exponent,
`re ∑ y_i ^ j ≤ j δ + L r ^ j` for `j ≥ 1` with `(1 + x) r ≤ ρ₀ < 1`, then `x` cannot be small:
`x ≥ log (1/(C L δ))/(C L)` with `C = 144 (1 + ρ₀)/(1 - ρ₀)`. This one-sided power-sum
inequality, which tolerates the error `L r ^ j` at every `j`, is the power-sum input of the
Deuring–Heilbronn repulsion of the zeros of Dirichlet `L`-functions.

The proof averages the hypothesis against the Fejér weights
`c_j = (1 - j/(J+1)) (1 + cos jθ)`, `1 ≤ j ≤ J`, where `θ` is the argument of a point of largest
modulus. By the bounds of `TauCeti.Analysis.SpecialFunctions.Trigonometric.FejerSum`, the
weighted sum `∑_j c_j re (w ^ j)` is at least `-1` on the closed unit disc
(`Complex.neg_one_le_sum_one_sub_div_mul_one_add_cos_mul_re_pow`) and at least `J/4 - 3/4` at
`w = e^{iθ}` (`Real.div_four_sub_le_sum_one_sub_div_mul_one_add_cos_mul_cos`). Applied to the
points rescaled by the largest modulus, these bounds are compared with the hypothesis for
`J = ⌈8 L (1 + ρ₀)/(1 - ρ₀)⌉`.

Multisets represent the points with repetitions, as for the zeros of an analytic function
counted with multiplicity (`AnalyticOnNhd.zeroMultiset` in
`TauCeti.Analysis.Analytic.ZeroCount`). The bound `L` is real, as in the application,
where it is a multiple of `log (q (|γ| + 2))`.

## Main results

* `Complex.sum_map_sum_mul_re_pow`: summing a weighted sum of real parts of powers over a
  rescaled multiset gives the weighted sum of the real parts of its power sums.
* `Complex.one_le_mul_exp_of_re_sum_pow_le`: power sums with a dominant term, in the form
  `1 ≤ 144 K L δ exp (9 K L x)` with `K = (1 + ρ₀)/(1 - ρ₀)`.
* `Complex.log_one_div_div_le_of_re_sum_pow_le`: power sums with a dominant term, solved for
  `x`.
* `Complex.log_one_div_div_le_of_re_sum_pow_le_of_le_half`: the form with `r = 1/2`,
  `x ≤ 1/2` and the constant `2016`.

## References

* L. Alpöge's Lean formalization of the Riemann hypothesis for Dirichlet `L`-functions,
  <https://github.com/leanprover-community/riemann-hypothesis>, is the source of the form with
  `r = 1/2` (there with the constant `2080`) and of the route through the Fejér weights; it
  derives the Deuring–Heilbronn repulsion from them.
* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, AMS Colloquium Publications 53 (2004),
  Chapter 18 (the Deuring–Heilbronn phenomenon).
-/

public section

open Finset Complex

namespace Complex

/-- Summing `∑_{j ∈ S} c_j re ((t y) ^ j)` over the points `y` of a multiset `s`, for a real
scale `t`, gives `∑_{j ∈ S} c_j t ^ j re (∑_{y ∈ s} y ^ j)`. -/
theorem sum_map_sum_mul_re_pow (s : Multiset ℂ) (S : Finset ℕ) (c : ℕ → ℝ) (t : ℝ) :
    (s.map fun y ↦ ∑ j ∈ S, c j * (((t : ℂ) * y) ^ j).re).sum =
      ∑ j ∈ S, c j * t ^ j * ((s.map (· ^ j)).sum).re := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    rw [ih, ← sum_add_distrib]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [mul_pow, ← ofReal_pow, re_ofReal_mul, add_re]
    ring

/-- A multiset with a point and at most `L` elements has `1 ≤ L`. -/
private theorem one_le_of_card_le {s : Multiset ℂ} {L : ℝ} {y : ℂ} (hy : y ∈ s)
    (hs : (Multiset.card s : ℝ) ≤ L) : 1 ≤ L :=
  le_trans (by exact_mod_cast Multiset.card_pos_iff_exists_mem.2 ⟨y, hy⟩) hs

/-- `(1 + x) r ≤ ρ₀` with `0 ≤ x` and `0 ≤ r` forces `0 ≤ ρ₀`. -/
private theorem nonneg_of_one_add_mul_le {r ρ₀ x : ℝ} (hx : 0 ≤ x) (hr : 0 ≤ r)
    (hxr : (1 + x) * r ≤ ρ₀) : 0 ≤ ρ₀ :=
  (mul_nonneg (by linarith) hr).trans hxr

/-- The lower bound of the Fejér-weighted power sums: rescaled by the largest
modulus `‖y₁‖`, the dominant point contributes at least `J/4 - 3/4` and every other point at
least `-1`. -/
private theorem le_sum_map_sum_fejer_cos_mul_re_pow (s : Multiset ℂ) (J : ℕ) {y₁ : ℂ}
    (hy₁ : y₁ ∈ s) (hmax : ∀ y ∈ s, ‖y‖ ≤ ‖y₁‖) (hR : 0 < ‖y₁‖) :
    (J : ℝ) / 4 - 3 / 4 - (Multiset.card s - 1) ≤
      (s.map fun y ↦ ∑ j ∈ Icc 1 J, (1 - j / (J + 1 : ℝ)) * (1 + Real.cos (j * arg y₁)) *
        ((((‖y₁‖⁻¹ : ℝ) : ℂ) * y) ^ j).re).sum := by
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem hy₁
  have h₁ : ((‖y₁‖⁻¹ : ℝ) : ℂ) * y₁ = exp (arg y₁ * I) := by
    calc ((‖y₁‖⁻¹ : ℝ) : ℂ) * y₁ = ((‖y₁‖⁻¹ : ℝ) : ℂ) * (‖y₁‖ * exp (arg y₁ * I)) := by
          rw [norm_mul_exp_arg_mul_I]
      _ = exp (arg y₁ * I) := by
          rw [← mul_assoc, ← ofReal_mul, inv_mul_cancel₀ hR.ne', ofReal_one, one_mul]
  have ht : (Multiset.card t : ℝ) • (-1 : ℝ) ≤ (t.map fun y ↦ ∑ j ∈ Icc 1 J,
      (1 - j / (J + 1 : ℝ)) * (1 + Real.cos (j * arg y₁)) *
        ((((‖y₁‖⁻¹ : ℝ) : ℂ) * y) ^ j).re).sum := by
    rw [Nat.cast_smul_eq_nsmul, ← Multiset.card_map _ t]
    refine Multiset.card_nsmul_le_sum fun z hz ↦ ?_
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hz
    refine neg_one_le_sum_one_sub_div_mul_one_add_cos_mul_re_pow J _ ?_
    rw [norm_mul, norm_real, Real.norm_of_nonneg (by positivity), inv_mul_le_one₀ hR]
    exact hmax y (Multiset.mem_cons_of_mem hy)
  simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, h₁,
    re_exp_ofReal_mul_I_pow, Nat.cast_succ]
  rw [smul_eq_mul, mul_neg_one] at ht
  linarith [Real.div_four_sub_le_sum_one_sub_div_mul_one_add_cos_mul_cos J (arg y₁)]

/-- One term of the upper bound of the Fejér-weighted power sums. -/
private theorem fejer_term_le {c t p r ρ₀ x L δ : ℝ} {j J : ℕ} (hj : j ≤ J) (hc₀ : 0 ≤ c)
    (hc : c ≤ 2) (ht₀ : 0 ≤ t) (ht : t ≤ 1 + x) (hx : 0 ≤ x) (hr : 0 ≤ r) (hL : 0 ≤ L)
    (hδ : 0 ≤ δ) (hxr : (1 + x) * r ≤ ρ₀) (hp : p ≤ j * δ + L * r ^ j) :
    c * t ^ j * p ≤ 2 * (J * δ * (1 + x) ^ J) + 2 * (L * ρ₀ ^ j) := by
  have h₁ : t ^ j * (j * δ) ≤ J * δ * (1 + x) ^ J := by
    rw [mul_comm]
    gcongr
    calc t ^ j ≤ (1 + x) ^ j := by gcongr
      _ ≤ (1 + x) ^ J := pow_le_pow_right₀ (by linarith) hj
  have h₂ : t ^ j * (L * r ^ j) ≤ L * ρ₀ ^ j := by
    rw [mul_left_comm, ← mul_pow]
    gcongr
    calc t * r ≤ (1 + x) * r := by gcongr
      _ ≤ ρ₀ := hxr
  calc c * t ^ j * p ≤ c * (t ^ j * (j * δ) + t ^ j * (L * r ^ j)) := by
        rw [← mul_add, mul_assoc]; gcongr
    _ ≤ 2 * (J * δ * (1 + x) ^ J) + 2 * (L * ρ₀ ^ j) := by
        rw [mul_add]; gcongr

/-- The upper bound of the Fejér-weighted power sums: with weights in `[0, 2]` and the rescaling
factor at most `1 + x`, the hypothesis on the power sums bounds the weighted sum by
`2 J² δ (1 + x)^J + 2 L ρ₀/(1 - ρ₀)`. -/
private theorem sum_fejer_mul_re_sum_pow_le (s : Multiset ℂ) (c : ℕ → ℝ) (J : ℕ)
    {t r ρ₀ x L δ : ℝ}
    (hc₀ : ∀ j ∈ Icc 1 J, 0 ≤ c j) (hc : ∀ j ∈ Icc 1 J, c j ≤ 2) (ht₀ : 0 ≤ t) (ht : t ≤ 1 + x)
    (hx : 0 ≤ x) (hr : 0 ≤ r) (hL : 0 ≤ L) (hδ : 0 ≤ δ) (hxr : (1 + x) * r ≤ ρ₀)
    (hρ₀ : ρ₀ < 1) (hpow : ∀ j ∈ Icc 1 J, ((s.map (· ^ j)).sum).re ≤ j * δ + L * r ^ j) :
    ∑ j ∈ Icc 1 J, c j * t ^ j * ((s.map (· ^ j)).sum).re ≤
      2 * J ^ 2 * δ * (1 + x) ^ J + 2 * L * (ρ₀ / (1 - ρ₀)) := by
  have hρ : 0 ≤ ρ₀ := nonneg_of_one_add_mul_le hx hr hxr
  have hgeom : ∑ j ∈ Icc 1 J, ρ₀ ^ j ≤ ρ₀ / (1 - ρ₀) := by
    have hI : Icc 1 J = Ico 1 (J + 1) := by ext; simp only [mem_Icc, mem_Ico]; omega
    simpa [hI] using geom_sum_Ico_le_of_lt_one (m := 1) (n := J + 1) hρ hρ₀
  calc ∑ j ∈ Icc 1 J, c j * t ^ j * ((s.map (· ^ j)).sum).re
      ≤ ∑ j ∈ Icc 1 J, (2 * (J * δ * (1 + x) ^ J) + 2 * (L * ρ₀ ^ j)) :=
        sum_le_sum fun j hj ↦ fejer_term_le (mem_Icc.mp hj).2 (hc₀ j hj) (hc j hj) ht₀ ht hx hr
          hL hδ hxr (hpow j hj)
    _ = 2 * J ^ 2 * δ * (1 + x) ^ J + 2 * L * ∑ j ∈ Icc 1 J, ρ₀ ^ j := by
        rw [sum_add_distrib, sum_const, Nat.card_Icc, ← mul_sum, ← mul_sum, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ 2 * J ^ 2 * δ * (1 + x) ^ J + 2 * L * (ρ₀ / (1 - ρ₀)) := by gcongr

/-- The final bookkeeping: if `J/4 - 3/4 - (N - 1) ≤ 2 J² δ (1 + x)^J + L (K - 1)` with
`N ≤ L` and `8 K L ≤ J ≤ 9 K L`, then `1 ≤ 144 K L δ exp (9 K L x)`. -/
private theorem one_le_mul_exp_of_le {J : ℕ} {K L N δ x : ℝ} (hJ₁ : 8 * K * L ≤ J)
    (hJ₂ : (J : ℝ) ≤ 9 * K * L) (hx : 0 ≤ x) (hN : N ≤ L)
    (h : (J : ℝ) / 4 - 3 / 4 - (N - 1) ≤ 2 * J ^ 2 * δ * (1 + x) ^ J + L * (K - 1)) :
    1 ≤ 144 * K * L * δ * Real.exp (9 * K * L * x) := by
  have hJ : (0 : ℝ) < J := by
    -- For `J = 0` the hypotheses force `K L = 0` and then `1/4 ≤ N - L ≤ 0`.
    by_contra! hJ
    have h₀ : (J : ℝ) = 0 := le_antisymm hJ J.cast_nonneg
    have h₂ : 2 * (J : ℝ) ^ 2 * δ * (1 + x) ^ J = 0 := by rw [h₀]; ring
    linarith
  have h₁ : (J : ℝ) * 1 ≤ J * (16 * J * δ * (1 + x) ^ J) := by linarith
  have hδ : 0 ≤ δ := by
    by_contra! hδ
    have : 16 * J * δ * (1 + x) ^ J ≤ 0 := mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (by positivity) hδ.le) (pow_nonneg (by linarith) _)
    linarith [mul_le_mul_of_nonneg_left this hJ.le]
  have h₂ : (1 + x) ^ J ≤ Real.exp (9 * K * L * x) := by
    calc (1 + x) ^ J ≤ Real.exp x ^ J := by
          gcongr; linarith [Real.add_one_le_exp x]
      _ = Real.exp (J * x) := (Real.exp_natCast_mul J x).symm
      _ ≤ Real.exp (9 * K * L * x) := by gcongr
  calc (1 : ℝ) ≤ 16 * J * δ * (1 + x) ^ J := le_of_mul_le_mul_left h₁ hJ
    _ ≤ 16 * (9 * K * L) * δ * Real.exp (9 * K * L * x) := by
        gcongr
        exact mul_nonneg (by linarith) hδ
    _ = 144 * K * L * δ * Real.exp (9 * K * L * x) := by ring

/-- **Power sums with a dominant term, exponential form.** Let `0 ≤ r`, `0 ≤ x` and `ρ₀ < 1`
with `(1 + x) r ≤ ρ₀`, and put `K = (1 + ρ₀)/(1 - ρ₀)`. Let `s` be a multiset of complex numbers
with at most `L` elements, one of modulus at least `1/(1 + x)`. If
`re ∑_{y ∈ s} y ^ j ≤ j δ + L r ^ j` for every `j ≥ 1`, then `1 ≤ 144 K L δ exp (9 K L x)`.

With `C = 144 K` and `δ > 0` this reads `x ≥ 16 log (1/(C L δ))/(C L)`, the bound of
`log_one_div_div_le_of_re_sum_pow_le` with `16 log (1/(C L δ))` in place of `log (1/(C L δ))`.
The hypotheses force `δ > 0` and `L ≥ 1`. -/
theorem one_le_mul_exp_of_re_sum_pow_le {s : Multiset ℂ} {r ρ₀ x L δ : ℝ} (hr : 0 ≤ r)
    (hx : 0 ≤ x) (hxr : (1 + x) * r ≤ ρ₀) (hρ₀ : ρ₀ < 1) (hs : (Multiset.card s : ℝ) ≤ L)
    (hmax : ∃ y ∈ s, (1 + x)⁻¹ ≤ ‖y‖)
    (hpow : ∀ j : ℕ, 1 ≤ j → ((s.map (· ^ j)).sum).re ≤ j * δ + L * r ^ j) :
    1 ≤ 144 * ((1 + ρ₀) / (1 - ρ₀)) * L * δ *
      Real.exp (9 * ((1 + ρ₀) / (1 - ρ₀)) * L * x) := by
  obtain ⟨y₀, hy₀, hy₀x⟩ := hmax
  obtain ⟨y₁, hy₁, hy₁max⟩ := Multiset.exists_max_image (‖·‖)
    (Multiset.ne_zero_iff_exists_mem.2 ⟨y₀, hy₀⟩)
  have hR : 0 < ‖y₁‖ := (inv_pos.2 (by linarith)).trans_le (hy₀x.trans (hy₁max y₀ hy₀))
  have hRx : ‖y₁‖⁻¹ ≤ 1 + x := by
    rw [inv_le_comm₀ hR (by linarith)]; exact hy₀x.trans (hy₁max y₀ hy₀)
  have hρ : 0 ≤ ρ₀ := nonneg_of_one_add_mul_le hx hr hxr
  have hK : 1 ≤ (1 + ρ₀) / (1 - ρ₀) := by rw [le_div_iff₀ (by linarith)]; linarith
  have hL : 1 ≤ L := one_le_of_card_le hy₀ hs
  have hKL : 0 ≤ 8 * ((1 + ρ₀) / (1 - ρ₀)) * L := by positivity
  set J := ⌈8 * ((1 + ρ₀) / (1 - ρ₀)) * L⌉₊
  have hJ₂ : (J : ℝ) ≤ 9 * ((1 + ρ₀) / (1 - ρ₀)) * L := by
    linarith [Nat.ceil_lt_add_one hKL, one_le_mul_of_one_le_of_one_le hK hL]
  have hlow := le_sum_map_sum_fejer_cos_mul_re_pow s J hy₁ hy₁max hR
  have hswap := sum_map_sum_mul_re_pow s (Icc 1 J)
    (fun j ↦ (1 - j / (J + 1 : ℝ)) * (1 + Real.cos (j * arg y₁))) ‖y₁‖⁻¹
  have hup := sum_fejer_mul_re_sum_pow_le (L := L) (δ := max δ 0) s
    (fun j ↦ (1 - j / (J + 1 : ℝ)) * (1 + Real.cos (j * arg y₁))) J
    (fun j hj ↦ Real.one_sub_div_mul_one_add_cos_nonneg (by linarith [(mem_Icc.mp hj).2]) _)
    (fun j _ ↦ Real.one_sub_div_mul_one_add_cos_le_two j J _) (inv_nonneg.2 hR.le) hRx hx hr
    (by linarith) (le_max_right δ 0) hxr hρ₀
    fun j hj ↦ (hpow j (mem_Icc.mp hj).1).trans (by gcongr; exact le_max_left δ 0)
  have hgeom : 2 * L * (ρ₀ / (1 - ρ₀)) = L * ((1 + ρ₀) / (1 - ρ₀) - 1) := by
    field_simp [(by linarith : (1 : ℝ) - ρ₀ ≠ 0)]; ring
  have key := one_le_mul_exp_of_le (δ := max δ 0) (Nat.le_ceil _) hJ₂ hx hs (by linarith)
  -- The argument ran with `max δ 0` in place of `δ`; `δ ≤ 0` would give `1 ≤ 0`.
  rcases le_total δ 0 with hδ | hδ
  · rw [max_eq_right hδ, mul_zero, zero_mul] at key
    linarith
  · rwa [max_eq_left hδ] at key

/-- **Power sums with a dominant term.** Let `0 ≤ r`, `0 ≤ x` and `ρ₀ < 1` with
`(1 + x) r ≤ ρ₀`, and put `C = 144 (1 + ρ₀)/(1 - ρ₀)`. Let `s` be a multiset of complex numbers
with at most `L` elements, one of modulus at least `1/(1 + x)`. If
`re ∑_{y ∈ s} y ^ j ≤ j δ + L r ^ j` for every `j ≥ 1`, then `x ≥ log (1/(C L δ))/(C L)`.

For `0 ≤ x ≤ x₀` and `(1 + x₀) r < 1` one may take `ρ₀ = (1 + x₀) r`. No hypothesis `L ≥ 1` or
`δ > 0` is needed: the first follows from `s ≠ 0`, and for `δ ≤ 0` the hypotheses are
contradictory. The exponential form `one_le_mul_exp_of_re_sum_pow_le` gives the same bound with
`16 log (1/(C L δ))` in place of `log (1/(C L δ))`. -/
theorem log_one_div_div_le_of_re_sum_pow_le {s : Multiset ℂ} {r ρ₀ x L δ : ℝ} (hr : 0 ≤ r)
    (hx : 0 ≤ x) (hxr : (1 + x) * r ≤ ρ₀) (hρ₀ : ρ₀ < 1) (hs : (Multiset.card s : ℝ) ≤ L)
    (hmax : ∃ y ∈ s, (1 + x)⁻¹ ≤ ‖y‖)
    (hpow : ∀ j : ℕ, 1 ≤ j → ((s.map (· ^ j)).sum).re ≤ j * δ + L * r ^ j) :
    Real.log (1 / (144 * (1 + ρ₀) / (1 - ρ₀) * L * δ)) / (144 * (1 + ρ₀) / (1 - ρ₀) * L) ≤ x := by
  have key := one_le_mul_exp_of_re_sum_pow_le hr hx hxr hρ₀ hs hmax hpow
  obtain ⟨y₀, hy₀, -⟩ := hmax
  have hL : 1 ≤ L := one_le_of_card_le hy₀ hs
  have hρ : 0 ≤ ρ₀ := nonneg_of_one_add_mul_le hx hr hxr
  have hK : 0 < (1 + ρ₀) / (1 - ρ₀) := div_pos (by linarith) (by linarith)
  have hA : 0 < 144 * ((1 + ρ₀) / (1 - ρ₀)) * L * δ := by
    by_contra! hA
    linarith [mul_nonpos_of_nonpos_of_nonneg hA
      (Real.exp_pos (9 * ((1 + ρ₀) / (1 - ρ₀)) * L * x)).le]
  -- Take logarithms in `1 ≤ A exp (9 K L x)`, `A = 144 K L δ`.
  have hlog := Real.log_le_log one_pos key
  rw [Real.log_one, Real.log_mul hA.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
  have hKLx : 0 ≤ (1 + ρ₀) / (1 - ρ₀) * L * x :=
    mul_nonneg (mul_nonneg hK.le (by linarith)) hx
  rw [mul_div_assoc, div_le_iff₀ (mul_pos (mul_pos (by norm_num) hK) (by linarith)), one_div,
    Real.log_inv]
  linarith

/-- **Power sums with a dominant term, the case `r = 1/2`.** Let
`0 ≤ x ≤ 1/2` and let `s` be a multiset of complex numbers with at most `L` elements, one of
modulus at least `1/(1 + x)`. If `re ∑_{y ∈ s} y ^ j ≤ 2 j δ + L 2^(-j)` for every `j ≥ 1`, then
`x ≥ log (1/(2016 L δ))/(2016 L)`. This is `log_one_div_div_le_of_re_sum_pow_le` at `r = 1/2`,
`ρ₀ = 3/4` (where `C = 1008`) with `2 δ` in place of `δ`. -/
theorem log_one_div_div_le_of_re_sum_pow_le_of_le_half {s : Multiset ℂ} {x L δ : ℝ}
    (hx : 0 ≤ x) (hx₂ : x ≤ 1 / 2) (hs : (Multiset.card s : ℝ) ≤ L)
    (hmax : ∃ y ∈ s, (1 + x)⁻¹ ≤ ‖y‖)
    (hpow : ∀ j : ℕ, 1 ≤ j → ((s.map (· ^ j)).sum).re ≤ 2 * j * δ + L * 2⁻¹ ^ j) :
    Real.log (1 / (2016 * L * δ)) / (2016 * L) ≤ x := by
  have h := log_one_div_div_le_of_re_sum_pow_le (r := 2⁻¹) (ρ₀ := 3 / 4) (δ := 2 * δ)
    (by norm_num) hx (by linarith) (by norm_num) hs hmax fun j hj ↦ by linarith [hpow j hj]
  have hC : (144 * (1 + 3 / 4) / (1 - 3 / 4) : ℝ) = 1008 := by norm_num
  have hCδ : 1008 * L * (2 * δ) = 2016 * L * δ := by ring
  rw [hC, hCδ] at h
  obtain ⟨y₀, hy₀, -⟩ := hmax
  have hL : 1 ≤ L := one_le_of_card_le hy₀ hs
  rcases le_total (Real.log (1 / (2016 * L * δ))) 0 with hlog | hlog
  · exact (div_nonpos_of_nonpos_of_nonneg hlog (by positivity)).trans hx
  · exact (div_le_div_of_nonneg_left hlog (by positivity) (by linarith)).trans h

end Complex
