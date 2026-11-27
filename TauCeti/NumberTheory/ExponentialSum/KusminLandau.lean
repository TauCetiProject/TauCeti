/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ExponentialSum.Interval
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Bounds
import TauCeti.Analysis.SpecialFunctions.Trigonometric.HalfAngle

/-!
# The Kusmin–Landau inequality

An exponential sum `∑ e(f(n))`, `e(x) = exp(2πix)`, over the integers of an interval is bounded
independently of the length of the interval when the derivative `f'` is monotone and stays away
from the integers. If `k + α ≤ f'(x) ≤ k + 1 - β` for an integer `k` and reals `α, β > 0` with
`α + β ≤ 1`, then

  `‖∑_{a ≤ n ≤ b} e(f(n))‖ ≤ (cot (πα/2) + cot (πβ/2)) / 2`.

For `α = β = θ` this is Landau's sharp constant `cot (πθ/2)`, which is at most `2/(πθ)` and is
attained at `θ = 1/2` by `f(x) = x/2` over an odd number of consecutive integers. For
`α = 1/U` and `β = 1/V` it gives the asymmetric bound `(U + V)/π` of Hiary, Patel and Yang.
The sum over the integers of `[a, b]` is `TauCeti.intervalExpSum f a b`: a half-open sum
`∑_{X < n ≤ X + Y}` is the case `a = ⌊X⌋ + 1` (`TauCeti.intervalExpSum_intCast_add_one`), and
`∑_{a ≤ n < b}` the case of the right endpoint `⌈b⌉ - 1`.

The proof is Abel summation. With `ψₙ = f(n + 1) - f(n)` and `cₙ = (e(ψₙ) - 1)⁻¹`, every term is
`e(f(n)) = cₙ (e(f(n + 1)) - e(f(n)))`, and `cₙ = -(1 + i cot (πψₙ)) / 2`
(`TauCeti.inv_expTwoPiI_sub_one`). Summation by parts bounds the sum by the norms of the first and
last `cₙ` plus `∑ ‖cₙ₊₁ - cₙ‖`. The real parts of the `cₙ` are all `-1/2`, and by the mean value
theorem the increments `ψₙ` are values of `f'`, hence monotone, so their cotangents are monotone
and the last sum telescopes. The half-angle formula `(1 + cos x) / sin x = cot (x/2)`
(`TauCeti.cot_half`) turns the result into the displayed constant.

## Main results

* `TauCeti.norm_sum_range_expTwoPiI_le_cot_add_cot`: the discrete form, for phases at consecutive
  integers whose increments are monotone and lie in `[k + α, k + 1 - β]`.
* `TauCeti.norm_intervalExpSum_le_cot_add_cot`: the inequality for a phase with monotone derivative
  in `[k + α, k + 1 - β]`.
* `TauCeti.norm_intervalExpSum_le_cot`, `TauCeti.norm_intervalExpSum_le_two_div_pi_mul`: Landau's
  sharp form `cot (πθ/2)` and its consequence `2/(πθ)`, for `k + θ ≤ f' ≤ k + 1 - θ`.
* `TauCeti.norm_intervalExpSum_le_add_div_pi`: the asymmetric form `(U + V)/π`, for
  `ℓ + 1/U ≤ f' ≤ ℓ + 1 - 1/V`.

## References

* J. Arias de Reyna, *Explicit van der Corput's d-th derivative estimate*, arXiv:2407.02094
  (2024), Lemma 1 and Remark 2, for Landau's form with the constant `cot (πθ/2)`.
* G. A. Hiary, D. Patel and A. Yang, *An improved explicit estimate for ζ(1/2 + it)*,
  arXiv:2207.02366 (2022), Lemma 2.3, for the asymmetric form.
-/

public section

open Finset Real

namespace TauCeti

/-! ### Abel summation -/

/-- Abel summation for an exponential sum against coefficients `cⱼ` with
`cⱼ (e(φ(j + 1) - φ(j)) - 1) = 1`, so that `e(φ(j)) = cⱼ (e(φ(j + 1)) - e(φ(j)))`. -/
private theorem norm_sum_range_expTwoPiI_le_of_mul_sub_one {φ : ℕ → ℝ} {c : ℕ → ℂ} {N : ℕ}
    (hc : ∀ j ≤ N, c j * (expTwoPiI (φ (j + 1) - φ j) - 1) = 1) :
    ‖∑ j ∈ range (N + 2), expTwoPiI (φ j)‖ ≤
      ‖c 0‖ + ‖c N‖ + ∑ j ∈ range N, ‖c (j + 1) - c j‖ := by
  have key (j : ℕ) (hj : j ≤ N) :
      c j * expTwoPiI (φ (j + 1)) = (1 + c j) * expTwoPiI (φ j) := by
    have h := expTwoPiI_add (φ j) (φ (j + 1) - φ j)
    rw [add_sub_cancel] at h
    rw [h]
    linear_combination expTwoPiI (φ j) * hc j hj
  -- the partial sums, corrected by a boundary term, change by `(cₙ₊₁ - cₙ) e(φ(n + 1))`
  have hR (n : ℕ) (hn : n ≤ N) :
      ‖∑ j ∈ range (n + 1), expTwoPiI (φ j) - c n * expTwoPiI (φ (n + 1))‖ ≤
        ‖c 0‖ + ∑ j ∈ range n, ‖c (j + 1) - c j‖ := by
    induction n with
    | zero =>
      rw [zero_add, sum_range_one, key 0 hn, sum_range_zero, add_zero, ← one_sub_mul,
        sub_add_cancel_left, neg_mul, norm_neg, norm_mul, norm_expTwoPiI, mul_one]
    | succ n ih =>
      rw [sum_range_succ, sum_range_succ (fun j ↦ ‖c (j + 1) - c j‖), ← add_assoc]
      calc ‖∑ j ∈ range (n + 1), expTwoPiI (φ j) + expTwoPiI (φ (n + 1)) -
              c (n + 1) * expTwoPiI (φ (n + 1 + 1))‖
          = ‖(∑ j ∈ range (n + 1), expTwoPiI (φ j) - c n * expTwoPiI (φ (n + 1))) -
              (c (n + 1) - c n) * expTwoPiI (φ (n + 1))‖ := by
            rw [key (n + 1) hn]
            ring_nf
        _ ≤ _ := by
            refine (norm_sub_le _ _).trans (add_le_add (ih (by omega)) ?_)
            rw [norm_mul, norm_expTwoPiI, mul_one]
  have h1 : 1 + c N = c N * expTwoPiI (φ (N + 1) - φ N) := by
    linear_combination -(hc N le_rfl)
  rw [sum_range_succ]
  calc ‖∑ j ∈ range (N + 1), expTwoPiI (φ j) + expTwoPiI (φ (N + 1))‖
      = ‖(∑ j ∈ range (N + 1), expTwoPiI (φ j) - c N * expTwoPiI (φ (N + 1))) +
          (1 + c N) * expTwoPiI (φ (N + 1))‖ := by ring_nf
    _ ≤ ‖c 0‖ + ∑ j ∈ range N, ‖c (j + 1) - c j‖ + ‖c N‖ := by
      refine (norm_add_le _ _).trans (add_le_add (hR N le_rfl) ?_)
      rw [norm_mul, norm_expTwoPiI, mul_one, h1, norm_mul, norm_expTwoPiI, mul_one]
    _ = _ := by ring

/-! ### The constant -/

/-- The boundary terms: for `α ≤ x ≤ y ≤ 1 - β`,
`1/(2 sin (πx)) + 1/(2 sin (πy)) + (cot (πx) - cot (πy))/2 ≤ (cot (πα/2) + cot (πβ/2))/2`. The
left side is `(cot (πx/2) + cot (π(1 - y)/2))/2` by the half-angle formula. -/
private theorem inv_two_mul_sin_add_inv_two_mul_sin_add_le {α β x y : ℝ} (hα : 0 < α)
    (hβ : 0 < β) (hx : α ≤ x) (hxy : x ≤ y) (hy : y ≤ 1 - β) :
    (2 * sin (π * x))⁻¹ + (2 * sin (π * y))⁻¹ + (cot (π * x) - cot (π * y)) / 2 ≤
      (cot (π * α / 2) + cot (π * β / 2)) / 2 := by
  have hsx : 0 < sin (π * x) := sin_pi_mul_pos_of_pos_of_lt_one (by linarith) (by linarith)
  have hsy : 0 < sin (π * y) := sin_pi_mul_pos_of_pos_of_lt_one (by linarith) (by linarith)
  have h₁ : (sin (π * x))⁻¹ + cot (π * x) = cot (π * x / 2) := by
    rw [cot_half, cot_eq_cos_div_sin]
    field_simp
  have h₂ : (sin (π * y))⁻¹ - cot (π * y) = cot (π * (1 - y) / 2) := by
    rw [cot_half, mul_one_sub, sin_pi_sub, cos_pi_sub, cot_eq_cos_div_sin]
    field_simp
    ring
  have h₃ : cot (π * x / 2) ≤ cot (π * α / 2) := strictAntiOn_cot.antitoneOn
    ⟨by positivity, by nlinarith [pi_pos]⟩ ⟨by nlinarith [pi_pos], by nlinarith [pi_pos]⟩
    (by gcongr)
  have h₄ : cot (π * (1 - y) / 2) ≤ cot (π * β / 2) := strictAntiOn_cot.antitoneOn
    ⟨by positivity, by nlinarith [pi_pos]⟩ ⟨by nlinarith [pi_pos], by nlinarith [pi_pos]⟩
    (by gcongr; linarith)
  calc (2 * sin (π * x))⁻¹ + (2 * sin (π * y))⁻¹ + (cot (π * x) - cot (π * y)) / 2
      = ((sin (π * x))⁻¹ + cot (π * x)) / 2 + ((sin (π * y))⁻¹ - cot (π * y)) / 2 := by
        rw [mul_inv, mul_inv]
        ring
    _ ≤ _ := by
        rw [h₁, h₂]
        linarith

/-- The constant `(cot (πα/2) + cot (πβ/2))/2` is at least `1`, the norm of a single term. -/
private theorem one_le_cot_add_cot_div_two {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hαβ : α + β ≤ 1) : 1 ≤ (cot (π * α / 2) + cot (π * β / 2)) / 2 := by
  have h := inv_two_mul_sin_add_inv_two_mul_sin_add_le hα hβ le_rfl le_rfl (by linarith)
  have hs := sin_pi_mul_pos_of_pos_of_lt_one hα (by linarith)
  have h₁ : 1 ≤ (sin (π * α))⁻¹ := (one_le_inv₀ hs).2 (sin_le_one _)
  rw [sub_self, zero_div, add_zero, mul_inv] at h
  linarith

/-! ### The discrete inequality -/

/-- The discrete inequality for monotone increments. -/
private theorem norm_sum_range_expTwoPiI_le_of_monotoneOn {φ : ℕ → ℝ} {N : ℕ} {k : ℤ}
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (hαβ : α + β ≤ 1)
    (hmono : MonotoneOn (fun j ↦ φ (j + 1) - φ j) (Set.Iio N))
    (hlow : ∀ j < N, k + α ≤ φ (j + 1) - φ j) (hup : ∀ j < N, φ (j + 1) - φ j ≤ k + 1 - β) :
    ‖∑ j ∈ range (N + 1), expTwoPiI (φ j)‖ ≤ (cot (π * α / 2) + cot (π * β / 2)) / 2 := by
  rcases N with _ | n
  · simpa [norm_expTwoPiI] using one_le_cot_add_cot_div_two hα hβ hαβ
  -- the increments, shifted by `k`, lie in `[α, 1 - β] ⊆ (0, 1)`
  set d : ℕ → ℝ := fun j ↦ φ (j + 1) - φ j - k with hd
  have hdα (j : ℕ) (hj : j ≤ n) : α ≤ d j := by linarith [hlow j (by omega)]
  have hdβ (j : ℕ) (hj : j ≤ n) : d j ≤ 1 - β := by linarith [hup j (by omega)]
  have hle (i j : ℕ) (hj : j ≤ n) (hij : i ≤ j) : d i ≤ d j := by
    have := hmono (show i < n + 1 by omega) (show j < n + 1 by omega) hij
    simp only [hd]
    linarith
  have hs (j : ℕ) (hj : j ≤ n) : 0 < sin (π * d j) :=
    sin_pi_mul_pos_of_pos_of_lt_one (by linarith [hdα j hj]) (by linarith [hdβ j hj])
  have hne (j : ℕ) (hj : j ≤ n) : expTwoPiI (d j) - 1 ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_expTwoPiI_sub_one, abs_of_pos (hs j hj)]
    exact (mul_pos two_pos (hs j hj)).ne'
  -- Abel summation against the coefficients `(e(d j) - 1)⁻¹ = -(1 + i cot (π d j)) / 2`
  have hcd (j : ℕ) (hj : j ≤ n) :
      (expTwoPiI (d j) - 1)⁻¹ * (expTwoPiI (φ (j + 1) - φ j) - 1) = 1 := by
    rw [show φ (j + 1) - φ j = d j + k by simp [hd], expTwoPiI_add_intCast]
    exact inv_mul_cancel₀ (hne j hj)
  have hnorm (j : ℕ) (hj : j ≤ n) : ‖(expTwoPiI (d j) - 1)⁻¹‖ = (2 * sin (π * d j))⁻¹ := by
    rw [norm_inv, norm_expTwoPiI_sub_one, abs_of_pos (hs j hj)]
  have hdiff (j : ℕ) (hj : j ∈ range n) :
      ‖(expTwoPiI (d (j + 1)) - 1)⁻¹ - (expTwoPiI (d j) - 1)⁻¹‖ =
        (cot (π * d j) - cot (π * d (j + 1))) / 2 := by
    have hj' := mem_range.1 hj
    have hanti : cot (π * d (j + 1)) ≤ cot (π * d j) := strictAntiOn_cot.antitoneOn
      ⟨by nlinarith [pi_pos, hdα j hj'.le], by nlinarith [pi_pos, hdβ j hj'.le]⟩
      ⟨by nlinarith [pi_pos, hdα (j + 1) hj'], by nlinarith [pi_pos, hdβ (j + 1) hj']⟩
      (by gcongr; exact hle j (j + 1) hj' (by omega))
    rw [inv_expTwoPiI_sub_one (sub_ne_zero.1 (hne (j + 1) hj')),
      inv_expTwoPiI_sub_one (sub_ne_zero.1 (hne j hj'.le)),
      show -(1 + (cot (π * d (j + 1)) : ℂ) * Complex.I) / 2 -
        -(1 + (cot (π * d j) : ℂ) * Complex.I) / 2 =
        (((cot (π * d j) - cot (π * d (j + 1))) / 2 : ℝ) : ℂ) * Complex.I by push_cast; ring,
      norm_mul, Complex.norm_I, mul_one, Complex.norm_real, norm_eq_abs,
      abs_of_nonneg (by linarith)]
  refine (norm_sum_range_expTwoPiI_le_of_mul_sub_one hcd).trans ?_
  rw [hnorm 0 (Nat.zero_le n), hnorm n le_rfl, sum_congr rfl hdiff, ← sum_div,
    sum_range_sub' (fun j ↦ cot (π * d j))]
  exact inv_two_mul_sin_add_inv_two_mul_sin_add_le hα hβ (hdα 0 (Nat.zero_le n))
    (hle 0 n le_rfl (Nat.zero_le n)) (hdβ n le_rfl)

/-- **The Kusmin–Landau inequality, discrete form.** Let `φ(0), …, φ(N)` be real phases whose
increments `φ(j + 1) - φ(j)` form a monotone sequence (increasing or decreasing) in
`[k + α, k + 1 - β]` for an integer `k`, where `α, β > 0` and `α + β ≤ 1`. Then
`‖∑_{j ≤ N} e(φ(j))‖ ≤ (cot (πα/2) + cot (πβ/2))/2`, whatever the number of terms. -/
theorem norm_sum_range_expTwoPiI_le_cot_add_cot {φ : ℕ → ℝ} {N : ℕ} {k : ℤ} {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hαβ : α + β ≤ 1)
    (hmono : MonotoneOn (fun j ↦ φ (j + 1) - φ j) (Set.Iio N) ∨
      AntitoneOn (fun j ↦ φ (j + 1) - φ j) (Set.Iio N))
    (hlow : ∀ j < N, k + α ≤ φ (j + 1) - φ j) (hup : ∀ j < N, φ (j + 1) - φ j ≤ k + 1 - β) :
    ‖∑ j ∈ range (N + 1), expTwoPiI (φ j)‖ ≤ (cot (π * α / 2) + cot (π * β / 2)) / 2 := by
  rcases hmono with hmono | hanti
  · exact norm_sum_range_expTwoPiI_le_of_monotoneOn hα hβ hαβ hmono hlow hup
  -- decreasing increments: apply the increasing case to the conjugate phase `-φ`
  have h := norm_sum_range_expTwoPiI_le_of_monotoneOn (φ := fun j ↦ -φ j) (k := -k - 1) hβ hα
    (by linarith) (fun i hi j hj hij ↦ by have := hanti hi hj hij; simp only at this ⊢; linarith)
    (fun j hj ↦ by push_cast; linarith [hup j hj]) (fun j hj ↦ by push_cast; linarith [hlow j hj])
  rw [add_comm (cot (π * α / 2))]
  calc ‖∑ j ∈ range (N + 1), expTwoPiI (φ j)‖ = ‖∑ j ∈ range (N + 1), expTwoPiI (-φ j)‖ := by
        rw [← Complex.norm_conj, map_sum]
        simp_rw [conj_expTwoPiI]
    _ ≤ _ := h

/-! ### The inequality on an interval -/

/-- **The Kusmin–Landau inequality.** Let `f` be continuous on `[a, b]` with a monotone
(increasing or decreasing) derivative `f'` on `(a, b)` such that `k + α ≤ f' ≤ k + 1 - β` there,
for an integer `k` and reals `α, β > 0` with `α + β ≤ 1`. Then the sum of `e(f(n))` over the
integers `a ≤ n ≤ b` satisfies `‖∑ e(f(n))‖ ≤ (cot (πα/2) + cot (πβ/2))/2`. -/
theorem norm_intervalExpSum_le_cot_add_cot {f f' : ℝ → ℝ} {a b α β : ℝ} {k : ℤ}
    (hα : 0 < α) (hβ : 0 < β) (hαβ : α + β ≤ 1) (hf : ContinuousOn f (Set.Icc a b))
    (hf' : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x)
    (hmono : MonotoneOn f' (Set.Ioo a b) ∨ AntitoneOn f' (Set.Ioo a b))
    (hlow : ∀ x ∈ Set.Ioo a b, k + α ≤ f' x) (hup : ∀ x ∈ Set.Ioo a b, f' x ≤ k + 1 - β) :
    ‖intervalExpSum f a b‖ ≤ (cot (π * α / 2) + cot (π * β / 2)) / 2 := by
  rcases lt_or_ge ⌊b⌋ ⌈a⌉ with hba | hab
  · refine (norm_intervalExpSum_le_toNat f a b).trans ?_
    rw [show (⌊b⌋ + 1 - ⌈a⌉).toNat = 0 by omega, Nat.cast_zero]
    linarith [one_le_cot_add_cot_div_two hα hβ hαβ]
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ⌊b⌋ = ⌈a⌉ + N := ⟨(⌊b⌋ - ⌈a⌉).toNat, by omega⟩
  have hsum : intervalExpSum f a b = ∑ j ∈ range (N + 1), expTwoPiI (f (⌈a⌉ + j)) := by
    rw [intervalExpSum_def, Int.Icc_eq_finset_map, sum_map,
      show (⌊b⌋ + 1 - ⌈a⌉).toNat = N + 1 by omega]
    simp
  rw [hsum]
  -- by the mean value theorem, each increment is a value of `f'` on its unit interval
  have hmvt (j : ℕ) (hj : j < N) : ∃ ξ ∈ Set.Ioo a b, (⌈a⌉ + j : ℝ) < ξ ∧ ξ < ⌈a⌉ + j + 1 ∧
      f' ξ = f (⌈a⌉ + (j + 1 : ℕ)) - f (⌈a⌉ + j) := by
    have ha : a ≤ ⌈a⌉ := Int.le_ceil a
    have hb : (⌈a⌉ + j + 1 : ℝ) ≤ b := by
      have h₁ : ((⌈a⌉ + N : ℤ) : ℝ) ≤ b := hN ▸ Int.floor_le b
      have h₂ : (j : ℝ) + 1 ≤ N := by exact_mod_cast hj
      push_cast at h₁
      linarith
    obtain ⟨ξ, hξ, h⟩ := exists_hasDerivAt_eq_slope f f'
      (by linarith : (⌈a⌉ + j : ℝ) < ⌈a⌉ + j + 1) (hf.mono (Set.Icc_subset_Icc (by linarith) hb))
      (fun x hx ↦ hf' x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    refine ⟨ξ, ⟨by linarith [hξ.1], by linarith [hξ.2]⟩, hξ.1, hξ.2, ?_⟩
    rw [h]
    push_cast
    ring_nf
  -- earlier increments are values of `f'` at earlier points
  have key (i j : ℕ) (hj : j < N) (hij : i ≤ j) : ∃ ξ ∈ Set.Ioo a b, ∃ ξ' ∈ Set.Ioo a b,
      ξ ≤ ξ' ∧ f' ξ = f (⌈a⌉ + (i + 1 : ℕ)) - f (⌈a⌉ + i) ∧
        f' ξ' = f (⌈a⌉ + (j + 1 : ℕ)) - f (⌈a⌉ + j) := by
    rcases hij.eq_or_lt with rfl | hlt
    · obtain ⟨ξ, hξ, -, -, h⟩ := hmvt i hj
      exact ⟨ξ, hξ, ξ, hξ, le_rfl, h, h⟩
    obtain ⟨ξ, hξ, -, h₂, h₃⟩ := hmvt i (hlt.trans hj)
    obtain ⟨ξ', hξ', h₁', -, h₃'⟩ := hmvt j hj
    have : (i : ℝ) + 1 ≤ j := by exact_mod_cast hlt
    exact ⟨ξ, hξ, ξ', hξ', by linarith, h₃, h₃'⟩
  refine norm_sum_range_expTwoPiI_le_cot_add_cot (k := k) hα hβ hαβ
    (hmono.imp (fun h i _ j hj hij ↦ ?_) (fun h i _ j hj hij ↦ ?_)) (fun j hj ↦ ?_)
    (fun j hj ↦ ?_)
  · obtain ⟨ξ, hξ, ξ', hξ', hle, h₁, h₂⟩ := key i j hj hij
    simpa only [← h₁, ← h₂] using h hξ hξ' hle
  · obtain ⟨ξ, hξ, ξ', hξ', hle, h₁, h₂⟩ := key i j hj hij
    simpa only [← h₁, ← h₂] using h hξ hξ' hle
  · obtain ⟨ξ, hξ, -, -, h⟩ := hmvt j hj
    simpa [h] using hlow ξ hξ
  · obtain ⟨ξ, hξ, -, -, h⟩ := hmvt j hj
    simpa [h] using hup ξ hξ

/-- **The Kusmin–Landau inequality, Landau's sharp form.** If `f` is continuous on `[a, b]` with a
monotone derivative `f'` on `(a, b)` and `k + θ ≤ f' ≤ k + 1 - θ` there, for an integer `k` and
`0 < θ ≤ 1/2`, then `‖∑_{a ≤ n ≤ b} e(f(n))‖ ≤ cot (πθ/2)`. The constant is attained at
`θ = 1/2`. -/
theorem norm_intervalExpSum_le_cot {f f' : ℝ → ℝ} {a b θ : ℝ} {k : ℤ} (hθ : 0 < θ)
    (hθ' : θ ≤ 1 / 2) (hf : ContinuousOn f (Set.Icc a b))
    (hf' : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x)
    (hmono : MonotoneOn f' (Set.Ioo a b) ∨ AntitoneOn f' (Set.Ioo a b))
    (hlow : ∀ x ∈ Set.Ioo a b, k + θ ≤ f' x) (hup : ∀ x ∈ Set.Ioo a b, f' x ≤ k + 1 - θ) :
    ‖intervalExpSum f a b‖ ≤ cot (π * θ / 2) := by
  simpa using norm_intervalExpSum_le_cot_add_cot hθ hθ (by linarith) hf hf' hmono hlow hup

/-- **The Kusmin–Landau inequality** in the form `‖∑_{a ≤ n ≤ b} e(f(n))‖ ≤ 2/(πθ)`, under the
hypotheses of `TauCeti.norm_intervalExpSum_le_cot`, since `cot x < 1/x` on `(0, π)`. -/
theorem norm_intervalExpSum_le_two_div_pi_mul {f f' : ℝ → ℝ} {a b θ : ℝ} {k : ℤ} (hθ : 0 < θ)
    (hθ' : θ ≤ 1 / 2) (hf : ContinuousOn f (Set.Icc a b))
    (hf' : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x)
    (hmono : MonotoneOn f' (Set.Ioo a b) ∨ AntitoneOn f' (Set.Ioo a b))
    (hlow : ∀ x ∈ Set.Ioo a b, k + θ ≤ f' x) (hup : ∀ x ∈ Set.Ioo a b, f' x ≤ k + 1 - θ) :
    ‖intervalExpSum f a b‖ ≤ 2 / (π * θ) := by
  refine (norm_intervalExpSum_le_cot hθ hθ' hf hf' hmono hlow hup).trans ?_
  have h := cot_lt_inv (x := π * θ / 2) (by positivity) (by nlinarith [pi_pos])
  rw [inv_div] at h
  exact h.le

/-- **The Kusmin–Landau inequality, asymmetric form** (Hiary, Patel and Yang). If `f` is continuous
on `[a, b]` with a monotone derivative `f'` on `(a, b)` and `ℓ + 1/U ≤ f' ≤ ℓ + 1 - 1/V` there,
for an integer `ℓ` and `U, V > 0` with `1/U + 1/V ≤ 1` (so that `U, V > 1`), then
`‖∑_{a ≤ n ≤ b} e(f(n))‖ ≤ (U + V)/π`. -/
theorem norm_intervalExpSum_le_add_div_pi {f f' : ℝ → ℝ} {a b U V : ℝ} {ℓ : ℤ} (hU : 0 < U)
    (hV : 0 < V) (hUV : U⁻¹ + V⁻¹ ≤ 1) (hf : ContinuousOn f (Set.Icc a b))
    (hf' : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x)
    (hmono : MonotoneOn f' (Set.Ioo a b) ∨ AntitoneOn f' (Set.Ioo a b))
    (hlow : ∀ x ∈ Set.Ioo a b, ℓ + U⁻¹ ≤ f' x) (hup : ∀ x ∈ Set.Ioo a b, f' x ≤ ℓ + 1 - V⁻¹) :
    ‖intervalExpSum f a b‖ ≤ (U + V) / π := by
  have hU' := inv_pos.2 hU
  have hV' := inv_pos.2 hV
  refine (norm_intervalExpSum_le_cot_add_cot hU' hV' hUV hf hf' hmono hlow hup).trans ?_
  have h₁ := cot_lt_inv (x := π * U⁻¹ / 2) (by positivity) (by nlinarith [pi_pos])
  have h₂ := cot_lt_inv (x := π * V⁻¹ / 2) (by positivity) (by nlinarith [pi_pos])
  have e₁ : (π * U⁻¹ / 2)⁻¹ = 2 * U / π := by field_simp
  have e₂ : (π * V⁻¹ / 2)⁻¹ = 2 * V / π := by field_simp
  rw [e₁] at h₁
  rw [e₂] at h₂
  have : (2 * U / π + 2 * V / π) / 2 = (U + V) / π := by ring
  linarith

/-- The hypotheses of `TauCeti.norm_intervalExpSum_le_cot` hold for `f(x) = x/2` at `θ = 1/2`. -/
example : ‖intervalExpSum (fun x ↦ x / 2) 0 2‖ ≤ cot (π * (1 / 2) / 2) :=
  norm_intervalExpSum_le_cot (f' := fun _ ↦ 1 / 2) (k := 0) (by norm_num) le_rfl (by fun_prop)
    (fun x _ ↦ by simpa using (hasDerivAt_id x).div_const 2) (Or.inl monotoneOn_const)
    (fun _ _ ↦ by norm_num) (fun _ _ ↦ by norm_num)

/-- Landau's constant is attained: for `f(x) = x/2` the sum over `[0, 2]` is
`e(0) + e(1/2) + e(1) = 1 - 1 + 1 = 1 = cot (π/4)`. -/
example : ‖intervalExpSum (fun x ↦ x / 2) 0 2‖ = cot (π * (1 / 2) / 2) := by
  have hcot : cot (π * (1 / 2) / 2) = 1 := by
    rw [show π * (1 / 2) / 2 = π / 4 by ring, cot_eq_cos_div_sin, cos_pi_div_four,
      sin_pi_div_four, div_self (by positivity)]
  have h : expTwoPiI 2⁻¹ = -1 := by
    rw [expTwoPiI_def, ← Complex.exp_pi_mul_I]
    congr 1
    push_cast
    ring
  have hI : Icc (0 : ℤ) 2 = {0, 1, 2} := by decide
  rw [hcot, ← Int.cast_zero, ← Int.cast_two, intervalExpSum_intCast, hI]
  simp [h]

end TauCeti
