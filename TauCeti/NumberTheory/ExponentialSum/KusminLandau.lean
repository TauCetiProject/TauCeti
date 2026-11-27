/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ExponentialSum.Interval
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Bounds

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
(`TauCeti.inv_expTwoPiI_sub_one`). Summation by parts (`Finset.sum_range_by_parts`) bounds the sum
by the norms of the first and last `cₙ` plus `∑ ‖cₙ₊₁ - cₙ‖`. The real parts of the `cₙ` are all
`-1/2`, and by the mean value theorem the increments `ψₙ` are values of `f'`, hence monotone, so
their cotangents are monotone and the last sum telescopes. By the half-angle formula the two
boundary terms are at most `cot (πα/2)/2` and `cot (πβ/2)/2`
(`TauCeti.inv_sin_add_cot_le_cot_half`, `TauCeti.inv_sin_sub_cot_le_cot_half`).

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
  obtain ⟨u, hu⟩ : ∃ u : ℕ → ℂ, ∀ j, expTwoPiI (φ j) = u j := ⟨_, fun _ ↦ rfl⟩
  have hu₁ (j : ℕ) : ‖u j‖ = 1 := by rw [← hu, norm_expTwoPiI]
  -- every term but the last is `cⱼ (uⱼ₊₁ - uⱼ)`
  have key (j : ℕ) (hj : j ≤ N) : u j = c j • (u (j + 1) - u j) := by
    have h := expTwoPiI_add (φ j) (φ (j + 1) - φ j)
    rw [add_sub_cancel, hu, hu] at h
    rw [smul_eq_mul, h]
    linear_combination -u j * hc j hj
  -- summation by parts; the partial sums of `uⱼ₊₁ - uⱼ` telescope to `uₖ - u₀`
  have hS : ∑ j ∈ range (N + 2), u j =
      (1 + c N) * u (N + 1) - c 0 * u 0 - ∑ j ∈ range N, (c (j + 1) - c j) * u (j + 1) := by
    rw [sum_range_succ, sum_congr rfl fun j hj ↦ key j (Nat.lt_add_one_iff.1 (mem_range.1 hj)),
      sum_range_by_parts, Nat.add_sub_cancel]
    simp only [sum_range_sub, smul_eq_mul]
    simp only [mul_sub, sum_sub_distrib]
    rw [← sum_mul, sum_range_sub]
    ring
  have hN : ‖1 + c N‖ = ‖c N‖ := by
    have h : 1 + c N = c N * expTwoPiI (φ (N + 1) - φ N) := by
      linear_combination -(hc N le_rfl)
    rw [h, norm_mul, norm_expTwoPiI, mul_one]
  simp only [hu]
  rw [hS]
  calc ‖(1 + c N) * u (N + 1) - c 0 * u 0 - ∑ j ∈ range N, (c (j + 1) - c j) * u (j + 1)‖
      ≤ ‖1 + c N‖ + ‖c 0‖ + ∑ j ∈ range N, ‖c (j + 1) - c j‖ := by
        refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans_eq ?_) ?_)
        · rw [norm_mul, norm_mul, hu₁, hu₁, mul_one, mul_one]
        · exact (norm_sum_le _ _).trans_eq (sum_congr rfl fun j _ ↦ by rw [norm_mul, hu₁, mul_one])
    _ = _ := by
        rw [hN]
        ring

/-! ### The discrete inequality -/

/-- The discrete inequality for monotone increments. -/
private theorem norm_sum_range_expTwoPiI_le_of_monotoneOn {φ : ℕ → ℝ} {N : ℕ} {k : ℤ}
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (hαβ : α + β ≤ 1)
    (hmono : MonotoneOn (fun j ↦ φ (j + 1) - φ j) (Set.Iio N))
    (hlow : ∀ j < N, k + α ≤ φ (j + 1) - φ j) (hup : ∀ j < N, φ (j + 1) - φ j ≤ k + 1 - β) :
    ‖∑ j ∈ range (N + 1), expTwoPiI (φ j)‖ ≤ (cot (π * α / 2) + cot (π * β / 2)) / 2 := by
  rcases N with _ | n
  · have h := two_le_cot_half_add_cot_half (a := π * α) (b := π * β) (by positivity)
      (by positivity) (by nlinarith [pi_pos])
    have h' : (1 : ℝ) ≤ (cot (π * α / 2) + cot (π * β / 2)) / 2 := by linarith
    simpa [norm_expTwoPiI] using h'
  -- the increments, shifted by `k`, lie in `[α, 1 - β] ⊆ (0, 1)`
  set d : ℕ → ℝ := fun j ↦ φ (j + 1) - φ j - k with hd
  have hdα (j : ℕ) (hj : j ≤ n) : α ≤ d j := by linarith [hlow j (by omega)]
  have hdβ (j : ℕ) (hj : j ≤ n) : d j ≤ 1 - β := by linarith [hup j (by omega)]
  have hle (i j : ℕ) (hj : j ≤ n) (hij : i ≤ j) : d i ≤ d j := by
    have := hmono (Set.mem_Iio.2 (by omega)) (Set.mem_Iio.2 (by omega)) hij
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
    have h : φ (j + 1) - φ j = d j + k := by simp [hd]
    rw [h, expTwoPiI_add_intCast]
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
    rw [norm_inv_expTwoPiI_sub_one_sub_inv_expTwoPiI_sub_one (sub_ne_zero.1 (hne j hj'.le))
      (sub_ne_zero.1 (hne (j + 1) hj')), abs_of_nonneg (by linarith)]
  refine (norm_sum_range_expTwoPiI_le_of_mul_sub_one hcd).trans ?_
  rw [hnorm 0 (Nat.zero_le n), hnorm n le_rfl, sum_congr rfl hdiff, ← sum_div,
    sum_range_sub' (fun j ↦ cot (π * d j))]
  -- the boundary terms, by the half-angle formula
  have h₀ := inv_sin_add_cot_le_cot_half (a := π * α) (x := π * d 0) (by positivity)
    (mul_le_mul_of_nonneg_left (hdα 0 (Nat.zero_le n)) pi_pos.le)
    (by nlinarith [pi_pos, hdβ 0 (Nat.zero_le n)])
  have h₁ := inv_sin_sub_cot_le_cot_half (b := π * β) (y := π * d n) (by positivity)
    (by nlinarith [pi_pos, hdα n le_rfl]) (by nlinarith [pi_pos, hdβ n le_rfl])
  rw [mul_inv, mul_inv]
  linarith

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
    have h : (⌊b⌋ + 1 - ⌈a⌉).toNat = 0 := by omega
    rw [h, Nat.cast_zero]
    linarith [two_le_cot_half_add_cot_half (a := π * α) (b := π * β) (by positivity)
      (by positivity) (by nlinarith [pi_pos])]
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ⌊b⌋ = ⌈a⌉ + N := ⟨(⌊b⌋ - ⌈a⌉).toNat, by omega⟩
  have hsum : intervalExpSum f a b = ∑ j ∈ range (N + 1), expTwoPiI (f (⌈a⌉ + j)) := by
    have h : (⌊b⌋ + 1 - ⌈a⌉).toNat = N + 1 := by omega
    rw [intervalExpSum_def, Int.Icc_eq_finset_map, sum_map, h]
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
  iterate 2
    obtain ⟨ξ, hξ, ξ', hξ', hle, h₁, h₂⟩ := key i j (Set.mem_Iio.1 hj) hij
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
    have h : π * (1 / 2) / 2 = π / 4 := by ring
    rw [h, cot_eq_cos_div_sin, cos_pi_div_four, sin_pi_div_four, div_self (by positivity)]
  have h : expTwoPiI 2⁻¹ = -1 := by
    rw [expTwoPiI_def, ← Complex.exp_pi_mul_I]
    congr 1
    push_cast
    ring
  have hI : Icc (0 : ℤ) 2 = {0, 1, 2} := by decide
  rw [hcot, ← Int.cast_zero, ← Int.cast_two, intervalExpSum_intCast, hI]
  simp [h]

end TauCeti
