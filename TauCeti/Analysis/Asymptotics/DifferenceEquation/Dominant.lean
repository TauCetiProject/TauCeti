/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Asymptotics.AsymptoticExpansion
public import TauCeti.Analysis.Asymptotics.DifferenceEquation.FormalSolution
import Mathlib.Analysis.SpecificLimits.Basic
import TauCeti.Algebra.ContinuedFractions.ReductionOfOrder
import TauCeti.Analysis.PSeries
import TauCeti.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.Analysis.SpecificLimits.ForcedIncrements

/-!
# Dominant solutions of second-order linear difference equations

Consider the difference equation

  `w (n + 2) + f n * w (n + 1) + g n * w n = 0`

whose coefficients have Poincaré expansions `f n ∼ ∑ fₛ n⁻ˢ` and `g n ∼ ∑ gₛ n⁻ˢ` as `n → ∞`.
Let `ρ` be a root of the characteristic equation `ρ² + f₀ ρ + g₀ = 0` (DLMF 2.9.5) of strictly
larger modulus than the other root `g₀ / ρ`, that is `‖g₀‖ < ‖ρ‖ ^ 2`, and let `α` and the
coefficients `aₛ = TauCeti.differenceCoeff fs gs ρ α` be given by DLMF 2.9.6 and 2.9.7. This file
proves that the equation has a solution with the asymptotic expansion

  `w n ∼ ρⁿ n^α ∑ aₛ n⁻ˢ`

of DLMF 2.9.8. Together with the recessive solution of
`TauCeti.exists_eventually_difference_solution_of_norm_sq_lt`, this gives both solutions of
DLMF 2.9.8 when the characteristic roots have distinct moduli. Unlike the recessive solution, the
solution here is not unique: adding a multiple of the recessive solution does not change its
expansion.

## Main results

* `TauCeti.isBigO_div_pow_of_tendsto_div`: if `‖g n‖ ≤ γ` for large `n` and `w` is a solution
  with `rⁿ = O(w n)` where `γ < r²`, then every solution `v` with `v / w → 0` satisfies
  `v / w = O((γ / r²)ⁿ)`.
* `TauCeti.exists_eventually_difference_solution_of_norm_sq_gt`: a solution for large `n` with the
  expansion `ρⁿ n^α ∑ aₛ n⁻ˢ`.
* `TauCeti.exists_difference_solution_of_norm_sq_gt`: if moreover `g` vanishes nowhere, a solution
  for all `n` with that expansion.

## Implementation notes

Let `u` be the truncation of the formal solution after `M` terms, whose residual
`r n = u (n + 2) + f n * u (n + 1) + g n * u n` is `O(|ρ|ⁿ n^{Re α - M - 1})` by
`TauCeti.isBigO_formalDifferenceSolution_residual`. Let `v` be the solution that agrees with `u`
at two consecutive indices `n₀` and `n₀ + 1`, and write `x = v / u`. The differences
`δ n = x (n + 1) - x n` satisfy

  `δ (n + 1) * u (n + 2) = g n * u n * δ n - r n * x (n + 1)`,

and since `‖g n u n‖ ≤ q ‖u (n + 2)‖` with `q < 1` (because `‖g₀‖ < ‖ρ‖²`;
`TauCeti.eventually_norm_mul_norm_le_of_isEquivalent_pow_mul_cpow`) and
`‖r n‖ ≤ B n^{-M-1} ‖u (n + 2)‖`
(`TauCeti.exists_eventually_norm_le_mul_norm_of_isEquivalent_pow_mul_cpow`), the forcing term
controls `δ` by induction from `n₀` (`TauCeti.norm_sub_le_mul_of_norm_sub_add_two_le`). So `x`
tends to a nonzero limit `L` with `x n - L = O(n^{1 - M})`, and `v / L` is a solution close to
`u`. Each order of the expansion needs its own `M`. The solutions so obtained differ by solutions
that are `o(ρⁿ n^α)`, and such a solution is exponentially smaller than `ρⁿ n^α` by
`TauCeti.isBigO_div_pow_of_tendsto_div`: the Casoratian of two solutions is multiplied by `g n` at
each step, so it is `O(γⁿ)`.

## References

* NIST Digital Library of Mathematical Functions, §2.9(i), equations (2.9.1)–(2.9.8),
  <https://dlmf.nist.gov/2.9.i>.
* R. Wong and H. Li, Asymptotic expansions for second-order linear difference equations,
  *J. Comput. Appl. Math.* 41 (1992), 65–94.
-/

public section

open Filter Finset Asymptotics
open scoped Topology

namespace TauCeti

/-! ### Solutions that are small relative to a large solution -/

/-- **Small solutions are exponentially small.** Let `‖g n‖ ≤ γ` for large `n`, and let `w` and
`v` be solutions of `w (n + 2) + f n * w (n + 1) + g n * w n = 0` for large `n` with
`rⁿ = O(w n)` and `γ < r ^ 2`. If `v n / w n → 0`, then `v n / w n = O((γ / r²)ⁿ)`.

The Casoratian `w n * v (n + 1) - w (n + 1) * v n` is multiplied by `g n` at each step, so it is
`O(γⁿ)`, and it is `w n * w (n + 1)` times the increment of `v / w`. -/
theorem isBigO_div_pow_of_tendsto_div {𝕜 : Type*} [NormedField 𝕜] {f g w v : ℕ → 𝕜} {γ r : ℝ}
    (hγr : γ < r ^ 2) (hgγ : ∀ᶠ n in atTop, ‖g n‖ ≤ γ)
    (hw : ∀ᶠ n in atTop, w (n + 2) + f n * w (n + 1) + g n * w n = 0)
    (hv : ∀ᶠ n in atTop, v (n + 2) + f n * v (n + 1) + g n * v n = 0)
    (hrw : (fun n ↦ r ^ n) =O[atTop] w) (hvw : Tendsto (fun n ↦ v n / w n) atTop (𝓝 0)) :
    (fun n ↦ v n / w n) =O[atTop] fun n ↦ (γ / r ^ 2) ^ n := by
  set θ := γ / r ^ 2
  set x : ℕ → 𝕜 := fun n ↦ v n / w n with hx_def
  obtain ⟨c, hc0, hc⟩ := hrw.exists_pos
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.1 (hw.and (hv.and (hgγ.and hc.bound)))
  have hγ0 : 0 ≤ γ := (norm_nonneg _).trans (hn₁ n₁ le_rfl).2.2.1
  have hr2 : 0 < r ^ 2 := hγ0.trans_lt hγr
  have hr : 0 < |r| := abs_pos.2 fun h ↦ by simp [h] at hr2
  have hθ0 : 0 ≤ θ := div_nonneg hγ0 hr2.le
  have hθ1 : θ < 1 := (div_lt_one hr2).2 hγr
  -- `|r|ⁿ ≤ c ‖w n‖`, so `w n ≠ 0`
  have hwlow (n : ℕ) (hn : n₁ ≤ n) : |r| ^ n ≤ c * ‖w n‖ := by
    simpa [Real.norm_eq_abs, abs_pow] using (hn₁ n hn).2.2.2
  have hw0 (n : ℕ) (hn : n₁ ≤ n) : w n ≠ 0 :=
    norm_pos_iff.1 (pos_of_mul_pos_right ((pow_pos hr n).trans_le (hwlow n hn)) hc0.le)
  -- the Casoratian is `O(γⁿ)`
  set C : ℕ → 𝕜 := fun n ↦ w n * v (n + 1) - w (n + 1) * v n with hC_def
  have hCle (k : ℕ) : ‖C (n₁ + k)‖ ≤ γ ^ k * ‖C n₁‖ :=
    norm_casoratian_add_le_of_difference_eq_zero (fun n hn ↦ (hn₁ n hn).1)
      (fun n hn ↦ (hn₁ n hn).2.1) (fun n hn ↦ (hn₁ n hn).2.2.1) k
  -- the increments of `x` are geometrically small
  set A := c ^ 2 * ‖C n₁‖ / |r| ^ (2 * n₁ + 1)
  have hΔ (k : ℕ) : ‖x (n₁ + k + 1) - x (n₁ + k)‖ ≤ A * θ ^ k := by
    have hpos₀ : 0 < ‖w (n₁ + k)‖ := norm_pos_iff.2 (hw0 _ (by omega))
    have hpos₁ : 0 < ‖w (n₁ + k + 1)‖ := norm_pos_iff.2 (hw0 _ (by omega))
    have hstep : x (n₁ + k + 1) - x (n₁ + k) = C (n₁ + k) / (w (n₁ + k) * w (n₁ + k + 1)) := by
      simp only [hx_def, hC_def]
      field_simp [norm_pos_iff.1 hpos₀, norm_pos_iff.1 hpos₁]
    rw [hstep, norm_div, norm_mul, div_le_iff₀ (mul_pos hpos₀ hpos₁)]
    calc ‖C (n₁ + k)‖ ≤ γ ^ k * ‖C n₁‖ := hCle k
      _ = A * θ ^ k * (|r| ^ (n₁ + k) * |r| ^ (n₁ + k + 1)) / c ^ 2 := by
        simp only [A, θ, ← sq_abs r, div_pow, ← pow_mul]
        field_simp
        ring
      _ ≤ A * θ ^ k * (c * ‖w (n₁ + k)‖ * (c * ‖w (n₁ + k + 1)‖)) / c ^ 2 := by
        gcongr <;> exact hwlow _ (by omega)
      _ = A * θ ^ k * (‖w (n₁ + k)‖ * ‖w (n₁ + k + 1)‖) := by
        field_simp
  -- since `x → 0`, `x` is bounded by the tail of the geometric series
  have hxle (k : ℕ) : ‖x (k + n₁)‖ ≤ A * θ ^ k / (1 - θ) := by
    simpa using dist_le_of_le_geometric_of_tendsto θ A hθ1 (f := fun k ↦ x (k + n₁))
      (fun k ↦ by
        rw [dist_comm, dist_eq_norm, add_right_comm k 1 n₁, add_comm k n₁]
        exact hΔ k)
      (hvw.comp (tendsto_add_atTop_nat n₁)) k
  refine IsBigO.of_bound (A / (1 - θ) * (θ ^ n₁)⁻¹) ?_
  filter_upwards [eventually_gt_atTop n₁] with n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn.le
  rw [Real.norm_of_nonneg (pow_nonneg hθ0 _), add_comm n₁ k]
  refine (hxle k).trans_eq ?_
  rw [mul_assoc, mul_comm (θ ^ n₁)⁻¹, ← pow_sub_of_lt θ (by omega), Nat.add_sub_cancel]
  ring

/-! ### A solution near an approximate solution -/

/-- The solution of `w (k + 2) + f k * w (k + 1) + g k * w k = 0` with `w 0 = a` and `w 1 = b`. -/
private noncomputable def forwardSolution (f g : ℕ → ℂ) (a b : ℂ) : ℕ → ℂ
  | 0 => a
  | 1 => b
  | k + 2 => -(f k * forwardSolution f g a b (k + 1) + g k * forwardSolution f g a b k)

private lemma forwardSolution_add_two (f g : ℕ → ℂ) (a b : ℂ) (k : ℕ) :
    forwardSolution f g a b (k + 2) + f k * forwardSolution f g a b (k + 1) +
      g k * forwardSolution f g a b k = 0 := by
  simp only [forwardSolution]
  ring

/-- For a solution `v` of the difference equation, the increments of `x = v / u` satisfy
`‖x (k + 2) - x (k + 1)‖ ≤ q ‖x (k + 1) - x k‖ + B φ k ‖x (k + 1)‖` when
`‖g k‖ ‖u k‖ ≤ q ‖u (k + 2)‖` and the residual of `u` is at most `B φ k ‖u (k + 2)‖`: the
increments satisfy
`(x (k + 2) - x (k + 1)) u (k + 2) = g k u k (x (k + 1) - x k) - r k x (k + 1)`. -/
private lemma norm_div_sub_div_le {f g u v : ℕ → ℂ} {φ : ℕ → ℝ} {q B : ℝ} (hu : ∀ k, u k ≠ 0)
    (hv : ∀ k, v (k + 2) + f k * v (k + 1) + g k * v k = 0)
    (hgu : ∀ k, ‖g k‖ * ‖u k‖ ≤ q * ‖u (k + 2)‖)
    (hr : ∀ k, ‖u (k + 2) + f k * u (k + 1) + g k * u k‖ ≤ B * φ k * ‖u (k + 2)‖) (k : ℕ) :
    ‖v (k + 2) / u (k + 2) - v (k + 1) / u (k + 1)‖ ≤
      q * ‖v (k + 1) / u (k + 1) - v k / u k‖ + B * φ k * ‖v (k + 1) / u (k + 1)‖ := by
  set x : ℕ → ℂ := fun j ↦ v j / u j
  set r := u (k + 2) + f k * u (k + 1) + g k * u k
  have hrec : (x (k + 2) - x (k + 1)) * u (k + 2) =
      g k * u k * (x (k + 1) - x k) - r * x (k + 1) := by
    have hxu (j : ℕ) : v j = x j * u j := (div_mul_cancel₀ _ (hu j)).symm
    have h := hv k
    rw [hxu (k + 2), hxu (k + 1), hxu k] at h
    linear_combination h
  refine le_of_mul_le_mul_right ?_ (norm_pos_iff.2 (hu (k + 2)))
  calc ‖x (k + 2) - x (k + 1)‖ * ‖u (k + 2)‖
      = ‖g k * u k * (x (k + 1) - x k) - r * x (k + 1)‖ := by rw [← hrec, norm_mul]
    _ ≤ ‖g k‖ * ‖u k‖ * ‖x (k + 1) - x k‖ + ‖r‖ * ‖x (k + 1)‖ := by
        refine (norm_sub_le _ _).trans_eq ?_
        rw [norm_mul, norm_mul, norm_mul]
    _ ≤ q * ‖u (k + 2)‖ * ‖x (k + 1) - x k‖ + B * φ k * ‖u (k + 2)‖ * ‖x (k + 1)‖ :=
        add_le_add (mul_le_mul_of_nonneg_right (hgu k) (norm_nonneg _))
          (mul_le_mul_of_nonneg_right (hr k) (norm_nonneg _))
    _ = (q * ‖x (k + 1) - x k‖ + B * φ k * ‖x (k + 1)‖) * ‖u (k + 2)‖ := by ring

/-- **A solution near an approximate solution.** Let `u` vanish nowhere, with
`‖g k‖ ‖u k‖ ≤ q ‖u (k + 2)‖`, and let the residual of `u` be at most `B φ k ‖u (k + 2)‖`, where
`φ ≥ 0` is summable with `θ φ k ≤ φ (k + 1)` and `q < θ`. If `2B / (θ - q) ∑ φ ≤ 1/2`, the
difference equation has a solution `w` with `‖w k - u k‖ ≤ 4B / (θ - q) ‖u k‖ ∑_{j ≥ k} φ j`.

The solution is a multiple of the one that agrees with `u` at `0` and `1`. -/
private theorem exists_solution_of_forward_bounds {f g u : ℕ → ℂ} {φ : ℕ → ℝ} {q θ B : ℝ}
    (hu : ∀ k, u k ≠ 0) (hgu : ∀ k, ‖g k‖ * ‖u k‖ ≤ q * ‖u (k + 2)‖)
    (hr : ∀ k, ‖u (k + 2) + f k * u (k + 1) + g k * u k‖ ≤ B * φ k * ‖u (k + 2)‖)
    (hφ0 : ∀ k, 0 ≤ φ k) (hφθ : ∀ k, θ * φ k ≤ φ (k + 1)) (hφ : Summable φ)
    (hqθ : q < θ) (hB : 0 ≤ B) (hsmall : 2 * B / (θ - q) * ∑' k, φ k ≤ 1 / 2) :
    ∃ w : ℕ → ℂ, (∀ k, w (k + 2) + f k * w (k + 1) + g k * w k = 0) ∧
      ∀ k, ‖w k - u k‖ ≤ 4 * B / (θ - q) * ‖u k‖ * ∑' j, φ (j + k) := by
  set v := forwardSolution f g (u 0) (u 1) with hv_def
  have hv := forwardSolution_add_two f g (u 0) (u 1)
  rw [← hv_def] at hv
  set x : ℕ → ℂ := fun k ↦ v k / u k with hx_def
  set D := 2 * B / (θ - q)
  have hq : 0 ≤ q := le_of_mul_le_mul_right (by simpa using
    (mul_nonneg (norm_nonneg (g 0)) (norm_nonneg (u 0))).trans (hgu 0)) (norm_pos_iff.2 (hu 2))
  -- the increments `δ k = x (k + 1) - x k` are at most `D φ k`, so `x` tends to `L ≠ 0`
  have hx0 : x 0 = 1 := by simp [hx_def, hv_def, forwardSolution, div_self (hu 0)]
  have hx1 : x 1 = 1 := by simp [hx_def, hv_def, forwardSolution, div_self (hu 1)]
  have hD : 0 ≤ D := div_nonneg (by positivity) (sub_pos.2 hqθ).le
  have hDθ : q * D + B * 2 = D * θ := by
    simp only [D]
    field_simp [(sub_pos.2 hqθ).ne']
    ring
  have hδφ : ∀ k, ‖x (k + 1) - x k‖ ≤ D * φ k :=
    norm_sub_le_mul_of_norm_sub_add_two_le (M := 2) (norm_div_sub_div_le hu hv hgu hr) hφ0 hφ hq hB
      hD (by rw [hx1, hx0, sub_self, norm_zero]; exact mul_nonneg hD (hφ0 0))
      (by rw [hx0, norm_one]; linarith)
      fun k ↦ by rw [hDθ, mul_assoc]; gcongr; exact hφθ k
  set δ : ℕ → ℂ := fun k ↦ x (k + 1) - x k
  have hδs : Summable δ := Summable.of_norm_bounded (hφ.mul_left D) hδφ
  set L := 1 + ∑' j, δ j with hL_def
  have htail (k : ℕ) : ‖∑' j, δ (j + k)‖ ≤ D * ∑' j, φ (j + k) :=
    tsum_of_norm_bounded (((summable_nat_add_iff k).2 hφ).hasSum.mul_left D) fun j ↦ hδφ _
  have hL : 1 / 2 ≤ ‖L‖ := by
    have h := (htail 0).trans (by simpa using hsmall)
    simp only [add_zero] at h
    have h₂ := norm_sub_norm_le (1 : ℂ) (-∑' j, δ j)
    rw [norm_one, norm_neg, sub_neg_eq_add, ← hL_def] at h₂
    linarith
  have hxL (k : ℕ) : x k - L = -∑' j, δ (j + k) := by
    rw [← sub_add_cancel (x k) (x 0), ← sum_range_sub x k, hx0, hL_def,
      ← hδs.sum_add_tsum_nat_add k]
    ring
  -- the solution is `v / L`
  refine ⟨fun k ↦ v k / L, fun k ↦ ?_, fun k ↦ ?_⟩
  · linear_combination hv k / L
  · have heq : v k / L - u k = u k * (x k - L) / L := by
      simp only [hx_def]
      field_simp [hu k, norm_pos_iff.1 (by linarith : (0 : ℝ) < ‖L‖)]
    rw [heq, hxL, norm_div, norm_mul, norm_neg, div_le_iff₀ (by linarith)]
    have hT : 0 ≤ ∑' j, φ (j + k) := tsum_nonneg fun j ↦ hφ0 _
    calc ‖u k‖ * ‖∑' j, δ (j + k)‖ ≤ ‖u k‖ * (D * ∑' j, φ (j + k)) := by
          gcongr
          exact htail k
      _ = 4 * B / (θ - q) * ‖u k‖ * (∑' j, φ (j + k)) * (1 / 2) := by
          simp only [D]
          ring
      _ ≤ 4 * B / (θ - q) * ‖u k‖ * (∑' j, φ (j + k)) * ‖L‖ := by
          gcongr

/-- Undoing a shift: the hypotheses of `exists_solution_of_forward_bounds`, for the weight
`φ k = k^{-(N + 2)}`, holding for large `k` give a solution for large `n` with
`w n - u n = O(‖u n‖ n^{-N})`. -/
private theorem exists_eventually_solution_near {f g u : ℕ → ℂ} {q θ B : ℝ} {N : ℕ}
    (hqθ : q < θ) (hB : 0 ≤ B)
    (h : ∀ᶠ k : ℕ in atTop, u k ≠ 0 ∧ ‖g k‖ * ‖u k‖ ≤ q * ‖u (k + 2)‖ ∧
      ‖u (k + 2) + f k * u (k + 1) + g k * u k‖ ≤ B * ((k : ℝ) ^ (N + 2))⁻¹ * ‖u (k + 2)‖ ∧
      θ * ((k : ℝ) ^ (N + 2))⁻¹ ≤ (((k + 1 : ℕ) : ℝ) ^ (N + 2))⁻¹) :
    ∃ w : ℕ → ℂ, (∀ᶠ n in atTop, w (n + 2) + f n * w (n + 1) + g n * w n = 0) ∧
      (fun n ↦ w n - u n) =O[atTop] fun n ↦ ‖u n‖ * ((n : ℝ) ^ N)⁻¹ := by
  set φ : ℕ → ℝ := fun k ↦ ((k : ℝ) ^ (N + 2))⁻¹
  have hφs : Summable φ := Real.summable_nat_pow_inv.2 (by omega)
  -- the tails of `φ` are eventually small, and are `O(k^{-N})`
  have hsmall : ∀ᶠ n₀ in atTop, 2 * B / (θ - q) * ∑' j, φ (j + n₀) ≤ 1 / 2 := by
    have h₀ := (tendsto_sum_nat_add φ).const_mul (2 * B / (θ - q))
    rw [mul_zero] at h₀
    exact h₀.eventually (eventually_le_nhds (by norm_num))
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.1 (h.and (eventually_ge_atTop 1))
  obtain ⟨n₀, hn₀, hsm⟩ := ((eventually_ge_atTop n₁).and hsmall).exists
  have hkj (j : ℕ) := hn₁ (j + n₀) (by omega)
  -- the shifted problem satisfies the hypotheses for every index
  obtain ⟨v, hv, hvu⟩ := exists_solution_of_forward_bounds (f := fun j ↦ f (j + n₀))
    (g := fun j ↦ g (j + n₀)) (u := fun j ↦ u (j + n₀)) (φ := fun j ↦ φ (j + n₀))
    (fun j ↦ (hkj j).1.1)
    (fun j ↦ by simpa only [add_right_comm j n₀] using (hkj j).1.2.1)
    (fun j ↦ by simpa only [add_right_comm j n₀] using (hkj j).1.2.2.1)
    (fun j ↦ by positivity)
    (fun j ↦ by simpa only [add_right_comm j n₀] using (hkj j).1.2.2.2)
    ((summable_nat_add_iff n₀).2 hφs) hqθ hB hsm
  refine ⟨fun k ↦ v (k - n₀), eventually_atTop.2 ⟨n₀, fun k hk ↦ ?_⟩, ?_⟩
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
    simpa only [add_right_comm j n₀, Nat.add_sub_cancel] using hv j
  · refine IsBigO.of_bound (4 * B / (θ - q) * ∑' i : ℕ, (((i : ℝ) + 1) ^ 2)⁻¹) ?_
    filter_upwards [eventually_ge_atTop n₀] with k hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
    have hj := hvu j
    simp only [add_assoc] at hj
    simp only [Nat.add_sub_cancel, norm_mul, norm_norm, norm_inv, norm_pow, Real.norm_natCast]
    have hT := tsum_inv_natCast_add_pow_le N (k := j + n₀) (by have := (hkj j).2; omega)
    have hB' : 0 ≤ 4 * B / (θ - q) * ‖u (j + n₀)‖ := by positivity
    calc ‖v j - u (j + n₀)‖ ≤ 4 * B / (θ - q) * ‖u (j + n₀)‖ * ∑' i, φ (i + (j + n₀)) := hj
      _ ≤ 4 * B / (θ - q) * ‖u (j + n₀)‖ *
          ((∑' i : ℕ, (((i : ℝ) + 1) ^ 2)⁻¹) * (((j + n₀ : ℕ) : ℝ) ^ N)⁻¹) :=
          mul_le_mul_of_nonneg_left hT hB'
      _ = 4 * B / (θ - q) * (∑' i : ℕ, (((i : ℝ) + 1) ^ 2)⁻¹) *
          (‖u (j + n₀)‖ * (((j + n₀ : ℕ) : ℝ) ^ N)⁻¹) := by ring

/-! ### Comparisons with a solution equivalent to `ρⁿ n^α` -/

/-- If `u n ∼ ρⁿ n^α` with `ρ ≠ 0`, then `‖ρ‖ᵏ k^{Re α} / ‖u (k + 2)‖ → ‖ρ‖⁻²`. -/
theorem tendsto_div_norm_add_two_of_isEquivalent_pow_mul_cpow {u : ℕ → ℂ} {ρ α : ℂ} (hρ : ρ ≠ 0)
    (hu : u ~[atTop] fun n : ℕ ↦ ρ ^ n * (n : ℂ) ^ α) :
    Tendsto (fun k : ℕ ↦ ‖ρ‖ ^ k * (k : ℝ) ^ α.re / ‖u (k + 2)‖) atTop (𝓝 (‖ρ‖ ^ 2)⁻¹) := by
  have he := (tendsto_norm_div_of_isEquivalent_pow_mul_cpow hρ hu).comp (tendsto_add_atTop_nat 2)
  have hc : Tendsto (fun k : ℕ ↦ ((k : ℝ) / (k + 2)) ^ α.re) atTop (𝓝 1) := by
    simpa using (tendsto_natCast_div_add_atTop (2 : ℝ)).rpow_const (Or.inl one_ne_zero)
  have h := (hc.div he one_ne_zero).div_const (‖ρ‖ ^ 2)
  rw [div_one, one_div] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hR : ‖ρ‖ ≠ 0 := norm_ne_zero_iff.2 hρ
  have hk₂ : ((k : ℝ) + 2) ^ α.re ≠ 0 := (Real.rpow_pos_of_pos (by positivity) _).ne'
  simp only [Pi.div_apply, Function.comp_apply]
  push_cast
  rw [Real.div_rpow hk'.le (by positivity)]
  rcases eq_or_ne ‖u (k + 2)‖ 0 with h0 | h0
  · simp [h0]
  · field_simp [hR, hk₂, h0]
    ring

/-- If `u n ∼ ρⁿ n^α` and `g n → g₀` with `‖g₀‖ < q ‖ρ‖²`, then
`‖g k‖ ‖u k‖ ≤ q ‖u (k + 2)‖` for large `k`. -/
theorem eventually_norm_mul_norm_le_of_isEquivalent_pow_mul_cpow {E : Type*}
    [SeminormedAddCommGroup E] {g : ℕ → E} {u : ℕ → ℂ} {g₀ : E} {ρ α : ℂ} {q : ℝ} (hρ : ρ ≠ 0)
    (hu : u ~[atTop] fun n : ℕ ↦ ρ ^ n * (n : ℂ) ^ α) (hg : Tendsto g atTop (𝓝 g₀))
    (hq : ‖g₀‖ < q * ‖ρ‖ ^ 2) : ∀ᶠ k in atTop, ‖g k‖ * ‖u k‖ ≤ q * ‖u (k + 2)‖ := by
  have hlim : ‖g₀‖ * 1 * (‖ρ‖ ^ 2)⁻¹ < q := by
    rwa [mul_one, ← div_eq_mul_inv, div_lt_iff₀ (pow_pos (norm_pos_iff.2 hρ) 2)]
  have h := (hg.norm.mul (tendsto_norm_div_of_isEquivalent_pow_mul_cpow hρ hu)).mul
    (tendsto_div_norm_add_two_of_isEquivalent_pow_mul_cpow hρ hu)
  filter_upwards [h.eventually (eventually_lt_nhds hlim), eventually_ge_atTop 1,
    (tendsto_add_atTop_nat 2).eventually
      (hu.eventually_ne_zero (eventually_pow_mul_cpow_ne_zero α hρ))]
    with k hk hk1 hu₂
  have hP : 0 < ‖ρ‖ ^ k * (k : ℝ) ^ α.re :=
    mul_pos (pow_pos (norm_pos_iff.2 hρ) k) (Real.rpow_pos_of_pos (by exact_mod_cast hk1) _)
  have hlt : ‖g k‖ * ‖u k‖ / ‖u (k + 2)‖ < q := by
    refine lt_of_eq_of_lt ?_ hk
    field_simp [hP.ne', norm_ne_zero_iff.2 hu₂]
  exact ((div_lt_iff₀ (norm_pos_iff.2 hu₂)).1 hlt).le

/-- If `u n ∼ ρⁿ n^α` with `ρ ≠ 0` and `r k = O(‖ρ‖ᵏ k^{Re α} φ k)` with `φ ≥ 0`, then
`‖r k‖ ≤ B φ k ‖u (k + 2)‖` for some `B ≥ 0` and all large `k`. -/
theorem exists_eventually_norm_le_mul_norm_of_isEquivalent_pow_mul_cpow {E : Type*}
    [SeminormedAddCommGroup E] {u : ℕ → ℂ} {r : ℕ → E} {φ : ℕ → ℝ} {ρ α : ℂ}
    (hρ : ρ ≠ 0) (hu : u ~[atTop] fun n : ℕ ↦ ρ ^ n * (n : ℂ) ^ α) (hφ : ∀ k, 0 ≤ φ k)
    (hr : r =O[atTop] fun k : ℕ ↦ ‖ρ‖ ^ k * (k : ℝ) ^ α.re * φ k) :
    ∃ B, 0 ≤ B ∧ ∀ᶠ k in atTop, ‖r k‖ ≤ B * φ k * ‖u (k + 2)‖ := by
  obtain ⟨C, hC0, hC⟩ := hr.exists_nonneg
  refine ⟨C * (‖ρ‖ ^ 2)⁻¹ + 1, by positivity, ?_⟩
  have hs := (tendsto_div_norm_add_two_of_isEquivalent_pow_mul_cpow hρ hu).const_mul C
  filter_upwards [hC.bound, hs.eventually (eventually_le_nhds (lt_add_one _)),
    (tendsto_add_atTop_nat 2).eventually
      (hu.eventually_ne_zero (eventually_pow_mul_cpow_ne_zero α hρ))]
    with k hk hsk hu₂
  rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (hφ k))] at hk
  calc ‖r k‖ ≤ C * (‖ρ‖ ^ k * (k : ℝ) ^ α.re * φ k) := hk
    _ = C * (‖ρ‖ ^ k * (k : ℝ) ^ α.re / ‖u (k + 2)‖) * φ k * ‖u (k + 2)‖ := by
        field_simp [norm_ne_zero_iff.2 hu₂]
    _ ≤ (C * (‖ρ‖ ^ 2)⁻¹ + 1) * φ k * ‖u (k + 2)‖ := by
        gcongr
        exact hφ k

/-! ### Solutions to a given order -/

/-- **Bounds for the root of larger modulus.** Let `u n ∼ ρⁿ n^α`, let `g n → g₀` with
`‖g₀‖ < ‖ρ‖²`, and let the residual of `u` be `O(|ρ|ⁿ n^{Re α - N - 2})`. Then for some `q < θ`
and `B ≥ 0` the hypotheses of `exists_eventually_solution_near` hold for large `k`. -/
private lemma exists_eventually_forward_bounds {f g u : ℕ → ℂ} {ρ α g₀ : ℂ} {N : ℕ}
    (hu : u ~[atTop] fun n : ℕ ↦ ρ ^ n * (n : ℂ) ^ α) (hg : Tendsto g atTop (𝓝 g₀))
    (hgt : ‖g₀‖ < ‖ρ‖ ^ 2)
    (hr : (fun k ↦ u (k + 2) + f k * u (k + 1) + g k * u k) =O[atTop]
      fun k : ℕ ↦ ‖ρ‖ ^ k * (k : ℝ) ^ (α.re - (N + 2))) :
    ∃ q θ B : ℝ, q < θ ∧ 0 ≤ B ∧ ∀ᶠ k : ℕ in atTop, u k ≠ 0 ∧
      ‖g k‖ * ‖u k‖ ≤ q * ‖u (k + 2)‖ ∧
      ‖u (k + 2) + f k * u (k + 1) + g k * u k‖ ≤ B * ((k : ℝ) ^ (N + 2))⁻¹ * ‖u (k + 2)‖ ∧
      θ * ((k : ℝ) ^ (N + 2))⁻¹ ≤ (((k + 1 : ℕ) : ℝ) ^ (N + 2))⁻¹ := by
  have hR2 : 0 < ‖ρ‖ ^ 2 := (norm_nonneg _).trans_lt hgt
  have hρ : ρ ≠ 0 := fun h ↦ by simp [h] at hR2
  set q := (2 * ‖g₀‖ + ‖ρ‖ ^ 2) / (3 * ‖ρ‖ ^ 2)
  set θ := (‖g₀‖ + 2 * ‖ρ‖ ^ 2) / (3 * ‖ρ‖ ^ 2)
  have hq : ‖g₀‖ < q * ‖ρ‖ ^ 2 := by
    rw [div_mul_eq_mul_div, lt_div_iff₀ (by positivity)]
    nlinarith
  -- the residual is `O(|ρ|ᵏ k^{Re α} k^{-(N + 2)})`
  have hr' : (fun k ↦ u (k + 2) + f k * u (k + 1) + g k * u k) =O[atTop]
      fun k : ℕ ↦ ‖ρ‖ ^ k * (k : ℝ) ^ α.re * ((k : ℝ) ^ (N + 2))⁻¹ := by
    refine hr.congr' EventuallyEq.rfl ?_
    filter_upwards [eventually_ge_atTop 1] with k hk
    rw [Real.rpow_sub (by exact_mod_cast hk), div_eq_mul_inv, mul_assoc]
    norm_cast
  obtain ⟨B, hB, hrB⟩ := exists_eventually_norm_le_mul_norm_of_isEquivalent_pow_mul_cpow hρ hu
    (fun k ↦ by positivity) hr'
  have hθ : θ < 1 := (div_lt_one (by positivity)).2 (by linarith)
  refine ⟨q, θ, B, div_lt_div_of_pos_right (by linarith) (by positivity), hB, ?_⟩
  filter_upwards [hu.eventually_ne_zero (eventually_pow_mul_cpow_ne_zero α hρ),
    eventually_norm_mul_norm_le_of_isEquivalent_pow_mul_cpow hρ hu hg hq, hrB,
    eventually_mul_inv_pow_le_inv_add_one_pow hθ (N + 2)] with k h₁ h₂ h₃ h₄
  exact ⟨h₁, h₂, h₃, h₄⟩

/-- **A solution to a given order.** For every `N`, there is a solution for large `n` whose
difference from each truncation `ρⁿ n^α ∑_{s < N'} aₛ n⁻ˢ` with `N' ≤ N` is
`O(|ρ|ⁿ n^{Re α - N'})`. -/
private theorem exists_eventually_solution_isBigO_of_norm_sq_gt {f g fs gs : ℕ → ℂ} {ρ α : ℂ}
    (hf : HasAsymptoticExpansion atTop (fun q (n : ℕ) ↦ (n : ℂ)⁻¹ ^ q) fs f)
    (hg : HasAsymptoticExpansion atTop (fun q (n : ℕ) ↦ (n : ℂ)⁻¹ ^ q) gs g)
    (hg₀ : Tendsto g atTop (𝓝 (gs 0)))
    (hρ : ρ ^ 2 + fs 0 * ρ + gs 0 = 0) (hα : α * (fs 0 * ρ + 2 * gs 0) = fs 1 * ρ + gs 1)
    (hgt : ‖gs 0‖ < ‖ρ‖ ^ 2) (N : ℕ) :
    ∃ w : ℕ → ℂ, (∀ᶠ n in atTop, w (n + 2) + f n * w (n + 1) + g n * w n = 0) ∧
      ∀ N' ≤ N, (fun n ↦ w n - formalDifferenceSolution (differenceCoeff fs gs ρ α) ρ α N' n)
        =O[atTop] fun n ↦ ‖ρ‖ ^ n * (n : ℝ) ^ (α.re - N') := by
  set a := differenceCoeff fs gs ρ α
  have hρ₀ := mul_ne_zero_of_norm_sq_ne hρ hgt.ne'
  -- the comparison function `u` is the truncation after `N + 1` terms
  obtain ⟨u, hu_def⟩ : ∃ u, u = formalDifferenceSolution a ρ α (N + 1) := ⟨_, rfl⟩
  have hres := isBigO_formalDifferenceSolution_residual (a := a) (N := N + 1) hρ hα
    (fun s _ ↦ mul_differenceCoeff hρ₀ α s) (by simpa [inv_pow] using hf.isBigO (N + 1 + 1))
    (by simpa [inv_pow] using hg.isBigO (N + 1 + 1))
  rw [← hu_def, Nat.cast_add_one, add_assoc (N : ℝ), one_add_one_eq_two] at hres
  have hequiv := isEquivalent_formalDifferenceSolution (differenceCoeff_zero fs gs ρ α) ρ α
    (Nat.le_add_left 1 N)
  rw [← hu_def] at hequiv
  obtain ⟨q, θ, B, hqθ, hB, hbounds⟩ := exists_eventually_forward_bounds hequiv hg₀ hgt hres
  obtain ⟨w, hw, hwu⟩ := exists_eventually_solution_near hqθ hB hbounds
  refine ⟨w, hw, fun N' hN' ↦ ?_⟩
  -- `‖u n‖ n^{-N} = O(|ρ|ⁿ n^{Re α - N'})`
  have hun : (fun n : ℕ ↦ ‖u n‖ * ((n : ℝ) ^ N)⁻¹) =O[atTop]
      fun n ↦ ‖ρ‖ ^ n * (n : ℝ) ^ (α.re - N') := by
    have h₁ : (fun n ↦ ‖u n‖) =O[atTop] fun n : ℕ ↦ ‖ρ ^ n * (n : ℂ) ^ α‖ :=
      hequiv.isBigO.norm_left.norm_right
    refine (h₁.mul (isBigO_refl (fun n : ℕ ↦ ((n : ℝ) ^ N)⁻¹) atTop)).trans
      (IsBigO.of_bound 1 ?_)
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hN'N : (N' : ℝ) ≤ N := by exact_mod_cast hN'
    have hpow : (n : ℝ) ^ α.re * ((n : ℝ) ^ N)⁻¹ ≤ (n : ℝ) ^ (α.re - N') := by
      rw [← Real.rpow_natCast, ← Real.rpow_neg (by positivity), ← Real.rpow_add (by positivity)]
      exact Real.rpow_le_rpow_of_exponent_le hn' (by linarith)
    rw [norm_pow_mul_cpow ρ α (by omega), one_mul, Real.norm_of_nonneg (by positivity),
      Real.norm_of_nonneg (by positivity), mul_assoc]
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  have hut := isBigO_formalDifferenceSolution_sub a ρ α (hN'.trans N.le_succ)
  rw [← hu_def] at hut
  exact ((hwu.trans hun).add hut).congr_left fun n ↦ by ring

/-! ### The dominant solution -/

/-- Two solutions for large `n` that are both asymptotic to `ρⁿ n^α`, where `g n → g₀` with
`‖g₀‖ < ‖ρ‖²`, differ by `O(|ρ|ⁿ n^{Re α - N})` for every `N`: their difference is `o(ρⁿ n^α)`,
hence exponentially small by `TauCeti.isBigO_div_pow_of_tendsto_div`. -/
private lemma isBigO_sub_of_isEquivalent_of_norm_sq_gt {f g w w' : ℕ → ℂ} {ρ α g₀ : ℂ}
    (hg : Tendsto g atTop (𝓝 g₀)) (hgt : ‖g₀‖ < ‖ρ‖ ^ 2)
    (hw : ∀ᶠ n in atTop, w (n + 2) + f n * w (n + 1) + g n * w n = 0)
    (hw' : ∀ᶠ n in atTop, w' (n + 2) + f n * w' (n + 1) + g n * w' n = 0)
    (hwe : w ~[atTop] fun n : ℕ ↦ ρ ^ n * (n : ℂ) ^ α)
    (hw'e : w' ~[atTop] fun n : ℕ ↦ ρ ^ n * (n : ℂ) ^ α) (N : ℕ) :
    (fun n ↦ w' n - w n) =O[atTop] fun n ↦ ‖ρ‖ ^ n * (n : ℝ) ^ (α.re - N) := by
  have hR : 0 < ‖ρ‖ := lt_of_le_of_ne (norm_nonneg _) fun h ↦ by
    rw [← h] at hgt
    exact (norm_nonneg _).not_gt (by simpa using hgt)
  -- choose `γ` and `r` with `‖g₀‖ < γ < r² < ‖ρ‖²`
  obtain ⟨γ, hγ₁, hγ₂⟩ := exists_between hgt
  obtain ⟨r, hr₁, hr₂⟩ := exists_between ((Real.sqrt_lt' hR).2 hγ₂)
  have hr : 0 < r := (Real.sqrt_nonneg _).trans_lt hr₁
  have hγr : γ < r ^ 2 := (Real.sqrt_lt' hr).1 hr₁
  -- `rⁿ = O(w n)`, and `w' - w` is a solution which is `o(w)`
  have hrw : (fun n ↦ r ^ n) =O[atTop] w :=
    (isLittleO_pow_pow_mul_cpow_of_norm_lt α (by rwa [Real.norm_of_nonneg hr.le])).isBigO.trans
      hwe.symm.isBigO
  have hv : ∀ᶠ n in atTop, (w' (n + 2) - w (n + 2)) + f n * (w' (n + 1) - w (n + 1)) +
      g n * (w' n - w n) = 0 := by
    filter_upwards [hw, hw'] with n h h'
    linear_combination h' - h
  have hvw : (fun n ↦ w' n - w n) =o[atTop] w :=
    ((hw'e.isLittleO.sub hwe.isLittleO).congr_left fun n ↦ by simp).trans_isBigO
      hwe.symm.isBigO
  exact isBigO_norm_pow_mul_rpow_of_isBigO_div_pow (norm_pos_iff.1 hR)
    (div_nonneg ((norm_nonneg _).trans hγ₁.le) (by positivity))
    ((div_lt_one (by positivity)).2 hγr) hwe (isBigO_div_pow_of_tendsto_div hγr
      (hg.norm.eventually (eventually_le_nhds hγ₁)) hw hv hrw hvw.tendsto_div_nhds_zero) N

/-- **The dominant solution of a difference equation, for large `n`** (DLMF 2.9.8). Let
`f n ∼ ∑ fₛ n⁻ˢ` and `g n ∼ ∑ gₛ n⁻ˢ`, let `ρ` be a root of `ρ² + f₀ ρ + g₀ = 0` (DLMF 2.9.5)
with `‖g₀‖ < ‖ρ‖ ^ 2`, that is, of strictly larger modulus than the other root, and let `α`
satisfy DLMF 2.9.6. Then there is a solution of `w (n + 2) + f n * w (n + 1) + g n * w n = 0` for
large `n` with the expansion `w n ∼ ρⁿ n^α ∑ aₛ n⁻ˢ`, the coefficients `aₛ` being those of
DLMF 2.9.7 (`TauCeti.differenceCoeff`). -/
theorem exists_eventually_difference_solution_of_norm_sq_gt {f g fs gs : ℕ → ℂ} {ρ α : ℂ}
    (hf : HasAsymptoticExpansion atTop (fun q (n : ℕ) ↦ (n : ℂ)⁻¹ ^ q) fs f)
    (hg : HasAsymptoticExpansion atTop (fun q (n : ℕ) ↦ (n : ℂ)⁻¹ ^ q) gs g)
    (hρ : ρ ^ 2 + fs 0 * ρ + gs 0 = 0) (hα : α * (fs 0 * ρ + 2 * gs 0) = fs 1 * ρ + gs 1)
    (hgt : ‖gs 0‖ < ‖ρ‖ ^ 2) :
    ∃ w : ℕ → ℂ, (∀ᶠ n in atTop, w (n + 2) + f n * w (n + 1) + g n * w n = 0) ∧
      HasAsymptoticExpansion atTop (fun s (n : ℕ) ↦ ρ ^ n * (n : ℂ) ^ α * (n : ℂ)⁻¹ ^ s)
        (differenceCoeff fs gs ρ α) w := by
  set a := differenceCoeff fs gs ρ α
  have hg₀ : Tendsto g atTop (𝓝 (gs 0)) := by
    have h := (hg.isBigO 1).trans_tendsto
      (by simpa using tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℂ))
    simpa using h.add_const (gs 0)
  -- a remainder `O(|ρ|ⁿ n^{Re α - 1})` after the leading term makes `v` asymptotic to `ρⁿ n^α`
  have hlead {v : ℕ → ℂ}
      (hv : (fun n ↦ v n - formalDifferenceSolution a ρ α 1 n) =O[atTop]
        fun n ↦ ‖ρ‖ ^ n * (n : ℝ) ^ (α.re - (1 : ℕ))) :
      v ~[atTop] fun n : ℕ ↦ ρ ^ n * (n : ℂ) ^ α := by
    refine (hv.trans_isLittleO (isLittleO_norm_pow_mul_rpow_pow_mul_cpow ρ ?_)).congr_left
      fun n ↦ ?_
    · simp
    · simp [formalDifferenceSolution_def, a]
  obtain ⟨w, hw, hwO⟩ := exists_eventually_solution_isBigO_of_norm_sq_gt hf hg hg₀ hρ hα hgt 1
  refine ⟨w, hw, .of_isBigO fun N ↦ ?_⟩
  -- the solution `w'` built to order `N` differs from `w` by `O(|ρ|ⁿ n^{Re α - N})`
  obtain ⟨w', hw', hw'O⟩ := exists_eventually_solution_isBigO_of_norm_sq_gt hf hg hg₀ hρ hα hgt
    (N + 1)
  have hsub := isBigO_sub_of_isEquivalent_of_norm_sq_gt hg₀ hgt hw hw' (hlead (hwO 1 le_rfl))
    (hlead (hw'O 1 (by omega))) N
  refine (((hw'O N (by omega)).sub hsub).trans (IsBigO.of_bound 1 ?_)).congr'
    (Eventually.of_forall fun n ↦ ?_) EventuallyEq.rfl
  · filter_upwards [eventually_ge_atTop 1] with n hn
    rw [one_mul, norm_pow_mul_cpow_mul_inv_pow ρ α N (by omega),
      Real.norm_of_nonneg (by positivity)]
  · simp only [formalDifferenceSolution_def, mul_sum, smul_eq_mul]
    rw [sub_sub_sub_cancel_left]
    exact congrArg _ (sum_congr rfl fun s _ ↦ by ring)

/-- **The dominant solution of a difference equation** (DLMF 2.9.8). Under the hypotheses of
`TauCeti.exists_eventually_difference_solution_of_norm_sq_gt`, if moreover `g` vanishes nowhere,
there is a solution of `w (n + 2) + f n * w (n + 1) + g n * w n = 0` for all `n` with the
expansion `w n ∼ ρⁿ n^α ∑ aₛ n⁻ˢ`. -/
theorem exists_difference_solution_of_norm_sq_gt {f g fs gs : ℕ → ℂ} {ρ α : ℂ}
    (hf : HasAsymptoticExpansion atTop (fun q (n : ℕ) ↦ (n : ℂ)⁻¹ ^ q) fs f)
    (hg : HasAsymptoticExpansion atTop (fun q (n : ℕ) ↦ (n : ℂ)⁻¹ ^ q) gs g)
    (hg0 : ∀ n, g n ≠ 0) (hρ : ρ ^ 2 + fs 0 * ρ + gs 0 = 0)
    (hα : α * (fs 0 * ρ + 2 * gs 0) = fs 1 * ρ + gs 1) (hgt : ‖gs 0‖ < ‖ρ‖ ^ 2) :
    ∃ w : ℕ → ℂ, (∀ n, w (n + 2) + f n * w (n + 1) + g n * w n = 0) ∧
      HasAsymptoticExpansion atTop (fun s (n : ℕ) ↦ ρ ^ n * (n : ℂ) ^ α * (n : ℂ)⁻¹ ^ s)
        (differenceCoeff fs gs ρ α) w := by
  obtain ⟨w, hw, hexp⟩ := exists_eventually_difference_solution_of_norm_sq_gt hf hg hρ hα hgt
  obtain ⟨w', hw', hw'w⟩ := exists_difference_solution_eventuallyEq hg0 hw
  exact ⟨w', hw', hexp.congr' hw'w.symm⟩

end TauCeti
