/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import TauCeti.Analysis.Matrix.HardThreshold
public import TauCeti.Probability.Moments.CenteredTruncation
import TauCeti.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.MeasureTheory.Function.LpSeminorm.Truncation
import TauCeti.Probability.IdentDistrib
import TauCeti.Probability.LargeEntries

/-!
# Operator-norm truncation of rectangular data matrices

Let `x` be an array, indexed by `ℕ × ℕ`, of complex entries with a common law `ν` of finite
fourth moment that are independent within each row and within each column, and let `Xₙ` be its
top-left `p(n) × n` corner, where `p(n) ≤ K n` eventually. Cut off the entries at the
unnormalized level `n^a` with `a > 1/4`. Almost surely every row and every column of `Xₙ`
eventually has a bounded number of entries above the cutoff
(`TauCeti.Probability.ae_eventually_card_filter_lt_norm_lt`), and the largest entry of `Xₙ` is
`o(√n)` (`TauCeti.Probability.ae_eventually_norm_le_mul_sqrt`). The finite Schur test combines
these two facts: the discarded part of `Xₙ`, its entrywise hard threshold at `n^a`, has
operator norm `o(√n)` almost surely. When `ν` is centred, the mean subtracted in recentring
the retained entries contributes `o(√n)` as well. Hence `Xₙ` and the matrix of centered
truncations of its entries at `n^a` differ by `o(√n)` in operator norm almost surely. The
centered truncations are bounded and centred, so this reduces operator-norm bounds for `Xₙ / √n`,
and with them the upper edge of the sample covariance spectrum, to bounded centred entries.

## Main results

The results about the corners are filed under `TauCeti.Probability.SampleCovariance`.

* `SampleCovariance.ae_tendsto_l2_opNorm_hardThreshold_div_sqrt`: the discarded part has
  operator norm `o(√n)` almost surely.
* `SampleCovariance.ae_tendsto_l2_opNorm_sub_centeredTruncation_div_sqrt`: the corners and
  their centered truncations differ by `o(√n)` in operator norm almost surely.

## References

* Y. Q. Yin, Z. D. Bai, P. R. Krishnaiah, *On the limit of the largest eigenvalue of the large
  dimensional sample covariance matrix*, Probab. Theory Related Fields 78 (1988).
* Z. D. Bai, *Methodologies in spectral analysis of large dimensional random matrices, a review*,
  Statistica Sinica 9 (1999), §2.2.2.
* T. Tao, *Topics in Random Matrix Theory*, AMS (2012), §2.3.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Matrix Set
open scoped Topology ENNReal NNReal Matrix.Norms.L2Operator

namespace TauCeti.Probability.SampleCovariance

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

section OperatorNorm

variable {x : ℕ × ℕ → Ω → ℂ} {ν : Measure ℂ} {p : ℕ → ℕ}

/-- Entrywise, a corner minus the matrix of centered truncations of its entries at `n ^ a` is the
hard threshold of the corner at `n ^ a` plus the constant matrix of the common truncated mean. -/
private theorem of_sub_of_centeredTruncation_eq (hx : ∀ ij, HasLaw (x ij) ν P) (n : ℕ) (a : ℝ)
    (ω : Ω) :
    (Matrix.of fun (i : Fin (p n)) (j : Fin n) ↦ x (i, j) ω) -
        (Matrix.of fun (i : Fin (p n)) (j : Fin n) ↦
          centeredTruncation (x (i, j)) P ((n : ℝ≥0) ^ a) ω) =
      (Matrix.of fun (i : Fin (p n)) (j : Fin n) ↦ x (i, j) ω).hardThreshold ((n : ℝ) ^ a) +
        Matrix.of fun _ _ ↦ ∫ z, {z : ℂ | ‖id z‖ ≤ (n : ℝ) ^ a}.indicator id z ∂ν := by
  ext i j
  have hc := ((hx (i, j)).identDistrib HasLaw.id).integral_indicator_setOf_norm_le_eq
    ((n : ℝ) ^ a)
  simp only [Matrix.sub_apply, Matrix.add_apply, of_apply, hardThreshold_apply,
    centeredTruncation_def, NNReal.coe_rpow, NNReal.coe_natCast, hc]
  by_cases h : ‖x (i, j) ω‖ ≤ (n : ℝ) ^ a
  · simp [h, not_lt.2 h]
  · simp [h, lt_of_not_ge h]

/-- **The discarded part of the corners.** Let the array have complex entries with a common law
`ν` of finite fourth moment, independent within each row and within each column, and let
`p(n) ≤ K n` eventually. For `a > 1/4`, the
entrywise hard threshold at `n ^ a` of the `p(n) × n` corner, the matrix of its entries of norm
above `n ^ a`, has operator norm `o(√n)` almost surely. -/
theorem ae_tendsto_l2_opNorm_hardThreshold_div_sqrt (hx : ∀ ij, HasLaw (x ij) ν P)
    (hrow : ∀ i, iIndepFun (fun j ↦ x (i, j)) P)
    (hcol : ∀ j, iIndepFun (fun i ↦ x (i, j)) P) (h4 : MemLp id 4 ν) {K : ℝ}
    (hp : ∀ᶠ n in atTop, (p n : ℝ) ≤ K * n) {a : ℝ} (ha : 1 / 4 < a) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦
      ‖(Matrix.of fun (i : Fin (p n)) (j : Fin n) ↦ x (i, j) ω).hardThreshold ((n : ℝ) ^ a)‖ /
        √n) atTop (𝓝 0) := by
  obtain ⟨q, hq⟩ := exists_nat_gt (2 / (4 * a - 1))
  have hq' : 2 < q * (((4 : ℕ) : ℝ) * a - 1) := by
    push_cast
    exact (div_lt_iff₀ (by linarith)).1 hq
  have h4' : Integrable (fun z : ℂ ↦ ‖z‖ ^ 4) ν := h4.integrable_norm_pow (p := 4) (by norm_num)
  filter_upwards [ae_eventually_card_filter_lt_norm_lt hx hrow hcol h4' hp hq',
    ae_eventually_norm_le_mul_sqrt hx h4' hp] with ω hcount hmax
  refine tendsto_order.2 ⟨fun r hr ↦ .of_forall fun n ↦ hr.trans_le (by positivity), fun r hr ↦ ?_⟩
  have hε : 0 < r / (q + 1 : ℝ) := by positivity
  filter_upwards [hcount, hmax _ hε, eventually_gt_atTop 0] with n ⟨hrow, hcol⟩ hentry hn
  have hsqrt : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  rw [div_lt_iff₀ hsqrt]
  refine ((Matrix.of fun (i : Fin (p n)) (j : Fin n) ↦ x (i, j) ω).l2_opNorm_hardThreshold_le _
    (M := r / (q + 1) * √n) (by positivity) (fun i ↦ (hrow i).le) (fun j ↦ (hcol j).le)
    (fun i j _ ↦ by simpa only [of_apply] using hentry i j)).trans_lt ?_
  calc
    (q : ℝ) * (r / (q + 1) * √n) < (q + 1) * (r / (q + 1) * √n) := by gcongr; linarith
    _ = r * √n := by field_simp

/-- **Operator-norm truncation of the corners.** Let the array have complex entries with a common
centred law `ν` of finite fourth moment, independent within each row and within each column, and
let `p(n) ≤ K n` eventually. For
`a > 1/4`, the `p(n) × n` corner and the matrix of centered truncations of its entries at
`n ^ a` differ by `o(√n)` in operator norm almost surely. -/
theorem ae_tendsto_l2_opNorm_sub_centeredTruncation_div_sqrt (hx : ∀ ij, HasLaw (x ij) ν P)
    (hrow : ∀ i, iIndepFun (fun j ↦ x (i, j)) P)
    (hcol : ∀ j, iIndepFun (fun i ↦ x (i, j)) P) (h4 : MemLp id 4 ν)
    (hmean : ∫ z, z ∂ν = 0) {K : ℝ}
    (hp : ∀ᶠ n in atTop, (p n : ℝ) ≤ K * n) {a : ℝ} (ha : 1 / 4 < a) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ ‖(Matrix.of fun (i : Fin (p n)) (j : Fin n) ↦ x (i, j) ω) -
      Matrix.of fun (i : Fin (p n)) (j : Fin n) ↦
        centeredTruncation (x (i, j)) P ((n : ℝ≥0) ^ a) ω‖ / √n) atTop (𝓝 0) := by
  -- The common mean of the truncated entries at size `n`.
  let c (n : ℕ) : ℂ := ∫ z, {z : ℂ | ‖id z‖ ≤ (n : ℝ) ^ a}.indicator id z ∂ν
  -- The constant matrix of the means has operator norm at most `√(p n) * ‖c n‖ * √n`.
  have hconst (n : ℕ) :
      ‖(Matrix.of fun (_ : Fin (p n)) (_ : Fin n) ↦ c n)‖ / √n ≤ √(p n) * ‖c n‖ := by
    refine div_le_of_le_mul₀ (Real.sqrt_nonneg _) (by positivity) ?_
    refine (Matrix.l2_opNorm_le_sqrt_mul_of_row_col_sum_le
      (Matrix.of fun (_ : Fin (p n)) (_ : Fin n) ↦ c n) (r := n * ‖c n‖) (c := p n * ‖c n‖)
      (fun _ ↦ by simp) (fun _ ↦ by simp)).trans_eq ?_
    rw [show (n : ℝ) * ‖c n‖ * (p n * ‖c n‖) = (√(p n) * ‖c n‖ * √n) ^ 2 by
      rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _)]
      ring, Real.sqrt_sq (by positivity)]
  -- `√(p n) / (n ^ a) ^ 3 → 0`, comparing `p n` with `(|K| + 1) n`.
  have hquot : Tendsto (fun n ↦ √(p n) / ((n : ℝ) ^ a) ^ 3) atTop (𝓝 0) := by
    have hlim := ((tendsto_sqrt_div_rpow_pow_atTop_nhds_zero (a := a) (k := 3)
      (by push_cast; linarith)).comp tendsto_natCast_atTop_atTop).const_mul √(|K| + 1)
    rw [mul_zero] at hlim
    refine squeeze_zero' (.of_forall fun n ↦ by positivity) ?_ hlim
    filter_upwards [hp] with n hn
    dsimp only [Function.comp_apply]
    rw [← mul_div_assoc, ← Real.sqrt_mul (by positivity)]
    gcongr
    exact hn.trans (by nlinarith [le_abs_self K, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  -- The means vanish fast enough, by the fourth moment.
  have hc : Tendsto (fun n ↦ √(p n) * ‖c n‖) atTop (𝓝 0) :=
    h4.tendsto_mul_norm_integral_indicator_setOf_norm_le_nhds_zero (k := 3) hmean hquot
  filter_upwards [ae_tendsto_l2_opNorm_hardThreshold_div_sqrt hx hrow hcol h4 hp ha]
    with ω hω
  refine squeeze_zero (fun n ↦ by positivity) (fun n ↦ ?_) (by simpa using hω.add hc)
  rw [of_sub_of_centeredTruncation_eq hx]
  calc
    _ ≤ (‖(Matrix.of fun (i : Fin (p n)) (j : Fin n) ↦ x (i, j) ω).hardThreshold ((n : ℝ) ^ a)‖ +
        ‖(Matrix.of fun (_ : Fin (p n)) (_ : Fin n) ↦ c n)‖) / √n :=
      div_le_div_of_nonneg_right (norm_add_le _ _) (Real.sqrt_nonneg _)
    _ ≤ _ := by
      rw [add_div]
      exact add_le_add le_rfl (hconst n)

end OperatorNorm

end TauCeti.Probability.SampleCovariance
