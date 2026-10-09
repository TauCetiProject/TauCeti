/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import TauCeti.Analysis.InnerProductSpace.PiL2
public import TauCeti.MeasureTheory.Integral.CalderonZygmund.Decomposition

/-!
# The John–Nirenberg inequality

Let `Q₀` be a dyadic cube in `ℝⁿ = ι → ℝ`, `n ≥ 1`, and let `f : ℝⁿ → E` be integrable on `Q₀`
with **dyadic mean oscillation** at most `M` on `Q₀`: for every dyadic cube `Q ⊆ Q₀`,

`⨍_Q ‖f - f_Q‖ ≤ M`, where `f_Q = ⨍_Q f`.

The **John–Nirenberg inequality** says that `f` then deviates from its average exponentially
rarely:

`|{x ∈ Q₀ : ‖f x - f_{Q₀}‖ > s}| ≤ 2 exp (-(log 2) s / (2ⁿ⁺¹ M)) |Q₀|`

for every `s` (`TauCeti.volume_lt_norm_sub_setAverage_le`). Consequently `exp (σ ‖f - f_{Q₀}‖)`
is integrable on `Q₀`, with average bounded in terms of `σ M` and `n` alone, whenever
`exp (2ⁿ⁺¹ σ M) < 2` (`TauCeti.setLIntegral_exp_mul_norm_sub_setAverage_le`). So a function of
bounded mean oscillation is exponentially integrable, far beyond the `L¹` control its definition
provides. This is what lets Moser's proof of the Harnack inequality cross from bounds on negative
powers of a positive supersolution to bounds on positive powers: the logarithm of such a
supersolution has bounded mean oscillation.

Both statements hold on every cube, not only on dyadic ones. In the sup norm of `ι → ℝ` a cube
`∏ᵢ [cᵢ - r, cᵢ + r]` is the closed ball `closedBall c r`, and if `f` has mean oscillation at most
`M` on every closed ball inside it, then the same two bounds hold on `closedBall c r`
(`TauCeti.volume_lt_norm_sub_setAverage_closedBall_le`,
`TauCeti.setLIntegral_exp_mul_norm_sub_setAverage_closedBall_le`). For `0 < r` this follows from
the dyadic case by the affine change of variables carrying the unit dyadic cube onto
`closedBall c r`, which rescales Lebesgue measure by a constant and so preserves averages. For
`r ≤ 0` the closed ball is null and both bounds are immediate.

In `ℝⁿ = EuclideanSpace ℝ ι`, with any additive Haar measure, the inequality holds on Euclidean
balls up to a loss in the radius: if `f` has mean oscillation at most `M` on every Euclidean ball
inside `B(x₀, R)`, then `∫_{B'} exp (σ ‖f - f_{B'}‖) ≤ C |B'|` on `B' = B(x₀, R / (3√n))` whenever
`σ M ≤ A`, for constants `A > 0` and `C` depending only on `n`
(`TauCeti.exists_setLIntegral_exp_mul_norm_sub_setAverage_ball_le`). This follows from the cube
case, since a cube of half-side `ρ` and the Euclidean ball of radius `2√n ρ` about its centre have
comparable measures. For real `f` it gives Moser's crossover estimate
`(∫_{B'} exp (σ f)) (∫_{B'} exp (-σ f)) ≤ C |B'|²`
(`TauCeti.exists_setLIntegral_exp_mul_mul_setLIntegral_exp_neg_mul_ball_le`).

The proof iterates the Calderón–Zygmund decomposition. At height `2M`, the Calderón–Zygmund
cubes of `‖f - f_{Q₀}‖` restricted to `Q₀` lie inside `Q₀`, cover at most half of it, and carry
averages within `2ⁿ⁺¹ M` of `f_{Q₀}`, while `‖f - f_{Q₀}‖ ≤ 2M` almost everywhere off them. Each
step of size `2ⁿ⁺¹ M` in the level therefore halves the measure of the superlevel set
(`TauCeti.volume_lt_enorm_sub_setAverage_le_inv_two_pow`).

## Main declarations

* `TauCeti.volume_lt_enorm_sub_setAverage_le_inv_two_pow`: the set where `‖f - f_{Q₀}‖` exceeds
  `2ⁿ⁺¹ N M` has measure at most `2⁻ᴺ |Q₀|`.
* `TauCeti.volume_lt_norm_sub_setAverage_le`: the **John–Nirenberg inequality**, exponential
  decay of the distribution function of `‖f - f_{Q₀}‖`.
* `TauCeti.setLIntegral_exp_mul_norm_sub_setAverage_le`: exponential integrability.
* `TauCeti.volume_lt_norm_sub_setAverage_closedBall_le`,
  `TauCeti.setLIntegral_exp_mul_norm_sub_setAverage_closedBall_le`: the same two statements on an
  arbitrary cube `closedBall c r`.
* `TauCeti.exists_setLIntegral_exp_mul_norm_sub_setAverage_ball_le`: exponential integrability
  on Euclidean balls.
* `TauCeti.exists_setLIntegral_exp_mul_mul_setLIntegral_exp_neg_mul_ball_le`: Moser's crossover
  estimate for real functions of bounded mean oscillation on Euclidean balls.

## References

* F. John and L. Nirenberg, *On functions of bounded mean oscillation*, Comm. Pure Appl. Math.
  **14** (1961), 415–426.
* L. Grafakos, *Modern Fourier Analysis*, Theorem 3.1.6.
* E. Stein, *Harmonic Analysis*, Chapter IV, §1.3.
* J. Moser, *On Harnack's theorem for elliptic differential equations*, Comm. Pure Appl. Math.
  **14** (1961), 577–591.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 8.6 (the crossover estimate in the proof of the weak Harnack inequality).
-/

public section

namespace TauCeti

open MeasureTheory Set
open scoped ENNReal NNReal

variable {ι : Type*} [Fintype ι] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : (ι → ℝ) → E} {q₀ : ℤ × (ι → ℤ)} {M : ℝ≥0}

/-- **One Calderón–Zygmund step.** Let `f` be integrable on the dyadic cube `Q₀`, with
`⨍_{Q₀} ‖f - f_{Q₀}‖ ≤ M` for some `M ≠ 0`. Then there are dyadic cubes `Q ⊆ Q₀` of total measure
at most `|Q₀| / 2` such that the measure of the set where `‖f - f_{Q₀}‖ > 2ⁿ⁺¹ (N + 1) M` is at most
the sum over these cubes `Q` of the measures of the sets where `‖f - f_Q‖ > 2ⁿ⁺¹ N M` on `Q`.
The cubes are the Calderón–Zygmund cubes of `‖f - f_{Q₀}‖` on `Q₀` at height `2M`. -/
private theorem exists_volume_lt_enorm_sub_setAverage_le_tsum [Nonempty ι] [CompleteSpace E]
    (hM0 : M ≠ 0) (hf : IntegrableOn f (dyadicCube q₀.1 q₀.2))
    (hMQ : ⨍⁻ x in dyadicCube q₀.1 q₀.2, ‖f x - ⨍ y in dyadicCube q₀.1 q₀.2, f y ∂volume‖ₑ
      ∂volume ≤ M) (N : ℕ) :
    ∃ C : Set (ℤ × (ι → ℤ)), (∀ q ∈ C, dyadicCube q.1 q.2 ⊆ dyadicCube q₀.1 q₀.2) ∧
      ∑' q : C, volume (dyadicCube q.1.1 q.1.2) ≤ 2⁻¹ * volume (dyadicCube q₀.1 q₀.2) ∧
      volume {x ∈ dyadicCube q₀.1 q₀.2 | 2 ^ (Fintype.card ι + 1) * ↑(N + 1) * (M : ℝ≥0∞) <
          ‖f x - ⨍ y in dyadicCube q₀.1 q₀.2, f y ∂volume‖ₑ} ≤
        ∑' q : C, volume {x ∈ dyadicCube q.1.1 q.1.2 |
          2 ^ (Fintype.card ι + 1) * N * (M : ℝ≥0∞) <
            ‖f x - ⨍ y in dyadicCube q.1.1 q.1.2, f y ∂volume‖ₑ} := by
  set Q := dyadicCube q₀.1 q₀.2
  set c := ⨍ y in Q, f y ∂volume
  set n := Fintype.card ι
  have hQ : MeasurableSet Q := measurableSet_dyadicCube q₀.1 q₀.2
  -- The Calderón–Zygmund cubes of `g = 1_Q ‖f - c‖` at height `t = 2M`.
  set g : (ι → ℝ) → ℝ≥0∞ := Q.indicator fun x => ‖f x - c‖ₑ
  set t : ℝ≥0∞ := 2 * M
  set C := calderonZygmundCubes g t
  have ht0 : t ≠ 0 := mul_ne_zero two_ne_zero (ENNReal.coe_ne_zero.2 hM0)
  have hgm : AEMeasurable g :=
    (aemeasurable_indicator_iff hQ).2 (hf.1.sub aestronglyMeasurable_const).enorm
  have hg : ∫⁻ x, g x ≤ M * volume Q := by
    rw [lintegral_indicator hQ, ← measure_mul_setLAverage _ (volume_dyadicCube_ne_top _ _),
      mul_comm]
    gcongr
  have hg' : ∫⁻ x, g x ≠ ∞ :=
    (hg.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top (volume_dyadicCube_ne_top _ _).lt_top)).ne
  -- The cubes lie in `Q`.
  have hsub : ∀ q ∈ C, dyadicCube q.1 q.2 ⊆ Q := fun q hq =>
    dyadicCube_subset_of_mem_calderonZygmundCubes_indicator
      (hMQ.trans (le_mul_of_one_le_left' one_le_two)) hq
  -- They cover at most half of `Q`.
  have hvol : volume (⋃ q ∈ C, dyadicCube q.1 q.2) ≤ 2⁻¹ * volume Q := by
    set V := volume (⋃ q ∈ C, dyadicCube q.1 q.2)
    have h := (mul_volume_biUnion_calderonZygmundCubes_le (g := g) (t := t)).trans
      ((setLIntegral_le_lintegral _ _).trans hg)
    rw [show t * V = M * (2 * V) by ring] at h
    have h2 := (ENNReal.mul_le_mul_iff_right (ENNReal.coe_ne_zero.2 hM0) ENNReal.coe_ne_top).1 h
    rw [← ENNReal.div_eq_inv_mul, ENNReal.le_div_iff_mul_le (.inl two_ne_zero)
      (.inl ENNReal.ofNat_ne_top), mul_comm]
    exact h2
  -- On each cube, the average of `f` is within `2ⁿ⁺¹ M` of `c`.
  have havg : ∀ q ∈ C, ‖⨍ y in dyadicCube q.1 q.2, f y ∂volume - c‖ₑ ≤ 2 ^ (n + 1) * M := by
    intro q hq
    have hfq : IntegrableOn f (dyadicCube q.1 q.2) := hf.mono_set (hsub q hq)
    rw [← setAverage_const (volume_dyadicCube_pos q.1 q.2).ne' (volume_dyadicCube_ne_top _ _) c,
      ← setAverage_sub hfq (integrableOn_const (volume_dyadicCube_ne_top _ _))]
    refine (enorm_setAverage_le_setLAverage _ _ _).trans ?_
    refine le_of_eq_of_le (setLAverage_congr_fun (measurableSet_dyadicCube _ _) ?_)
      ((setLAverage_le_of_mem_calderonZygmundCubes hq).trans_eq ?_)
    · exact fun x hx => by simp only [g, indicator_of_mem (hsub q hq hx), Pi.sub_apply]
    · rw [pow_succ, mul_assoc]
  -- Off the cubes, `‖f - c‖ ≤ 2M` almost everywhere.
  have hae := ae_le_of_forall_notMem_calderonZygmundCubes hgm hg' ht0
  -- Hence, up to a null set, the superlevel set at `2ⁿ⁺¹ (N + 1) M` lies in the union over the
  -- cubes `Q'` of the superlevel sets at `2ⁿ⁺¹ N M` of `‖f - f_{Q'}‖` on `Q'`.
  refine ⟨C, hsub, ?_, ?_⟩
  · rw [← measure_biUnion C.to_countable pairwiseDisjoint_calderonZygmundCubes
      fun q _ => measurableSet_dyadicCube _ _]
    exact hvol
  calc volume {x ∈ Q | 2 ^ (n + 1) * ↑(N + 1) * (M : ℝ≥0∞) < ‖f x - c‖ₑ}
      ≤ volume (⋃ q ∈ C, {x ∈ dyadicCube q.1 q.2 | 2 ^ (n + 1) * N * (M : ℝ≥0∞) <
          ‖f x - ⨍ y in dyadicCube q.1 q.2, f y ∂volume‖ₑ}) := by
        refine measure_mono_ae ?_
        filter_upwards [hae] with x hx hxS
        simp only [mem_iUnion, mem_ofPred_eq]
        by_cases hmem : ∃ q ∈ C, x ∈ dyadicCube q.1 q.2
        · obtain ⟨q, hq, hxq⟩ := hmem
          refine ⟨q, hq, hxq, lt_of_not_ge fun hle => hxS.2.not_ge ?_⟩
          calc ‖f x - c‖ₑ
              ≤ ‖f x - ⨍ y in dyadicCube q.1 q.2, f y ∂volume‖ₑ +
                  ‖⨍ y in dyadicCube q.1 q.2, f y ∂volume - c‖ₑ := by
                simpa only [edist_eq_enorm_sub] using edist_triangle (f x) _ c
            _ ≤ 2 ^ (n + 1) * N * M + 2 ^ (n + 1) * M := add_le_add hle (havg q hq)
            _ = 2 ^ (n + 1) * ↑(N + 1) * M := by push_cast; ring
        · push Not at hmem
          have hle := hx hmem
          rw [show g x = ‖f x - c‖ₑ from indicator_of_mem hxS.1 _] at hle
          refine absurd hxS.2 (not_lt.2 (hle.trans ?_))
          calc t = 2 ^ 1 * 1 * M := by ring
            _ ≤ 2 ^ (n + 1) * ↑(N + 1) * M := by
              gcongr
              · exact one_le_two
              · omega
              · exact_mod_cast Nat.succ_pos N
    _ ≤ ∑' q : C, volume {x ∈ dyadicCube q.1.1 q.1.2 | 2 ^ (n + 1) * N * (M : ℝ≥0∞) <
          ‖f x - ⨍ y in dyadicCube q.1.1 q.1.2, f y ∂volume‖ₑ} :=
        measure_biUnion_le _ C.to_countable _

/-- **The John–Nirenberg inequality, dyadic form.** Let `f` be integrable on the dyadic cube
`Q₀ ⊆ ℝⁿ`, `n ≥ 1`, with mean oscillation `⨍_Q ‖f - f_Q‖ ≤ M` on every dyadic cube `Q ⊆ Q₀`.
Then the set of points of `Q₀` where `‖f - f_{Q₀}‖` exceeds `2ⁿ⁺¹ N M` has measure at most
`2⁻ᴺ |Q₀|`. -/
theorem volume_lt_enorm_sub_setAverage_le_inv_two_pow [Nonempty ι] [CompleteSpace E]
    (hf : IntegrableOn f (dyadicCube q₀.1 q₀.2))
    (hM : ∀ q : ℤ × (ι → ℤ), dyadicCube q.1 q.2 ⊆ dyadicCube q₀.1 q₀.2 →
      ⨍⁻ x in dyadicCube q.1 q.2, ‖f x - ⨍ y in dyadicCube q.1 q.2, f y ∂volume‖ₑ ∂volume ≤ M)
    (N : ℕ) :
    volume {x ∈ dyadicCube q₀.1 q₀.2 |
        2 ^ (Fintype.card ι + 1) * N * (M : ℝ≥0∞) <
          ‖f x - ⨍ y in dyadicCube q₀.1 q₀.2, f y ∂volume‖ₑ} ≤
      2⁻¹ ^ N * volume (dyadicCube q₀.1 q₀.2) := by
  rcases eq_or_ne M 0 with rfl | hM0
  · -- For `M = 0`, `f` equals its average almost everywhere on `Q₀`.
    have hm : AEMeasurable (fun x => ‖f x - ⨍ y in dyadicCube q₀.1 q₀.2, f y ∂volume‖ₑ)
        (volume.restrict (dyadicCube q₀.1 q₀.2)) :=
      (hf.1.sub aestronglyMeasurable_const).enorm
    have h := hM q₀ le_rfl
    rw [ENNReal.coe_zero, nonpos_iff_eq_zero, setLAverage_eq, ENNReal.div_eq_zero_iff,
      or_iff_left (volume_dyadicCube_ne_top _ _), lintegral_eq_zero_iff' hm, Filter.EventuallyEq,
      ae_restrict_iff' (measurableSet_dyadicCube q₀.1 q₀.2)] at h
    refine le_trans (le_of_eq (measure_eq_zero_iff_ae_notMem.2 ?_)) zero_le
    exact h.mono fun x hx hxS => hxS.2.ne' (by simpa using hx hxS.1)
  induction N generalizing q₀ with
  | zero =>
    rw [pow_zero, one_mul]
    exact measure_mono (sep_subset _ _)
  | succ N ih =>
    -- One Calderón–Zygmund step, then the induction hypothesis on each of its cubes.
    obtain ⟨C, hsub, hC, hcover⟩ :=
      exists_volume_lt_enorm_sub_setAverage_le_tsum hM0 hf (hM q₀ le_rfl) N
    calc _ ≤ _ := hcover
      _ ≤ ∑' q : C, 2⁻¹ ^ N * volume (dyadicCube q.1.1 q.1.2) :=
        ENNReal.tsum_le_tsum fun q =>
          ih (hf.mono_set (hsub q q.2)) fun q' hq' => hM q' (hq'.trans (hsub q q.2))
      _ = 2⁻¹ ^ N * ∑' q : C, volume (dyadicCube q.1.1 q.1.2) := ENNReal.tsum_mul_left
      _ ≤ 2⁻¹ ^ N * (2⁻¹ * volume (dyadicCube q₀.1 q₀.2)) := by gcongr
      _ = 2⁻¹ ^ (N + 1) * volume (dyadicCube q₀.1 q₀.2) := by rw [pow_succ, mul_assoc]

/-- The cast of the level `N 2ⁿ⁺¹ M` of `TauCeti.volume_lt_enorm_sub_setAverage_le_inv_two_pow`
from `ℝ≥0∞` to `ℝ`. -/
private theorem two_pow_mul_natCast_mul_coe_eq_ofReal (n N : ℕ) (M : ℝ≥0) :
    2 ^ n * (N : ℝ≥0∞) * M = ENNReal.ofReal (N * (2 ^ n * M)) := by
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat,
    ENNReal.ofReal_coe_nnreal]
  ring

/-- **The John–Nirenberg inequality.** Let `f` be integrable on the dyadic cube `Q₀ ⊆ ℝⁿ`,
`n ≥ 1`, with mean oscillation `⨍_Q ‖f - f_Q‖ ≤ M` on every dyadic cube `Q ⊆ Q₀`. Then for
every `s`,

`|{x ∈ Q₀ : ‖f x - f_{Q₀}‖ > s}| ≤ 2 exp (-(log 2) s / (2ⁿ⁺¹ M)) |Q₀|`.

For `M = 0` the right-hand side is `2 |Q₀|`, by the convention `s / 0 = 0`, and the bound is
trivial. -/
theorem volume_lt_norm_sub_setAverage_le [Nonempty ι] [CompleteSpace E]
    (hf : IntegrableOn f (dyadicCube q₀.1 q₀.2))
    (hM : ∀ q : ℤ × (ι → ℤ), dyadicCube q.1 q.2 ⊆ dyadicCube q₀.1 q₀.2 →
      ⨍⁻ x in dyadicCube q.1 q.2, ‖f x - ⨍ y in dyadicCube q.1 q.2, f y ∂volume‖ₑ ∂volume ≤ M)
    (s : ℝ) :
    volume {x ∈ dyadicCube q₀.1 q₀.2 | s < ‖f x - ⨍ y in dyadicCube q₀.1 q₀.2, f y ∂volume‖} ≤
      ENNReal.ofReal (2 * Real.exp (-(Real.log 2 * s / (2 ^ (Fintype.card ι + 1) * M)))) *
        volume (dyadicCube q₀.1 q₀.2) := by
  rcases eq_or_ne M 0 with rfl | hM0
  · simp only [NNReal.coe_zero, mul_zero, div_zero, neg_zero, Real.exp_zero, mul_one,
      ENNReal.ofReal_ofNat]
    exact (measure_mono (sep_subset _ _)).trans (le_mul_of_one_le_left' one_le_two)
  set a : ℝ := 2 ^ (Fintype.card ι + 1) * M
  have ha : 0 < a := mul_pos (by positivity) (NNReal.coe_pos.2 (pos_iff_ne_zero.2 hM0))
  set N := ⌊s / a⌋₊
  -- The set lies in the superlevel set at `N 2ⁿ⁺¹ M ≤ s`, of measure at most `2⁻ᴺ |Q₀|`.
  have hN : volume {x ∈ dyadicCube q₀.1 q₀.2 |
      s < ‖f x - ⨍ y in dyadicCube q₀.1 q₀.2, f y ∂volume‖} ≤
        2⁻¹ ^ N * volume (dyadicCube q₀.1 q₀.2) := by
    rcases lt_or_ge s 0 with hs | hs
    · have hN0 : N = 0 := Nat.floor_eq_zero.2 ((div_neg_of_neg_of_pos hs ha).trans one_pos)
      rw [hN0, pow_zero, one_mul]
      exact measure_mono (sep_subset _ _)
    refine le_trans (measure_mono ?_) (volume_lt_enorm_sub_setAverage_le_inv_two_pow hf hM N)
    intro x hx
    refine ⟨hx.1, ?_⟩
    have hNa : N * a ≤ s := (le_div_iff₀ ha).1 (Nat.floor_le (div_nonneg hs ha.le))
    rw [two_pow_mul_natCast_mul_coe_eq_ofReal, ← ofReal_norm,
      ENNReal.ofReal_lt_ofReal_iff ((hNa.trans_lt hx.2).trans_le' (by positivity))]
    exact hNa.trans_lt hx.2
  refine hN.trans (mul_le_mul_left ?_ _)
  -- Since `s / a < N + 1`, `2⁻ᴺ ≤ 2 exp (-(log 2) s / a)`.
  have hlt : s / a < N + 1 := Nat.lt_floor_add_one _
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_inv_of_pos two_pos,
    ← ENNReal.ofReal_pow (by norm_num)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc (2 : ℝ)⁻¹ ^ N = Real.exp (-(N * Real.log 2)) := by
        rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log two_pos, inv_pow]
    _ ≤ Real.exp (Real.log 2 + -(Real.log 2 * s / a)) := by
        refine Real.exp_le_exp.2 ?_
        have := mul_lt_mul_of_pos_left hlt hlog
        rw [mul_div_assoc]
        nlinarith
    _ = 2 * Real.exp (-(Real.log 2 * s / a)) := by rw [Real.exp_add, Real.exp_log two_pos]

omit [NormedSpace ℝ E] in
/-- Pointwise, `exp (σ ‖v‖) ≤ 1 + ∑_N ρ^(N + 1)`, the sum running over the `N` with
`N 2ⁿ M < ‖v‖`, where `ρ = exp (2ⁿ σ M)`. -/
private theorem ofReal_exp_mul_norm_le_one_add_tsum (σ : ℝ) (n : ℕ) (M : ℝ≥0) (v : E) :
    ENNReal.ofReal (Real.exp (σ * ‖v‖)) ≤ 1 + ∑' N : ℕ,
      if 2 ^ n * (N : ℝ≥0∞) * M < ‖v‖ₑ then ENNReal.ofReal (Real.exp (σ * (2 ^ n * M))) ^ (N + 1)
      else 0 := by
  rcases le_or_gt (σ * ‖v‖) 0 with hσy | hσy
  · rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.2 hσy)).trans le_self_add
  obtain ⟨hσ, hy⟩ := (pos_and_pos_or_neg_and_neg_of_mul_pos hσy).resolve_right
    fun h => (norm_nonneg _).not_gt h.2
  rcases eq_or_ne M 0 with rfl | hM0
  · -- For `M = 0`, every term of the sum is `1`.
    have hv : 0 < ‖v‖ₑ := enorm_pos.2 (norm_pos_iff.1 hy)
    simp only [ENNReal.coe_zero, mul_zero, hv, ↓reduceIte, NNReal.coe_zero, Real.exp_zero,
      ENNReal.ofReal_one, one_pow, ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero, add_top]
    exact le_top
  set a : ℝ := 2 ^ n * M
  have ha : 0 < a := mul_pos (by positivity) (NNReal.coe_pos.2 (pos_iff_ne_zero.2 hM0))
  -- The level `N = ⌈‖v‖ / a⌉ - 1` has `N a < ‖v‖ ≤ (N + 1) a`.
  set N := ⌈‖v‖ / a⌉₊ - 1
  have hN1 : ((N + 1 : ℕ) : ℝ) = ⌈‖v‖ / a⌉₊ := by
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (div_pos hy ha)).ne')]
  have hN : 2 ^ n * (N : ℝ≥0∞) * M < ‖v‖ₑ := by
    rw [two_pow_mul_natCast_mul_coe_eq_ofReal, ← ofReal_norm, ENNReal.ofReal_lt_ofReal_iff hy]
    have := Nat.ceil_lt_add_one (div_pos hy ha).le
    rw [← hN1, Nat.cast_add_one] at this
    have h' : (N : ℝ) < ‖v‖ / a := by linarith
    exact (lt_div_iff₀ ha).1 h'
  refine le_add_left (le_trans ?_ (ENNReal.le_tsum N))
  simp only [hN, ↓reduceIte]
  rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  rw [← mul_assoc, mul_comm _ σ, mul_assoc, hN1]
  exact mul_le_mul_of_nonneg_left ((div_le_iff₀ ha).1 (Nat.le_ceil _)) hσ.le |>.trans_eq
    (by ring)

/-- **Exponential integrability of functions of bounded mean oscillation.** Let `f` be
integrable on the dyadic cube `Q₀ ⊆ ℝⁿ`, `n ≥ 1`, with mean oscillation `⨍_Q ‖f - f_Q‖ ≤ M` on
every dyadic cube `Q ⊆ Q₀`. If `ρ = exp (2ⁿ⁺¹ σ M) < 2`, then

`∫_{Q₀} exp (σ ‖f - f_{Q₀}‖) ≤ (1 + 2ρ / (2 - ρ)) |Q₀|`. -/
theorem setLIntegral_exp_mul_norm_sub_setAverage_le [Nonempty ι] [CompleteSpace E]
    (hf : IntegrableOn f (dyadicCube q₀.1 q₀.2))
    (hM : ∀ q : ℤ × (ι → ℤ), dyadicCube q.1 q.2 ⊆ dyadicCube q₀.1 q₀.2 →
      ⨍⁻ x in dyadicCube q.1 q.2, ‖f x - ⨍ y in dyadicCube q.1 q.2, f y ∂volume‖ₑ ∂volume ≤ M)
    {σ : ℝ} (hρ : Real.exp (σ * (2 ^ (Fintype.card ι + 1) * M)) < 2) :
    ∫⁻ x in dyadicCube q₀.1 q₀.2,
        ENNReal.ofReal (Real.exp (σ * ‖f x - ⨍ y in dyadicCube q₀.1 q₀.2, f y ∂volume‖)) ≤
      ENNReal.ofReal (1 + 2 * Real.exp (σ * (2 ^ (Fintype.card ι + 1) * M)) /
        (2 - Real.exp (σ * (2 ^ (Fintype.card ι + 1) * M)))) * volume (dyadicCube q₀.1 q₀.2) := by
  set Q := dyadicCube q₀.1 q₀.2
  set c := ⨍ y in Q, f y ∂volume
  set n := Fintype.card ι
  set a : ℝ := 2 ^ (n + 1) * M
  set ρ := Real.exp (σ * a)
  set r := ENNReal.ofReal ρ
  have hQ : MeasurableSet Q := measurableSet_dyadicCube q₀.1 q₀.2
  -- The superlevel sets of `‖f - c‖` at the levels `N 2ⁿ⁺¹ M`.
  set T : ℕ → Set (ι → ℝ) := fun N => {x | 2 ^ (n + 1) * (N : ℝ≥0∞) * M < ‖f x - c‖ₑ}
  have hT (N : ℕ) : NullMeasurableSet (T N) (volume.restrict Q) :=
    nullMeasurableSet_lt aemeasurable_const (hf.1.sub aestronglyMeasurable_const).enorm
  -- Pointwise, `exp (σ ‖f - c‖) ≤ 1 + ∑_N 1_{T N} ρ^(N + 1)`.
  have hpt (x : ι → ℝ) : ENNReal.ofReal (Real.exp (σ * ‖f x - c‖)) ≤
      1 + ∑' N : ℕ, (T N).indicator (fun _ => r ^ (N + 1)) x := by
    simp only [indicator_apply, T, mem_ofPred_eq]
    exact ofReal_exp_mul_norm_le_one_add_tsum σ (n + 1) M (f x - c)
  -- Integrate, bounding the measure of each `T N ∩ Q` by the dyadic John–Nirenberg inequality.
  have hvT (N : ℕ) : volume.restrict Q (T N) ≤ 2⁻¹ ^ N * volume Q := by
    rw [Measure.restrict_apply' hQ]
    refine le_trans (measure_mono ?_) (volume_lt_enorm_sub_setAverage_le_inv_two_pow hf hM N)
    exact fun x hx => ⟨hx.2, hx.1⟩
  have hconst : 1 + r * (1 - r * 2⁻¹)⁻¹ = ENNReal.ofReal (1 + 2 * ρ / (2 - ρ)) := by
    have hρ0 : 0 < ρ := Real.exp_pos _
    have h2 : 0 < 1 - ρ / 2 := by linarith
    rw [show 2 * ρ / (2 - ρ) = ρ * (1 - ρ / 2)⁻¹ by field_simp,
      ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one,
      ENNReal.ofReal_mul hρ0.le, ENNReal.ofReal_inv_of_pos h2,
      ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one, ENNReal.ofReal_div_of_pos two_pos,
      ENNReal.ofReal_ofNat, ENNReal.div_eq_inv_mul, mul_comm (2⁻¹ : ℝ≥0∞)]
  calc ∫⁻ x in Q, ENNReal.ofReal (Real.exp (σ * ‖f x - c‖))
      ≤ ∫⁻ x in Q, (1 + ∑' N : ℕ, (T N).indicator (fun _ => r ^ (N + 1)) x) := lintegral_mono hpt
    _ = volume Q + ∑' N : ℕ, r ^ (N + 1) * volume.restrict Q (T N) := by
        rw [lintegral_add_left measurable_const,
          lintegral_tsum fun N => aemeasurable_const.indicator₀ (hT N), setLIntegral_one]
        congr 1
        exact tsum_congr fun N => lintegral_indicator_const₀ (hT N) _
    _ ≤ volume Q + ∑' N : ℕ, r ^ (N + 1) * (2⁻¹ ^ N * volume Q) := by
        gcongr with N
        exact hvT N
    _ = (1 + r * (1 - r * 2⁻¹)⁻¹) * volume Q := by
        simp_rw [← mul_assoc, ENNReal.tsum_mul_right, pow_succ', mul_assoc, ← mul_pow,
          ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
        ring
    _ = _ := by rw [hconst]

section ClosedBall

/-! ### Arbitrary cubes

In the sup norm of `ι → ℝ` the closed ball `closedBall c r` is the closed cube
`∏ᵢ [cᵢ - r, cᵢ + r]`. For `0 < r`, the affine bijection `y ↦ 2r y + (c - r)` carries the unit
dyadic cube `[0, 1)ⁿ` onto this cube up to a null set and its dyadic subcubes onto closed balls
inside `closedBall c r` up to null sets, and it rescales Lebesgue measure by the constant `(2r)ⁿ`.
Averages are invariant under it, so the dyadic John–Nirenberg inequality for `f` composed with
this map gives the inequality on every cube of positive radius. For `r ≤ 0` the closed ball is
null, so both bounds hold trivially. -/

open Metric

variable {c : ι → ℝ} {r : ℝ}

/-- The affine bijection `y ↦ 2r y + (c - r)` of `ι → ℝ`. -/
private noncomputable def cubeEquiv (c : ι → ℝ) (hr : 0 < r) : (ι → ℝ) ≃ᵐ (ι → ℝ) :=
  ((Homeomorph.smulOfNeZero (2 * r) (by positivity)).trans
    (Homeomorph.addRight (c - fun _ => r))).toMeasurableEquiv

private theorem cubeEquiv_apply (hr : 0 < r) (y : ι → ℝ) :
    cubeEquiv c hr y = (2 * r) • y + (c - fun _ => r) :=
  rfl

/-- The affine bijection rescales Lebesgue measure by `(2r)⁻ⁿ`. -/
private theorem map_cubeEquiv (hr : 0 < r) :
    (volume : Measure (ι → ℝ)).map (cubeEquiv c hr) =
      ENNReal.ofReal ((2 * r) ^ Fintype.card ι)⁻¹ • volume := by
  have h : ⇑(cubeEquiv c hr) = (· + (c - fun _ => r)) ∘ ((2 * r) • ·) :=
    funext (cubeEquiv_apply hr)
  rw [h, ← Measure.map_map (measurable_add_const _) (measurable_const_smul _),
    Measure.map_addHaar_smul _ (by positivity), Measure.map_smul, map_add_right_eq_self,
    Module.finrank_fintype_fun_eq_card, abs_of_pos (by positivity)]
  exact (measurable_add_const _).aemeasurable

/-- The affine bijection multiplies sup distances by `2r`. -/
private theorem preimage_cubeEquiv_closedBall (hr : 0 < r) (z : ι → ℝ) (ρ : ℝ) :
    cubeEquiv c hr ⁻¹' closedBall (cubeEquiv c hr z) (2 * r * ρ) = closedBall z ρ := by
  ext y
  simp only [mem_preimage, mem_closedBall, dist_eq_norm, cubeEquiv_apply, add_sub_add_right_eq_sub,
    ← smul_sub, norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * r)]
  exact mul_le_mul_iff_right₀ (by positivity)

/-- The affine bijection carries the closure of the unit dyadic cube onto `closedBall c r`. -/
private theorem preimage_cubeEquiv_closedBall_self (hr : 0 < r) :
    cubeEquiv c hr ⁻¹' closedBall c r = closure (dyadicCube 0 (0 : ι → ℤ)) := by
  have hz : cubeEquiv c hr (fun i => (((0 : ι → ℤ) i : ℝ) + 2⁻¹) * 2 ^ (0 : ℤ)) = c := by
    ext i
    simp only [cubeEquiv_apply, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.zero_apply,
      Int.cast_zero, zero_add, zpow_zero, mul_one, smul_eq_mul]
    ring
  have hρ : 2 * r * ((2 : ℝ) ^ (0 : ℤ) / 2) = r := by
    rw [zpow_zero]
    ring
  have h := preimage_cubeEquiv_closedBall (c := c) hr
    (fun i => (((0 : ι → ℤ) i : ℝ) + 2⁻¹) * 2 ^ (0 : ℤ)) (2 ^ (0 : ℤ) / 2)
  rw [hz, hρ] at h
  rw [h, closure_dyadicCube]

private theorem ofReal_inv_two_mul_pow_ne_zero (hr : 0 < r) :
    ENNReal.ofReal ((2 * r) ^ Fintype.card ι)⁻¹ ≠ 0 :=
  (ENNReal.ofReal_pos.2 (by positivity)).ne'

omit [NormedSpace ℝ E] in
/-- An integrable function on `closedBall c r` pulls back to an integrable function on the unit
dyadic cube. -/
private theorem integrableOn_comp_cubeEquiv (hr : 0 < r) (hf : IntegrableOn f (closedBall c r)) :
    IntegrableOn (f ∘ cubeEquiv c hr) (dyadicCube 0 0) := by
  have h : IntegrableOn f (closedBall c r) ((volume : Measure (ι → ℝ)).map (cubeEquiv c hr)) := by
    rw [map_cubeEquiv hr, IntegrableOn, Measure.restrict_smul]
    exact hf.smul_measure ENNReal.ofReal_ne_top
  rw [integrableOn_map_equiv, preimage_cubeEquiv_closedBall_self hr] at h
  exact h.mono_set subset_closure

/-- Mean oscillation at most `M` on the closed balls inside `closedBall c r` pulls back to dyadic
mean oscillation at most `M` on the unit dyadic cube. -/
private theorem setLAverage_comp_cubeEquiv_le (hr : 0 < r)
    (hM : ∀ y ρ, closedBall y ρ ⊆ closedBall c r →
      ⨍⁻ x in closedBall y ρ, ‖f x - ⨍ z in closedBall y ρ, f z ∂volume‖ₑ ∂volume ≤ M)
    (q : ℤ × (ι → ℤ)) (hq : dyadicCube q.1 q.2 ⊆ dyadicCube 0 0) :
    ⨍⁻ x in dyadicCube q.1 q.2, ‖(f ∘ cubeEquiv c hr) x -
      ⨍ y in dyadicCube q.1 q.2, (f ∘ cubeEquiv c hr) y ∂volume‖ₑ ∂volume ≤ M := by
  set e := cubeEquiv c hr
  set z : ι → ℝ := fun i => ((q.2 i : ℝ) + 2⁻¹) * 2 ^ q.1
  set B := closedBall (e z) (2 * r * (2 ^ q.1 / 2))
  have hmap := map_cubeEquiv (c := c) hr
  have ha := ofReal_inv_two_mul_pow_ne_zero (ι := ι) hr
  have hpre : e ⁻¹' B = closure (dyadicCube q.1 q.2) := by
    rw [preimage_cubeEquiv_closedBall, closure_dyadicCube]
  have hae : dyadicCube q.1 q.2 =ᵐ[volume] e ⁻¹' B := by
    rw [hpre, closure_dyadicCube]
    exact dyadicCube_ae_eq_closedBall q.1 q.2
  have havg : ⨍ y in e ⁻¹' B, f (e y) ∂volume = ⨍ y in B, f y ∂volume :=
    setAverage_comp_preimage_of_map_eq_smul hmap ha ENNReal.ofReal_ne_top f B
  have hlavg : ⨍⁻ x in e ⁻¹' B, ‖f (e x) - ⨍ y in B, f y ∂volume‖ₑ ∂volume =
      ⨍⁻ x in B, ‖f x - ⨍ y in B, f y ∂volume‖ₑ ∂volume :=
    setLAverage_comp_preimage_of_map_eq_smul hmap ha ENNReal.ofReal_ne_top
      (fun x => ‖f x - ⨍ y in B, f y ∂volume‖ₑ) B
  simp only [Function.comp_apply]
  rw [setAverage_congr hae, setLAverage_congr hae, havg, hlavg]
  refine hM _ _ ?_
  rw [← e.surjective.preimage_subset_preimage_iff, hpre, preimage_cubeEquiv_closedBall_self hr]
  exact closure_mono hq

/-- **The John–Nirenberg inequality** on a cube. Let `f` be integrable on the closed sup-norm ball
`closedBall c r ⊆ ℝⁿ`, `n ≥ 1`, that is, on the cube `∏ᵢ [cᵢ - r, cᵢ + r]`, with mean oscillation
`⨍_B ‖f - f_B‖ ≤ M` on every closed ball `B ⊆ closedBall c r`. Then for every `s`,

`|{x ∈ closedBall c r : ‖f x - f_{closedBall c r}‖ > s}| ≤
  2 exp (-(log 2) s / (2ⁿ⁺¹ M)) |closedBall c r|`. -/
theorem volume_lt_norm_sub_setAverage_closedBall_le [Nonempty ι] [CompleteSpace E]
    (hf : IntegrableOn f (closedBall c r))
    (hM : ∀ y ρ, closedBall y ρ ⊆ closedBall c r →
      ⨍⁻ x in closedBall y ρ, ‖f x - ⨍ z in closedBall y ρ, f z ∂volume‖ₑ ∂volume ≤ M)
    (s : ℝ) :
    volume {x ∈ closedBall c r | s < ‖f x - ⨍ y in closedBall c r, f y ∂volume‖} ≤
      ENNReal.ofReal (2 * Real.exp (-(Real.log 2 * s / (2 ^ (Fintype.card ι + 1) * M)))) *
        volume (closedBall c r) := by
  rcases le_or_gt r 0 with hr | hr
  · rw [volume_closedBall_eq_zero_of_nonpos c hr, mul_zero]
    exact (measure_mono_null (sep_subset _ _)
      (volume_closedBall_eq_zero_of_nonpos c hr)).le
  set e := cubeEquiv c hr
  set B := closedBall c r
  have hmap := map_cubeEquiv (c := c) hr
  have ha := ofReal_inv_two_mul_pow_ne_zero (ι := ι) hr
  have hvol (S : Set (ι → ℝ)) :
      volume (e ⁻¹' S) = ENNReal.ofReal ((2 * r) ^ Fintype.card ι)⁻¹ * volume S := by
    rw [← e.map_apply, hmap, Measure.smul_apply, smul_eq_mul]
  have hB : e ⁻¹' B =ᵐ[volume] dyadicCube 0 0 := by
    rw [preimage_cubeEquiv_closedBall_self hr, closure_dyadicCube]
    exact (dyadicCube_ae_eq_closedBall 0 0).symm
  have havg : ⨍ y in dyadicCube 0 0, (f ∘ e) y ∂volume = ⨍ y in B, f y ∂volume := by
    rw [← setAverage_congr hB]
    exact setAverage_comp_preimage_of_map_eq_smul hmap ha ENNReal.ofReal_ne_top f B
  have hJN := volume_lt_norm_sub_setAverage_le (q₀ := (0, 0))
    (integrableOn_comp_cubeEquiv hr hf) (setLAverage_comp_cubeEquiv_le hr hM) s
  rw [havg] at hJN
  rw [← ENNReal.mul_le_mul_iff_right ha ENNReal.ofReal_ne_top, ← hvol, mul_left_comm, ← hvol]
  calc volume (e ⁻¹' {x ∈ B | s < ‖f x - ⨍ y in B, f y ∂volume‖})
      = volume {x ∈ dyadicCube 0 0 | s < ‖(f ∘ e) x - ⨍ y in B, f y ∂volume‖} :=
        measure_congr (hB.inter (ae_eq_refl _))
    _ ≤ _ := hJN
    _ = _ := by rw [measure_congr hB]

/-- **Exponential integrability of functions of bounded mean oscillation** on a cube. Let `f` be
integrable on the closed sup-norm ball `closedBall c r ⊆ ℝⁿ`, `n ≥ 1`, with mean oscillation
`⨍_B ‖f - f_B‖ ≤ M` on every closed ball `B ⊆ closedBall c r`. If `ρ = exp (2ⁿ⁺¹ σ M) < 2`, then

`∫_{closedBall c r} exp (σ ‖f - f_{closedBall c r}‖) ≤ (1 + 2ρ / (2 - ρ)) |closedBall c r|`. -/
theorem setLIntegral_exp_mul_norm_sub_setAverage_closedBall_le [Nonempty ι] [CompleteSpace E]
    (hf : IntegrableOn f (closedBall c r))
    (hM : ∀ y ρ, closedBall y ρ ⊆ closedBall c r →
      ⨍⁻ x in closedBall y ρ, ‖f x - ⨍ z in closedBall y ρ, f z ∂volume‖ₑ ∂volume ≤ M)
    {σ : ℝ} (hρ : Real.exp (σ * (2 ^ (Fintype.card ι + 1) * M)) < 2) :
    ∫⁻ x in closedBall c r,
        ENNReal.ofReal (Real.exp (σ * ‖f x - ⨍ y in closedBall c r, f y ∂volume‖)) ≤
      ENNReal.ofReal (1 + 2 * Real.exp (σ * (2 ^ (Fintype.card ι + 1) * M)) /
        (2 - Real.exp (σ * (2 ^ (Fintype.card ι + 1) * M)))) * volume (closedBall c r) := by
  rcases le_or_gt r 0 with hr | hr
  · rw [setLIntegral_measure_zero _ _ (volume_closedBall_eq_zero_of_nonpos c hr)]
    exact zero_le
  set e := cubeEquiv c hr
  set B := closedBall c r
  have hmap := map_cubeEquiv (c := c) hr
  have ha := ofReal_inv_two_mul_pow_ne_zero (ι := ι) hr
  have hB : e ⁻¹' B =ᵐ[volume] dyadicCube 0 0 := by
    rw [preimage_cubeEquiv_closedBall_self hr, closure_dyadicCube]
    exact (dyadicCube_ae_eq_closedBall 0 0).symm
  have havg : ⨍ y in dyadicCube 0 0, (f ∘ e) y ∂volume = ⨍ y in B, f y ∂volume := by
    rw [← setAverage_congr hB]
    exact setAverage_comp_preimage_of_map_eq_smul hmap ha ENNReal.ofReal_ne_top f B
  have hJN := setLIntegral_exp_mul_norm_sub_setAverage_le (q₀ := (0, 0))
    (integrableOn_comp_cubeEquiv hr hf) (setLAverage_comp_cubeEquiv_le hr hM) hρ
  rw [havg] at hJN
  have hint := setLIntegral_comp_preimage_of_map_eq_smul hmap
    (fun x => ENNReal.ofReal (Real.exp (σ * ‖f x - ⨍ y in B, f y ∂volume‖))) B
  have hvol : volume (e ⁻¹' B) = ENNReal.ofReal ((2 * r) ^ Fintype.card ι)⁻¹ * volume B := by
    rw [← e.map_apply, hmap, Measure.smul_apply, smul_eq_mul]
  rw [← ENNReal.mul_le_mul_iff_right ha ENNReal.ofReal_ne_top, ← hint, mul_left_comm, ← hvol]
  calc ∫⁻ x in e ⁻¹' B, ENNReal.ofReal (Real.exp (σ * ‖f (e x) - ⨍ y in B, f y ∂volume‖))
      = ∫⁻ x in dyadicCube 0 0,
          ENNReal.ofReal (Real.exp (σ * ‖(f ∘ e) x - ⨍ y in B, f y ∂volume‖)) :=
        setLIntegral_congr hB
    _ ≤ _ := hJN
    _ = _ := by rw [measure_congr hB]

end ClosedBall

section EuclideanBall

/-! ### Euclidean balls

In `ℝⁿ = EuclideanSpace ℝ ι`, with any additive Haar measure `μ`, suppose `f` has mean
oscillation at most `M` on every Euclidean ball inside `B(x₀, R)`. Let `s = √n` and let `Q₀` be
the cube of half-side `r₀ = R / (3s)` centred at `x₀`. A cube `Q ⊆ Q₀` of half-side `ρ` has
`ρ ≤ r₀`, so it lies in the Euclidean ball `B` of radius `2sρ` about its centre, and `B` lies in
`B(x₀, R)`. Since `B` lies in the cube of half-side `2sρ` about the same centre,
`μ B ≤ (2s)ⁿ μ Q`, and comparing mean oscillations on `Q ⊆ B` shows that `f` has mean oscillation
at most `2 (2s)ⁿ M` on every cube inside `Q₀`. The John–Nirenberg inequality on `Q₀`, read through
the measure-preserving equivalence `ofLp` between `EuclideanSpace ℝ ι` and `ι → ℝ`, then gives
exponential integrability on `Q₀`, and hence on the Euclidean ball `B(x₀, r₀) ⊆ Q₀`. This ball
contains the cube of half-side `r₀ / s`, so `μ Q₀ ≤ sⁿ μ B(x₀, r₀)`, and the averages of `f` over
`Q₀` and over `B(x₀, r₀)` differ by at most `sⁿ` times the mean oscillation on `Q₀`. -/

open Metric WithLp

/-- An additive Haar measure on `EuclideanSpace ℝ ι` is carried by `ofLp` to a positive finite
multiple of Lebesgue measure on `ι → ℝ`. -/
private theorem exists_map_toLp_symm_eq_smul (μ : Measure (EuclideanSpace ℝ ι))
    [μ.IsAddHaarMeasure] :
    ∃ a : ℝ≥0∞, a ≠ 0 ∧ a ≠ ⊤ ∧ μ.map (MeasurableEquiv.toLp 2 (ι → ℝ)).symm = a • volume := by
  refine ⟨Measure.addHaarScalarFactor μ volume, ENNReal.coe_ne_zero.2
    (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ volume).ne', ENNReal.coe_ne_top, ?_⟩
  conv_lhs => rw [Measure.isAddLeftInvariant_eq_smul μ volume]
  rw [Measure.map_smul, (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp ι).map_eq,
    Measure.coe_nnreal_smul]
  exact (MeasurableEquiv.toLp 2 (ι → ℝ)).symm.measurable.aemeasurable

/-- If `ofLp` carries `μ` to `a • volume`, then `μ` gives the preimage of `S` the measure
`a * volume S`. -/
private theorem measure_ofLp_preimage {μ : Measure (EuclideanSpace ℝ ι)} {a : ℝ≥0∞}
    (he : μ.map (MeasurableEquiv.toLp 2 (ι → ℝ)).symm = a • volume) (S : Set (ι → ℝ)) :
    μ (ofLp ⁻¹' S) = a * volume S := by
  rw [← MeasurableEquiv.coe_toLp_symm, ← MeasurableEquiv.map_apply, he, Measure.smul_apply,
    smul_eq_mul]

/-- **Mean oscillation on cubes from mean oscillation on Euclidean balls.** Let `f` have mean
oscillation at most `M` on every Euclidean ball inside `B(x₀, R)`. Then on every cube `Q` of
positive half-side inside the cube of half-side `R / (3√n)` centred at `x₀`, the mean oscillation
of `f` is at most `2 (2√n)ⁿ M`. -/
private theorem setLAverage_preimage_closedBall_le [Nonempty ι] [CompleteSpace E]
    {μ : Measure (EuclideanSpace ℝ ι)} [μ.IsAddHaarMeasure] {a : ℝ≥0∞} (ha : a ≠ 0)
    (he : μ.map (MeasurableEquiv.toLp 2 (ι → ℝ)).symm = a • volume)
    {f : EuclideanSpace ℝ ι → E} {x₀ : EuclideanSpace ℝ ι} {R : ℝ}
    (hf : IntegrableOn f (ball x₀ R) μ)
    (hM : ∀ y s, ball y s ⊆ ball x₀ R →
      ⨍⁻ x in ball y s, ‖f x - ⨍ z in ball y s, f z ∂μ‖ₑ ∂μ ≤ M)
    {y : ι → ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    (hy : closedBall y ρ ⊆ closedBall (ofLp x₀) (R / (3 * √(Fintype.card ι)))) :
    ⨍⁻ x in ofLp ⁻¹' closedBall y ρ, ‖f x - ⨍ z in ofLp ⁻¹' closedBall y ρ, f z ∂μ‖ₑ ∂μ ≤
      2 * ENNReal.ofReal ((2 * √(Fintype.card ι)) ^ Fintype.card ι) * M := by
  set n := Fintype.card ι
  set s := √(n : ℝ)
  have hs : 0 < s := Real.sqrt_pos.2 (by exact_mod_cast Fintype.card_pos)
  set r₀ := R / (3 * s)
  set Q := ofLp ⁻¹' closedBall y ρ
  set z : EuclideanSpace ℝ ι := toLp 2 y
  set B := ball z (2 * s * ρ)
  -- `ρ ≤ r₀`, by comparing the volumes of the two cubes.
  have hρr : ρ ≤ r₀ := by
    have hr₀ : 0 ≤ r₀ := dist_nonneg.trans (mem_closedBall.1 (hy (mem_closedBall_self hρ.le)))
    have h := measure_mono (μ := volume) hy
    rw [Real.volume_pi_closedBall _ hρ.le, Real.volume_pi_closedBall _ hr₀,
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
    have h' := (pow_le_pow_iff_left₀ (by positivity) (by positivity) Fintype.card_ne_zero).1 h
    linarith
  have hdist : dist z x₀ ≤ s * r₀ := (EuclideanSpace.dist_le_sqrt_card_mul_dist_ofLp z x₀).trans
    (mul_le_mul_of_nonneg_left (mem_closedBall.1 (hy (mem_closedBall_self hρ.le))) hs.le)
  have hQB : Q ⊆ B := fun x hx => by
    rw [mem_ball]
    calc dist x z ≤ s * dist (ofLp x) y := EuclideanSpace.dist_le_sqrt_card_mul_dist_ofLp x z
      _ ≤ s * ρ := mul_le_mul_of_nonneg_left (mem_closedBall.1 hx) hs.le
      _ < 2 * s * ρ := by nlinarith
  have hBR : B ⊆ ball x₀ R := ball_subset_ball' <| by
    have h3 : 3 * s * r₀ = R := by
      simp only [r₀]
      field_simp
    nlinarith
  have hBQ : B ⊆ ofLp ⁻¹' closedBall y (2 * s * ρ) := fun x hx =>
    mem_closedBall.2 (((PiLp.lipschitzWith_ofLp 2 _).dist_le_mul x z).trans
      (by simpa using (mem_ball.1 hx).le))
  have hQ0 : μ Q ≠ 0 := by
    rw [measure_ofLp_preimage he, Real.volume_pi_closedBall _ hρ.le]
    exact mul_ne_zero ha (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hratio : μ B / μ Q ≤ ENNReal.ofReal ((2 * s) ^ n) := by
    refine ENNReal.div_le_of_le_mul ((measure_mono hBQ).trans_eq ?_)
    rw [measure_ofLp_preimage he, measure_ofLp_preimage he,
      Real.volume_pi_closedBall _ (by positivity), Real.volume_pi_closedBall _ hρ.le,
      mul_left_comm (ENNReal.ofReal _),
      ← ENNReal.ofReal_mul (by positivity), ← mul_pow]
    congr 3
    ring
  calc ⨍⁻ x in Q, ‖f x - ⨍ z in Q, f z ∂μ‖ₑ ∂μ
      ≤ 2 * ⨍⁻ x in Q, ‖f x - ⨍ z in B, f z ∂μ‖ₑ ∂μ :=
        setLAverage_enorm_sub_setAverage_le (hf.mono_set (hQB.trans hBR)) _
    _ ≤ 2 * (μ B / μ Q * ⨍⁻ x in B, ‖f x - ⨍ z in B, f z ∂μ‖ₑ ∂μ) := by
        gcongr
        exact setLAverage_le_div_mul_setLAverage_of_subset hQB measure_ball_lt_top.ne
    _ ≤ 2 * (ENNReal.ofReal ((2 * s) ^ n) * M) := by
        gcongr
        exact hM _ _ hBR
    _ = _ := (mul_assoc _ _ _).symm

/-- The Euclidean ball `B(x₀, r)` lies in the cube of half-side `r` centred at `x₀`, whose measure
is at most `√nⁿ` times that of the ball. -/
private theorem measure_preimage_closedBall_le [Nonempty ι] {μ : Measure (EuclideanSpace ℝ ι)}
    {a : ℝ≥0∞} (he : μ.map (MeasurableEquiv.toLp 2 (ι → ℝ)).symm = a • volume)
    (x₀ : EuclideanSpace ℝ ι) {r : ℝ} (hr : 0 < r) :
    μ (ofLp ⁻¹' closedBall (ofLp x₀) r) ≤
      ENNReal.ofReal (√(Fintype.card ι) ^ Fintype.card ι) * μ (ball x₀ r) := by
  have hs : 0 < √(Fintype.card ι : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast Fintype.card_pos)
  -- The ball contains the cube of half-side `r / √n`.
  have hsub : ofLp ⁻¹' ball (ofLp x₀) (r / √(Fintype.card ι)) ⊆ ball x₀ r := fun x hx => by
    rw [mem_ball]
    calc dist x x₀ ≤ √(Fintype.card ι) * dist (ofLp x) (ofLp x₀) :=
          EuclideanSpace.dist_le_sqrt_card_mul_dist_ofLp x x₀
      _ < √(Fintype.card ι) * (r / √(Fintype.card ι)) :=
          mul_lt_mul_of_pos_left (mem_ball.1 hx) hs
      _ = r := by field_simp
  refine le_trans (le_of_eq ?_) (mul_le_mul_right (measure_mono hsub) _)
  rw [measure_ofLp_preimage he, measure_ofLp_preimage he, Real.volume_pi_closedBall _ hr.le,
    Real.volume_pi_ball _ (by positivity), mul_left_comm, ← ENNReal.ofReal_mul (by positivity),
    ← mul_pow]
  congr 3
  field_simp

/-- The John–Nirenberg inequality on the cube `Q₀` of half-side `R / (3√n)` centred at `x₀`, for
a function of mean oscillation at most `M` on the Euclidean balls inside `B(x₀, R)`. -/
private theorem setLIntegral_exp_preimage_closedBall_le [Nonempty ι] [CompleteSpace E]
    {μ : Measure (EuclideanSpace ℝ ι)} [μ.IsAddHaarMeasure] {a : ℝ≥0∞} (ha : a ≠ 0)
    (ha' : a ≠ ⊤) (he : μ.map (MeasurableEquiv.toLp 2 (ι → ℝ)).symm = a • volume)
    {f : EuclideanSpace ℝ ι → E} {x₀ : EuclideanSpace ℝ ι} {R : ℝ} (hR : 0 < R)
    (hf : IntegrableOn f (ball x₀ R) μ)
    (hM : ∀ y s, ball y s ⊆ ball x₀ R →
      ⨍⁻ x in ball y s, ‖f x - ⨍ z in ball y s, f z ∂μ‖ₑ ∂μ ≤ M)
    {M' : ℝ≥0} (hM' : 2 * ENNReal.ofReal ((2 * √(Fintype.card ι)) ^ Fintype.card ι) * M ≤ M')
    {σ : ℝ} (hρ : Real.exp (σ * (2 ^ (Fintype.card ι + 1) * M')) < 2) :
    ∫⁻ x in ofLp ⁻¹' closedBall (ofLp x₀) (R / (3 * √(Fintype.card ι))),
        ENNReal.ofReal (Real.exp (σ * ‖f x - ⨍ y in ofLp ⁻¹' closedBall (ofLp x₀)
          (R / (3 * √(Fintype.card ι))), f y ∂μ‖)) ∂μ ≤
      ENNReal.ofReal (1 + 2 * Real.exp (σ * (2 ^ (Fintype.card ι + 1) * M')) /
        (2 - Real.exp (σ * (2 ^ (Fintype.card ι + 1) * M')))) *
        μ (ofLp ⁻¹' closedBall (ofLp x₀) (R / (3 * √(Fintype.card ι)))) := by
  set e := (MeasurableEquiv.toLp 2 (ι → ℝ)).symm
  set r₀ := R / (3 * √(Fintype.card ι : ℝ))
  have hs : 0 < √(Fintype.card ι : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast Fintype.card_pos)
  have hr₀ : 0 < r₀ := by positivity
  -- `f` read in the coordinates `ι → ℝ`.
  set g : (ι → ℝ) → E := fun y => f (toLp 2 y) with hg_def
  have hge : ∀ x, g (e x) = f x := fun x => by
    simp only [hg_def, e, MeasurableEquiv.toLp_symm_apply, toLp_ofLp]
  have hpre (S : Set (ι → ℝ)) : e ⁻¹' S = ofLp ⁻¹' S := by
    rw [MeasurableEquiv.coe_toLp_symm]
  -- The cube lies in `B(x₀, R)`, since its points are within `√n r₀ = R / 3` of `x₀`.
  have hQR : ofLp ⁻¹' closedBall (ofLp x₀) r₀ ⊆ ball x₀ R := fun x hx => by
    rw [mem_ball]
    calc dist x x₀ ≤ √(Fintype.card ι) * dist (ofLp x) (ofLp x₀) :=
          EuclideanSpace.dist_le_sqrt_card_mul_dist_ofLp x x₀
      _ ≤ √(Fintype.card ι) * r₀ := mul_le_mul_of_nonneg_left (mem_closedBall.1 hx) hs.le
      _ < R := by
          simp only [r₀]
          field_simp
          linarith
  have hg : IntegrableOn g (closedBall (ofLp x₀) r₀) := by
    have h : IntegrableOn g (closedBall (ofLp x₀) r₀) (μ.map e) := by
      rw [integrableOn_map_equiv, hpre, Function.comp_def]
      simp_rw [hge]
      exact hf.mono_set hQR
    rwa [he, IntegrableOn, Measure.restrict_smul, integrable_smul_measure ha ha'] at h
  have hMg : ∀ y ρ, closedBall y ρ ⊆ closedBall (ofLp x₀) r₀ →
      ⨍⁻ x in closedBall y ρ, ‖g x - ⨍ z in closedBall y ρ, g z ∂volume‖ₑ ∂volume ≤ M' := by
    intro y ρ hy
    rcases le_or_gt ρ 0 with hρ0 | hρ0
    · rw [setLAverage_eq, setLIntegral_measure_zero _ _
        (volume_closedBall_eq_zero_of_nonpos y hρ0), ENNReal.zero_div]
      exact zero_le
    rw [← setLAverage_comp_preimage_of_map_eq_smul he ha ha',
      ← setAverage_comp_preimage_of_map_eq_smul he ha ha', hpre]
    simp_rw [hge]
    exact (setLAverage_preimage_closedBall_le ha he hf hM hρ0 hy).trans hM'
  have havg : ⨍ y in closedBall (ofLp x₀) r₀, g y ∂volume =
      ⨍ x in ofLp ⁻¹' closedBall (ofLp x₀) r₀, f x ∂μ := by
    rw [← setAverage_comp_preimage_of_map_eq_smul he ha ha' g, hpre]
    simp_rw [hge]
  have hJN := setLIntegral_exp_mul_norm_sub_setAverage_closedBall_le hg hMg hρ
  rw [havg] at hJN
  have hint := setLIntegral_comp_preimage_of_map_eq_smul he
    (fun y => ENNReal.ofReal (Real.exp (σ * ‖g y -
      ⨍ x in ofLp ⁻¹' closedBall (ofLp x₀) r₀, f x ∂μ‖))) (closedBall (ofLp x₀) r₀)
  rw [hpre] at hint
  simp_rw [hge] at hint
  calc ∫⁻ x in ofLp ⁻¹' closedBall (ofLp x₀) r₀,
        ENNReal.ofReal (Real.exp (σ * ‖f x - ⨍ y in ofLp ⁻¹' closedBall (ofLp x₀) r₀, f y ∂μ‖)) ∂μ
      = a * ∫⁻ y in closedBall (ofLp x₀) r₀, ENNReal.ofReal (Real.exp (σ * ‖g y -
          ⨍ x in ofLp ⁻¹' closedBall (ofLp x₀) r₀, f x ∂μ‖)) := hint
    _ ≤ a * (ENNReal.ofReal (1 + 2 * Real.exp (σ * (2 ^ (Fintype.card ι + 1) * M')) /
          (2 - Real.exp (σ * (2 ^ (Fintype.card ι + 1) * M')))) *
          volume (closedBall (ofLp x₀) r₀)) := by gcongr
    _ = _ := by rw [mul_left_comm, ← measure_ofLp_preimage he]

/-- The John–Nirenberg inequality on the Euclidean ball `B(x₀, R / (3√n))`, with explicit constants,
for a function of mean oscillation at most `M` on the Euclidean balls inside `B(x₀, R)`. -/
private theorem setLIntegral_exp_mul_norm_sub_setAverage_ball_le_of_nonneg [Nonempty ι]
    [CompleteSpace E] {μ : Measure (EuclideanSpace ℝ ι)} [μ.IsAddHaarMeasure]
    {f : EuclideanSpace ℝ ι → E} {x₀ : EuclideanSpace ℝ ι} {R : ℝ}
    (hf : IntegrableOn f (ball x₀ R) μ)
    (hM : ∀ y s, ball y s ⊆ ball x₀ R →
      ⨍⁻ x in ball y s, ‖f x - ⨍ z in ball y s, f z ∂μ‖ₑ ∂μ ≤ M)
    {M' : ℝ≥0} (hM' : 2 * ENNReal.ofReal ((2 * √(Fintype.card ι)) ^ Fintype.card ι) * M ≤ M')
    {σ : ℝ} (hσ : 0 ≤ σ) (hρ : Real.exp (σ * (2 ^ (Fintype.card ι + 1) * M')) < 2) :
    ∫⁻ x in ball x₀ (R / (3 * √(Fintype.card ι))),
        ENNReal.ofReal (Real.exp (σ * ‖f x - ⨍ y in ball x₀ (R / (3 * √(Fintype.card ι))),
          f y ∂μ‖)) ∂μ ≤
      ENNReal.ofReal (√(Fintype.card ι) ^ Fintype.card ι *
        Real.exp (σ * (√(Fintype.card ι) ^ Fintype.card ι * M')) *
        (1 + 2 * Real.exp (σ * (2 ^ (Fintype.card ι + 1) * M')) /
          (2 - Real.exp (σ * (2 ^ (Fintype.card ι + 1) * M'))))) *
        μ (ball x₀ (R / (3 * √(Fintype.card ι)))) := by
  obtain ⟨a, ha, ha', he⟩ := exists_map_toLp_symm_eq_smul μ
  have hs : 0 < √(Fintype.card ι : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast Fintype.card_pos)
  rcases le_or_gt R 0 with hR | hR
  · rw [ball_eq_empty.2 (div_nonpos_of_nonpos_of_nonneg hR (by positivity)),
      Measure.restrict_empty, lintegral_zero_measure]
    exact zero_le
  set n := Fintype.card ι
  set s := √(n : ℝ)
  set r₀ := R / (3 * s)
  have hr₀ : 0 < r₀ := by positivity
  set Q := ofLp ⁻¹' closedBall (ofLp x₀) r₀
  set B := ball x₀ r₀
  set ρ := Real.exp (σ * (2 ^ (n + 1) * M'))
  have hBQ : B ⊆ Q := fun x hx =>
    mem_closedBall.2 (((PiLp.lipschitzWith_ofLp 2 _).dist_le_mul x x₀).trans
      (by simpa using (mem_ball.1 hx).le))
  have hQB : μ Q ≤ ENNReal.ofReal (s ^ n) * μ B := measure_preimage_closedBall_le he x₀ hr₀
  have hQtop : μ Q ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne) hQB
  have hBR : B ⊆ ball x₀ R := ball_subset_ball <| by
    simp only [r₀]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Real.one_le_sqrt.2 (show (1 : ℝ) ≤ n by exact_mod_cast Fintype.card_pos)]
  have hJN := setLIntegral_exp_preimage_closedBall_le ha ha' he hR hf hM hM' hρ
  -- The averages of `f` over `B` and over `Q` differ by at most `sⁿ M'`.
  have hd : ‖(⨍ y in Q, f y ∂μ) - ⨍ y in B, f y ∂μ‖ ≤ s ^ n * M' := by
    have hB0 : μ B ≠ 0 := (measure_ball_pos μ x₀ hr₀).ne'
    have hosc : ⨍⁻ x in Q, ‖f x - ⨍ y in Q, f y ∂μ‖ₑ ∂μ ≤ M' :=
      (setLAverage_preimage_closedBall_le ha he hf hM hr₀ subset_rfl).trans hM'
    have h : ‖(⨍ y in B, f y ∂μ) - ⨍ y in Q, f y ∂μ‖ₑ ≤ ENNReal.ofReal (s ^ n) * M' :=
      (enorm_setAverage_sub_le_of_subset hBQ hB0 hQtop (hf.mono_set hBR) _).trans <| by
        gcongr
        exact ENNReal.div_le_of_le_mul hQB
    rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal,
      ← ENNReal.ofReal_mul (by positivity)] at h
    rw [norm_sub_rev]
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h
  have hC₁ : 0 ≤ 1 + 2 * ρ / (2 - ρ) := by
    have : 0 < 2 - ρ := by linarith
    positivity
  calc ∫⁻ x in B, ENNReal.ofReal (Real.exp (σ * ‖f x - ⨍ y in B, f y ∂μ‖)) ∂μ
      ≤ ∫⁻ x in B, ENNReal.ofReal (Real.exp (σ * (s ^ n * M'))) *
          ENNReal.ofReal (Real.exp (σ * ‖f x - ⨍ y in Q, f y ∂μ‖)) ∂μ := by
        refine lintegral_mono fun x => ?_
        rw [← ENNReal.ofReal_mul (by positivity), ← Real.exp_add, ← mul_add]
        gcongr
        exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (by rw [add_comm]; gcongr)
    _ = ENNReal.ofReal (Real.exp (σ * (s ^ n * M'))) *
          ∫⁻ x in B, ENNReal.ofReal (Real.exp (σ * ‖f x - ⨍ y in Q, f y ∂μ‖)) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (Real.exp (σ * (s ^ n * M'))) *
          ∫⁻ x in Q, ENNReal.ofReal (Real.exp (σ * ‖f x - ⨍ y in Q, f y ∂μ‖)) ∂μ := by
        gcongr
    _ ≤ ENNReal.ofReal (Real.exp (σ * (s ^ n * M'))) *
          (ENNReal.ofReal (1 + 2 * ρ / (2 - ρ)) * (ENNReal.ofReal (s ^ n) * μ B)) := by
        gcongr
        exact hJN.trans (by gcongr)
    _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
        ring

/-- **The John–Nirenberg inequality on Euclidean balls.** There are constants `A > 0` and `C`,
depending only on the dimension `n`, such that the following holds for every additive Haar
measure `μ` on `ℝⁿ = EuclideanSpace ℝ ι`. Let `f : ℝⁿ → E` be integrable on the ball `B(x₀, R)`,
with mean oscillation `⨍_B ‖f - f_B‖ ≤ M` on every ball `B ⊆ B(x₀, R)`. If `σ M ≤ A`, then on the
concentric ball `B' = B(x₀, R / (3√n))`,

`∫_{B'} exp (σ ‖f - f_{B'}‖) ≤ C |B'|`. -/
theorem exists_setLIntegral_exp_mul_norm_sub_setAverage_ball_le :
    ∃ A : ℝ, 0 < A ∧ ∃ C : ℝ≥0, ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [CompleteSpace E] {μ : Measure (EuclideanSpace ℝ ι)} [μ.IsAddHaarMeasure]
      {f : EuclideanSpace ℝ ι → E} {x₀ : EuclideanSpace ℝ ι} {R : ℝ} {M : ℝ≥0} {σ : ℝ},
      IntegrableOn f (ball x₀ R) μ →
      (∀ y s, ball y s ⊆ ball x₀ R →
        ⨍⁻ x in ball y s, ‖f x - ⨍ z in ball y s, f z ∂μ‖ₑ ∂μ ≤ M) →
      σ * M ≤ A →
      ∫⁻ x in ball x₀ (R / (3 * √(Fintype.card ι))),
          ENNReal.ofReal (Real.exp (σ * ‖f x - ⨍ y in ball x₀ (R / (3 * √(Fintype.card ι))),
            f y ∂μ‖)) ∂μ ≤
        C * μ (ball x₀ (R / (3 * √(Fintype.card ι)))) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · -- In dimension `0` the ball `B(x₀, R / 0) = B(x₀, 0)` is empty.
    refine ⟨1, one_pos, 0, fun {E} _ _ _ μ _ f x₀ R M σ _ _ _ => ?_⟩
    simp [Fintype.card_eq_zero]
  set n := Fintype.card ι
  set s := √(n : ℝ)
  have hs : 1 ≤ s := Real.one_le_sqrt.2 (by exact_mod_cast Fintype.card_pos)
  set K := (2 * s) ^ n
  have hK : 0 < K := by positivity
  set A := Real.log (3 / 2) / (2 ^ (n + 2) * K)
  have hA : 0 < A := div_pos (Real.log_pos (by norm_num)) (by positivity)
  set C : ℝ≥0 := ⟨s ^ n * Real.exp (s ^ n * (2 * K) * A) * 7, by positivity⟩
  have hC : 1 ≤ (C : ℝ) := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
    (one_le_pow₀ hs) (Real.one_le_exp (by positivity))) (by norm_num)
  refine ⟨A, hA, C, fun {E} _ _ _ μ _ f x₀ R M σ hf hM hσM => ?_⟩
  rw [← ENNReal.ofReal_coe_nnreal]
  set B := ball x₀ (R / (3 * s))
  rcases le_or_gt σ 0 with hσ | hσ
  · calc ∫⁻ x in B, ENNReal.ofReal (Real.exp (σ * ‖f x - ⨍ y in B, f y ∂μ‖)) ∂μ
        ≤ ∫⁻ _ in B, 1 ∂μ := lintegral_mono fun x => ENNReal.ofReal_le_one.2
          (Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg hσ (norm_nonneg _)))
      _ = μ B := by rw [setLIntegral_const, one_mul]
      _ ≤ ENNReal.ofReal C * μ B := le_mul_of_one_le_left' (ENNReal.one_le_ofReal.2 hC)
  set M' : ℝ≥0 := 2 * K.toNNReal * M
  have hM'K : (M' : ℝ) = 2 * K * M := by
    simp only [M', NNReal.coe_mul, Real.coe_toNNReal _ hK.le, NNReal.coe_ofNat]
  have hM' : 2 * ENNReal.ofReal K * M ≤ M' := by
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_coe_nnreal (p := M'), hM'K,
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_ofNat]
  set ρ := Real.exp (σ * (2 ^ (n + 1) * M'))
  have hρ : ρ ≤ 3 / 2 := by
    have hkey : σ * (2 ^ (n + 1) * M') ≤ Real.log (3 / 2) := by
      calc σ * (2 ^ (n + 1) * M') = 2 ^ (n + 2) * K * (σ * M) := by rw [hM'K]; ring
        _ ≤ 2 ^ (n + 2) * K * A := by gcongr
        _ = Real.log (3 / 2) := by simp only [A]; field_simp
    calc ρ ≤ Real.exp (Real.log (3 / 2)) := Real.exp_le_exp.2 hkey
      _ = 3 / 2 := Real.exp_log (by norm_num)
  have hexp : σ * (s ^ n * M') ≤ s ^ n * (2 * K) * A := by
    calc σ * (s ^ n * M') = s ^ n * (2 * K) * (σ * M) := by rw [hM'K]; ring
      _ ≤ s ^ n * (2 * K) * A := by gcongr
  have hC₁ : 1 + 2 * ρ / (2 - ρ) ≤ 7 := by
    have : 2 * ρ / (2 - ρ) ≤ 6 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    linarith
  have hfinal : s ^ n * Real.exp (σ * (s ^ n * M')) * (1 + 2 * ρ / (2 - ρ)) ≤ C := by
    have : 0 < 2 - ρ := by linarith
    calc _ ≤ s ^ n * Real.exp (s ^ n * (2 * K) * A) * 7 := by gcongr
      _ = C := rfl
  refine (setLIntegral_exp_mul_norm_sub_setAverage_ball_le_of_nonneg hf hM hM' hσ.le
    (by linarith)).trans ?_
  gcongr

/-- **Moser's crossover estimate.** There are constants `A > 0` and `C`, depending only on the
dimension `n`, such that the following holds for every additive Haar measure `μ` on
`ℝⁿ = EuclideanSpace ℝ ι`. Let `f : ℝⁿ → ℝ` be integrable on the ball `B(x₀, R)`, with mean
oscillation `⨍_B |f - f_B| ≤ M` on every ball `B ⊆ B(x₀, R)`. If `|σ| M ≤ A`, then on the
concentric ball `B' = B(x₀, R / (3√n))`,

`(∫_{B'} exp (σ f)) (∫_{B'} exp (-σ f)) ≤ C |B'|²`.

For `f = log u`, with `u` positive, this compares the averages of `u^σ` and of `u^(-σ)` over `B'`:
it is the step of Moser's proof of the Harnack inequality that links the bounds for positive
powers of a supersolution to those for its negative powers. -/
theorem exists_setLIntegral_exp_mul_mul_setLIntegral_exp_neg_mul_ball_le :
    ∃ A : ℝ, 0 < A ∧ ∃ C : ℝ≥0, ∀ {μ : Measure (EuclideanSpace ℝ ι)} [μ.IsAddHaarMeasure]
      {f : EuclideanSpace ℝ ι → ℝ} {x₀ : EuclideanSpace ℝ ι} {R : ℝ} {M : ℝ≥0} {σ : ℝ},
      IntegrableOn f (ball x₀ R) μ →
      (∀ y s, ball y s ⊆ ball x₀ R →
        ⨍⁻ x in ball y s, ‖f x - ⨍ z in ball y s, f z ∂μ‖ₑ ∂μ ≤ M) →
      |σ| * M ≤ A →
      (∫⁻ x in ball x₀ (R / (3 * √(Fintype.card ι))), ENNReal.ofReal (Real.exp (σ * f x)) ∂μ) *
          ∫⁻ x in ball x₀ (R / (3 * √(Fintype.card ι))),
            ENNReal.ofReal (Real.exp (-(σ * f x))) ∂μ ≤
        C * μ (ball x₀ (R / (3 * √(Fintype.card ι)))) ^ 2 := by
  obtain ⟨A, hA, C, h⟩ := exists_setLIntegral_exp_mul_norm_sub_setAverage_ball_le (ι := ι)
  refine ⟨A, hA, C ^ 2, fun {μ} _ f x₀ R M σ hf hM hσM => ?_⟩
  set B := ball x₀ (R / (3 * √(Fintype.card ι)))
  set c := ⨍ y in B, f y ∂μ
  set I := ∫⁻ x in B, ENNReal.ofReal (Real.exp (|σ| * ‖f x - c‖)) ∂μ
  have hI : I ≤ C * μ B := h hf hM hσM
  -- `exp (τ f) ≤ exp (τ c) exp (|τ| |f - c|)` pointwise.
  have hle (τ : ℝ) (hτ : |τ| = |σ|) :
      ∫⁻ x in B, ENNReal.ofReal (Real.exp (τ * f x)) ∂μ ≤
        ENNReal.ofReal (Real.exp (τ * c)) * I := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun x => ?_
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ← hτ]
    gcongr
    calc τ * f x = τ * c + τ * (f x - c) := by ring
      _ ≤ τ * c + |τ| * ‖f x - c‖ := by
          rw [Real.norm_eq_abs, ← abs_mul]
          gcongr
          exact le_abs_self _
  have hneg := hle (-σ) (abs_neg σ)
  simp only [neg_mul] at hneg
  calc (∫⁻ x in B, ENNReal.ofReal (Real.exp (σ * f x)) ∂μ) *
        ∫⁻ x in B, ENNReal.ofReal (Real.exp (-(σ * f x))) ∂μ
      ≤ (ENNReal.ofReal (Real.exp (σ * c)) * I) * (ENNReal.ofReal (Real.exp (-(σ * c))) * I) := by
        gcongr
        exact hle σ rfl
    _ = I ^ 2 := by
        rw [mul_mul_mul_comm, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
          add_neg_cancel, Real.exp_zero, ENNReal.ofReal_one, one_mul, sq]
    _ ≤ (C * μ B) ^ 2 := by gcongr
    _ = ((C ^ 2 : ℝ≥0) : ℝ≥0∞) * μ B ^ 2 := by
        rw [ENNReal.coe_pow, mul_pow]

end EuclideanBall

end TauCeti
