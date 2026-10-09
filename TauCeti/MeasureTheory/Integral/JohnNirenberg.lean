/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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

## References

* F. John and L. Nirenberg, *On functions of bounded mean oscillation*, Comm. Pure Appl. Math.
  **14** (1961), 415–426.
* L. Grafakos, *Modern Fourier Analysis*, Theorem 3.1.6.
* E. Stein, *Harmonic Analysis*, Chapter IV, §1.3.
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

end TauCeti
