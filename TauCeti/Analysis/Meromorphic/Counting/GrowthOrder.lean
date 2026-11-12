/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.GrowthOrder
public import TauCeti.Analysis.Meromorphic.Counting.Jensen
import Mathlib.Data.Int.Log

/-!
# Zeros of an entire function of finite order

Let `f` be entire of order at most `A` (`TauCeti.OrderLE f A`), and let
`n(r) = TauCeti.zeroCount f univ (closedBall 0 r)` be the number of zeros of `f` in
`closedBall 0 r`, counted with multiplicity. Jensen's bound on the discs of radii `r` and `2 r`
gives `n(r) = O(r ^ B)` as `r → ∞` for every `B > A`. Splitting the zeros into the dyadic shells
`2 ^ k ≤ ‖ρ‖ < 2 ^ (k + 1)` turns this into the convergence of `∑_ρ m_ρ ‖ρ‖ ^ (-s)` for every
`s > A`, where `m_ρ` is the multiplicity of the zero `ρ`: the exponent of convergence of the zeros
is at most the order.

The zeros are indexed by the support of `MeromorphicOn.divisor f univ`, with the divisor value as
multiplicity, so no enumeration of the zeros is chosen. At order at most `1` the exponent `s = 2`
gives the summability of `∑_ρ m_ρ ‖ρ‖ ^ (-2)`, on which the genus-one canonical product
`∏_ρ E₁(z / ρ) ^ m_ρ` converges.

No nonvanishing hypothesis is needed. The identically zero function has zero divisor, a function
of negative order is constant, and otherwise the trailing-coefficient form of Jensen's bound
applies at the origin whatever the order of vanishing there.

## Main results

* `TauCeti.OrderLE.isBigO_zeroCount_closedBall`: `n(r) = O(r ^ B)` as `r → ∞` for every `B > A`.
* `TauCeti.OrderLE.summable_divisor_mul_norm_rpow_neg`: `∑_ρ m_ρ ‖ρ‖ ^ (-s)` converges for every
  `s > A`.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., GTM 74, §11.
* E. C. Titchmarsh, *The Theory of Functions*, 2nd ed., Chapter VIII.
-/

public section

open Set Metric Filter Asymptotics Topology Real

namespace TauCeti

variable {f : ℂ → ℂ} {A : ℝ}

/-- A nonconstant entire function of order at most `A` has `0 ≤ A` and finite order of vanishing
at the origin. -/
private lemma nonneg_and_analyticOrderAt_ne_top (h : OrderLE f A) (hf : Differentiable ℂ f)
    (hc : ¬ f.IsConst) : 0 ≤ A ∧ analyticOrderAt f 0 ≠ ⊤ := by
  refine ⟨not_lt.1 fun hA ↦ hc (h.isConst hf hA), fun h0 ↦ hc ?_⟩
  rw [AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero 0 hf.analyticAt] at h0
  exact fun _ _ ↦ by simp [h0]

/-- **Jensen's bound at radii `r` and `2 r`.** If `f` is entire, of finite order `m` at `0` with
trailing coefficient `a`, and bounded by `M ≥ 1` on `sphere 0 (2 r)` with `1 ≤ r`, then
`n(r) ≤ m + (log M - log ‖a‖) / log 2`. -/
private lemma zeroCount_closedBall_le (hf : Differentiable ℂ f) (hord : analyticOrderAt f 0 ≠ ⊤)
    {r M : ℝ} (hr : 1 ≤ r) (hM : 1 ≤ M) (hbound : ∀ z ∈ sphere (0 : ℂ) (2 * r), ‖f z‖ ≤ M) :
    (zeroCount f univ (closedBall 0 r) : ℝ) ≤
      analyticOrderNatAt f 0 + (log M - log ‖meromorphicTrailingCoeffAt f 0‖) / log 2 := by
  have hr0 : 0 < r := one_pos.trans_le hr
  have ha : meromorphicTrailingCoeffAt f 0 ≠ 0 :=
    (hf.analyticAt 0).meromorphicAt.meromorphicTrailingCoeffAt_ne_zero <| by
      rw [(hf.analyticAt 0).meromorphicOrderAt_eq]
      simpa using hord
  have hJ := AnalyticOnNhd.zeroCount_le_analyticOrderNatAt_add (c := 0) hr0
    (by linarith : r < 2 * r) hM (fun z _ ↦ hf.analyticAt z) hord hbound univ subset_rfl
  have hlog2 : 0 < log 2 := log_pos one_lt_two
  rw [show 2 * r / r = 2 by field_simp, log_div (by positivity) (norm_ne_zero_iff.2 ha)] at hJ
  refine hJ.trans ?_
  have : 0 ≤ (analyticOrderNatAt f 0 : ℝ) * log (2 * r) :=
    mul_nonneg (Nat.cast_nonneg _) (log_nonneg (by linarith))
  rw [add_le_add_iff_left]
  exact div_le_div_of_nonneg_right (by linarith) hlog2.le

/-- **Zeros of an entire function of finite order.** If `f` is entire of order at most `A`, then
for every `B > A` the number `n(r)` of zeros of `f` in `closedBall 0 r`, counted with
multiplicity, is `O(r ^ B)` as `r → ∞`. -/
theorem OrderLE.isBigO_zeroCount_closedBall (h : OrderLE f A) (hf : Differentiable ℂ f) {B : ℝ}
    (hB : A < B) :
    (fun r : ℝ ↦ (zeroCount f univ (closedBall 0 r) : ℝ)) =O[atTop] fun r ↦ r ^ B := by
  by_cases hc : f.IsConst
  · rw [show f = fun _ ↦ f 0 from funext fun z ↦ hc z 0]
    simpa using isBigO_zero (fun r : ℝ ↦ r ^ B) atTop
  obtain ⟨hA, hord⟩ := nonneg_and_analyticOrderAt_ne_top h hf hc
  have hB0 : 0 < B := hA.trans_lt hB
  -- A bound `‖f z‖ ≤ C exp (‖z‖ ^ B)` for `‖z‖ ≥ ρ₀`.
  obtain ⟨C, hC⟩ := (h.isBigO hB).bound
  obtain ⟨ρ₀, hρ₀⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.1 hC
  -- The constant part of Jensen's bound, and the coefficient of `r ^ B`.
  set K : ℝ := analyticOrderNatAt f 0 + (log (1 + |C|) - log ‖meromorphicTrailingCoeffAt f 0‖) /
    log 2
  refine IsBigO.of_bound (|K| + 2 ^ B / log 2) ?_
  filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop (ρ₀ / 2)] with r hr hrρ
  have hr0 : 0 ≤ r := zero_le_one.trans hr
  have hrB : 1 ≤ r ^ B := one_le_rpow hr hB0.le
  set M : ℝ := (1 + |C|) * exp ((2 * r) ^ B)
  have hM : 1 ≤ M := one_le_mul_of_one_le_of_one_le (by linarith [abs_nonneg C])
    (one_le_exp (by positivity))
  have hbound : ∀ z ∈ sphere (0 : ℂ) (2 * r), ‖f z‖ ≤ M := fun z hz ↦ by
    rw [mem_sphere_zero_iff_norm] at hz
    have := hρ₀.2 (show ρ₀ ≤ ‖z‖ by linarith)
    rw [norm_eq_abs, abs_exp, hz] at this
    exact this.trans (mul_le_mul_of_nonneg_right (by linarith [le_abs_self C]) (exp_pos _).le)
  have hJ := zeroCount_closedBall_le hf hord hr hM hbound
  rw [log_mul (by positivity) (exp_pos _).ne', log_exp, mul_rpow zero_le_two hr0] at hJ
  rw [norm_of_nonneg (Nat.cast_nonneg _), norm_of_nonneg (rpow_nonneg hr0 _)]
  calc (zeroCount f univ (closedBall 0 r) : ℝ) ≤ K + 2 ^ B / log 2 * r ^ B := by
        refine hJ.trans_eq ?_
        simp only [K]
        ring
    _ ≤ |K| * r ^ B + 2 ^ B / log 2 * r ^ B := by
        gcongr
        exact (le_abs_self K).trans (le_mul_of_one_le_right (abs_nonneg K) hrB)
    _ = (|K| + 2 ^ B / log 2) * r ^ B := by ring

/-- The dyadic shell containing a real `x ≥ 1`: `2 ^ k ≤ x < 2 ^ (k + 1)` for
`k = Nat.log 2 ⌊x⌋₊`. -/
private lemma two_pow_log_floor_le_and_lt {x : ℝ} (hx : 1 ≤ x) :
    2 ^ Nat.log 2 ⌊x⌋₊ ≤ x ∧ x < 2 ^ (Nat.log 2 ⌊x⌋₊ + 1) := by
  have hlog : ((Nat.log 2 ⌊x⌋₊ : ℕ) : ℤ) = Int.log 2 x := (Int.log_of_one_le_right 2 hx).symm
  have h₁ := Int.zpow_log_le_self (R := ℝ) one_lt_two (zero_lt_one.trans_le hx)
  have h₂ := Int.lt_zpow_succ_log_self (R := ℝ) one_lt_two x
  rw [← hlog] at h₁ h₂
  rw [zpow_natCast] at h₁
  rw [← Nat.cast_succ, zpow_natCast] at h₂
  exact ⟨by exact_mod_cast h₁, by exact_mod_cast h₂⟩

/-- **The zeros in a dyadic shell.** If `n(2 ^ (j + 1)) ≤ C (2 ^ (j + 1)) ^ B`, then the zeros
`ρ` of an entire function `f` with `2 ^ j ≤ ‖ρ‖ < 2 ^ (j + 1)` contribute at most
`C 2 ^ B (2 ^ (B - s)) ^ j` to `∑_ρ m_ρ ‖ρ‖ ^ (-s)` for `s ≥ 0`. -/
private lemma sum_divisor_mul_norm_rpow_neg_le (hf : Differentiable ℂ f) {B C s : ℝ} (hs : 0 ≤ s)
    {j : ℕ} {F : Finset ℂ} (hF : ∀ ρ ∈ F, 2 ^ j ≤ ‖ρ‖ ∧ ‖ρ‖ < 2 ^ (j + 1))
    (hN : (zeroCount f univ (closedBall 0 (2 ^ (j + 1))) : ℝ) ≤ C * ((2 : ℝ) ^ (j + 1)) ^ B) :
    ∑ ρ ∈ F, (MeromorphicOn.divisor f univ ρ : ℝ) * ‖ρ‖ ^ (-s) ≤
      C * 2 ^ B * ((2 : ℝ) ^ (B - s)) ^ j := by
  have hnonneg : ∀ ρ, 0 ≤ MeromorphicOn.divisor f univ ρ :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg fun z _ ↦ hf.analyticAt z
  have hsub : ↑F ⊆ closedBall (0 : ℂ) (2 ^ (j + 1)) := fun ρ hρ ↦ by
    simpa using (hF ρ hρ).2.le
  have hcount : ∑ ρ ∈ F, (MeromorphicOn.divisor f univ ρ : ℝ) ≤ C * ((2 : ℝ) ^ (j + 1)) ^ B :=
    calc ∑ ρ ∈ F, (MeromorphicOn.divisor f univ ρ : ℝ)
        = ((∑ ρ ∈ F, (MeromorphicOn.divisor f univ ρ).toNat : ℕ) : ℝ) := by
          push_cast
          exact Finset.sum_congr rfl fun ρ _ ↦ by
            exact_mod_cast (Int.toNat_of_nonneg (hnonneg ρ)).symm
      _ ≤ zeroCount f univ (closedBall 0 (2 ^ (j + 1))) := by
          rw [← zeroCount_coe_finset]
          exact_mod_cast zeroCount_mono hsub <| zeroCount_support_finite <|
            MeromorphicOn.divisor_finite_inter_support_of_isCompact (isCompact_closedBall _ _)
              (subset_univ _) subset_rfl
      _ ≤ C * ((2 : ℝ) ^ (j + 1)) ^ B := hN
  calc ∑ ρ ∈ F, (MeromorphicOn.divisor f univ ρ : ℝ) * ‖ρ‖ ^ (-s)
      ≤ ∑ ρ ∈ F, (MeromorphicOn.divisor f univ ρ : ℝ) * ((2 : ℝ) ^ j) ^ (-s) :=
        Finset.sum_le_sum fun ρ hρ ↦ mul_le_mul_of_nonneg_left
          (rpow_le_rpow_of_nonpos (by positivity) (hF ρ hρ).1 (by linarith))
          (Int.cast_nonneg (hnonneg ρ))
    _ = (∑ ρ ∈ F, (MeromorphicOn.divisor f univ ρ : ℝ)) * ((2 : ℝ) ^ j) ^ (-s) :=
        (Finset.sum_mul ..).symm
    _ ≤ C * ((2 : ℝ) ^ (j + 1)) ^ B * ((2 : ℝ) ^ j) ^ (-s) := by gcongr
    _ = C * 2 ^ B * ((2 : ℝ) ^ (B - s)) ^ j := by
        rw [pow_succ, mul_rpow (by positivity) zero_le_two, ← rpow_pow_comm zero_le_two,
          ← rpow_pow_comm zero_le_two, sub_eq_add_neg, rpow_add two_pos, mul_pow]
        ring

/-- **Convergence of the zeros of an entire function of finite order.** If `f` is entire of order
at most `A`, then `∑_ρ m_ρ ‖ρ‖ ^ (-s)` converges for every `s > A`, the sum running over the
zeros `ρ` of `f` with their multiplicities `m_ρ`, read off the divisor of `f` on `ℂ`. -/
theorem OrderLE.summable_divisor_mul_norm_rpow_neg (h : OrderLE f A) (hf : Differentiable ℂ f)
    {s : ℝ} (hs : A < s) :
    Summable fun ρ : ℂ ↦ (MeromorphicOn.divisor f univ ρ : ℝ) * ‖ρ‖ ^ (-s) := by
  classical
  by_cases hc : f.IsConst
  · rw [show f = fun _ ↦ f 0 from funext fun z ↦ hc z 0, MeromorphicOn.divisor_const]
    simp
  obtain ⟨hA, -⟩ := nonneg_and_analyticOrderAt_ne_top h hf hc
  obtain ⟨B, hAB, hBs⟩ := exists_between hs
  have hs0 : 0 < s := (hA.trans_lt hAB).trans hBs
  -- A bound `n(r) ≤ C r ^ B` for `r ≥ r₀`.
  obtain ⟨C, hC0, hC⟩ := (h.isBigO_zeroCount_closedBall hf hAB).exists_pos
  obtain ⟨r₀, hr₀⟩ := eventually_atTop.1 hC.bound
  set R₀ := max r₀ 1
  set g : ℂ → ℝ := fun ρ ↦ (MeromorphicOn.divisor f univ ρ : ℝ) * ‖ρ‖ ^ (-s)
  have hg0 : 0 ≤ g := fun ρ ↦ mul_nonneg (Int.cast_nonneg <|
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg (fun z _ ↦ hf.analyticAt z) ρ) (by positivity)
  rw [← indicator_self_add_compl (closedBall 0 R₀) g]
  -- Inside `closedBall 0 R₀` only finitely many zeros contribute.
  have hfin := MeromorphicOn.divisor_finite_inter_support_of_isCompact (f := f)
    (isCompact_closedBall (0 : ℂ) R₀) (subset_univ _) subset_rfl
  refine Summable.add (summable_of_ne_finset_zero (s := hfin.toFinset) fun ρ hρ ↦ ?_) ?_
  · rw [Set.Finite.mem_toFinset, mem_inter_iff, Function.mem_support, not_and_or, not_not] at hρ
    rcases hρ with hρ | hρ
    · exact indicator_of_notMem hρ g
    · simp [g, hρ]
  -- Outside, the zeros in the dyadic shell `2 ^ j ≤ ‖ρ‖ < 2 ^ (j + 1)` contribute at most
  -- `C 2 ^ B q ^ j` with `q = 2 ^ (B - s) < 1`.
  set q : ℝ := 2 ^ (B - s)
  have hgeom : Summable fun j : ℕ ↦ C * 2 ^ B * q ^ j :=
    (summable_geometric_of_lt_one (by positivity)
      (rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith))).mul_left _
  refine summable_of_sum_le (c := ∑' j : ℕ, C * 2 ^ B * q ^ j)
    (fun ρ ↦ indicator_nonneg (fun ρ _ ↦ hg0 ρ) ρ) fun F ↦ ?_
  let k : ℂ → ℕ := fun ρ ↦ Nat.log 2 ⌊‖ρ‖⌋₊
  set F' := F.filter (· ∉ closedBall (0 : ℂ) R₀)
  have hF' : ∀ ρ ∈ F', R₀ < ‖ρ‖ := fun ρ hρ ↦ by simpa [F'] using (Finset.mem_filter.1 hρ).2
  have hk : ∀ ρ ∈ F', 2 ^ k ρ ≤ ‖ρ‖ ∧ ‖ρ‖ < 2 ^ (k ρ + 1) := fun ρ hρ ↦
    two_pow_log_floor_le_and_lt ((le_max_right r₀ 1).trans (hF' ρ hρ).le)
  calc ∑ ρ ∈ F, (closedBall (0 : ℂ) R₀)ᶜ.indicator g ρ = ∑ ρ ∈ F', g ρ := by
        rw [Finset.sum_filter]
        exact Finset.sum_congr rfl fun ρ _ ↦ by simp [indicator_apply]
    _ = ∑ j ∈ F'.image k, ∑ ρ ∈ F' with k ρ = j, g ρ :=
        (Finset.sum_fiberwise_of_maps_to (fun ρ hρ ↦ Finset.mem_image_of_mem k hρ) _).symm
    _ ≤ ∑ j ∈ F'.image k, C * 2 ^ B * q ^ j := Finset.sum_le_sum fun j hj ↦ by
        obtain ⟨ρ₁, hρ₁, rfl⟩ := Finset.mem_image.1 hj
        refine sum_divisor_mul_norm_rpow_neg_le hf hs0.le (fun ρ hρ ↦ ?_) ?_
        · obtain ⟨hρ, hkρ⟩ := Finset.mem_filter.1 hρ
          rw [← hkρ]
          exact hk ρ hρ
        · have hN := hr₀ _ ((le_max_left r₀ 1).trans ((hF' ρ₁ hρ₁).trans (hk ρ₁ hρ₁).2).le)
          rwa [norm_of_nonneg (Nat.cast_nonneg _), norm_of_nonneg (by positivity)] at hN
    _ ≤ ∑' j, C * 2 ^ B * q ^ j := hgeom.sum_le_tsum _ fun j _ ↦ by positivity

end TauCeti
