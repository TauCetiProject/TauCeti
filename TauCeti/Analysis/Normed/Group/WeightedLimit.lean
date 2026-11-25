/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Uniform

/-!
# Weighted limits and truncation

A sequence of families in a complete seminormed additive group has coefficientwise limits
at positive weights when the weighted differences satisfy a uniform Cauchy bound. At nonpositive
weights every value satisfies the one-sided error bound. For nonnegative weights, weighted
vanishing at infinity passes to the limit.

A family with weighted norms vanishing at infinity is also approximated by its finite truncations
in any seminorm bounded by uniform bounds on the weighted coefficients.

## Main results

* `TauCeti.exists_weighted_error_eventually_le`: coefficientwise limits and a uniform upper bound
  on the weighted errors.
* `TauCeti.tendsto_cofinite_zero_of_weighted_uniform_limit`: preservation of vanishing at infinity.
* `TauCeti.completeSpace_of_weighted_coeff`: completeness when weighted limits lie in the carrier.
* `TauCeti.tendsto_trunc_of_weighted_coeff_decay`: convergence of finite truncations.
-/

public section

namespace TauCeti

open Filter
open scoped Topology

/-- A sequence of families that is uniformly Cauchy in the weighted coefficient norms
`‖A k t‖ * w t` has a family `a` with a uniform upper bound on the weighted errors; at indices
with positive weight `a t` is the coefficientwise limit. No decay, boundedness or positivity
hypothesis on the weights is needed. -/
theorem exists_weighted_error_eventually_le {ι E : Type*}
    [SeminormedAddCommGroup E] [CompleteSpace E] (w : ι → ℝ) (A : ℕ → ι → E)
    (hC : ∀ ε > 0, ∃ N, ∀ k ≥ N, ∀ l ≥ N, ∀ t, ‖A k t - A l t‖ * w t < ε) :
    ∃ a : ι → E,
      (∀ t, 0 < w t → Tendsto (fun k ↦ A k t) atTop (𝓝 (a t))) ∧
      ∀ ε > 0, ∃ N, ∀ k ≥ N, ∀ t, ‖A k t - a t‖ * w t ≤ ε := by
  have hlim : ∀ t, ∃ a : E, 0 < w t → Tendsto (fun k ↦ A k t) atTop (𝓝 a) := fun t ↦ by
    by_cases ht : 0 < w t
    · refine (cauchySeq_tendsto_of_complete ?_).imp fun a ha _ ↦ ha
      refine Metric.cauchySeq_iff.mpr fun ε hε ↦ ?_
      obtain ⟨N, hN⟩ := hC (ε * w t) (mul_pos hε ht)
      exact ⟨N, fun k hk l hl ↦ by
        rw [dist_eq_norm]
        exact lt_of_mul_lt_mul_right (hN k hk l hl t) ht.le⟩
    · exact ⟨0, fun h ↦ absurd h ht⟩
  choose a ha using hlim
  refine ⟨a, ha, fun ε hε ↦ ?_⟩
  obtain ⟨N, hN⟩ := hC ε hε
  refine ⟨N, fun k hk t ↦ ?_⟩
  by_cases ht : 0 < w t
  · exact le_of_tendsto (((tendsto_const_nhds.sub (ha t ht)).norm).mul_const (w t))
      (eventually_atTop.mpr ⟨N, fun l hl ↦ (hN k hk l hl t).le⟩)
  · exact (mul_nonpos_of_nonneg_of_nonpos (norm_nonneg _) (not_lt.mp ht)).trans hε.le

/-- Vanishing at infinity of weighted coefficient norms is preserved by uniform weighted limits. -/
theorem tendsto_cofinite_zero_of_weighted_uniform_limit {ι E : Type*}
    [SeminormedAddCommGroup E] {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) {A : ℕ → ι → E} {a : ι → E}
    (hres : ∀ k, Tendsto (fun t ↦ ‖A k t‖ * w t) cofinite (𝓝 0))
    (hunif : ∀ ε > 0, ∃ N, ∀ k ≥ N, ∀ t, ‖A k t - a t‖ * w t ≤ ε) :
    Tendsto (fun t ↦ ‖a t‖ * w t) cofinite (𝓝 0) := by
  refine tendsto_order.mpr ⟨fun b hb ↦ .of_forall fun t ↦
    hb.trans_le (mul_nonneg (norm_nonneg _) (hw t)), fun ε hε ↦ ?_⟩
  obtain ⟨N, hN⟩ := hunif (ε / 2) (half_pos hε)
  filter_upwards [(hres N).eventually (gt_mem_nhds (half_pos hε))] with t ht
  calc
    ‖a t‖ * w t ≤ ‖A N t‖ * w t +
        ‖A N t - a t‖ * w t := by
      rw [← add_mul]
      exact mul_le_mul_of_nonneg_right (norm_le_norm_add_norm_sub _ _) (hw t)
    _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le ht (hN N le_rfl t)
    _ = ε := add_halves ε

/-- A seminormed additive group whose norm bounds are equivalent to uniform weighted coefficient
bounds is complete if the coefficient group is complete and each uniform weighted limit of
coefficient families is realized by an element of the group. -/
theorem completeSpace_of_weighted_coeff {ι D E : Type*}
    [SeminormedAddCommGroup D] [SeminormedAddCommGroup E] [CompleteSpace E]
    (coeff : ι → D →+ E) (w : ι → ℝ)
    (hnorm : ∀ (x : D) {C : ℝ}, ‖x‖ ≤ C ↔ ∀ i, ‖coeff i x‖ * w i ≤ C)
    (hlimit : ∀ (F : ℕ → D) (a : ι → E),
      (∀ ε > 0, ∃ N, ∀ k ≥ N, ∀ i, ‖coeff i (F k) - a i‖ * w i ≤ ε) →
      ∃ x : D, ∀ i, coeff i x = a i) : CompleteSpace D := by
  refine Metric.complete_of_cauchySeq_tendsto fun F hF ↦ ?_
  obtain ⟨a, _, ha⟩ := exists_weighted_error_eventually_le w (fun k i ↦ coeff i (F k)) (by
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hF ε hε
    refine ⟨N, fun k hk l hl i ↦ ?_⟩
    have hcoeff := (hnorm (F k - F l)).mp le_rfl i
    rw [map_sub] at hcoeff
    exact hcoeff.trans_lt ((dist_eq_norm _ _).symm.trans_lt (hN k hk l hl)))
  obtain ⟨x, hx⟩ := hlimit F a ha
  refine ⟨x, Metric.tendsto_atTop.mpr fun ε hε ↦ ?_⟩
  obtain ⟨N, hN⟩ := ha (ε / 2) (half_pos hε)
  refine ⟨N, fun k hk ↦ (?_ : _ ≤ ε / 2).trans_lt (half_lt_self hε)⟩
  rw [dist_eq_norm, hnorm]
  simpa only [map_sub, hx] using hN k hk

/-- Finite truncations converge when the weighted coefficients vanish at infinity and uniform
bounds on weighted coefficients bound the seminorm. -/
theorem tendsto_trunc_of_weighted_coeff_decay {ι D E : Type*} [DecidableEq ι]
    [SeminormedAddCommGroup D]
    [SeminormedAddCommGroup E] (coeff : D → ι → E) (w : ι → ℝ) {a : D}
    {trunc : Finset ι → D}
    (hbound : ∀ (x : D) {C : ℝ}, (∀ i, ‖coeff x i‖ * w i ≤ C) → ‖x‖ ≤ C)
    (hdecay : Tendsto (fun i ↦ ‖coeff a i‖ * w i) cofinite (𝓝 0))
    (htrunc : ∀ s i, ‖coeff (trunc s - a) i‖ * w i = if i ∈ s then 0 else ‖coeff a i‖ * w i) :
    Tendsto trunc atTop (𝓝 a) := by
  classical
  refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
  have hs : {i | ε / 2 ≤ ‖coeff a i‖ * w i}.Finite := by
    simpa only [eventually_cofinite, not_lt] using hdecay.eventually (gt_mem_nhds (half_pos hε))
  refine (eventually_ge_atTop hs.toFinset).mono fun s hss ↦ ?_
  rw [dist_eq_norm]
  refine (hbound _ fun i ↦ ?_).trans_lt (half_lt_self hε)
  rw [htrunc]
  split_ifs with hi
  · exact (half_pos hε).le
  · exact (not_le.mp fun h ↦ hi (hss (hs.mem_toFinset.mpr h))).le

end TauCeti
