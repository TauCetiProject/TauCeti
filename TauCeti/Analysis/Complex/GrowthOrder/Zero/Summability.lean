/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import TauCeti.Analysis.Complex.GrowthOrder.Zero.Count
public import TauCeti.Analysis.PSeries

/-!
# Summability over zeros of an entire function of finite order

For an entire function of order at most `A` that is nonzero at the origin,
its zeros, counted with multiplicity, have summable reciprocal `p`th powers
whenever `p > A`. Nonpositive exponents reduce to constants by Liouville's theorem.
The family is indexed by the support of Mathlib's native divisor on the whole plane.
Its integer values are nonnegative because the function is entire.

The proof uses `TauCeti.OrderLE.isBigO_sum_divisor` at an intermediate
exponent `B < p`. On each dyadic annulus, the contribution is bounded by a
constant times `2 ^ ((B - p) * n)`. Mathlib's `summable_partition` and its
geometric-series theorem then give summability. Local finiteness of the
native divisor handles the zeros in the unit disk. No enumeration of the
zeros is required.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Chapter 11.
-/

public section

open Filter Metric Topology
open scoped BigOperators

namespace TauCeti

/-- The reciprocal `p`th powers of the zeros of an entire function of order at most `A`
are summable with their divisor multiplicities for every `p > A`, provided the function
is nonzero at the origin. Nonpositive exponents reduce to the constant-function case. -/
theorem OrderLE.summable_divisor_mul_norm_rpow {f : ℂ → ℂ} {A p : ℝ}
    (h : OrderLE f A) (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0) (hAp : A < p) :
    Summable (fun ρ : (MeromorphicOn.divisor f Set.univ).support ↦
      (MeromorphicOn.divisor f Set.univ ρ : ℝ) * ‖(ρ : ℂ)‖ ^ (-p)) := by
  classical
  by_cases hp : 0 < p
  · let d := MeromorphicOn.divisor f Set.univ
    let r (ρ : d.support) : ℝ := max 1 ‖(ρ : ℂ)‖
    let w (ρ : d.support) : ℝ := d ρ
    have hfa : AnalyticOnNhd ℂ f Set.univ := fun z _ ↦ hf.analyticAt z
    have hw (ρ : d.support) : 0 ≤ w ρ := by
      dsimp only [w, d]
      exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfa ρ
    have hfinite (R : ℝ) : {ρ : d.support | r ρ ≤ R}.Finite := by
      apply (MeromorphicOn.divisor_norm_sublevel_finite f R).subset
      intro ρ hρ
      simp only [Set.mem_ofPred_eq, r] at hρ ⊢
      exact (le_max_right _ _).trans hρ
    have hcompare (R : ℝ) : (∑' ρ : {ρ : d.support | r ρ ≤ R}, w ρ) ≤
        ((∑ᶠ z, MeromorphicOn.divisor f (closedBall 0 R) z : ℤ) : ℝ) := by
      have hsub : ∀ ρ : d.support, ρ ∈ {ρ | r ρ ≤ R} → ‖(ρ : ℂ)‖ ≤ R := by
        intro ρ hρ
        simp only [Set.mem_ofPred_eq, r] at hρ
        exact (le_max_right _ _).trans hρ
      simpa only [w, d] using
        hfa.tsum_divisor_subtype_le_sum_closedBall (R := R) {ρ : d.support | r ρ ≤ R} hsub
    -- Choose an intermediate counting exponent, strictly below p.
    let B : ℝ := (max A 0 + p) / 2
    have hAB : A < B := by
      have := le_max_left A 0
      have := max_lt hAp hp
      dsimp [B]
      linarith
    have hBp : B < p := by have := max_lt hAp hp; dsimp [B]; linarith
    obtain ⟨C, _, hC⟩ := h.eventually_sum_divisor_le hf hf0 hAB
    have hcount : ∀ᶠ R : ℝ in atTop,
        (∑' ρ : {ρ : d.support | r ρ ≤ R}, w ρ) ≤ C * R ^ B :=
      hC.mono (fun R hR ↦ (hcompare R).trans hR)
    have hs := summable_mul_rpow_of_count_growth r w (fun ρ ↦ le_max_left _ _) hw hfinite
      hp.le hBp hcount
    -- Replacing the radius by max(1, radius) changes only finitely many terms.
    apply hs.congr_cofinite
    filter_upwards [(MeromorphicOn.divisor_norm_sublevel_finite f 1).eventually_cofinite_notMem]
      with ρ hρ
    have hρnorm : 1 ≤ ‖(ρ : ℂ)‖ := le_of_lt (lt_of_not_ge hρ)
    simp only [r, w, d, max_eq_right hρnorm]
  · have hA : A < 0 := hAp.trans_le (le_of_not_gt hp)
    have hc := h.isConst hf hA
    have heq : f = fun _ : ℂ ↦ f 0 := funext fun z ↦ hc z 0
    rw [heq]
    simp [MeromorphicOn.divisor_const]

end TauCeti
