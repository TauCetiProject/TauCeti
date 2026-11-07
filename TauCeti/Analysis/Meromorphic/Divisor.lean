/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Divisor
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Divisors and orders of meromorphic functions

Divisor values record finite meromorphic orders, while local finiteness controls sums over
their support.

At a point `z ∈ U`, Mathlib's `MeromorphicOn.divisor f U` evaluates to
`(meromorphicOrderAt f z).untop₀`, while zero counts of analytic functions are stated in terms of
`analyticOrderNatAt f z`. This file records the bridge between the two vocabularies at a point
where `f` is analytic.

## Main results

* `MeromorphicOn.divisor_eq_analyticOrderNatAt` — at a point where `f` is analytic, the divisor
  reads `analyticOrderNatAt f z`.
-/

public section

/-- The divisor of a whole-space function has finitely many support points in every norm
sublevel set over a proper normed field. No meromorphy hypothesis on the representative is
needed because its divisor is zero when it is not meromorphic. -/
theorem MeromorphicOn.divisor_norm_sublevel_finite
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (f : 𝕜 → E) (R : ℝ) :
    {ρ : (divisor f Set.univ).support | ‖(ρ : 𝕜)‖ ≤ R}.Finite := by
  let d := divisor f Set.univ
  have hd := LocallyFiniteSupport.finite_inter_support_of_isCompact
    (Function.locallyFinsupp.locallyFiniteSupport d) (isCompact_closedBall 0 R)
  apply (Set.finite_image_iff (f := fun ρ : d.support ↦ (ρ : 𝕜))
    Subtype.coe_injective.injOn).mp
  apply hd.subset
  rintro z ⟨ρ, hρ, rfl⟩
  have hρ' : ‖(ρ : 𝕜)‖ ≤ R := hρ
  exact ⟨by simpa only [Metric.mem_closedBall, dist_zero_right] using hρ', ρ.property⟩

/-- The sum of the divisor of an analytic function is nonnegative. This also applies to the
default zero value of a finite sum with infinite support. -/
theorem AnalyticOnNhd.sum_divisor_nonneg
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {f : 𝕜 → E} {U : Set 𝕜} (hf : AnalyticOnNhd 𝕜 f U) :
    0 ≤ (∑ᶠ z, MeromorphicOn.divisor f U z : ℤ) :=
  finsum_nonneg (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf)

/-- Summing divisor multiplicities over a bounded subset of whole-space support is bounded
by the divisor count on the containing closed ball. -/
theorem AnalyticOnNhd.tsum_divisor_subtype_le_sum_closedBall
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f : 𝕜 → E} {R : ℝ}
    (hf : AnalyticOnNhd 𝕜 f Set.univ) (s : Set (MeromorphicOn.divisor f Set.univ).support)
    (hs : ∀ ρ ∈ s, ‖(ρ : 𝕜)‖ ≤ R) :
    (∑' ρ : s, (MeromorphicOn.divisor f Set.univ ρ.val : ℝ)) ≤
      ((∑ᶠ z, MeromorphicOn.divisor f (Metric.closedBall 0 R) z : ℤ) : ℝ) := by
  classical
  have hsfinite : s.Finite := (MeromorphicOn.divisor_norm_sublevel_finite f R).subset
    (fun ρ hρ ↦ by simpa only [Set.mem_ofPred_eq] using hs ρ hρ)
  let : Fintype s := hsfinite.fintype
  let D := MeromorphicOn.divisor f (Metric.closedBall 0 R)
  have hD : Function.HasFiniteSupport D := D.finiteSupport (isCompact_closedBall 0 R)
  have hcast : Function.HasFiniteSupport (fun z ↦ (D z : ℝ)) :=
    hD.subset (fun z hz h0 ↦ hz (by simp [h0]))
  have hball : AnalyticOnNhd 𝕜 f (Metric.closedBall 0 R) := fun z _ ↦ hf z (Set.mem_univ z)
  let e : s → 𝕜 := fun ρ ↦ (ρ.val : 𝕜)
  have hde (ρ : s) : D (e ρ) = MeromorphicOn.divisor f Set.univ ρ.val := by
    have hρ : ‖e ρ‖ ≤ R := hs ρ.val ρ.property
    rw [MeromorphicOn.divisor_apply hball.meromorphicOn
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using hρ),
      MeromorphicOn.divisor_apply hf.meromorphicOn (Set.mem_univ _)]
  calc
    _ ≤ ∑' z, (D z : ℝ) := by
      apply Summable.tsum_le_tsum_of_inj e
        (fun ρ σ hρσ ↦ Subtype.ext (Subtype.ext hρσ))
        (fun z _ ↦ by exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hball z)
        (fun ρ ↦ by rw [hde ρ]) Summable.of_finite (summable_of_hasFiniteSupport hcast)
    _ = ∑ᶠ z, (D z : ℝ) := tsum_eq_finsum hcast
    _ = ((∑ᶠ z, D z : ℤ) : ℝ) := (map_finsum (Int.castRingHom ℝ) hD).symm

/-- At a point `z ∈ U` where a function meromorphic on `U` is analytic, its divisor on `U`
equals its order of vanishing `analyticOrderNatAt f z`. This includes a point near which `f`
vanishes identically: there the analytic order is infinite and both sides read `0`.

The divisor is defined through `meromorphicOrderAt`, while zero counts of analytic functions are
stated through `analyticOrderNatAt`; this lemma translates between the two, so that a statement
about divisor values of a function analytic on `U` becomes one about its orders of vanishing. It
says nothing at a pole, where `f` is not analytic. -/
theorem MeromorphicOn.divisor_eq_analyticOrderNatAt {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f : 𝕜 → E} {U : Set 𝕜} {z : 𝕜}
    (hm : MeromorphicOn f U) (hf : AnalyticAt 𝕜 f z) (hz : z ∈ U) :
    divisor f U z = (analyticOrderNatAt f z : ℤ) := by
  rw [hm.divisor_apply hz, hf.meromorphicOrderAt_eq, analyticOrderNatAt]
  cases analyticOrderAt f z <;> simp
