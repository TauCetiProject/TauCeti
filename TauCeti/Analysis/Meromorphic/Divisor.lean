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
`analyticOrderNatAt f z`. The comparison identifies the local multiplicity; in particular the
divisor vanishes where `f` is analytic and nonzero, with no meromorphy hypothesis. Local
finiteness also gives finite divisor support on subsets of compact sets and bounded regions whose
closures lie in the meromorphic domain. For whole-space divisors, it makes norm sublevels
of support finite and bounds sums over their subsets by the corresponding closed-ball count.

## Main results

* `MeromorphicOn.divisor_eq_analyticOrderNatAt` — at a point where `f` is analytic, the divisor
  reads `analyticOrderNatAt f z`.
* `AnalyticAt.divisor_apply_eq_zero` — the divisor vanishes where `f` is analytic and nonzero.
* `AnalyticAt.notMem_divisor_support_of_ne_zero` — such a point is off the divisor support.
* `MeromorphicOn.divisor_norm_sublevel_finite` — finitely many support points occur in each
  norm sublevel over a proper normed field.
* `AnalyticOnNhd.tsum_divisor_subtype_le_sum_closedBall` — a support-subset multiplicity sum
  is bounded by the containing closed-ball count.
* `MeromorphicOn.meromorphicOrderAt_eq_of_divisor_eq` — equal divisors determine equal finite
  meromorphic orders.
* `MeromorphicOn.zero_lt_divisor_iff_of_analyticAt` — at a point of analyticity and finite order,
  the divisor is positive exactly at a zero.
* `AnalyticOnNhd.mem_divisor_support_iff`: for a function analytic on a neighbourhood of a
  preconnected set and somewhere nonzero there, the divisor support is the zero set.
* `MeromorphicOn.divisor_finite_inter_support_of_isCompact` — finite divisor support on a
  subset of a compact set in the meromorphic domain.
* `MeromorphicOn.divisor_finite_inter_support` — finite divisor support on a bounded region
  whose closure lies in the meromorphic domain.
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

/-- The divisor of a function vanishes at a point where the function is analytic and nonzero.
No meromorphy hypothesis is needed: if `f` is not meromorphic on `U`, or `z ∉ U`, the divisor is
`0` by definition. In particular an entire function with `f 0 ≠ 0` has `0` outside the support of
its divisor. -/
theorem AnalyticAt.divisor_apply_eq_zero {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f : 𝕜 → E} {U : Set 𝕜} {z : 𝕜}
    (hf : AnalyticAt 𝕜 f z) (hfz : f z ≠ 0) : MeromorphicOn.divisor f U z = 0 := by
  by_cases hm : MeromorphicOn f U
  · by_cases hz : z ∈ U
    · rw [hm.divisor_eq_analyticOrderNatAt hf hz, analyticOrderNatAt,
        hf.analyticOrderAt_eq_zero.mpr hfz, ENat.toNat_zero, Nat.cast_zero]
    · simp [hz]
  · exact MeromorphicOn.divisor_eq_zero_of_not_meromorphicOn hm

/-- A point where a function is analytic and nonzero is off the support of its divisor on any
set. -/
theorem AnalyticAt.notMem_divisor_support_of_ne_zero {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f : 𝕜 → E} {U : Set 𝕜} {z : 𝕜}
    (hf : AnalyticAt 𝕜 f z) (hfz : f z ≠ 0) : z ∉ (MeromorphicOn.divisor f U).support :=
  Function.notMem_support.mpr (hf.divisor_apply_eq_zero hfz)

/-- Equal divisors determine equal meromorphic orders at a point where both orders are finite.
The two functions may take values in different normed spaces over the same field. -/
theorem MeromorphicOn.meromorphicOrderAt_eq_of_divisor_eq
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {U : Set 𝕜} {f : 𝕜 → E} {g : 𝕜 → F}
    (hf : MeromorphicOn f U) (hg : MeromorphicOn g U)
    (hd : MeromorphicOn.divisor f U = MeromorphicOn.divisor g U) {z : 𝕜} (hz : z ∈ U)
    (hfz : meromorphicOrderAt f z ≠ ⊤) (hgz : meromorphicOrderAt g z ≠ ⊤) :
    meromorphicOrderAt f z = meromorphicOrderAt g z := by
  have heq := congrArg (fun d : Function.locallyFinsuppWithin U ℤ ↦ d z) hd
  rw [hf.divisor_apply hz, hg.divisor_apply hz] at heq
  have hcoe := congrArg (fun n : ℤ ↦ (n : WithTop ℤ)) heq
  simpa only [WithTop.coe_untop₀_of_ne_top hfz, WithTop.coe_untop₀_of_ne_top hgz] using hcoe

/-- At a point `z ∈ U` where a function meromorphic on `U` is analytic and does not vanish
identically nearby, its divisor on `U` is positive exactly when `f z = 0`. -/
theorem MeromorphicOn.zero_lt_divisor_iff_of_analyticAt {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f : 𝕜 → E} {U : Set 𝕜} {z : 𝕜}
    (hm : MeromorphicOn f U) (hf : AnalyticAt 𝕜 f z) (hz : z ∈ U)
    (htop : meromorphicOrderAt f z ≠ ⊤) :
    0 < divisor f U z ↔ f z = 0 := by
  rw [hf.meromorphicOrderAt_eq] at htop
  have h : analyticOrderAt f z ≠ ⊤ := fun h ↦ htop (by simp [h])
  rw [hm.divisor_eq_analyticOrderNatAt hf hz, Nat.cast_pos, Nat.pos_iff_ne_zero,
    ← hf.analyticOrderAt_ne_zero, ← Nat.cast_analyticOrderNatAt h, Nat.cast_ne_zero]

/-- For a function analytic on a neighbourhood of a preconnected set `U` and nonzero at some point
of `U`, a point of `U` lies in the support of the divisor on `U` exactly when it is a zero. -/
theorem AnalyticOnNhd.mem_divisor_support_iff {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f : 𝕜 → E} {U : Set 𝕜} {w z : 𝕜}
    (hf : AnalyticOnNhd 𝕜 f U) (hU : IsPreconnected U) (hw : w ∈ U) (hfw : f w ≠ 0)
    (hz : z ∈ U) : z ∈ (MeromorphicOn.divisor f U).support ↔ f z = 0 := by
  have hw' : analyticOrderAt f w ≠ ⊤ := by
    rw [(hf w hw).analyticOrderAt_eq_zero.mpr hfw]
    exact ENat.zero_ne_top
  have h := hf.analyticOrderAt_ne_top_of_isPreconnected hU hw hz hw'
  rw [Function.mem_support, hf.meromorphicOn.divisor_eq_analyticOrderNatAt (hf z hz) hz,
    Nat.cast_ne_zero, ← (hf z hz).analyticOrderAt_ne_zero, ← Nat.cast_analyticOrderNatAt h,
    Nat.cast_ne_zero]

open Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f : 𝕜 → E} {U R K : Set 𝕜}

/-- A meromorphic divisor has finite support on any subset of a compact set in its domain. For `f`
not meromorphic on `U` the divisor is zero. -/
theorem MeromorphicOn.divisor_finite_inter_support_of_isCompact
    (hK : IsCompact K) (hKU : K ⊆ U) (hRK : R ⊆ K) :
    (R ∩ Function.support (MeromorphicOn.divisor f U)).Finite := by
  by_cases hf : MeromorphicOn f U
  swap
  · have : Function.support (MeromorphicOn.divisor f U) = ∅ := by
      ext z
      simp [MeromorphicOn.divisor_eq_zero_of_not_meromorphicOn hf]
    simp [this]
  apply ((MeromorphicOn.divisor f K).finiteSupport hK).subset
  intro z hz
  simpa only [Function.mem_support, hf.divisor_apply (hKU (hRK hz.1)),
    (hf.mono_set hKU).divisor_apply (hRK hz.1)] using hz.2

/-- A bounded region has finite divisor support when its closure is in the meromorphic domain. -/
theorem MeromorphicOn.divisor_finite_inter_support [ProperSpace 𝕜]
    (hR : Bornology.IsBounded R) (hRU : closure R ⊆ U) :
    (R ∩ Function.support (MeromorphicOn.divisor f U)).Finite :=
  MeromorphicOn.divisor_finite_inter_support_of_isCompact hR.isCompact_closure hRU subset_closure
