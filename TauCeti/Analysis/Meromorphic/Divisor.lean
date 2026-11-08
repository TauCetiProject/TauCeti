/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Divisor

/-!
# Divisors and orders of meromorphic functions

Divisor values record finite meromorphic orders, while local finiteness controls sums over
their support.

At a point `z ∈ U`, Mathlib's `MeromorphicOn.divisor f U` evaluates to
`(meromorphicOrderAt f z).untop₀`, while zero counts of analytic functions are stated in terms of
`analyticOrderNatAt f z`. This file records the bridge between the two vocabularies at a point
where `f` is analytic. It also records finite divisor support on subsets of compact sets
and on bounded regions whose closures lie in the meromorphic domain.

## Main results

* `MeromorphicOn.divisor_eq_analyticOrderNatAt` — at a point where `f` is analytic, the divisor
  reads `analyticOrderNatAt f z`.
* `MeromorphicOn.meromorphicOrderAt_eq_of_divisor_eq` — equal divisors determine equal finite
  meromorphic orders.
* `MeromorphicOn.divisor_finite_inter_support_of_isCompact` — finite divisor support on a
  subset of a compact set in the meromorphic domain.
* `MeromorphicOn.divisor_finite_inter_support` — finite divisor support on a bounded region
  whose closure lies in the meromorphic domain.
-/

public section

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

open Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f : 𝕜 → E} {U R K : Set 𝕜}

/-- A meromorphic divisor has finite support on any subset of a compact set in its domain. -/
theorem MeromorphicOn.divisor_finite_inter_support_of_isCompact
    (hf : MeromorphicOn f U) (hK : IsCompact K) (hKU : K ⊆ U) (hRK : R ⊆ K) :
    (R ∩ Function.support (MeromorphicOn.divisor f U)).Finite := by
  apply ((MeromorphicOn.divisor f K).finiteSupport hK).subset
  intro z hz
  simpa only [Function.mem_support, hf.divisor_apply (hKU (hRK hz.1)),
    (hf.mono_set hKU).divisor_apply (hRK hz.1)] using hz.2

/-- A bounded region has finite divisor support when its closure is in the meromorphic domain. -/
theorem MeromorphicOn.divisor_finite_inter_support [ProperSpace 𝕜]
    (hf : MeromorphicOn f U) (hR : Bornology.IsBounded R) (hRU : closure R ⊆ U) :
    (R ∩ Function.support (MeromorphicOn.divisor f U)).Finite :=
  hf.divisor_finite_inter_support_of_isCompact hR.isCompact_closure hRU subset_closure
