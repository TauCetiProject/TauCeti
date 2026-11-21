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
* `MeromorphicOn.inter_support_analyticOrderNatAt_subset_support_divisor`,
  `AnalyticOnNhd.support_divisor_eq`, and `AnalyticOnNhd.support_divisor_univ_eq` — support
  relations between `analyticOrderNatAt f` and `MeromorphicOn.divisor f`.
* `AnalyticAt.divisor_apply_eq_zero` — the divisor vanishes where `f` is analytic and nonzero.
* `AnalyticAt.notMem_divisor_support_of_ne_zero`, `AnalyticAt.apply_eq_zero_of_divisor_ne_zero` —
  such a point is off the divisor support, so any support point where `f` is analytic is a zero.
* `AnalyticOnNhd.divisor_eq_of_eq_sub_pow_smul_of_ne` and
  `AnalyticOnNhd.divisor_eq_update_of_eq_sub_pow_smul` — factoring out `(z - z₀) ^ m` leaves the
  divisor unchanged away from `z₀` and clears it at `z₀` when the quotient is nonzero there.
* `AnalyticOnNhd.divisor_neg_eq_of_even` — the whole-space divisor of an even analytic function is
  even.
* `MeromorphicOn.divisor_norm_sublevel_finite` — finitely many support points occur in each
  norm sublevel over a proper normed field.
* `AnalyticOnNhd.tsum_divisor_subtype_le_sum_closedBall` — a support-subset multiplicity sum
  is bounded by the containing closed-ball count.
* `MeromorphicOn.meromorphicOrderAt_eq_of_divisor_eq` — equal divisors determine equal finite
  meromorphic orders.
* `MeromorphicOn.zero_lt_divisor_iff_of_analyticAt` — at a point of analyticity and finite order,
  the divisor is positive exactly at a zero.
* `AnalyticOnNhd.divisor_apply_eq_zero_iff`: on a preconnected set where `f` is analytic and
  somewhere nonzero, the divisor vanishes exactly off the zeros.
* `MeromorphicOn.divisor_finite_inter_support_of_isCompact` — finite divisor support on a
  subset of a compact set in the meromorphic domain.
* `MeromorphicOn.divisor_finite_inter_support` — finite divisor support on a bounded region
  whose closure lies in the meromorphic domain.
* `MeromorphicOn.divisor_congr_nhdsNE` and `Filter.EventuallyEq.divisor_eq` — divisor congruence
  from punctured-neighbourhood or neighbourhood-of-set germ equality.
* `MeromorphicOn.negPart_divisor_apply_eq_zero_iff` — at `z ∈ U`, `(divisor f U)⁻ z = 0` iff
  `0 ≤ meromorphicOrderAt f z`.
* `MeromorphicOn.divisor_neg`, `AnalyticOnNhd.negPart_divisor_add_right`, and
  `AnalyticOnNhd.negPart_divisor_add_left` — invariance of divisors under negation and of pole
  divisors under adding an analytic function (without meromorphicity hypotheses on the other
  summand).
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

/-- If the divisor of `f` on `U` is nonzero at a point where `f` is analytic, then `f` vanishes
there. No meromorphy hypothesis on `U` is needed. -/
theorem AnalyticAt.apply_eq_zero_of_divisor_ne_zero {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f : 𝕜 → E} {U : Set 𝕜} {z : 𝕜}
    (hf : AnalyticAt 𝕜 f z) (hz : MeromorphicOn.divisor f U z ≠ 0) : f z = 0 := by
  by_contra hfz
  exact hz (hf.divisor_apply_eq_zero hfz)

/-- On the meromorphic domain `U`, every point where `analyticOrderNatAt f` is nonzero lies in the
support of `MeromorphicOn.divisor f U`. At non-analytic points `analyticOrderNatAt f` is zero by
definition. -/
theorem MeromorphicOn.inter_support_analyticOrderNatAt_subset_support_divisor {𝕜 E : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f : 𝕜 → E} {U : Set 𝕜}
    (hm : MeromorphicOn f U) :
    U ∩ Function.support (analyticOrderNatAt f) ⊆ (divisor f U).support := by
  rintro z ⟨hzU, hz⟩
  by_cases hf : AnalyticAt 𝕜 f z
  · rw [Function.mem_support, hm.divisor_eq_analyticOrderNatAt hf hzU, Int.natCast_ne_zero]
    exact hz
  · exact False.elim (hz (analyticOrderNatAt_of_not_analyticAt hf))

/-- For a function analytic on a neighbourhood of `U`, the support of its divisor on `U` equals
`U ∩ Function.support (analyticOrderNatAt f)`. -/
theorem AnalyticOnNhd.support_divisor_eq {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f : 𝕜 → E} {U : Set 𝕜} (hf : AnalyticOnNhd 𝕜 f U) :
    (MeromorphicOn.divisor f U).support = U ∩ Function.support (analyticOrderNatAt f) := by
  refine Set.Subset.antisymm ?_
    hf.meromorphicOn.inter_support_analyticOrderNatAt_subset_support_divisor
  intro z hz
  have hzU : z ∈ U := by
    by_contra hnot
    exact hz (Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hnot)
  refine ⟨hzU, ?_⟩
  rwa [Function.mem_support, hf.meromorphicOn.divisor_eq_analyticOrderNatAt (hf z hzU) hzU,
    Int.natCast_ne_zero] at hz

/-- For a function analytic on the whole space, its divisor support equals the support of
`analyticOrderNatAt f`. -/
theorem AnalyticOnNhd.support_divisor_univ_eq {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f : 𝕜 → E} (hf : AnalyticOnNhd 𝕜 f Set.univ) :
    (MeromorphicOn.divisor f Set.univ).support = Function.support (analyticOrderNatAt f) := by
  rw [hf.support_divisor_eq, Set.univ_inter]

/-- If `f z = (z - z₀) ^ m • g z` with `g` analytic on a neighbourhood of `U`, then the divisors of
`g` and `f` on `U` agree at every point `w ≠ z₀`. -/
theorem AnalyticOnNhd.divisor_eq_of_eq_sub_pow_smul_of_ne
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {f g : 𝕜 → E} {U : Set 𝕜} (hg : AnalyticOnNhd 𝕜 g U) {z₀ w : 𝕜} {m : ℕ}
    (hfg : ∀ z, f z = (z - z₀) ^ m • g z) (hw : w ≠ z₀) :
    MeromorphicOn.divisor g U w = MeromorphicOn.divisor f U w := by
  by_cases hwU : w ∈ U
  · have hsmul : f = (fun z : 𝕜 ↦ (z - z₀) ^ m) • g := funext hfg
    have hf : AnalyticOnNhd 𝕜 f U := fun z hz ↦ by
      rw [hsmul]
      exact ((analyticAt_id.sub analyticAt_const).pow m).smul (hg z hz)
    rw [MeromorphicOn.divisor_eq_analyticOrderNatAt hg.meromorphicOn (hg w hwU) hwU,
      MeromorphicOn.divisor_eq_analyticOrderNatAt hf.meromorphicOn (hf w hwU) hwU,
      analyticOrderNatAt, analyticOrderNatAt]
    have hpow_an : AnalyticAt 𝕜 (fun z : 𝕜 ↦ (z - z₀) ^ m) w := by fun_prop
    have hpow_ne : (w - z₀) ^ m ≠ 0 := pow_ne_zero m (sub_ne_zero.mpr hw)
    rw [hsmul, analyticOrderAt_smul hpow_an (hg w hwU),
      hpow_an.analyticOrderAt_eq_zero.mpr hpow_ne, zero_add]
  · simp [hwU]

/-- If `f z = (z - z₀) ^ m • g z` with `g` analytic on a neighbourhood of `U` and `g z₀ ≠ 0`, then
the divisor of `g` on `U` vanishes at `z₀` and agrees with that of `f` elsewhere. -/
theorem AnalyticOnNhd.divisor_eq_update_of_eq_sub_pow_smul
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [DecidableEq 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {f g : 𝕜 → E} {U : Set 𝕜} (hg : AnalyticOnNhd 𝕜 g U) {z₀ : 𝕜} (hg0 : g z₀ ≠ 0) {m : ℕ}
    (hfg : ∀ z, f z = (z - z₀) ^ m • g z) (w : 𝕜) :
    MeromorphicOn.divisor g U w = if w = z₀ then 0 else MeromorphicOn.divisor f U w := by
  split_ifs with hw
  · subst hw
    by_cases hwU : w ∈ U
    · exact (hg w hwU).divisor_apply_eq_zero hg0
    · simp [hwU]
  · exact hg.divisor_eq_of_eq_sub_pow_smul_of_ne hfg hw

/-- The whole-space divisor of an even analytic function is invariant under negation. -/
theorem AnalyticOnNhd.divisor_neg_eq_of_even
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {g : 𝕜 → E} (hg : AnalyticOnNhd 𝕜 g Set.univ) (heven : g.Even) (ρ : 𝕜) :
    MeromorphicOn.divisor g Set.univ (-ρ) = MeromorphicOn.divisor g Set.univ ρ := by
  rw [MeromorphicOn.divisor_eq_analyticOrderNatAt hg.meromorphicOn (hg (-ρ) (Set.mem_univ _))
      (Set.mem_univ _),
    MeromorphicOn.divisor_eq_analyticOrderNatAt hg.meromorphicOn (hg ρ (Set.mem_univ _))
      (Set.mem_univ _), analyticOrderNatAt, analyticOrderNatAt]
  have hcomp : g ∘ (-id : 𝕜 → 𝕜) = g := funext heven
  have hsub : analyticOrderAt (fun z : 𝕜 ↦ -z - -ρ) ρ = (1 : ℕ) :=
    (AnalyticAt.analyticOrderAt_eq_natCast (by fun_prop)).mpr
      ⟨fun _ ↦ (-1 : 𝕜), analyticAt_const, neg_ne_zero.mpr one_ne_zero,
        Filter.Eventually.of_forall fun z ↦ by simp only [pow_one, smul_eq_mul]; ring⟩
  have hord := (hg (-ρ) (Set.mem_univ _)).analyticOrderAt_comp (g := (-id : 𝕜 → 𝕜))
    (z₀ := ρ) analyticAt_id.neg
  dsimp only [Pi.neg_apply, id_eq] at hord
  rw [hcomp, hsub, Nat.cast_one, mul_one] at hord
  rw [hord]

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

/-- On a preconnected set where `f` is analytic and somewhere nonzero, the divisor of `f`
vanishes exactly where `f` does not. The converse direction
`AnalyticAt.divisor_apply_eq_zero` needs no preconnectedness; the forward direction uses it to
rule out a point near which `f` vanishes identically. -/
theorem AnalyticOnNhd.divisor_apply_eq_zero_iff {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f : 𝕜 → E} {U : Set 𝕜} {w z : 𝕜}
    (hf : AnalyticOnNhd 𝕜 f U) (hU : IsPreconnected U) (hw : w ∈ U) (hfw : f w ≠ 0)
    (hz : z ∈ U) : MeromorphicOn.divisor f U z = 0 ↔ f z ≠ 0 := by
  refine ⟨fun hd hfz ↦ ?_, (hf z hz).divisor_apply_eq_zero⟩
  have htop : analyticOrderAt f z ≠ ⊤ := hf.analyticOrderAt_ne_top_of_isPreconnected hU hw hz
    (by simp [(hf w hw).analyticOrderAt_eq_zero.mpr hfw])
  have hpos := (hf.meromorphicOn.zero_lt_divisor_iff_of_analyticAt (hf z hz) hz
    (by simp [(hf z hz).meromorphicOrderAt_eq, htop])).mpr hfz
  omega

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

open scoped Topology in
/-- Functions with identical punctured germs at every point of `U` have equal meromorphic divisors
on `U`. No meromorphy hypothesis is required: if one is not meromorphic on `U`, neither is the
other, and both divisors are zero. -/
theorem MeromorphicOn.divisor_congr_nhdsNE {g : 𝕜 → E}
    (hfg : ∀ z ∈ U, f =ᶠ[𝓝[≠] z] g) :
    MeromorphicOn.divisor f U = MeromorphicOn.divisor g U := by
  have hmero : MeromorphicOn f U ↔ MeromorphicOn g U :=
    forall₂_congr fun z hz ↦ MeromorphicAt.meromorphicAt_congr (hfg z hz)
  ext z
  by_cases hz : z ∈ U
  · by_cases hf : MeromorphicOn f U
    · rw [hf.divisor_apply hz, (hmero.1 hf).divisor_apply hz,
        meromorphicOrderAt_congr (hfg z hz)]
    · rw [MeromorphicOn.divisor_eq_zero_of_not_meromorphicOn hf,
        MeromorphicOn.divisor_eq_zero_of_not_meromorphicOn (hmero.not.1 hf)]
  · simp [hz]

open scoped Topology in
/-- Functions equal on a neighbourhood of `U` have identical meromorphic divisors on `U`. -/
theorem Filter.EventuallyEq.divisor_eq {g : 𝕜 → E} (hfg : f =ᶠ[𝓝ˢ U] g) :
    MeromorphicOn.divisor f U = MeromorphicOn.divisor g U :=
  MeromorphicOn.divisor_congr_nhdsNE fun _ hz ↦
    hfg.filter_mono (nhdsWithin_le_nhds.trans (nhds_le_nhdsSet hz))

/-- At a point `z ∈ U` of a meromorphic domain, the pole divisor `(MeromorphicOn.divisor f U)⁻`
vanishes iff `f` has nonnegative meromorphic order at `z` (including infinite order `⊤`). -/
theorem MeromorphicOn.negPart_divisor_apply_eq_zero_iff {z : 𝕜}
    (hf : MeromorphicOn f U) (hz : z ∈ U) :
    (MeromorphicOn.divisor f U)⁻ z = 0 ↔ 0 ≤ meromorphicOrderAt f z := by
  simp [Function.locallyFinsuppWithin.negPart_apply, hf.divisor_apply hz]

/-- Negating a function leaves its meromorphic divisor unchanged. -/
@[to_fun (attr := simp) MeromorphicOn.divisor_fun_neg]
theorem MeromorphicOn.divisor_neg (f : 𝕜 → E) (U : Set 𝕜) :
    MeromorphicOn.divisor (-f) U = MeromorphicOn.divisor f U := by
  rw [← neg_one_smul 𝕜 f, MeromorphicOn.divisor_const_smul (neg_ne_zero.2 one_ne_zero)]

/-- Adding a function analytic on `U` on the right leaves the pole divisor `(divisor · U)⁻`
unchanged, without requiring `f` to be meromorphic on `U` (if `f` is not meromorphic on `U`,
neither is `f + g`, so both divisors vanish by totalization). -/
@[to_fun AnalyticOnNhd.negPart_divisor_fun_add_right]
theorem AnalyticOnNhd.negPart_divisor_add_right {g : 𝕜 → E}
    (hg : AnalyticOnNhd 𝕜 g U) (f : 𝕜 → E) :
    (MeromorphicOn.divisor (f + g) U)⁻ = (MeromorphicOn.divisor f U)⁻ := by
  by_cases hf : MeromorphicOn f U
  · exact hf.negPart_divisor_add_of_analyticNhdOn_right hg
  · have hfg : ¬MeromorphicOn (f + g) U := fun h ↦
      hf (by simpa only [add_neg_cancel_right] using h.add hg.neg.meromorphicOn)
    ext z
    simp [MeromorphicOn.divisor_eq_zero_of_not_meromorphicOn hf,
      MeromorphicOn.divisor_eq_zero_of_not_meromorphicOn hfg]

/-- Adding a function analytic on `U` on the left leaves the pole divisor `(divisor · U)⁻`
unchanged, without requiring `g` to be meromorphic on `U`. -/
@[to_fun AnalyticOnNhd.negPart_divisor_fun_add_left]
theorem AnalyticOnNhd.negPart_divisor_add_left
    (hf : AnalyticOnNhd 𝕜 f U) (g : 𝕜 → E) :
    (MeromorphicOn.divisor (f + g) U)⁻ = (MeromorphicOn.divisor g U)⁻ := by
  rw [add_comm]
  exact hf.negPart_divisor_add_right g
