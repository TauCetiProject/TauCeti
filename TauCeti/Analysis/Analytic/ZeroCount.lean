/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Analysis.Meromorphic.Divisor
public import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.RCLike.Lemmas
import TauCeti.Analysis.Analytic.IsolatedZeros
import TauCeti.Analysis.Meromorphic.Divisor
import TauCeti.Analysis.Meromorphic.Order

/-!
# The zero count of an analytic function on a disc

The zero count of `f` on an open disc is the finitely supported sum
`∑ᶠ z ∈ ball c R, analyticOrderNatAt f z`. It is what the argument principle produces — through
`TauCeti.Contour.argumentPrinciple_divisor` and the bridge
`MeromorphicOn.divisor_eq_analyticOrderNatAt` — and what Rouché's theorem
(`TauCeti.rouche_symm`) and Hurwitz's theorem (`TauCeti.hurwitz`) compare. This file collects the
four facts about that sum which those consumers need, none of which mentions either theorem.
They are stated for a function `f : 𝕜 → E` into a normed space; the detection criterion needs the
closed disc to be preconnected, so it is stated over `RCLike 𝕜`.

The same zeros, listed with multiplicity rather than summed, form the finite multiset
`AnalyticOnNhd.zeroMultiset`, read off from Mathlib's `MeromorphicOn.divisor`. When `f` has no
zero on the bounding sphere, the multiplicity of each point of the closed disc is its order of
vanishing. Symmetric functions of this multiset are what the weighted argument principle
(`TauCeti.Contour.sum_map_zeroMultiset_eq_circleIntegral`) computes.

Care is needed about points of *infinite* order, where `f` vanishes identically nearby:
`analyticOrderNatAt` reads `0` there, exactly as it does where `f` does not vanish at all, so the
count does not see such a point. That is why detecting a zero from a vanishing count
(`AnalyticOnNhd.finsum_analyticOrderNatAt_ball_eq_zero_iff`) needs a hypothesis ruling infinite
order out. One point of the closed disc at which `f` is nonzero is enough: the disc is convex, hence
preconnected, so `AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected` propagates the finite
order there to every point.

## Main results

* `MeromorphicOn.analyticOrderNatAt_le_finsum_ball` — the order of vanishing at a single point of
  the open disc is at most the total count.
* `TauCeti.finsum_mem_analyticOrderNatAt_eq_zero_of_forall_ne_zero` — a function without zeros on
  a set has count `0` there.
* `AnalyticOnNhd.exists_finset_finsum_analyticOrderNatAt_ball_eq_sum` — a function analytic on a
  closed disc and nonzero somewhere on it has finitely many zeros in the open disc, which carry
  the whole count.
* `AnalyticOnNhd.finsum_analyticOrderNatAt_ball_eq_zero_iff` — conversely, given a point of the
  closed disc where `f` does not vanish, a count of `0` means there is no zero in the open disc at
  all.
* `AnalyticOnNhd.zeroMultiset` — the zeros in the open disc, counted with multiplicity
  (`AnalyticOnNhd.natCast_count_zeroMultiset`).
* `AnalyticOnNhd.mem_zeroMultiset_iff`, `AnalyticOnNhd.analyticOrderAt_eq_count_zeroMultiset` —
  with no zero on the sphere, its members are the zeros in the open disc and its multiplicities are
  the orders of vanishing.
* `AnalyticOnNhd.zeroMultiset_eq_replicate` — a single zero of order `d` at the center gives `d`
  copies of the center.

## References

* [Mathlib PR #33505](https://github.com/leanprover-community/mathlib4/pull/33505), the preceding
  human-curated Riemann-mapping development and its local analytic prerequisites.
-/

public section

open Metric

section NontriviallyNormedField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {f : 𝕜 → E} {c : 𝕜} {R : ℝ}

/-- The order of vanishing at a single point of the open disc is at most the total zero count of a
function meromorphic on the closed disc. At a pole or a point of infinite order the left side reads
`0`, so the bound holds trivially there. -/
theorem MeromorphicOn.analyticOrderNatAt_le_finsum_ball [ProperSpace 𝕜]
    (hf : MeromorphicOn f (closedBall c R)) {z₀ : 𝕜} (hz₀ : z₀ ∈ ball c R) :
    analyticOrderNatAt f z₀ ≤ ∑ᶠ z ∈ ball c R, analyticOrderNatAt f z := by
  -- the count is supported in the support of `MeromorphicOn.divisor`, which is finite
  refine (single_le_finsum z₀ (hf.divisor_ball_support_finite.subset fun z hz => ?_)
    fun _ => Nat.zero_le _).trans_eq' (by simp [hz₀])
  classical
  rw [Function.mem_support, finsum_eq_if] at hz
  split_ifs at hz with hzb
  · have hA : AnalyticAt 𝕜 f z := by
      by_contra h
      exact hz (analyticOrderNatAt_of_not_analyticAt h)
    rw [Function.mem_support, (hf.mono_set ball_subset_closedBall).divisor_apply hzb,
      hA.meromorphicOrderAt_eq]
    cases h : analyticOrderAt f z <;> simp_all [analyticOrderNatAt]
  · exact absurd rfl hz

/-- A function without zeros on a set `s` has zero count `0` there. -/
theorem TauCeti.finsum_mem_analyticOrderNatAt_eq_zero_of_forall_ne_zero {s : Set 𝕜}
    (hne : ∀ z ∈ s, f z ≠ 0) : (∑ᶠ z ∈ s, analyticOrderNatAt f z) = 0 :=
  finsum_mem_of_eqOn_zero fun z hz => by
    simp [analyticOrderNatAt, analyticOrderAt_eq_zero.2 (.inr (hne z hz))]

end NontriviallyNormedField

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f : 𝕜 → E} {c : 𝕜} {R : ℝ}

/-- **The zero count detects zeros.** For `f` analytic on `closedBall c R` and nonvanishing at
*some* point of that closed disc, the count `∑ᶠ z ∈ ball c R, analyticOrderNatAt f z` vanishes
precisely when `f` has no zero in the open disc.

The nonvanishing hypothesis cannot be dropped: `analyticOrderNatAt` sends a point of infinite order
to `0`, so the identically zero function has count `0` while vanishing everywhere. -/
theorem AnalyticOnNhd.finsum_analyticOrderNatAt_ball_eq_zero_iff
    (hf : AnalyticOnNhd 𝕜 f (closedBall c R)) (hne : ∃ z ∈ closedBall c R, f z ≠ 0) :
    (∑ᶠ z ∈ ball c R, analyticOrderNatAt f z) = 0 ↔ ∀ z ∈ ball c R, f z ≠ 0 := by
  refine ⟨fun hsum z₀ hz₀ h0 => ?_, TauCeti.finsum_mem_analyticOrderNatAt_eq_zero_of_forall_ne_zero⟩
  obtain ⟨w, hw, hwne⟩ := hne
  have htop : analyticOrderAt f z₀ ≠ ⊤ :=
    hf.analyticOrderAt_ne_top_of_isPreconnected (convex_closedBall c R).isPreconnected hw
      (ball_subset_closedBall hz₀) (by simp [(hf w hw).analyticOrderAt_eq_zero.2 hwne])
  have hle := hf.meromorphicOn.analyticOrderNatAt_le_finsum_ball hz₀
  rw [hsum] at hle
  simp [analyticOrderNatAt, ENat.toNat_eq_zero, htop,
    (hf z₀ (ball_subset_closedBall hz₀)).analyticOrderAt_eq_zero, h0] at hle

/-- If `g` is analytic on a closed disc and does not vanish at some point of it, then it has
finitely many zeros in the open disc, and the sum over the open disc of the orders of vanishing of
`g` is the sum of those orders over the finite set `S` of zeros. -/
theorem AnalyticOnNhd.exists_finset_finsum_analyticOrderNatAt_ball_eq_sum {g : 𝕜 → E}
    {c a : 𝕜} {r : ℝ}
    (hg : AnalyticOnNhd 𝕜 g (closedBall c r)) (ha : a ∈ closedBall c r) (hga : g a ≠ 0) :
    ∃ S : Finset 𝕜, (∀ z, z ∈ S ↔ z ∈ ball c r ∧ g z = 0) ∧
      (∑ᶠ z ∈ ball c r, analyticOrderNatAt g z) = ∑ z ∈ S, analyticOrderNatAt g z := by
  classical
  have hfin : {z | z ∈ ball c r ∧ g z = 0}.Finite :=
    (hg.finite_setOf_mem_and_eq_zero_of_isCompact (convex_closedBall _ _).isPreconnected
      ha hga (isCompact_closedBall _ _) subset_rfl).subset
      fun z hz => ⟨ball_subset_closedBall hz.1, hz.2⟩
  refine ⟨hfin.toFinset, fun z => by simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq],
    finsum_mem_eq_sum_of_subset _ (fun z hz => ?_) fun z hz => ?_⟩
  · exact (hfin.mem_toFinset (a := z)).2
      ⟨hz.1, apply_eq_zero_of_analyticOrderNatAt_ne_zero (Function.mem_support.1 hz.2)⟩
  · exact (Finset.mem_coe.1 hz |> hfin.mem_toFinset.1).1

/-! ### The multiset of zeros in a disc -/

namespace AnalyticOnNhd

variable {g : 𝕜 → E}

/-- The multiset of zeros in `ball c R` of a function `g` analytic on `closedBall c R`, counted with
multiplicity via `MeromorphicOn.divisor` (see `AnalyticOnNhd.natCast_count_zeroMultiset`). -/
noncomputable def zeroMultiset (hg : AnalyticOnNhd 𝕜 g (closedBall c R)) : Multiset 𝕜 :=
  (Finsupp.ofSupportFinite (fun z ↦ (MeromorphicOn.divisor g (ball c R) z).toNat) <|
    (MeromorphicOn.divisor_ball_support_finite hg.meromorphicOn).subset fun z hz ↦
      Function.mem_support.2 fun h0 ↦ Function.mem_support.1 hz (by simp [h0])).toMultiset

/-- The multiplicity of a point in `zeroMultiset` is the value of Mathlib's
`MeromorphicOn.divisor` of `g` on `ball c R` there. -/
@[simp]
theorem natCast_count_zeroMultiset [DecidableEq 𝕜] (hg : AnalyticOnNhd 𝕜 g (closedBall c R))
    (z : 𝕜) :
    (Multiset.count z hg.zeroMultiset : ℤ) = MeromorphicOn.divisor g (ball c R) z := by
  rw [zeroMultiset, Finsupp.count_toMultiset, Finsupp.ofSupportFinite_coe]
  exact Int.toNat_of_nonneg
    (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (hg.mono ball_subset_closedBall) z)

/-- The zeros counted by `zeroMultiset` lie in the open disc. -/
theorem mem_ball_of_mem_zeroMultiset (hg : AnalyticOnNhd 𝕜 g (closedBall c R)) {a : 𝕜}
    (ha : a ∈ hg.zeroMultiset) : a ∈ ball c R := by
  classical
  refine (MeromorphicOn.divisor g (ball c R)).supportWithinDomain
    (Function.mem_support.2 fun h0 ↦ ?_)
  have h := hg.natCast_count_zeroMultiset a
  rw [h0, Nat.cast_eq_zero, Multiset.count_eq_zero] at h
  exact h ha

/-- If `g` has no zero on `sphere c R`, the multiplicity of a point of the closed disc in
`zeroMultiset` is the meromorphic order of `g` there. -/
theorem meromorphicOrderAt_eq_count_zeroMultiset [DecidableEq 𝕜]
    (hg : AnalyticOnNhd 𝕜 g (closedBall c R)) (hsphere : ∀ ζ ∈ sphere c R, g ζ ≠ 0)
    {z : 𝕜} (hz : z ∈ closedBall c R) :
    meromorphicOrderAt g z = ((Multiset.count z hg.zeroMultiset : ℕ) : WithTop ℤ) := by
  rcases (ball_union_sphere (x := c) (ε := R) ▸ hz) with hzb | hzs
  · rw [← WithTop.coe_untop₀_of_ne_top
        (hg.meromorphicOrderAt_ne_top_of_forall_mem_sphere_ne_zero hsphere hz),
      ← (hg.mono ball_subset_closedBall).meromorphicOn.divisor_apply hzb,
      ← hg.natCast_count_zeroMultiset z]
    norm_cast
  · have hc0 : Multiset.count z hg.zeroMultiset = 0 := Multiset.count_eq_zero.2 fun hmem ↦
      (mem_ball.1 (hg.mem_ball_of_mem_zeroMultiset hmem)).ne (mem_sphere.1 hzs)
    rw [(hg z hz).meromorphicOrderAt_eq, (hg z hz).analyticOrderAt_eq_zero.2 (hsphere z hzs), hc0]
    simp

/-- If `g` has no zero on `sphere c R`, the multiplicity of a point of the closed disc in
`zeroMultiset` is the order of vanishing of `g` there. -/
theorem analyticOrderAt_eq_count_zeroMultiset [DecidableEq 𝕜]
    (hg : AnalyticOnNhd 𝕜 g (closedBall c R)) (hsphere : ∀ ζ ∈ sphere c R, g ζ ≠ 0)
    {z : 𝕜} (hz : z ∈ closedBall c R) :
    analyticOrderAt g z = Multiset.count z hg.zeroMultiset := by
  have h := hg.meromorphicOrderAt_eq_count_zeroMultiset hsphere hz
  rw [(hg z hz).meromorphicOrderAt_eq] at h
  exact ENat.map_natCast_injective (by simpa using h)

/-- If `g` has no zero on `sphere c R`, the members of `zeroMultiset` are exactly the zeros of `g`
in the open disc. -/
@[simp]
theorem mem_zeroMultiset_iff (hg : AnalyticOnNhd 𝕜 g (closedBall c R))
    (hsphere : ∀ ζ ∈ sphere c R, g ζ ≠ 0) {a : 𝕜} :
    a ∈ hg.zeroMultiset ↔ a ∈ ball c R ∧ g a = 0 := by
  classical
  refine ⟨fun ha ↦ ⟨hg.mem_ball_of_mem_zeroMultiset ha, ?_⟩, fun ⟨ha, h0⟩ ↦ ?_⟩
  · have hac := ball_subset_closedBall (hg.mem_ball_of_mem_zeroMultiset ha)
    have h := hg.analyticOrderAt_eq_count_zeroMultiset hsphere hac
    by_contra hne
    rw [(hg a hac).analyticOrderAt_eq_zero.2 hne] at h
    exact Multiset.count_ne_zero.2 ha (by exact_mod_cast h.symm)
  · have h := hg.analyticOrderAt_eq_count_zeroMultiset hsphere (ball_subset_closedBall ha)
    refine Multiset.count_ne_zero.1 fun hc ↦ ?_
    rw [hc, Nat.cast_zero, (hg a (ball_subset_closedBall ha)).analyticOrderAt_eq_zero] at h
    exact h h0

/-- If `c` is the only zero of `g` on `closedBall c R` and `g` vanishes there to order `d`, then
`zeroMultiset` is `d` copies of `c`. -/
theorem zeroMultiset_eq_replicate (hg : AnalyticOnNhd 𝕜 g (closedBall c R)) (hR : 0 < R)
    {d : ℕ} (hd : analyticOrderAt g c = d) (honly : ∀ z ∈ closedBall c R, z ≠ c → g z ≠ 0) :
    hg.zeroMultiset = Multiset.replicate d c := by
  classical
  have hgb : AnalyticOnNhd 𝕜 g (ball c R) := hg.mono ball_subset_closedBall
  ext z
  rw [Multiset.count_replicate]
  have hcount := hg.natCast_count_zeroMultiset z
  split_ifs with hcz
  · subst hcz
    rw [MeromorphicOn.divisor_eq_analyticOrderNatAt hgb.meromorphicOn
      (hg c (mem_closedBall_self hR.le)) (mem_ball_self hR), analyticOrderNatAt, hd,
      ENat.toNat_natCast] at hcount
    exact_mod_cast hcount
  · by_cases hzb : z ∈ ball c R
    · rw [MeromorphicOn.divisor_eq_analyticOrderNatAt hgb.meromorphicOn
        (hg z (ball_subset_closedBall hzb)) hzb, analyticOrderNatAt,
        (hg z (ball_subset_closedBall hzb)).analyticOrderAt_eq_zero.2
          (honly z (ball_subset_closedBall hzb) (Ne.symm hcz)),
        ENat.toNat_zero, Nat.cast_zero] at hcount
      exact_mod_cast hcount
    · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hzb] at hcount
      exact_mod_cast hcount

end AnalyticOnNhd

end RCLike
