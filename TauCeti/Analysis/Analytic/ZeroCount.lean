/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.RCLike.Lemmas
import TauCeti.Analysis.Analytic.IsolatedZeros
import TauCeti.Analysis.Meromorphic.Order

/-!
# The zero count of an analytic function on a disc

The zero count of `f` on an open disc is the finitely supported sum
`∑ᶠ z ∈ ball c R, analyticOrderNatAt f z`. It is what the argument principle produces — through
`TauCeti.Contour.argumentPrinciple_divisor` and the bridge
`MeromorphicOn.divisor_eq_analyticOrderNatAt` — and what Rouché's theorem
(`TauCeti.rouche_symm`) and Hurwitz's theorem (`TauCeti.hurwitz`) compare. This file collects the
facts about that sum which those consumers need, none of which mentions either theorem.
They are stated for a function `f : 𝕜 → E` into a normed space; the detection criterion and the
results that use nonvanishing on the bounding sphere need the closed disc to be preconnected, so
they are stated over `RCLike 𝕜`.

The same zeros, listed with multiplicity rather than summed, form the multiset
`AnalyticOnNhd.zeroMultiset f s`, the sum over `z ∈ s` of `analyticOrderNatAt f z` copies of `z`.
For `f` analytic on a closed disc and `s` the open disc it is finite, with the zero count as its
cardinality. When `f` has no zero on the bounding sphere, the multiplicity of each point of the
closed disc is its order of vanishing. Symmetric functions of this multiset are what the weighted
argument principle (`TauCeti.Contour.sum_map_zeroMultiset_eq_circleIntegral`) computes.

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
* `MeromorphicOn.finite_ball_inter_support_analyticOrderNatAt` — only finitely many points of the
  open disc have nonzero order.
* `TauCeti.finsum_mem_analyticOrderNatAt_eq_zero_of_forall_ne_zero` — a function without zeros on
  a set has count `0` there.
* `AnalyticOnNhd.exists_finset_finsum_analyticOrderNatAt_ball_eq_sum` — a function analytic on a
  closed disc and nonzero somewhere on it has finitely many zeros in the open disc, which carry
  the whole count.
* `AnalyticOnNhd.finsum_analyticOrderNatAt_ball_eq_zero_iff` — conversely, given a point of the
  closed disc where `f` does not vanish, a count of `0` means there is no zero in the open disc at
  all.
* `AnalyticOnNhd.zeroMultiset` — the zeros in a set, counted with multiplicity. On the open disc,
  `AnalyticOnNhd.count_zeroMultiset`, `AnalyticOnNhd.mem_zeroMultiset` and
  `AnalyticOnNhd.card_zeroMultiset` compute its multiplicities, members and cardinality.
* `AnalyticOnNhd.mem_zeroMultiset_iff`, `AnalyticOnNhd.analyticOrderAt_eq_count_zeroMultiset` —
  with no zero on the sphere, its members are the zeros in the open disc and its multiplicities are
  the orders of vanishing.
* `AnalyticOnNhd.zeroMultiset_eq_replicate` — a single zero of order `d` in the open disc gives `d`
  copies of that zero.

## References

* [Mathlib PR #33505](https://github.com/leanprover-community/mathlib4/pull/33505), the preceding
  human-curated Riemann-mapping development and its local analytic prerequisites.
-/

public section

open Metric

section NontriviallyNormedField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {f : 𝕜 → E} {c : 𝕜} {R : ℝ}

/-- A function meromorphic on a closed disc has only finitely many points of nonzero order of
vanishing in the open disc. -/
theorem MeromorphicOn.finite_ball_inter_support_analyticOrderNatAt [ProperSpace 𝕜]
    (hf : MeromorphicOn f (closedBall c R)) :
    (ball c R ∩ Function.support (analyticOrderNatAt f)).Finite := by
  -- the points in question lie in the support of `MeromorphicOn.divisor`, which is finite
  refine hf.divisor_ball_support_finite.subset fun z ⟨hzb, hz⟩ => ?_
  have hA : AnalyticAt 𝕜 f z := by
    by_contra h
    exact hz (analyticOrderNatAt_of_not_analyticAt h)
  rw [Function.mem_support, (hf.mono_set ball_subset_closedBall).divisor_apply hzb,
    hA.meromorphicOrderAt_eq]
  cases h : analyticOrderAt f z <;> simp_all [analyticOrderNatAt]

/-- The order of vanishing at a single point of the open disc is at most the total zero count of a
function meromorphic on the closed disc. At a pole or a point of infinite order the left side reads
`0`, so the bound holds trivially there. -/
theorem MeromorphicOn.analyticOrderNatAt_le_finsum_ball [ProperSpace 𝕜]
    (hf : MeromorphicOn f (closedBall c R)) {z₀ : 𝕜} (hz₀ : z₀ ∈ ball c R) :
    analyticOrderNatAt f z₀ ≤ ∑ᶠ z ∈ ball c R, analyticOrderNatAt f z := by
  refine (single_le_finsum z₀
    (hf.finite_ball_inter_support_analyticOrderNatAt.subset fun z hz => ?_)
    fun _ => Nat.zero_le _).trans_eq' (by simp [hz₀])
  classical
  rw [Function.mem_support, finsum_eq_if] at hz
  split_ifs at hz with hzb
  exacts [⟨hzb, hz⟩, absurd rfl hz]

/-- A function without zeros on a set `s` has zero count `0` there. -/
theorem TauCeti.finsum_mem_analyticOrderNatAt_eq_zero_of_forall_ne_zero {s : Set 𝕜}
    (hne : ∀ z ∈ s, f z ≠ 0) : (∑ᶠ z ∈ s, analyticOrderNatAt f z) = 0 :=
  finsum_mem_of_eqOn_zero fun z hz => by
    simp [analyticOrderNatAt, analyticOrderAt_eq_zero.2 (.inr (hne z hz))]

/-! ### The multiset of zeros -/

namespace AnalyticOnNhd

variable {g : 𝕜 → E}

/-- The multiset of zeros of `g` in a set `s`: each `z ∈ s` is repeated `analyticOrderNatAt g z`
times. For `g` analytic on `closedBall c R` and `s = ball c R` these are the zeros of `g` in the
open disc, counted with multiplicity (`AnalyticOnNhd.count_zeroMultiset`). Points of infinite order
are not counted, and by the convention for `finsum` the multiset is `0` when infinitely many points
of `s` have nonzero order. -/
noncomputable def zeroMultiset (g : 𝕜 → E) (s : Set 𝕜) : Multiset 𝕜 :=
  ∑ᶠ z ∈ s, Multiset.replicate (analyticOrderNatAt g z) z

/-- The points of `zeroMultiset g s` lie in `s`. -/
theorem mem_of_mem_zeroMultiset {s : Set 𝕜} {a : 𝕜} (ha : a ∈ zeroMultiset g s) : a ∈ s := by
  classical
  rw [zeroMultiset] at ha
  by_cases hfin :
      (s ∩ Function.support fun z ↦ Multiset.replicate (analyticOrderNatAt g z) z).Finite
  · rw [finsum_mem_eq_sum_of_inter_support_eq _ (t := hfin.toFinset) (by simp), Multiset.mem_sum]
      at ha
    obtain ⟨z, hz, haz⟩ := ha
    rw [Multiset.eq_of_mem_replicate haz]
    exact ((Set.Finite.mem_toFinset _).1 hz).1
  · rw [finsum_mem_eq_zero_of_infinite hfin] at ha
    exact absurd ha (Multiset.notMem_zero a)

variable [ProperSpace 𝕜]

/-- For `g` analytic on `closedBall c R`, a finsum over `ball c R` of a function with the same
support as `analyticOrderNatAt g` is a sum over the finitely many zeros in the open disc. -/
private theorem finsum_mem_ball_eq_sum {M : Type*} [AddCommMonoid M]
    (hg : AnalyticOnNhd 𝕜 g (closedBall c R)) {φ : 𝕜 → M}
    (hφ : Function.support φ = Function.support (analyticOrderNatAt g)) :
    ∑ᶠ z ∈ ball c R, φ z =
      ∑ z ∈ hg.meromorphicOn.finite_ball_inter_support_analyticOrderNatAt.toFinset, φ z :=
  finsum_mem_eq_sum_of_inter_support_eq _ (by
    rw [Set.Finite.coe_toFinset, hφ, Set.inter_assoc, Set.inter_self])

/-- For `g` analytic on `closedBall c R`, `zeroMultiset g (ball c R)` is a finite sum. -/
private theorem zeroMultiset_ball_eq_sum (hg : AnalyticOnNhd 𝕜 g (closedBall c R)) :
    zeroMultiset g (ball c R) =
      ∑ z ∈ hg.meromorphicOn.finite_ball_inter_support_analyticOrderNatAt.toFinset,
        Multiset.replicate (analyticOrderNatAt g z) z := by
  refine finsum_mem_ball_eq_sum hg ?_
  ext z
  rw [Function.mem_support, Function.mem_support, Ne, ← Multiset.card_eq_zero,
    Multiset.card_replicate]

/-- For `g` analytic on `closedBall c R`, the multiplicity of a point of the open disc in
`zeroMultiset g (ball c R)` is the order of vanishing of `g` there, and no other point occurs. -/
@[simp]
theorem count_zeroMultiset [DecidableEq 𝕜] (hg : AnalyticOnNhd 𝕜 g (closedBall c R)) (z : 𝕜) :
    (zeroMultiset g (ball c R)).count z = (ball c R).indicator (analyticOrderNatAt g) z := by
  rw [zeroMultiset_ball_eq_sum hg, Multiset.count_sum']
  simp only [Multiset.count_replicate, Finset.sum_ite_eq', Set.Finite.mem_toFinset]
  by_cases hz : z ∈ ball c R
  · by_cases h0 : analyticOrderNatAt g z = 0 <;> simp [hz, h0]
  · simp [hz]

/-- For `g` analytic on `closedBall c R`, the points of `zeroMultiset g (ball c R)` are the points
of the open disc where `g` has positive finite order of vanishing. -/
@[simp]
theorem mem_zeroMultiset (hg : AnalyticOnNhd 𝕜 g (closedBall c R)) {a : 𝕜} :
    a ∈ zeroMultiset g (ball c R) ↔ a ∈ ball c R ∧ 0 < analyticOrderNatAt g a := by
  classical
  rw [← Multiset.count_pos, count_zeroMultiset hg]
  by_cases ha : a ∈ ball c R <;> simp [ha]

/-- For `g` analytic on `closedBall c R`, the cardinality of `zeroMultiset g (ball c R)` is the
zero count `∑ᶠ z ∈ ball c R, analyticOrderNatAt g z`. -/
@[simp]
theorem card_zeroMultiset (hg : AnalyticOnNhd 𝕜 g (closedBall c R)) :
    Multiset.card (zeroMultiset g (ball c R)) = ∑ᶠ z ∈ ball c R, analyticOrderNatAt g z := by
  rw [zeroMultiset_ball_eq_sum hg, Multiset.card_sum, finsum_mem_ball_eq_sum hg rfl]
  simp only [Multiset.card_replicate]

/-- If `z₀` is the only zero of `g` in `ball c R` and `g` vanishes there to order `d`, then
`zeroMultiset g (ball c R)` is `d` copies of `z₀`. -/
theorem zeroMultiset_eq_replicate (hg : AnalyticOnNhd 𝕜 g (closedBall c R)) {z₀ : 𝕜}
    (hz₀ : z₀ ∈ ball c R) {d : ℕ} (hd : analyticOrderAt g z₀ = d)
    (honly : ∀ z ∈ ball c R, z ≠ z₀ → g z ≠ 0) :
    zeroMultiset g (ball c R) = Multiset.replicate d z₀ := by
  classical
  ext z
  rw [count_zeroMultiset hg, Multiset.count_replicate]
  by_cases hz : z ∈ ball c R
  · rw [Set.indicator_of_mem hz]
    split_ifs with hzz
    · subst hzz
      simp [analyticOrderNatAt, hd]
    · simp [analyticOrderNatAt,
        (hg z (ball_subset_closedBall hz)).analyticOrderAt_eq_zero.2 (honly z hz (Ne.symm hzz))]
  · rw [Set.indicator_of_notMem hz]
    split_ifs with hzz
    · exact absurd (hzz ▸ hz₀) hz
    · rfl

end AnalyticOnNhd

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

/-! ### The zeros in a disc with no zero on the boundary -/

namespace AnalyticOnNhd

variable {g : 𝕜 → E}

/-- If `g` is analytic on `closedBall c R` with no zero on `sphere c R`, the multiplicity of a
point of the closed disc in `zeroMultiset g (ball c R)` is the order of vanishing of `g` there. -/
theorem analyticOrderAt_eq_count_zeroMultiset [DecidableEq 𝕜]
    (hg : AnalyticOnNhd 𝕜 g (closedBall c R)) (hsphere : ∀ ζ ∈ sphere c R, g ζ ≠ 0)
    {z : 𝕜} (hz : z ∈ closedBall c R) :
    analyticOrderAt g z = (zeroMultiset g (ball c R)).count z := by
  rw [count_zeroMultiset hg]
  rcases (ball_union_sphere (x := c) (ε := R) ▸ hz) with hzb | hzs
  · have htop : analyticOrderAt g z ≠ ⊤ := fun h ↦
      hg.meromorphicOrderAt_ne_top_of_forall_mem_sphere_ne_zero hsphere hz
        (by rw [(hg z hz).meromorphicOrderAt_eq, h, ENat.map_top])
    rw [Set.indicator_of_mem hzb, Nat.cast_analyticOrderNatAt htop]
  · rw [Set.indicator_of_notMem fun hzb ↦ (mem_ball.1 hzb).ne (mem_sphere.1 hzs),
      (hg z hz).analyticOrderAt_eq_zero.2 (hsphere z hzs), Nat.cast_zero]

/-- If `g` is analytic on `closedBall c R` with no zero on `sphere c R`, the multiplicity of a
point of the closed disc in `zeroMultiset g (ball c R)` is the meromorphic order of `g` there. -/
theorem meromorphicOrderAt_eq_count_zeroMultiset [DecidableEq 𝕜]
    (hg : AnalyticOnNhd 𝕜 g (closedBall c R)) (hsphere : ∀ ζ ∈ sphere c R, g ζ ≠ 0)
    {z : 𝕜} (hz : z ∈ closedBall c R) :
    meromorphicOrderAt g z = (((zeroMultiset g (ball c R)).count z : ℕ) : WithTop ℤ) := by
  rw [(hg z hz).meromorphicOrderAt_eq, hg.analyticOrderAt_eq_count_zeroMultiset hsphere hz]
  simp

/-- If `g` is analytic on `closedBall c R` with no zero on `sphere c R`, the members of
`zeroMultiset g (ball c R)` are exactly the zeros of `g` in the open disc. -/
theorem mem_zeroMultiset_iff (hg : AnalyticOnNhd 𝕜 g (closedBall c R))
    (hsphere : ∀ ζ ∈ sphere c R, g ζ ≠ 0) {a : 𝕜} :
    a ∈ zeroMultiset g (ball c R) ↔ a ∈ ball c R ∧ g a = 0 := by
  classical
  refine ⟨fun ha ↦ ⟨mem_of_mem_zeroMultiset ha, ?_⟩, fun ⟨ha, h0⟩ ↦ ?_⟩
  · have hac := ball_subset_closedBall (mem_of_mem_zeroMultiset ha)
    have h := hg.analyticOrderAt_eq_count_zeroMultiset hsphere hac
    by_contra hne
    rw [(hg a hac).analyticOrderAt_eq_zero.2 hne] at h
    exact Multiset.count_ne_zero.2 ha (by exact_mod_cast h.symm)
  · have h := hg.analyticOrderAt_eq_count_zeroMultiset hsphere (ball_subset_closedBall ha)
    refine Multiset.count_ne_zero.1 fun hc ↦ ?_
    rw [hc, Nat.cast_zero, (hg a (ball_subset_closedBall ha)).analyticOrderAt_eq_zero] at h
    exact h h0

end AnalyticOnNhd

end RCLike
