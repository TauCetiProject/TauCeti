/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Amenable.Foelner
public import TauCeti.GroupTheory.Amenable.LevelSet

/-!
# Følner sets from almost invariant finitely supported functions

Let a group `G` act on a type `X`, and translate functions by `(g • p) x = p (g⁻¹ • x)`. If a
nonnegative finitely supported function `p : X → ℝ` is almost invariant under a finite set
`K ⊆ G` in `ℓ¹`, in the sense that

```text
∑_{g ∈ K} ∑_x |p (g⁻¹ • x) - p x| < ε · ∑_x p x,
```

then some finite nonempty set `F ⊆ X` satisfies

```text
∑_{g ∈ K} |g • F ∆ F| < ε · |F|.
```

Such a set is found among the superlevel sets `{x | t < p x}`, `t ≥ 0`.

This passes from Reiter's condition (almost invariant finitely supported probabilities) to Følner's
condition (almost invariant finite sets). The finite layer-cake identities
`TauCeti.exists_finsupp_layerCake` express the mass of `p` and each translation distance as
weighted sums of level-set cardinalities and boundaries. A strict inequality between the
weighted sums holds at some level, giving the desired set without measure-theoretic arguments.

## Main results

* `TauCeti.exists_finset_sum_card_smul_symmDiff_lt_of_sum_tsum_lt`: a finite nonempty set whose
  total boundary `∑_{g ∈ K} |g • F ∆ F|` is less than `ε |F|`.
* `TauCeti.exists_finset_card_smul_symmDiff_lt_of_sum_tsum_lt`: the same set satisfies
  `|g • F ∆ F| < ε |F|` for each `g ∈ K`.
* `TauCeti.hasFoelnerSets_of_forall_exists_sum_tsum_abs_sub_lt`: a group satisfying Reiter's
  condition, for its left regular action, has Følner sets.

## References

* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Theorem G.5.1 and the proof of
  Proposition G.5.2.
* A. Garrido, *An introduction to amenable groups*, Theorem 3.6.
-/

public section

open Finset Function
open scoped Pointwise symmDiff

namespace TauCeti

variable {G X : Type*} [Group G] [MulAction G X] [DecidableEq X]

/-- **Reiter implies Følner, summed form.** If a nonnegative finitely supported function `p` on
`X` satisfies `∑_{g ∈ K} ∑_x |p (g⁻¹ • x) - p x| < ε · ∑_x p x`, then some finite nonempty set
`F ⊆ X` has total boundary `∑_{g ∈ K} |g • F ∆ F| < ε |F|`. -/
theorem exists_finset_sum_card_smul_symmDiff_lt_of_sum_tsum_lt {p : X → ℝ} (hp : 0 ≤ p)
    (hfin : p.HasFiniteSupport) {K : Finset G} {ε : ℝ}
    (h : ∑ g ∈ K, ∑' x, |p (g⁻¹ • x) - p x| < ε * ∑' x, p x) :
    ∃ F : Finset X, F.Nonempty ∧ ∑ g ∈ K, (#((g • F) ∆ F) : ℝ) < ε * #F := by
  classical
  obtain ⟨w, hw, -, hmass, hboundary⟩ := exists_finsupp_layerCake (G := G) hp hfin
  let F (t : ℝ) := hfin.toFinset.filter (fun x => t < p x)
  -- Both sides use the same nonnegative widths, so one level satisfies the strict inequality.
  have h' : (∑ t ∈ w.support, w t * ∑ g ∈ K, (#((g • F t) ∆ F t) : ℝ)) <
      ∑ t ∈ w.support, w t * (ε * #(F t)) := by
    simp only [hboundary, hmass, Finsupp.sum] at h
    rw [sum_comm] at h
    simpa only [F, ← mul_sum, mul_sum, mul_left_comm] using h
  obtain ⟨t, -, ht⟩ := exists_lt_of_sum_lt h'
  have hlt : ∑ g ∈ K, (#((g • F t) ∆ F t) : ℝ) < ε * #(F t) :=
    lt_of_mul_lt_mul_left ht (hw t)
  refine ⟨F t, ?_, hlt⟩
  by_contra hn
  simp [not_nonempty_iff_eq_empty.1 hn] at hlt

/-- **Reiter implies Følner.** If a nonnegative finitely supported function `p` on `X` satisfies
`∑_{g ∈ K} ∑_x |p (g⁻¹ • x) - p x| < ε · ∑_x p x`, then some finite nonempty set `F ⊆ X` satisfies
`|g • F ∆ F| < ε |F|` for every `g ∈ K`. -/
theorem exists_finset_card_smul_symmDiff_lt_of_sum_tsum_lt {p : X → ℝ} (hp : 0 ≤ p)
    (hfin : p.HasFiniteSupport) {K : Finset G} {ε : ℝ}
    (h : ∑ g ∈ K, ∑' x, |p (g⁻¹ • x) - p x| < ε * ∑' x, p x) :
    ∃ F : Finset X, F.Nonempty ∧ ∀ g ∈ K, (#((g • F) ∆ F) : ℝ) < ε * #F := by
  obtain ⟨F, hF, hlt⟩ := exists_finset_sum_card_smul_symmDiff_lt_of_sum_tsum_lt hp hfin h
  exact ⟨F, hF, fun g hg ↦ (single_le_sum (f := fun g ↦ (#((g • F) ∆ F) : ℝ))
    (fun _ _ ↦ Nat.cast_nonneg _) hg).trans_lt hlt⟩

/-- A group satisfying **Reiter's condition** has Følner sets: if for every finite `K` and
`ε > 0` there is a finitely supported probability density `p` with
`∑_{g ∈ K} ∑_x |p (g⁻¹ x) - p x| < ε`, then `G` has Følner sets. -/
theorem hasFoelnerSets_of_forall_exists_sum_tsum_abs_sub_lt
    (h : ∀ K : Finset G, ∀ ε : ℝ, 0 < ε →
      ∃ p : G → ℝ, 0 ≤ p ∧ p.HasFiniteSupport ∧ ∑' x, p x = 1 ∧
        ∑ g ∈ K, ∑' x, |p (g⁻¹ * x) - p x| < ε) :
    HasFoelnerSets G := by
  classical
  refine hasFoelnerSets_iff.2 fun K ε hε ↦ ?_
  obtain ⟨p, hp0, hpfin, hp1, hp⟩ := h K ε hε
  exact exists_finset_card_smul_symmDiff_lt_of_sum_tsum_lt hp0 hpfin (by simpa [hp1] using hp)

end TauCeti
