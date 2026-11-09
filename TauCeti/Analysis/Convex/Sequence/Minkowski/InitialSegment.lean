/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Sequence.Minkowski.Basic

/-!
# Initial segments of Minkowski sums

If the slopes before a point of one convex polygon are no larger than the slopes of a
second polygon, the minimizing split at that point leaves the second polygon at its anchor.
Consequently the initial segment survives in the Minkowski sum, with the anchor shift and
height translation supplied by the second polygon. Equal slopes are allowed: the minimizing
split need not be unique.

These statements apply to finite polygons and to half-lines, including terminal rays. They
are useful for recovering initial Newton slopes of a product from one of its factors.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, Chapter IV §§3–4.
-/

public section

namespace TauCeti

variable {h g : ℕ → WithTop ℝ}

/-- If all slopes of `h` before `i` are at most all slopes of `g`, the split `(i, b)`
minimizes the Minkowski sum, where `b` is the first finite index of `g`. This includes a
singleton second polygon, whose slope condition is empty. -/
theorem minkowskiSum_add_eq_of_unitSlope_le (hh : IsConvexSeq h) (hg : IsConvexSeq g)
    {i b : ℕ} (hi : h i ≠ ⊤) (hb : g b ≠ ⊤) (hbefore : ∀ j < b, g j = ⊤)
    (hslopes : ∀ k ∈ finiteEdges h, k < i →
      ∀ j ∈ finiteEdges g, unitSlope h k ≤ unitSlope g j) :
    minkowskiSum h g (i + b) = h i + g b := by
  obtain ⟨c, m, hline, heq⟩ := hh.exists_affine_minorant_eq hi
  have hm : IsSupportingLine h m ((h i).untop₀ - m * i) := by
    apply isSupportingLine_iff_forall.mpr
    intro n
    convert hline n using 2
    linarith
  have hm' := (hh.isSupportingLine_iff_unitSlope hi m).mp hm
  by_cases hb' : g (b + 1) = ⊤
  · have hgline : IsSupportingLine g m ((g b).untop₀ - m * b) := by
      apply (hg.isSupportingLine_iff_unitSlope hb m).mpr
      exact ⟨fun j hj hjfin => False.elim (hjfin (hbefore j (by omega))),
        fun hj => False.elim (hj hb')⟩
    apply minkowskiSum_add_eq_of_mem_supportingFace hm _ hgline
    all_goals simp [mem_supportingFace, WithTop.coe_untop₀_of_ne_top, hi, hb]
  · let σ := min m (unitSlope g b)
    have hhline : IsSupportingLine h σ ((h i).untop₀ - σ * i) := by
      apply (hh.isSupportingLine_iff_unitSlope hi σ).mpr
      constructor
      · intro k hk hkfin
        exact le_min (hm'.1 k hk hkfin)
          (hslopes k (mem_finiteEdges.mpr ⟨hkfin, hk ▸ hi⟩) (by omega)
            b (mem_finiteEdges.mpr ⟨hb, hb'⟩))
      · intro hn
        exact (min_le_left _ _).trans (hm'.2 hn)
    have hgline : IsSupportingLine g σ ((g b).untop₀ - σ * b) := by
      apply (hg.isSupportingLine_iff_unitSlope hb σ).mpr
      exact ⟨fun j hj hjfin => False.elim (hjfin (hbefore j (by omega))),
        fun _ => min_le_right _ _⟩
    apply minkowskiSum_add_eq_of_mem_supportingFace hhline _ hgline
    all_goals simp [mem_supportingFace, WithTop.coe_untop₀_of_ne_top, hi, hb]

/-- Slope separation preserves the whole initial segment through `p`, not just its finite
heights. The second polygon shifts indices by its anchor and translates heights by its
initial height. -/
theorem minkowskiSum_eqOn_initialSegment (hh : IsConvexSeq h) (hg : IsConvexSeq g)
    {p b : ℕ} (hp : h p ≠ ⊤) (hb : g b ≠ ⊤) (hbefore : ∀ j < b, g j = ⊤)
    (hslopes : ∀ k ∈ finiteEdges h, k < p →
      ∀ j ∈ finiteEdges g, unitSlope h k ≤ unitSlope g j) :
    ∀ i ≤ p, minkowskiSum h g (i + b) = h i + g b := by
  intro i hip
  by_cases hi : h i = ⊤
  · have hprior : ∀ j < i + 1, h j = ⊤ := by
      intro j hj
      by_contra hjfin
      exact (hh.ne_top_of_le_of_le hjfin hp (by omega) hip) hi
    rw [hi, top_add]
    exact minkowskiSum_eq_top_of_lt_add hprior hbefore (by omega)
  · exact minkowskiSum_add_eq_of_unitSlope_le hh hg hi hb hbefore
      (fun k hk hki => hslopes k hk (hki.trans_le hip))

/-- Every genuine unit edge before `p` keeps its slope in the Minkowski sum, after shifting
by the second polygon's anchor. No outgoing edge at `p` is asserted. -/
theorem unitSlope_minkowskiSum_of_unitSlope_le (hh : IsConvexSeq h) (hg : IsConvexSeq g)
    {p b : ℕ} (hp : h p ≠ ⊤) (hb : g b ≠ ⊤) (hbefore : ∀ j < b, g j = ⊤)
    (hslopes : ∀ k ∈ finiteEdges h, k < p →
      ∀ j ∈ finiteEdges g, unitSlope h k ≤ unitSlope g j)
    {i : ℕ} (hi : i ∈ finiteEdges h) (hip : i < p) :
    i + b ∈ finiteEdges (minkowskiSum h g) ∧
      unitSlope (minkowskiSum h g) (i + b) = unitSlope h i := by
  have heq := minkowskiSum_eqOn_initialSegment hh hg hp hb hbefore hslopes
  have hi₀ := heq i hip.le
  have hi₁ := heq (i + 1) hip
  rw [mem_finiteEdges] at hi
  have hi₁' : minkowskiSum h g (i + b + 1) = h (i + 1) + g b := by
    simpa only [add_right_comm i b 1] using hi₁
  refine ⟨mem_finiteEdges.mpr ⟨?_, ?_⟩, ?_⟩
  · rw [hi₀]
    exact WithTop.add_ne_top.mpr ⟨hi.1, hb⟩
  · rw [hi₁']
    exact WithTop.add_ne_top.mpr ⟨hi.2, hb⟩
  · simp only [unitSlope_def, hi₀, hi₁', WithTop.untop₀_add hi.1 hb,
      WithTop.untop₀_add hi.2 hb]
    ring

end TauCeti
