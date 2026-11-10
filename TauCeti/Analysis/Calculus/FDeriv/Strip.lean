/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Topology.MetricSpace.ProperSpace.Real
public import TauCeti.Topology.Compactness.Normed

/-!
# Uniform derivative bounds on a strip of the plane

Let `k l : ℝ × ℝ → Y` be `C¹` maps on a strip `|u.1| < r` into a real normed space. Suppose both
have derivative `A` along the segment `{0} × [a, b]`, agree off the slab `a ≤ u.2 ≤ b`, and that
the derivative of `l` is invariant under translation in the second coordinate. Then on a thinner
strip both derivatives are within `ε` of `A` (`TauCeti.exists_pos_forall_norm_fderiv_sub_lt`).

Over the compact segment this is continuity of the derivatives together with the tube lemma
(`IsCompact.eventually_forall_of_forall_eventually`). Off the slab the derivative of `k` is that of
`l`, which is read back at one of the ends of the segment by the translation invariance.

This is the uniform estimate behind straightening a concordance near an arc: there `k` and `l` are
the concordance and the standard strip read in coordinates, which agree near the two ends of the
time interval.
-/

public section

open Set

namespace TauCeti

/-- **Uniform derivative bounds on a strip.** Let `k` and `l` be `C¹` on the strip `|u.1| < r`,
equal off the slab `a ≤ u.2 ≤ b`, with derivative `A` along the segment `{0} × [a, b]`, and with
the derivative of `l` independent of the second coordinate. Then on a thinner strip both
derivatives are within `ε` of `A`. -/
theorem exists_pos_forall_norm_fderiv_sub_lt {Y : Type*} [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] {k l : ℝ × ℝ → Y} {r a b ε : ℝ} {A : ℝ × ℝ →L[ℝ] Y} (hr : 0 < r)
    (hab : a ≤ b) (hε : 0 < ε) (hkC : ContDiffOn ℝ 1 k {u | |u.1| < r})
    (hlC : ContDiffOn ℝ 1 l {u | |u.1| < r})
    (hkl : ∀ u : ℝ × ℝ, |u.1| < r → (u.2 < a ∨ b < u.2) → k u = l u)
    (hlt : ∀ (u : ℝ × ℝ) (s : ℝ), fderiv ℝ l (u + (0, s)) = fderiv ℝ l u)
    (hkA : ∀ t ∈ Icc a b, fderiv ℝ k (0, t) = A) (hlA : ∀ t ∈ Icc a b, fderiv ℝ l (0, t) = A) :
    ∃ ρ > 0, ρ ≤ r ∧ ∀ u : ℝ × ℝ, |u.1| < ρ →
      ‖fderiv ℝ k u - A‖ < ε ∧ ‖fderiv ℝ l u - A‖ < ε := by
  set W : Set (ℝ × ℝ) := {u | |u.1| < r}
  have hW : IsOpen W := isOpen_lt (continuous_abs.comp continuous_fst) continuous_const
  -- Over the segment `{0} × [a, b]` this is continuity of the derivatives.
  obtain ⟨ρ₁, hρ₁, hρ₁O⟩ := isCompact_Icc.exists_pos_forall_norm_lt
      (Q := fun θ t => ((θ, t) : ℝ × ℝ) ∈ W ∩ (fun u => (fderiv ℝ k u, fderiv ℝ l u)) ⁻¹'
        {q | ‖q.1 - A‖ < ε ∧ ‖q.2 - A‖ < ε}) fun t ht =>
      IsOpen.mem_nhds (x := ((0 : ℝ), t))
        (((hkC.continuousOn_fderiv_of_isOpen hW le_rfl).prodMk
          (hlC.continuousOn_fderiv_of_isOpen hW le_rfl)).isOpen_inter_preimage hW
          ((isOpen_lt (continuous_norm.comp (continuous_fst.sub continuous_const))
            continuous_const).inter
            (isOpen_lt (continuous_norm.comp (continuous_snd.sub continuous_const))
              continuous_const)))
      ⟨by simpa [W] using hr, by simp [hkA t ht, hlA t ht, hε]⟩
  simp only [Real.norm_eq_abs] at hρ₁O
  refine ⟨min ρ₁ r, lt_min hρ₁ hr, min_le_right _ _, fun u hu => ?_⟩
  have hu₁ : |u.1| < ρ₁ := hu.trans_le (min_le_left _ _)
  by_cases ht : u.2 ∈ Icc a b
  · exact (hρ₁O hu₁ u.2 ht).2
  -- Off `[a, b]` the two maps agree near `u`, and the derivative of `l` is read at `a` or `b`.
  have hev (O : Set (ℝ × ℝ)) (hO : IsOpen O) (huO : u ∈ O)
      (hO' : ∀ v ∈ O, v.2 < a ∨ b < v.2) : fderiv ℝ k u = fderiv ℝ l u := by
    refine Filter.EventuallyEq.fderiv_eq ?_
    filter_upwards [(hO.inter hW).mem_nhds ⟨huO, hu.trans_le (min_le_right _ _)⟩] with v hv
    exact hkl v hv.2 (hO' v hv.1)
  rcases not_and_or.1 ht with h0 | h1
  · have hlu : fderiv ℝ l u = fderiv ℝ l (u.1, a) := by simpa using hlt (u.1, a) (u.2 - a)
    rw [hev {v | v.2 < a} (isOpen_lt continuous_snd continuous_const) (not_le.1 h0)
      (fun v hv => Or.inl hv), hlu]
    have := (hρ₁O hu₁ a ⟨le_rfl, hab⟩).2.2
    exact ⟨this, this⟩
  · have hlu : fderiv ℝ l u = fderiv ℝ l (u.1, b) := by simpa using hlt (u.1, b) (u.2 - b)
    rw [hev {v | b < v.2} (isOpen_lt continuous_const continuous_snd) (not_le.1 h1)
      (fun v hv => Or.inr hv), hlu]
    have := (hρ₁O hu₁ b ⟨hab, le_rfl⟩).2.2
    exact ⟨this, this⟩

end TauCeti
