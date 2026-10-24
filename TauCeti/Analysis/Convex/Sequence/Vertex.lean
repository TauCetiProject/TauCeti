/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Sequence.Envelope

/-!
# Contact at vertices of a lower convex envelope

An interior vertex of a convex height sequence is a strict increase between two
adjacent finite unit slopes. For a lower convex envelope, every such vertex is
an original point of the sequence. Equivalently, at a noncontact interior index
the two adjacent slopes agree. Thus subdividing a straight segment does not
introduce geometric vertices, and a missing coefficient cannot be a vertex.

The stronger local characterization `IsLowerConvexEnvelope.eq_min_of_finite_neighbors`
says that each interior height is the minimum of its coefficient height and the
average of its two neighboring heights. All results allow unbounded finite domains
and infinite coefficient heights.
-/

public section

namespace TauCeti

namespace IsLowerConvexEnvelope

variable {a h : ℕ → WithTop ℝ}

/-- At an index with two finite neighbors, an envelope height is the minimum of
the original point height and the neighboring average. In particular it can lie
strictly below the original point only along a straight segment. -/
theorem eq_min_of_finite_neighbors (hh : IsLowerConvexEnvelope a h) {n : ℕ}
    (hn : h n ≠ ⊤) (hn₂ : h (n + 2) ≠ ⊤) :
    h (n + 1) = min (a (n + 1))
      (((h n).untop₀ + (h (n + 2)).untop₀) / 2 : ℝ) := by
  have hn₁ : h (n + 1) ≠ ⊤ :=
    hh.isConvexSeq.ne_top_of_le_of_le hn hn₂ (by omega) (by omega)
  have hmid := (isConvexSeq_iff_two_mul_le.mp hh.isConvexSeq).2 n hn hn₂
  have havg : h (n + 1) ≤
      ((((h n).untop₀ + (h (n + 2)).untop₀) / 2 : ℝ) : WithTop ℝ) := by
    rw [← WithTop.coe_untop₀_of_ne_top hn₁, WithTop.coe_le_coe]
    linarith
  let z := min (a (n + 1))
    ((((h n).untop₀ + (h (n + 2)).untop₀) / 2 : ℝ) : WithTop ℝ)
  have hz : z ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_right _ _)
  lift z to ℝ using hz with y hy
  have hlow : h (n + 1) ≤ (y : WithTop ℝ) := by
    rw [hy]
    exact le_min (hh.le _) havg
  have hhigh : (y : WithTop ℝ) ≤
      ((((h n).untop₀ + (h (n + 2)).untop₀) / 2 : ℝ) : WithTop ℝ) := by
    rw [hy]
    exact min_le_right _ _
  have hcv := hh.isConvexSeq.update_of_le (y := y) hn hn₂
    (by rwa [← WithTop.coe_untop₀_of_ne_top hn₁, WithTop.coe_le_coe] at hlow)
    (by rw [WithTop.coe_le_coe] at hhigh; linarith)
  have hle : Function.update h (n + 1) (y : WithTop ℝ) ≤ a :=
    update_le_iff.mpr ⟨by rw [hy]; exact min_le_left _ _, fun k _ => hh.le k⟩
  have hmax := hh.greatest hcv hle (n + 1)
  simp only [Function.update_self] at hmax
  simpa only [hy] using le_antisymm hlow hmax

/-- Every interior strict slope change of a lower convex envelope is an original
point. Both slopes are genuine finite edges; there are no endpoint sentinels. -/
theorem eq_of_unitSlope_lt (hh : IsLowerConvexEnvelope a h) {n : ℕ}
    (hn : h n ≠ ⊤) (hn₂ : h (n + 2) ≠ ⊤)
    (hs : unitSlope h n < unitSlope h (n + 1)) : h (n + 1) = a (n + 1) := by
  have hn₁ : h (n + 1) ≠ ⊤ :=
    hh.isConvexSeq.ne_top_of_le_of_le hn hn₂ (by omega) (by omega)
  have hstrict : h (n + 1) <
      ((((h n).untop₀ + (h (n + 2)).untop₀) / 2 : ℝ) : WithTop ℝ) := by
    rw [← WithTop.coe_untop₀_of_ne_top hn₁, WithTop.coe_lt_coe]
    simp only [unitSlope_def, Nat.add_assoc] at hs
    linarith
  have heq := hh.eq_min_of_finite_neighbors hn hn₂
  by_cases hle : a (n + 1) ≤
      ((((h n).untop₀ + (h (n + 2)).untop₀) / 2 : ℝ) : WithTop ℝ)
  · simpa only [min_eq_left hle] using heq
  · rw [min_eq_right (le_of_not_ge hle)] at heq
    exact False.elim ((ne_of_lt hstrict) heq)

/-- At a noncontact interior index the two neighboring finite slopes agree.
This also applies when the original point height is infinite. -/
theorem unitSlope_eq_of_lt (hh : IsLowerConvexEnvelope a h) {n : ℕ}
    (hn : h n ≠ ⊤) (hn₂ : h (n + 2) ≠ ⊤)
    (ha : h (n + 1) < a (n + 1)) : unitSlope h n = unitSlope h (n + 1) := by
  have hn₁ : h (n + 1) ≠ ⊤ :=
    hh.isConvexSeq.ne_top_of_le_of_le hn hn₂ (by omega) (by omega)
  have hmono := hh.isConvexSeq.monotoneOn (a := n) (b := n + 1)
    (mem_finiteEdges.mpr ⟨hn, hn₁⟩) (mem_finiteEdges.mpr ⟨hn₁, hn₂⟩) (by omega)
  exact hmono.eq_of_not_lt fun hs => (ne_of_lt ha) (hh.eq_of_unitSlope_lt hn hn₂ hs)

end IsLowerConvexEnvelope

end TauCeti
