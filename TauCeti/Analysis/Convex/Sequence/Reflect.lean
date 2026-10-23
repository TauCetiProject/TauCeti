/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Sequence.Envelope

/-!
# Reflection of height sequences

Reflecting a height sequence `h` in an index `N` gives the sequence
`n ↦ if n ≤ N then h (N - n) else ⊤`, which plots the points of `h` on `[0, N]` in reverse
order. This is the geometry of reversing the coefficients of a polynomial of degree at most `N`.

Reflection preserves convexity. For points that are infinite beyond `N`, it commutes with taking
the lower convex envelope; the hypothesis is needed, since reflection discards the points beyond
`N`, which may affect the envelope on `[0, N]`. The finite unit edge `[m, m + 1]` of such a
sequence moves to `[N - 1 - m, N - m]`, and its slope is negated. Thus reflection reverses the
order of the finite slopes and negates them.

## Main results

* `IsConvexSeq.reflect`: reflection preserves convexity.
* `IsLowerConvexEnvelope.reflect` and `lowerConvexEnvelope_reflect`: reflection commutes with
  taking the lower convex envelope of points that are infinite beyond `N`.
* `finiteEdges_reflect` and `unitSlope_reflect`: reflection reverses the finite unit edges and
  negates their slopes.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Graduate Texts in Mathematics 58, Springer, 1984, Chapter IV §3.
-/

public section

namespace TauCeti

variable {a h : ℕ → WithTop ℝ}

/-- Reflecting heights in `N`, with infinite heights beyond `N`, preserves convexity. The heights
of `h` beyond `N` are discarded. -/
theorem IsConvexSeq.reflect (hh : IsConvexSeq h) (N : ℕ) :
    IsConvexSeq fun n => if n ≤ N then h (N - n) else ⊤ := by
  have hmem {n : ℕ} : (if n ≤ N then h (N - n) else ⊤) ≠ ⊤ ↔ n ≤ N ∧ h (N - n) ≠ ⊤ := by
    split_ifs with hn <;> simp [hn]
  refine isConvexSeq_iff_two_mul_le.mpr ⟨⟨fun i hi j hj l hl => ?_⟩, fun n hn hn₂ => ?_⟩
  · obtain ⟨-, hi⟩ := hmem.mp hi
    obtain ⟨hjN, hj⟩ := hmem.mp hj
    exact hmem.mpr ⟨hl.2.trans hjN,
      hh.ne_top_of_le_of_le hj hi (by have := hl.2; omega) (by have := hl.1; omega)⟩
  · obtain ⟨-, hn⟩ := hmem.mp hn
    obtain ⟨hn₂N, hn₂⟩ := hmem.mp hn₂
    have e₀ : N - n = N - (n + 2) + 2 := by omega
    have e₁ : N - (n + 1) = N - (n + 2) + 1 := by omega
    rw [e₀] at hn
    have key := (isConvexSeq_iff_two_mul_le.mp hh).2 (N - (n + 2)) hn₂ hn
    simp only [show n ≤ N by omega, show n + 1 ≤ N by omega, hn₂N, ite_true, e₀, e₁]
    linarith

/-- Reflecting points in `N`, when they are infinite beyond `N`, reflects their lower convex
envelope in the same way. -/
theorem IsLowerConvexEnvelope.reflect (hh : IsLowerConvexEnvelope a h) {N : ℕ}
    (ha : ∀ n, N < n → a n = ⊤) :
    IsLowerConvexEnvelope (fun n => if n ≤ N then a (N - n) else ⊤)
      (fun n => if n ≤ N then h (N - n) else ⊤) := by
  refine ⟨hh.isConvexSeq.reflect N, fun n => ?_, fun g hg hga n => ?_⟩
  · dsimp only
    split_ifs
    exacts [hh.le _, le_rfl]
  · -- Reflecting `g` back gives a convex minorant of `a`.
    have hle := hh.greatest (hg.reflect N) fun m => by
      dsimp only
      split_ifs with hm
      · simpa [Nat.sub_sub_self hm] using hga (N - m)
      · simp [ha m (by omega)]
    dsimp only
    split_ifs with hn
    · simpa [Nat.sub_sub_self hn] using hle (N - n)
    · exact le_top

/-- Reflecting points in `N`, when they are infinite beyond `N`, reflects their lower convex
envelope in the same way. -/
theorem lowerConvexEnvelope_reflect {N : ℕ} (ha : ∀ n, N < n → a n = ⊤) :
    lowerConvexEnvelope (fun n => if n ≤ N then a (N - n) else ⊤) =
      fun n => if n ≤ N then lowerConvexEnvelope a (N - n) else ⊤ :=
  ((isLowerConvexEnvelope_lowerConvexEnvelope (isAdmissible_of_forall_gt ha)).reflect ha
    |>.eq_lowerConvexEnvelope).symm

/-- Reflecting heights in `N`, when they are infinite beyond `N`, reverses the finite unit
edges: the edge `[m, m + 1]` moves to `[N - 1 - m, N - m]`. -/
theorem finiteEdges_reflect {N : ℕ} (hh : ∀ n, N < n → h n = ⊤) :
    finiteEdges (fun n => if n ≤ N then h (N - n) else ⊤) = (N - 1 - ·) '' finiteEdges h := by
  ext n
  simp only [mem_finiteEdges, Set.mem_image]
  constructor
  · rintro ⟨h₀, h₁⟩
    have hn : n + 1 ≤ N := by
      by_contra hn
      simp [hn] at h₁
    refine ⟨N - 1 - n, ⟨?_, ?_⟩, by omega⟩
    · simpa [hn, show N - (n + 1) = N - 1 - n by omega] using h₁
    · simpa [show n ≤ N by omega, show N - 1 - n + 1 = N - n by omega] using h₀
  · rintro ⟨m, ⟨h₀, h₁⟩, rfl⟩
    have hm : m + 1 ≤ N := by
      by_contra hm
      exact h₁ (hh _ (by omega))
    simp only [show N - 1 - m ≤ N by omega, show N - 1 - m + 1 ≤ N by omega, ite_true,
      show N - (N - 1 - m) = m + 1 by omega, show N - (N - 1 - m + 1) = m by omega]
    exact ⟨h₁, h₀⟩

/-- Reflecting heights in `N` negates the unit slopes and reverses their order. -/
theorem unitSlope_reflect (h : ℕ → WithTop ℝ) {N n : ℕ} (hn : n < N) :
    unitSlope (fun n => if n ≤ N then h (N - n) else ⊤) n = -unitSlope h (N - 1 - n) := by
  simp only [unitSlope_def, show n + 1 ≤ N by omega, show n ≤ N by omega, ite_true,
    show N - (n + 1) = N - 1 - n by omega, show N - n = N - 1 - n + 1 by omega]
  ring

end TauCeti
