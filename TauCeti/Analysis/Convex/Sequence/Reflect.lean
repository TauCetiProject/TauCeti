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

Reflection preserves convexity and reverses the finite unit edges, negating their slopes
(`IsConvexSeq.reflect`, `finiteEdges_reflect` and `unitSlope_reflect`, in
`TauCeti.Analysis.Convex.Sequence.Basic`). This file shows that, for points that are infinite
beyond `N`, reflection commutes with taking the lower convex envelope; the hypothesis is needed,
since reflection discards the points beyond `N`, which may affect the envelope on `[0, N]`.

## Main results

* `IsLowerConvexEnvelope.reflect` and `lowerConvexEnvelope_reflect`: reflection commutes with
  taking the lower convex envelope of points that are infinite beyond `N`.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Graduate Texts in Mathematics 58, Springer, 1984, Chapter IV §3.
-/

public section

namespace TauCeti

variable {a h : ℕ → WithTop ℝ}

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

end TauCeti
