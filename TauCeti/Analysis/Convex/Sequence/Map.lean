/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Sequence.Envelope

/-!
# Changing the height scale of a convex sequence

An ordered additive automorphism of the real heights preserves the
lower-envelope universal property (`IsLowerConvexEnvelope.map`) and admissibility
(`isAdmissible_map_iff`). It commutes with the total lower convex envelope
(`lowerConvexEnvelope_map`), including the fallback on inadmissible sequences.
The finite-edge, unit-increment and convexity transport lemmas are in
`TauCeti.Analysis.Convex.Sequence.Basic`. These results allow a positive change
of valuation scale without rebuilding the polygon.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, Chapter IV §3.
-/

public section

namespace TauCeti

variable {a h : ℕ → WithTop ℝ} (e : ℝ ≃+o ℝ)

/-- Changing the height scale preserves the lower-envelope universal property. -/
theorem IsLowerConvexEnvelope.map (hh : IsLowerConvexEnvelope a h) (e : ℝ ≃+o ℝ) :
    IsLowerConvexEnvelope (fun n => WithTop.map e (a n))
      (fun n => WithTop.map e (h n)) := by
  let E := e.toOrderIso.withTopCongr
  refine ⟨hh.isConvexSeq.map e, fun n => ?_, fun g hg hga n => ?_⟩
  · exact E.monotone (hh.le n)
  · have hback : (fun n => WithTop.map e.symm (g n)) ≤ a := by
      intro k
      exact E.symm_apply_le.mpr (hga k)
    have hle := hh.greatest (hg.map e.symm) hback n
    exact E.symm_apply_le.mp hle

/-- Admissibility is invariant under an ordered additive change of real height scale. -/
@[simp]
theorem isAdmissible_map_iff :
    IsAdmissible (fun n => WithTop.map e (a n)) ↔ IsAdmissible a := by
  rw [← exists_isLowerConvexEnvelope_iff, ← exists_isLowerConvexEnvelope_iff]
  refine ⟨fun ⟨h, hh⟩ => ?_, fun ⟨h, hh⟩ => ⟨_, hh.map e⟩⟩
  refine ⟨fun n => WithTop.map e.symm (h n), ?_⟩
  have hinv : e.symm ∘ e = id := funext e.symm_apply_apply
  simpa only [WithTop.map_map, hinv, WithTop.map_id, id_eq] using hh.map e.symm

/-- An ordered additive change of scale commutes with the total lower convex envelope.
For inadmissible sequences both sides are the all-infinite fallback. -/
theorem lowerConvexEnvelope_map :
    lowerConvexEnvelope (fun n => WithTop.map e (a n)) =
      fun n => WithTop.map e (lowerConvexEnvelope a n) := by
  by_cases ha : IsAdmissible a
  · exact ((isLowerConvexEnvelope_lowerConvexEnvelope ha).map e).eq_lowerConvexEnvelope.symm
  · have ha' : ¬ IsAdmissible (fun n => WithTop.map e (a n)) := by
      rwa [isAdmissible_map_iff]
    rw [lowerConvexEnvelope_of_not_isAdmissible ha',
      lowerConvexEnvelope_of_not_isAdmissible ha]
    rfl

end TauCeti
