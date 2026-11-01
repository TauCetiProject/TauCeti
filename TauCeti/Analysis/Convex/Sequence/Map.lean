/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Sequence.Envelope
public import Mathlib.Algebra.Order.Hom.Monoid

/-!
# Changing the height scale of a convex sequence

An ordered additive automorphism of the real heights preserves finite domains,
convexity and the greatest-convex-minorant property. Consequently it commutes with
the lower convex envelope, including the fallback on inadmissible sequences.
Unit increments transform by the same automorphism. In particular these results
allow a positive change of valuation scale without rebuilding the polygon.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, Chapter IV §3.
-/

public section

namespace TauCeti

variable {a h : ℕ → WithTop ℝ} (e : ℝ ≃+o ℝ)

/-- Changing the height scale leaves the finite unit edges unchanged. -/
@[simp]
theorem finiteEdges_map (f : ℝ → ℝ) :
    finiteEdges (fun n => WithTop.map f (h n)) = finiteEdges h := by
  ext n
  simp

/-- Unit increments transform additively with the height scale. This also respects
the zero default at infinite heights; only finite edges represent geometric slopes. -/
@[simp]
theorem unitSlope_map {F : Type*} [FunLike F ℝ ℝ] [AddMonoidHomClass F ℝ ℝ]
    (f : F) (n : ℕ) :
    unitSlope (fun n => WithTop.map f (h n)) n = f (unitSlope h n) := by
  simp only [unitSlope_def, map_sub]
  generalize h n = x, h (n + 1) = y
  induction x using WithTop.recTopCoe <;>
    induction y using WithTop.recTopCoe <;> simp

/-- An ordered additive change of height scale preserves convexity. -/
theorem IsConvexSeq.map (hh : IsConvexSeq h) {F : Type*} [FunLike F ℝ ℝ]
    [AddMonoidHomClass F ℝ ℝ] [OrderHomClass F ℝ ℝ] (f : F) :
    IsConvexSeq (fun n => WithTop.map f (h n)) := by
  refine ⟨?_, ?_⟩
  · simpa only [ne_eq, WithTop.map_eq_top_iff] using hh.ordConnected
  · intro i hi j hj hij
    rw [finiteEdges_map] at hi hj
    simp only [unitSlope_map]
    exact OrderHomClass.mono f (hh.monotoneOn hi hj hij)

/-- An ordered additive change of height scale preserves and reflects convexity. -/
@[simp]
theorem isConvexSeq_map_iff :
    IsConvexSeq (fun n => WithTop.map e (h n)) ↔ IsConvexSeq h := by
  refine ⟨fun hh => ?_, fun hh => hh.map e⟩
  have hinv : e.symm ∘ e = id := funext e.symm_apply_apply
  simpa only [WithTop.map_map, hinv, WithTop.map_id, id_eq] using hh.map e.symm

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
