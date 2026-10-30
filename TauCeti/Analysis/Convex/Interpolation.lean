/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Convex

/-!
# Uniform approximation by barycentric interpolation

On a sufficiently small simplex, barycentric interpolation of a uniformly continuous map
approximates its value at every point of that simplex. The size bound is independent of the
number of vertices and of the shape of the simplex. The domain may be any subset of a real
normed space, provided the barycentre being evaluated belongs to it.

This is the estimate in values used alongside derivative estimates in secant approximation.

## References

* J. Munkres, *Elementary Differential Topology*, Annals of Math. Studies 54 (1966),
  Chapter II, Section 9 (secant approximations).
-/

public section

open Finset

/-- Barycentric interpolation of a uniformly continuous map approximates its value at the
barycentre, uniformly over all finite families of points with sufficiently small diameter.
Only the points and the barycentre need to belong to the domain. -/
theorem UniformContinuous.exists_pos_forall_norm_sum_smul_sub_lt
    {V E : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] {s : Set V} {f : s → E}
    (hf : UniformContinuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ {β : Type*} [Fintype β] (p : β → s) (w : β → ℝ),
      (∀ a, 0 ≤ w a) → (∑ a, w a = 1) →
      (∀ a b, ‖(p a : V) - p b‖ ≤ δ) →
      ∀ q : s, (q : V) = ∑ a, w a • (p a : V) →
        ‖(∑ a, w a • f (p a)) - f q‖ < ε := by
  obtain ⟨η, hη, hηf⟩ := Metric.uniformContinuous_iff.mp hf (ε / 2) (half_pos hε)
  refine ⟨η / 2, half_pos hη, fun {β} _ p w hw hsum hp q hq => ?_⟩
  have hnear (a : β) : ‖(p a : V) - q‖ ≤ η / 2 := by
    have heq : (p a : V) - q = ∑ b, w b • ((p a : V) - p b) := by
      simp [smul_sub, sum_sub_distrib, ← sum_smul, hsum, hq]
    rw [heq]
    exact norm_sum_smul_le (fun b _ => hw b) (by simpa using hsum) (fun b _ => hp a b)
  have herr (a : β) : ‖f (p a) - f q‖ ≤ ε / 2 := by
    simpa only [dist_eq_norm] using (hηf (by
      simpa only [Subtype.dist_eq, dist_eq_norm] using
        (hnear a).trans_lt (half_lt_self hη))).le
  have heq : (∑ a, w a • f (p a)) - f q = ∑ a, w a • (f (p a) - f q) := by
    simp [smul_sub, sum_sub_distrib, ← sum_smul, hsum]
  rw [heq]
  exact (norm_sum_smul_le (fun a _ => hw a) (by simpa using hsum)
    (fun a _ => herr a)).trans_lt (half_lt_self hε)
