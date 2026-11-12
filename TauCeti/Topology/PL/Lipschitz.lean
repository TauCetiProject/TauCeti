/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Lipschitz
public import TauCeti.Topology.PL.Compact

/-!
# Lipschitz regularity of piecewise-affine maps

A map with a finite piecewise-affine decomposition is Lipschitz on a convex set.
The affine pieces can meet along faces where the map is not differentiable. The
finite-closed-cover estimate combines their operator norm bounds without requiring
any control on the number of pieces a segment crosses.

Consequently a locally PL map on a compact convex subset of a finite real coordinate
space is Lipschitz. This connects local polyhedral descriptions to the metric estimates
used in comparing triangulations.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Chapters 1–2.
* J. Munkres, *Elementary Differential Topology*, Chapter II, Section 9.
-/

public section

open Set
open scoped NNReal

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {s : Set E}

/-- A finite piecewise-affine decomposition on a convex set gives a global Lipschitz
bound. No finite-dimensionality or compactness assumption is needed. -/
theorem IsPiecewiseAffineOn.exists_lipschitzOnWith (hf : IsPiecewiseAffineOn f s)
    (hs : Convex ℝ s) : ∃ K, LipschitzOnWith K f s := by
  obtain ⟨n, C, A, hC, hcover, heq⟩ := isPiecewiseAffineOn_iff.mp hf
  refine ⟨∑ i, ‖(A i).contLinear‖₊,
    hs.lipschitzOnWith_of_finite_closed_cover C (fun i => (hC i).isClosed) hcover fun i => ?_⟩
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  rw [heq i hx, heq i hy, dist_eq_norm, dist_eq_norm,
    ← vsub_eq_sub (A i x) (A i y), ← (A i).contLinear_apply_vsub, vsub_eq_sub]
  exact ((A i).contLinear.le_opNorm (x - y)).trans <|
    mul_le_mul_of_nonneg_right (by
      exact_mod_cast Finset.single_le_sum
        (f := fun j : Fin n => ‖(A j).contLinear‖₊) (fun _ _ => zero_le)
        (Finset.mem_univ i)) (norm_nonneg _)

/-- A locally PL map on a compact convex subset of a finite real coordinate space is
Lipschitz on that set. -/
theorem IsPLOn.exists_lipschitzOnWith_of_isCompact {ι : Type*} [Fintype ι]
    {f : (ι → ℝ) → F} {s : Set (ι → ℝ)} (hf : IsPLOn f s)
    (hcompact : IsCompact s) (hconv : Convex ℝ s) : ∃ K, LipschitzOnWith K f s :=
  (hf.isPiecewiseAffineOn_of_isCompact hcompact).exists_lipschitzOnWith hconv

end TauCeti
