/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.Finiteness.Prod
public import TauCeti.Analysis.Convex.Polyhedron.Basic
public import TauCeti.Geometry.Convex.Cone.FiniteGeneration
public import TauCeti.Analysis.Convex.Homogenization

/-!
# Homogenization of convex polyhedra

In a finite-dimensional Hausdorff space, the homogenization of a convex polyhedron is a
finitely generated cone (`TauCeti.IsConvexPolyhedron.fg_homogenization`).
The general affine-inequality description of homogenization is developed in
`TauCeti.Analysis.Convex.Homogenization`.

## Provenance

Adapted from `Mei/Geometry/Convex/Polyhedron/Homogenization/Inequalities.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca`, licensed under Apache 2.0.
-/

public section

open Set

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V]

namespace TauCeti

/-- **Homogenization of a convex polyhedron.** In a finite-dimensional Hausdorff space, the
homogenization of a convex polyhedron is a finitely generated cone. -/
theorem IsConvexPolyhedron.fg_homogenization [ContinuousSMul ℝ V] [T2Space V] [Module.Finite ℝ V]
    {P : Set V} (hP : IsConvexPolyhedron P) : P.homogenization.FG := by
  classical
  obtain ⟨n, g, rfl⟩ := isConvexPolyhedron_iff.mp hP
  rcases Set.eq_empty_or_nonempty {x : V | ∀ i, g i x ≤ 0} with h | hne
  · rw [h, homogenization_empty]
    exact Submodule.fg_bot
  · rw [homogenization_setOf_forall_eq g hne]
    -- The cone is cut out by the finitely many functionals `snd` and `-homogenize (g i)`.
    refine PointedCone.DualFG.fg (p := LinearMap.id)
      ⟨insert (LinearMap.snd ℝ V ℝ) (Finset.univ.image fun i => -(g i).homogenize.toLinearMap),
        ?_⟩
    ext z
    simp [PointedCone.mem_dual]

end TauCeti
