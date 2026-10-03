/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.Bounded
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-!
# Products of von Neumann bounded sets

A product `s ×ˢ t` of von Neumann bounded subsets of two topological vector spaces is von Neumann
bounded in the product space. This is used to check the boundedness condition in Mathlib's
`Bundle.RiemannianMetric` for the product of two Riemannian metrics.
-/

public section

open Set

namespace Bornology

variable {𝕜 E F : Type*} [NormedDivisionRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F]

/-- A product of von Neumann bounded sets is von Neumann bounded. -/
protected theorem IsVonNBounded.prod {s : Set E} {t : Set F} (hs : IsVonNBounded 𝕜 s)
    (ht : IsVonNBounded 𝕜 t) : IsVonNBounded 𝕜 (s ×ˢ t) := by
  refine ((hs.image (ContinuousLinearMap.inl 𝕜 E F)).add
    (ht.image (ContinuousLinearMap.inr 𝕜 E F))).subset ?_
  rintro ⟨a, b⟩ ⟨ha, hb⟩
  exact ⟨(a, 0), ⟨a, ha, rfl⟩, (0, b), ⟨b, hb, rfl⟩, by simp⟩

end Bornology
