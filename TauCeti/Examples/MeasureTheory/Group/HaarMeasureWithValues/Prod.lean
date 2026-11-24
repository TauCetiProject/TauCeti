/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.MeasureTheory.Group.HaarMeasureWithValues.Prod

/-!
# Examples of products of Haar measures with values in a ring

* If `μ` and `ν` count points, then `μ.prod ν` counts the points of a rectangle.
* A product with the zero measure is the zero measure.
* The slice of a rectangle `U ×ˢ V` at a point of `U` is `V`.
-/

open TopologicalSpace

namespace TauCeti.HaarMeasureWithValues

variable {G H : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G] [T2Space G]
  [Group H] [TopologicalSpace H] [ContinuousMul H] [T2Space H]

/-! ### Counting volumes -/

example (μ : HaarMeasureWithValues ℕ G) (ν : HaarMeasureWithValues ℕ H)
    (hμ : ∀ K, μ K = (K : Set G).ncard) (hν : ∀ K, ν K = (K : Set H).ncard)
    (U : CompactOpens G) (V : CompactOpens H) :
    μ.prod ν (U ×ˢ V) = ((U ×ˢ V : CompactOpens (G × H)) : Set (G × H)).ncard := by
  rw [prod_apply_prod, hμ, hν, CompactOpens.coe_prod, Set.ncard_prod]

/-! ### The zero measure -/

example (A : Type*) [Semiring A] (ν : HaarMeasureWithValues A H) (K : CompactOpens (G × H)) :
    (0 : HaarMeasureWithValues A G).prod ν K = 0 := by
  simp

example (A : Type*) [Semiring A] (μ : HaarMeasureWithValues A G) (K : CompactOpens (G × H)) :
    μ.prod (0 : HaarMeasureWithValues A H) K = 0 := by
  simp

/-! ### Slices -/

example (U : CompactOpens G) (V : CompactOpens H) {g : G} (hg : g ∈ U) :
    (U ×ˢ V).slice g = V := by
  simp [hg]

end TauCeti.HaarMeasureWithValues
