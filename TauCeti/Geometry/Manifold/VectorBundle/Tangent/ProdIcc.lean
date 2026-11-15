/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Icc
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# The differential of the inclusion of a product with an interval

* `TauCeti.Manifold.isInvertible_mfderiv_prodMap_id_subtypeVal_Icc`: the differential of the
  inclusion `M × [a, b] → M × ℝ` is invertible, also at the boundary.
-/

public section

open Manifold Set

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {a b : ℝ} [Fact (a < b)]

/-- The differential of the inclusion `M × [a, b] → M × ℝ` is invertible, also at the boundary. -/
theorem isInvertible_mfderiv_prodMap_id_subtypeVal_Icc (p : M × Icc a b) :
    (mfderiv (I.prod (𝓡∂ 1)) (I.prod 𝓘(ℝ)) (Prod.map id Subtype.val : M × Icc a b → M × ℝ)
      p).IsInvertible :=
  isInvertible_mfderiv_prodMap mdifferentiableAt_id
    ((contMDiff_subtypeVal_Icc (n := 1)).mdifferentiableAt one_ne_zero)
    (by rw [mfderiv_id]; exact ⟨ContinuousLinearEquiv.refl ℝ _, rfl⟩)
    (TauCeti.isInvertible_mfderiv_subtypeVal_Icc p.2)

end TauCeti.Manifold
