/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.L2Space
public import TauCeti.Analysis.InnerProductSpace.Adjoint

/-!
# The adjoint of a Hölder multiplication operator on `L²`

Let `B : E →L[ℝ] F →L[ℝ] G` be a continuous bilinear map into real Hilbert spaces and
`b ∈ L^∞(μ; E)` an essentially bounded coefficient. Hölder multiplication
`f ↦ B(b, f) = ContinuousLinearMap.holderL μ ∞ 2 2 B b f` is a bounded operator from `L²(μ; F)` to
`L²(μ; G)`. Its Hilbert space adjoint is Hölder multiplication by the pointwise adjoints
`B(b x, ·)† : G →L[ℝ] F`, that is by the bilinear map `adjointRealCLM ∘L B`
(`ContinuousLinearMap.adjoint_holderL_apply`): pairing in `L²` is integration of the pointwise
pairings, and at each point `⟪h, B(b x, f)⟫ = ⟪B(b x, ·)† h, f⟫`.

For instance, multiplication by a field of matrices is adjoint to multiplication by the field of
transposed matrices, as for the zeroth-order part of a first-order differential operator and of its
formal adjoint.
-/

public section

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace ContinuousLinearMap

variable {α E F G : Type*} {mα : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]

/-- **The adjoint of a Hölder multiplication operator.** For a continuous bilinear map
`B : E →L[ℝ] F →L[ℝ] G` into real Hilbert spaces and `b ∈ L^∞(μ; E)`, the Hilbert space adjoint
of multiplication `f ↦ B(b, f)` from `L²(μ; F)` to `L²(μ; G)` is multiplication by the pointwise
adjoints `B(b x, ·)†`. -/
theorem adjoint_holderL_apply (B : E →L[ℝ] F →L[ℝ] G) (b : Lp E ∞ μ) (h : Lp G 2 μ) :
    adjoint (B.holderL μ ∞ 2 2 b) h = (adjointRealCLM ∘L B).holderL μ ∞ 2 2 b h := by
  refine ext_inner_right ℝ fun f ↦ ?_
  rw [adjoint_inner_left, L2.inner_def, L2.inner_def, holderL_apply_apply, holderL_apply_apply]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_holder (r := 2) B b f, coeFn_holder (r := 2) (adjointRealCLM ∘L B) b h]
    with x h₁ h₂
  rw [h₁, h₂, comp_apply, adjointRealCLM_apply, adjoint_inner_left]

end ContinuousLinearMap
