/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.OpenMapping.ClosedRange
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.Analysis.Normed.Ring.ZeroSequenceOfUnits

/-!
# Closed range from a finite-dimensional cokernel

This file applies `ContinuousLinearMap.isClosed_range_of_isCompl_of_completeSpace_right` (from
`TauCeti.Topology.Algebra.OpenMapping.ClosedRange`) to prove that a continuous linear map from a
complete first-countable uniform vector space into a `T₀` Baire topological vector space over a
complete nontrivially normed field has closed range whenever its cokernel is finite dimensional,
assuming jointly continuous scalar multiplication (`ContinuousSMul`) on both spaces.

## Main results

* `ContinuousLinearMap.isClosed_range_of_finite_coker`: over a complete nontrivially normed field,
  a continuous linear map from a complete first-countable uniform vector space into a `T₀` Baire
  topological vector space (with `ContinuousSMul` on both spaces) with finite-dimensional cokernel
  has closed range.

## Attribution & References

The coproduct argument generalizes the former Banach-space proof of
`ContinuousLinearMap.isClosed_range_of_finite_coker` in
`TauCeti/Analysis/Fredholm/ClosedRange.lean`.

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, Appendix A.1 (for the
  Banach-space closed-range criterion from a finite-dimensional cokernel).
-/

public section

open Topology

namespace ContinuousLinearMap

/-- **Closed range from a finite-dimensional cokernel.** Let `f : E →L[𝕜] F` be a continuous
linear map from a complete first-countable uniform vector space `E` into a `T₀` Baire
topological vector space `F` over a complete nontrivially normed field `𝕜`, with jointly continuous
scalar multiplication (`ContinuousSMul`) on both `E` and `F`. If the cokernel `F ⧸ f.range` is
finite dimensional, then `f.range` is closed.

This applies to all Fréchet spaces, F-spaces, and Banach spaces over `ℝ`, `ℂ`, or `ℚ_[p]`, with
no local convexity, normability, or injectivity hypothesis, and requires neither completeness nor
first-countability on the ambient codomain `F`. -/
theorem isClosed_range_of_finite_coker {𝕜 E F : Type*}
    [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E]
    [(𝓝 (0 : E)).IsCountablyGenerated] [Module 𝕜 E] [ContinuousSMul 𝕜 E]
    [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F] [T0Space F] [BaireSpace F]
    [Module 𝕜 F] [ContinuousSMul 𝕜 F]
    (f : E →L[𝕜] F) [FiniteDimensional 𝕜 (F ⧸ f.range)] :
    IsClosed (f.range : Set F) := by
  obtain ⟨G, hG⟩ := f.range.exists_isCompl
  have : FiniteDimensional 𝕜 G := (f.range.quotientEquivOfIsCompl G hG).finiteDimensional
  let : UniformSpace G := IsTopologicalAddGroup.rightUniformSpace G
  have : IsUniformAddGroup G := isUniformAddGroup_of_addCommGroup
  have : CompleteSpace G := FiniteDimensional.completeSpace 𝕜 G
  have : FirstCountableTopology G := (Module.finBasis 𝕜 G).equivFun
    |>.toContinuousLinearEquiv.toHomeomorph.isInducing.firstCountableTopology
  exact f.isClosed_range_of_isCompl_of_completeSpace_right G hG
    (fun _ ↦ (continuous_id.smul continuous_const).continuousAt)
    (fun _ ↦ (continuous_id.smul continuous_const).continuousAt)

end ContinuousLinearMap

end
