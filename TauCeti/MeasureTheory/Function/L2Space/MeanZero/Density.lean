/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Measure.Regular
public import TauCeti.MeasureTheory.Function.L2Space.MeanZero
import TauCeti.Analysis.InnerProductSpace.Projection.Completeness
import TauCeti.MeasureTheory.Function.Lp.Const

/-!
# Density of bounded continuous mean-zero functions in `L²₀`

On a normal space `X` with its Borel σ-algebra, a weakly regular finite measure `P`, and a Hilbert
space `E` such that either `X` or `E` is second-countable (`SecondCountableTopologyEither X E`),
centering the dense subspace `BoundedContinuousFunction.toLp_denseRange` along the orthogonal
projection onto `MeasureTheory.Measure.meanZeroL2` shows that bounded continuous mean-zero
functions are dense in `L²₀(P)`.

## Main results

* `MeasureTheory.Measure.meanZeroL2_subset_closure_boundedContinuous`: density of bounded
  continuous mean-zero elements in `L²₀(P)`, obtained by centering
  `BoundedContinuousFunction.toLp_denseRange` when `X` or `E` is second-countable.
-/

public section

noncomputable section

open MeasureTheory Set Topology
open scoped BoundedContinuousFunction

namespace MeasureTheory.Measure

variable {X : Type*} [MeasurableSpace X]

/-- On a normal space `X` with its Borel σ-algebra, a weakly regular finite measure `P`, and a
Hilbert space `E` such that either `X` or `E` is second-countable
(`SecondCountableTopologyEither X E`), bounded continuous mean-zero functions are dense in
`L²₀(P)`, obtained by centering `BoundedContinuousFunction.toLp_denseRange`. -/
theorem meanZeroL2_subset_closure_boundedContinuous (P : Measure X) [IsFiniteMeasure P]
    (𝕜 : Type*) {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [CompleteSpace E] [NormedSpace ℝ E]
    [TopologicalSpace X] [NormalSpace X] [BorelSpace X] [SecondCountableTopologyEither X E]
    [P.WeaklyRegular] :
    (meanZeroL2 P 𝕜 (E := E) : Set (Lp E 2 P)) ⊆
      closure {u | u ∈ meanZeroL2 P 𝕜 ∧ ∃ g : X →ᵇ E, (u : X → E) =ᵐ[P] g} := by
  rw [← (meanZeroL2 P 𝕜 (E := E)).closure_image_starProjection_of_dense
    (BoundedContinuousFunction.toLp_denseRange E P 𝕜 (p := 2) (by norm_num))]
  refine closure_mono ?_
  rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
  refine ⟨Submodule.starProjection_apply_mem _ _, ?_⟩
  set c := ⨍ x, (BoundedContinuousFunction.toLp 2 P 𝕜 g : X → E) x ∂P
  refine ⟨g - BoundedContinuousFunction.const X c, ?_⟩
  rw [starProjection_meanZeroL2_eq_sub_const_average]
  filter_upwards [Lp.coeFn_sub_const (BoundedContinuousFunction.toLp 2 P 𝕜 g) c,
    BoundedContinuousFunction.coeFn_toLp 2 P 𝕜 g] with x hsub hg
  rw [hsub, hg]
  simp only [FunLike.coe_sub, BoundedContinuousFunction.const_apply, Pi.sub_apply]

end MeasureTheory.Measure
