/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Convex.ConvexSpace.NNReal
public import TauCeti.MeasureTheory.MeasurableSpace.StdSimplex
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Measurable simplex embeddings and the nonnegative-real Borel structure

For finite coordinate types with topologically measurable coefficients, the weight map is a
measurable embedding. Its inverse extends measurably to all weight vectors by choosing a
fallback simplex point; this permits mixing distributions against simplex-supported laws.

The weight-coordinate measurable structure on `Convexity.StdSimplex ℝ≥0 ι` agrees with the
Borel structure of its coordinate topology when `ι` is finite. Thus continuous families of
probability vectors also give measurable parameters for finite laws.
-/

public section

open MeasureTheory
open scoped NNReal

namespace Convexity.StdSimplex

variable {ι : Type*} [Finite ι]

variable {R : Type*} [PartialOrder R] [Semiring R] [MeasurableSpace R]
  [TopologicalSpace R] [OpensMeasurableSpace R] [OrderClosedTopology R]
  [ContinuousAdd R] [SecondCountableTopology R]

/-- The weight vector embeds a finite standard simplex as a measurable subset of the
coordinate space. -/
theorem measurableEmbedding_toFun_comp_weights :
    MeasurableEmbedding fun p : StdSimplex R ι ↦ (p.weights : ι → R) := by
  let _ := Fintype.ofFinite ι
  refine MeasurableEmbedding.iff_comap_eq.mpr ⟨injective_toFun_comp_weights, rfl, ?_⟩
  rw [range_toFun_comp_weights]
  exact (MeasurableSet.iInter fun i ↦
    (isClosed_Ici.preimage (continuous_apply i)).measurableSet).inter
      (isClosed_eq (by fun_prop) continuous_const).measurableSet

/-- The extension of the inverse weight map is measurable, including outside the simplex. -/
@[fun_prop]
theorem measurable_extendWeights (p : StdSimplex R ι) : Measurable p.extendWeights := by
  rw [extendWeights_def]
  exact measurableEmbedding_toFun_comp_weights.measurable_extend measurable_id measurable_const

/-- The coordinate measurable structure of the finite nonnegative-real simplex is Borel. -/
instance instBorelSpaceNNReal : BorelSpace (StdSimplex ℝ≥0 ι) where
  measurable_eq := by
    simp only [instMeasurableSpace, borel_comap, Finsupp.equivFunOnFinite_apply,
      ← BorelSpace.measurable_eq (α := ι → ℝ≥0)]

end Convexity.StdSimplex
