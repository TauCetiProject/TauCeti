/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.Defs
public import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# The finite simplex of nonnegative real weights

The finite simplex `Convexity.StdSimplex ℝ≥0 ι` carries the topology induced by its weight
vector. This makes continuity of probability vectors equivalent to continuity of their weights,
including at zero weights. The weights also sum to one after casting them to `ℝ`.

This is the finite-coordinate construction of Mathlib's
`Convexity.StdSimplex.topologicalSpaceInduced`. That construction requires a coefficient ring
and therefore does not apply to `ℝ≥0`.
-/

public section

open Topology
open scoped NNReal

namespace Convexity.StdSimplex

variable {X : Type*}

/-- The weights of a point of a standard simplex over `ℝ≥0`, cast to `ℝ`, sum to `1`. -/
theorem sum_coe_weights [Fintype X] (p : StdSimplex ℝ≥0 X) : ∑ i, (p.weights i : ℝ) = 1 := by
  exact_mod_cast p.total_of_fintype

/-- Scaling the real weights of a point of a standard simplex over `ℝ≥0` by `c` gives weights
summing to `c`. -/
theorem sum_mul_coe_weights [Fintype X] (p : StdSimplex ℝ≥0 X) (c : ℝ) :
    ∑ i, c * (p.weights i : ℝ) = c := by
  rw [← Finset.mul_sum, sum_coe_weights, mul_one]


variable {ι : Type*} [Finite ι]

/-- The coordinate topology on the finite simplex of nonnegative real weights. -/
noncomputable instance instTopologicalSpaceNNReal (ι : Type*) [Finite ι] :
    TopologicalSpace (StdSimplex ℝ≥0 ι) :=
  .induced (fun (p : StdSimplex ℝ≥0 ι) i ↦ Finsupp.equivFunOnFinite p.weights i) inferInstance

/-- The finite nonnegative-real simplex embeds into its space of weight vectors. -/
theorem isEmbedding_toFun_comp_weights_nnreal :
    IsEmbedding (fun p : StdSimplex ℝ≥0 ι ↦ (p.weights : ι → ℝ≥0)) where
  eq_induced := by simp only [instTopologicalSpaceNNReal, Finsupp.equivFunOnFinite_apply]
  injective _ _ h := StdSimplex.ext (Finsupp.ext (congrFun h))

/-- Continuity into the finite nonnegative-real simplex is continuity of the weight vector. -/
theorem continuous_iff_toFun_comp_weights_nnreal {X : Type*} [TopologicalSpace X]
    {f : X → StdSimplex ℝ≥0 ι} :
    Continuous f ↔ Continuous (fun x ↦ ((f x).weights : ι → ℝ≥0)) :=
  isEmbedding_toFun_comp_weights_nnreal.continuous_iff

/-- Every weight is continuous on the finite nonnegative-real simplex. -/
@[fun_prop]
theorem continuous_weights_apply_nnreal (i : ι) :
    Continuous (fun p : StdSimplex ℝ≥0 ι ↦ p.weights i) :=
  (continuous_apply i).comp isEmbedding_toFun_comp_weights_nnreal.continuous

end Convexity.StdSimplex
