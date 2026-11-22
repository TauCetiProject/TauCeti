/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Completion
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.SpecificLimits.Basic
import TauCeti.Analysis.Normed.Group.InfiniteSum

/-!
# Absolutely convergent series in the completion of a seminormed group

Every point `u` of the completion of a seminormed group `V` is the sum of a series of points of
`V` whose norms have sum less than any prescribed `c > ‖u‖`. The series is obtained from
`DenseRange.exists_hasSum_norm_lt` applied to `UniformSpace.Completion.toCompl`. Applied to the
completion of an algebraic tensor product, this is the step that turns finite decompositions of
algebraic tensors into series decompositions of completed tensors.

## Main results

* `UniformSpace.Completion.exists_hasSum_coe_of_norm_lt`: if `‖u‖ < c`, then `u = ∑ n, v n` for
  some `v : ℕ → V` with `∑ n, ‖v n‖ < c`.
-/

public section

open Filter Topology

namespace UniformSpace.Completion

variable {V : Type*} [SeminormedAddCommGroup V]

/-- Every point `u` of the completion of a seminormed group `V` is the sum of a series of points
of `V` whose norms have sum less than any prescribed bound `c > ‖u‖`. -/
theorem exists_hasSum_coe_of_norm_lt (u : Completion V) {c : ℝ} (hu : ‖u‖ < c) :
    ∃ v : ℕ → V, HasSum (fun n ↦ (v n : Completion V)) u ∧ Summable (fun n ↦ ‖v n‖) ∧
      ∑' n, ‖v n‖ < c := by
  simpa only [toCompl_apply, norm_coe] using
    (denseRange_coe (α := V)).exists_hasSum_norm_lt (f := (toCompl : V →+ Completion V)) u hu

end UniformSpace.Completion
