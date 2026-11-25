/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Normed.Module.Convex

/-!
# Contractibility of the closed unit ball

The closed unit ball of a real seminormed space is convex and nonempty, hence contractible by
Mathlib's `Convex.contractibleSpace`. This file records the fact as an instance, so that
contractibility of the closed unit ball, the model cell of a CW complex, is found by instance
search. Mathlib's `Metric.contractibleSpace_closedBall` covers a general radius, but needs the
side condition `0 ≤ r`, which instance search cannot discharge.

## Main declarations

* `Metric.contractibleSpace_closedBall_one`: the closed unit ball is contractible.
-/

public section

namespace Metric

/-- The closed unit ball of a real seminormed space is contractible, being convex. -/
instance contractibleSpace_closedBall_one {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] {x : E} : ContractibleSpace (closedBall x 1) :=
  (convex_closedBall x 1).contractibleSpace ⟨x, mem_closedBall_self zero_le_one⟩

end Metric
