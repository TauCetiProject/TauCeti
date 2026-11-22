/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.WithLp
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.Basic

/-!
# Linear-algebraic structure on the `WithLp` type synonym

Supplies `WithLp.instModuleFree` and `WithLp.finrank_eq`.
-/

public section

open scoped ENNReal

namespace WithLp

variable (p : ℝ≥0∞) (K V : Type*) [Semiring K] [AddCommGroup V] [Module K V]

instance instModuleFree [Module.Free K V] : Module.Free K (WithLp p V) :=
  Module.Free.of_equiv (WithLp.linearEquiv p K V).symm

/-- `WithLp` does not change `Module.finrank`. -/
theorem finrank_eq : Module.finrank K (WithLp p V) = Module.finrank K V :=
  (WithLp.linearEquiv p K V).finrank_eq

end WithLp
