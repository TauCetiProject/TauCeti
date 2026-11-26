/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.WithLp
public import Mathlib.LinearAlgebra.FreeModule.Basic

/-!
# Free-module instance on `WithLp`

Mathlib's `Mathlib.Analysis.Normed.Lp.WithLp` transfers `Module.Finite` across `WithLp.linearEquiv`
(`WithLp.instModuleFinite`), without importing `Mathlib.LinearAlgebra.FreeModule.Basic`. This file
supplies the companion `Module.Free` instance `WithLp.instModuleFree`.
-/

public section

open scoped ENNReal

namespace WithLp

/-- `WithLp p V` is a free `K`-module whenever `V` is, via `WithLp.linearEquiv`. -/
instance instModuleFree {p : ℝ≥0∞} {K V : Type*}
    [Semiring K] [AddCommGroup V] [Module K V] [Module.Free K V] :
    Module.Free K (WithLp p V) :=
  Module.Free.of_equiv (WithLp.linearEquiv p K V).symm

end WithLp
