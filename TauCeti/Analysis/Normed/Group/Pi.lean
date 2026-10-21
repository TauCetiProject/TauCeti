/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Constructions

/-!
# The sup norm over a one-point index type

A product of seminormed groups over a one-point index type carries the sup norm of its only
coordinate: `Pi.norm_unique` and `Pi.nnnorm_unique` (with multiplicative forms `Pi.norm_unique'`
and `Pi.nnnorm_unique'`). This is the norm counterpart of `IsometryEquiv.funUnique`, and it
identifies, for example, the norm of `x : Fin 1 → ℝ` with `|x 0|`.
-/

public section

variable {ι : Type*} {G : ι → Type*} [Fintype ι] [Unique ι] [∀ i, SeminormedGroup (G i)]

/-- Over a one-point index type, the sup norm is the norm of the only coordinate. -/
@[to_additive Pi.nnnorm_unique
  /-- Over a one-point index type, the sup norm is the norm of the only coordinate. -/]
lemma Pi.nnnorm_unique' (f : ∀ i, G i) : ‖f‖₊ = ‖f default‖₊ := by
  rw [Pi.nnnorm_def', Finset.univ_unique, Finset.sup_singleton]

/-- Over a one-point index type, the sup norm is the norm of the only coordinate. -/
@[to_additive Pi.norm_unique
  /-- Over a one-point index type, the sup norm is the norm of the only coordinate. -/]
lemma Pi.norm_unique' (f : ∀ i, G i) : ‖f‖ = ‖f default‖ :=
  congrArg NNReal.toReal (Pi.nnnorm_unique' f)
