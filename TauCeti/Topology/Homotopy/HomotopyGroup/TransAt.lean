/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Evaluating concatenations of generalized loops

Mathlib's `GenLoop.transAt i f g` concatenates two generalized loops along the `i`-th cube
direction, running `f` on `tᵢ ≤ 1/2` and `g` on `tᵢ ≥ 1/2`, each at double speed. Its defining
formula clamps the rescaled coordinate with `Set.projIcc`. This file states the two halves of
that formula without the clamp: on each half, the concatenation is `f` or `g` evaluated at the
point whose `i`-th coordinate is replaced by any `a` with the rescaled value.

## Main declarations

* `GenLoop.transAt_apply_of_le`: on the first half, `transAt i f g` runs `f` at double speed.
* `GenLoop.transAt_apply_of_lt`: on the second half, `transAt i f g` runs `g` at double speed.
-/

public section

open scoped unitInterval Topology Topology.Homotopy
open Topology.Homotopy

namespace GenLoop

variable {N X : Type*} [TopologicalSpace X] {x : X} [DecidableEq N]

/-- On the first half of the `i`-th direction, `transAt i f g` runs `f` at double speed. -/
theorem transAt_apply_of_le (i : N) (f g : Ω^ N X x) {t : I^N} (h : (t i : ℝ) ≤ 1 / 2) {a : I}
    (ha : (a : ℝ) = 2 * t i) :
    transAt i f g t = f (Function.update t i a) := by
  simp only [transAt, coe_copy]
  rw [ite_eq_left h, Set.projIcc_of_mem _ ⟨by rw [← ha]; exact a.2.1,
    by rw [← ha]; exact a.2.2⟩]
  exact congrArg (fun b ↦ f (Function.update t i b)) (Subtype.ext ha.symm)

/-- On the second half of the `i`-th direction, `transAt i f g` runs `g` at double speed. -/
theorem transAt_apply_of_lt (i : N) (f g : Ω^ N X x) {t : I^N} (h : 1 / 2 < (t i : ℝ)) {a : I}
    (ha : (a : ℝ) = 2 * t i - 1) :
    transAt i f g t = g (Function.update t i a) := by
  simp only [transAt, coe_copy]
  rw [ite_eq_right (not_le.2 h), Set.projIcc_of_mem _ ⟨by rw [← ha]; exact a.2.1,
    by rw [← ha]; exact a.2.2⟩]
  exact congrArg (fun b ↦ g (Function.update t i b)) (Subtype.ext ha.symm)

end GenLoop
