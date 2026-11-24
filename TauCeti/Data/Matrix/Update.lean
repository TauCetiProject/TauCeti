/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Defs

/-!
# Updating one matrix of a tuple, read along a path

For a tuple `F : Fin k → Matrix X X C` and a path `x : Fin (k + 1) → X`, reading the `t`-th matrix
at the `t`-th step of the path gives the entries `F t (x t.castSucc) (x t.succ)`. Replacing the
`l`-th matrix of the tuple by `G` replaces exactly the `l`-th of these entries by
`G (x l.castSucc) (x l.succ)`. This is the step that turns the multilinearity of an operation fed
the entries along a path into the multilinearity of the corresponding operation on matrices.

## Main results

* `Matrix.update_apply_path`: updating one matrix of a tuple updates one entry along every path.
-/

public section

namespace Matrix

/-- Updating one matrix of a tuple updates one entry along every path: reading the `t`-th matrix
at the `t`-th step of a path `x`, after replacing the `l`-th matrix by `G`, replaces the `l`-th
entry by `G (x l.castSucc) (x l.succ)`. -/
theorem update_apply_path {X C : Type*} {k : ℕ} (F : Fin k → Matrix X X C)
    (x : Fin (k + 1) → X) (l : Fin k) (G : Matrix X X C) :
    (fun t => Function.update F l G t (x t.castSucc) (x t.succ)) =
      Function.update (fun t => F t (x t.castSucc) (x t.succ)) l (G (x l.castSucc) (x l.succ)) :=
  funext (Function.apply_update (fun t (G : Matrix X X C) => G (x t.castSucc) (x t.succ)) F l G)

end Matrix
