/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Rotating natural indices modulo the length

Natural indices can be read modulo the length of a nonempty finite ordinal through `Fin.ofNat`.
Rotating the result advances the original natural index by one, so a cyclic word indexed by
`Fin n` can be read as a periodic sequence indexed by `ℕ`.

## Main results

* `Fin.finRotate_ofNat`: rotation commutes with taking the successor of a natural index.
-/

public section

namespace Fin

open Fin.NatCast in
/-- Rotation advances a natural index by one modulo the length. -/
theorem finRotate_ofNat {n : ℕ} [NeZero n] (i : ℕ) :
    finRotate n (Fin.ofNat n i) = Fin.ofNat n (i + 1) := by
  rw [finRotate_apply, Fin.ofNat_eq_cast, Fin.ofNat_eq_cast, Nat.cast_succ]

end Fin
