/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.DiffAdd
import Mathlib.Data.ZMod.Basic

/-!
# Examples of Montgomery differential addition

On `y² = x³ + x` over `𝔽₇` (`A = 0`, `B = 1`), the points `P = (3, 3)` and `Q = (1, 3)` have
`P - Q = (5, 5)` and `P + Q = (3, 4)`; differential addition of `(3, 1)`, `(1, 1)` and `(5, 1)`
gives `(2, 3)`, which represents `x(P + Q) = 3`. For `(1, 3)` and `(1, 4) = (1, 3) + (0, 0)` the
difference is the distinguished point of order two, and the output is `(0, 0)`. Over `𝔽₅` the
point `T = (2, 0)` has order two but is not the distinguished one, and adding infinity to it with
difference `T` gives a nonzero representative of `T`. Modulo `35` the formula is applied to pairs
over a composite modulus.
-/

namespace TauCeti.Montgomery

-- Over `𝔽₇`: the output `(2, 3)` represents `x(P + Q) = 3`.
example : diffAdd (⟨3, 1⟩ : Pair (ZMod 7)) ⟨1, 1⟩ ⟨5, 1⟩ = ⟨2, 3⟩ := by
  ext <;> simp only [diffAdd_x, diffAdd_z, Pair.cross_def] <;> decide

example : (⟨2, 3⟩ : Pair (ZMod 7)).cross ⟨3, 1⟩ = 0 := by
  rw [Pair.cross_def]
  decide

-- Over `𝔽₇`: the difference `(1, 3) - (1, 4)` is the distinguished point of order two `(0, 0)`.
example : diffAdd (⟨1, 1⟩ : Pair (ZMod 7)) ⟨1, 1⟩ ⟨0, 1⟩ = 0 := by
  ext <;> simp only [diffAdd_x, diffAdd_z, Pair.cross_def] <;> decide

-- Over `𝔽₅`: a point of order two other than `(0, 0)` is not exceptional as a difference.
example : diffAdd (⟨2, 1⟩ : Pair (ZMod 5)) ⟨1, 0⟩ ⟨2, 1⟩ = ⟨1, 3⟩ := by
  ext <;> simp only [diffAdd_x, diffAdd_z, Pair.cross_def] <;> decide

example : (⟨1, 3⟩ : Pair (ZMod 5)).cross ⟨2, 1⟩ = 0 := by
  rw [Pair.cross_def]
  decide

-- Modulo `35`: the pairs of `[2]P`, `P` and `P` for the starting pair `(22, 1)`.
example : diffAdd (⟨21, 25⟩ : Pair (ZMod 35)) ⟨22, 1⟩ ⟨22, 1⟩ = ⟨1, 8⟩ := by
  ext <;> simp only [diffAdd_x, diffAdd_z, Pair.cross_def] <;> decide

end TauCeti.Montgomery
