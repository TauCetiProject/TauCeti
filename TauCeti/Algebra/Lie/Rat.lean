/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Basic
public import Mathlib.Algebra.Module.Rat

/-!
# Rational scalars in a Lie ring

The bracket of a Lie ring is biadditive, so it commutes with multiplication by rational scalars
whenever the additive group is a `ℚ`-module, with no `LieAlgebra ℚ` structure assumed. This lets
divided powers such as `Dⁿ x / n!` be moved through brackets in a Lie algebra over an arbitrary
commutative ring whose additive group happens to be a `ℚ`-module.

## Main results

* `TauCeti.rat_smul_lie`: `⁅q • x, y⁆ = q • ⁅x, y⁆`.
* `TauCeti.lie_rat_smul`: `⁅x, q • y⁆ = q • ⁅x, y⁆`.
-/

public section

namespace TauCeti

variable {L : Type*} [LieRing L] [Module ℚ L]

/-- `⁅q • x, y⁆ = q • ⁅x, y⁆` for a rational scalar `q`. -/
theorem rat_smul_lie (q : ℚ) (x y : L) : ⁅q • x, y⁆ = q • ⁅x, y⁆ :=
  map_rat_smul (AddMonoidHom.mk' (fun z : L => ⁅z, y⁆) fun a b => add_lie a b y) q x

/-- `⁅x, q • y⁆ = q • ⁅x, y⁆` for a rational scalar `q`. -/
theorem lie_rat_smul (q : ℚ) (x y : L) : ⁅x, q • y⁆ = q • ⁅x, y⁆ :=
  map_rat_smul (AddMonoidHom.mk' (fun z : L => ⁅x, z⁆) fun a b => lie_add x a b) q y

end TauCeti
