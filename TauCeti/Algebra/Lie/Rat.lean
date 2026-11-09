/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Basic
public import Mathlib.Algebra.Module.Rat

/-!
# Rational scalars in a Lie ring and its modules

The action of a Lie ring on a Lie ring module (in particular, the bracket of a Lie ring) is
biadditive, so it commutes with multiplication by rational scalars whenever the additive groups
involved are `ℚ`-modules, with no `LieAlgebra ℚ` or `LieModule ℚ L M` structure assumed. This lets
divided powers such as `Dⁿ x / n!` be moved through brackets in a Lie algebra over an arbitrary
commutative ring whose additive group happens to be a `ℚ`-module.

## Main results

* `TauCeti.rat_smul_lie`: `⁅q • x, m⁆ = q • ⁅x, m⁆`.
* `TauCeti.lie_rat_smul`: `⁅x, q • m⁆ = q • ⁅x, m⁆`.
-/

public section

namespace TauCeti

variable {L M : Type*} [LieRing L] [AddCommGroup M] [LieRingModule L M]

/-- `⁅q • x, m⁆ = q • ⁅x, m⁆` for a rational scalar `q`, since the Lie action is additive in the
acting argument. -/
theorem rat_smul_lie [Module ℚ L] [Module ℚ M] (q : ℚ) (x : L) (m : M) :
    ⁅q • x, m⁆ = q • ⁅x, m⁆ :=
  map_rat_smul (AddMonoidHom.mk' (fun z : L => ⁅z, m⁆) fun a b => add_lie a b m) q x

/-- `⁅x, q • m⁆ = q • ⁅x, m⁆` for a rational scalar `q`, since the Lie action is additive in the
module argument. -/
theorem lie_rat_smul [Module ℚ M] (q : ℚ) (x : L) (m : M) : ⁅x, q • m⁆ = q • ⁅x, m⁆ :=
  map_rat_smul (AddMonoidHom.mk' (fun z : M => ⁅x, z⁆) fun a b => lie_add x a b) q m

end TauCeti
