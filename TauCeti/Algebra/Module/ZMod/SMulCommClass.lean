/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZMod

/-!
# `ZMod n`-scalars commute with every additive action

A `ZMod n`-module structure on an abelian group is unique, and every additive endomorphism is
`ZMod n`-linear for it (`ZMod.map_smul`). So any distributive action on a `ZMod n`-module commutes
with the `ZMod n`-scalars. These are the `ZMod n` counterparts of Mathlib's
`AddMonoid.nat_smulCommClass` and `AddGroup.int_smulCommClass`, and they supply the linearity
hypothesis of a `G`-module with `ZMod n` coefficients.

## Main results

* `TauCeti.ZMod.smulCommClass`, `TauCeti.ZMod.smulCommClass'`: a distributive action on a
  `ZMod n`-module commutes with the `ZMod n`-scalars.
-/

public section

namespace TauCeti.ZMod

variable {n : ℕ} {M A : Type*} [AddCommGroup A] [Module (ZMod n) A] [DistribSMul M A]

/-- A distributive action on a `ZMod n`-module commutes with the `ZMod n`-scalars, each operator
being additive and hence `ZMod n`-linear. -/
instance smulCommClass : SMulCommClass (ZMod n) M A where
  smul_comm c x y := (ZMod.map_smul (DistribSMul.toAddMonoidHom A x) c y).symm

-- `SMulCommClass.symm` is not registered as an instance, as it would cause a loop
/-- A distributive action on a `ZMod n`-module commutes with the `ZMod n`-scalars. -/
instance smulCommClass' : SMulCommClass M (ZMod n) A :=
  .symm _ _ _

end TauCeti.ZMod
