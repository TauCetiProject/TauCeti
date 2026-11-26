/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Topology.Algebra.Group.ZPow

/-!
# `ZMod n`-scalars act continuously

The scalars of `ZMod n` act on a `ZMod n`-module through integer multiples, so they act
continuously on a topological `ZMod n`-module whose addition is continuous. This is the `ZMod n`
counterpart of Mathlib's `AddGroup.continuousConstSMul_int`.

## Main results

* `TauCeti.ZMod.continuousConstSMul`: a topological additive group that is a `ZMod n`-module has
  continuous `ZMod n`-scalars.
-/

public section

namespace TauCeti.ZMod

/-- The scalars of `ZMod n` act continuously on a topological `ZMod n`-module: they act through
integer multiples. -/
instance continuousConstSMul {n : ℕ} {M : Type*} [AddCommGroup M] [Module (ZMod n) M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] : ContinuousConstSMul (ZMod n) M where
  continuous_const_smul c := (continuous_zsmul (c.cast : ℤ)).congr fun m ↦ by
    rw [← Int.cast_smul_eq_zsmul (ZMod n), ZMod.intCast_zmod_cast]

end TauCeti.ZMod
