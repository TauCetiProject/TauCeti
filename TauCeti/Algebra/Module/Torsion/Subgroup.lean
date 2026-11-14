/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Module.Torsion.Free

/-!
# Torsion-freeness of additive subgroups

Every additive subgroup `H` of a `ℤ`-torsion-free abelian group `G` inherits `ℤ`-torsion-freeness
along `H.subtype` (`AddSubgroup.instIsTorsionFree`), matching `Submodule.instIsTorsionFree`.
-/

public section

namespace AddSubgroup

/-- An additive subgroup of a torsion-free abelian group is torsion-free over `ℤ`. -/
instance instIsTorsionFree {G : Type*} [AddCommGroup G] [Module.IsTorsionFree ℤ G]
    (H : AddSubgroup G) : Module.IsTorsionFree ℤ H :=
  H.subtype_injective.moduleIsTorsionFree H.subtype fun _ _ ↦ rfl

end AddSubgroup
