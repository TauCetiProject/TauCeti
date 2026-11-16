/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Submodule
public import Mathlib.Analysis.Normed.MulAction

/-!
# Bounded scalar actions on submodules of seminormed modules

Mathlib equips submodules and closed submodules of a seminormed module over a ring with the
restricted seminorm (`Submodule.seminormedAddCommGroup`, `ClosedSubmodule.seminormedAddCommGroup`),
and equips them with `NormedSpace` when the scalar ring is a normed field
(`Submodule.normedSpace`, `ClosedSubmodule.normedSpace`). When the scalars form a general
seminormed ring acting with `IsBoundedSMul`, the restricted action on any submodule or closed
submodule is again contractive (`IsBoundedSMul`), because the norm of a subtype element equals its
ambient norm.

Mathlib's group structure on a closed submodule of a seminormed group comes from
`ClosedSubmodule.seminormedAddCommGroup`, since `ClosedSubmodule` is only an
`AddSubmonoidClass`; `ClosedSubmodule.coe_neg` and `ClosedSubmodule.coe_sub` compute the ambient
value of a negation and a difference.
-/

public section

namespace ClosedSubmodule

variable {R M : Type*} [Ring R] [SeminormedAddCommGroup M] [Module R M] {S : ClosedSubmodule R M}

/-- The ambient value of a negation in a closed submodule of a seminormed group. -/
@[simp, norm_cast]
theorem coe_neg (x : S) : ((-x : S) : M) = -(x : M) :=
  (rfl)

/-- The ambient value of a difference in a closed submodule of a seminormed group. -/
@[simp, norm_cast]
theorem coe_sub (x y : S) : ((x - y : S) : M) = (x : M) - y :=
  (rfl)

end ClosedSubmodule

variable {R M : Type*} [SeminormedRing R] [SeminormedAddCommGroup M] [Module R M]
  [IsBoundedSMul R M]

/-- A submodule of a seminormed module with a bounded scalar action inherits a bounded scalar
action under the subspace norm. -/
instance Submodule.instIsBoundedSMul (S : Submodule R M) : IsBoundedSMul R S :=
  IsBoundedSMul.of_norm_smul_le fun r x ↦ norm_smul_le r (x : M)

/-- A closed submodule of a seminormed module with a bounded scalar action inherits a bounded
scalar action under the subspace norm. -/
instance ClosedSubmodule.instIsBoundedSMul (S : ClosedSubmodule R M) : IsBoundedSMul R S :=
  IsBoundedSMul.of_norm_smul_le fun r x ↦ norm_smul_le r (x : M)
