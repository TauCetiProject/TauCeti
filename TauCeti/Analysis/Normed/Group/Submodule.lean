/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Submodule
public import TauCeti.Topology.MetricSpace.Algebra

/-!
# Bounded scalar actions on submodules

Mathlib equips submodules and closed submodules of a seminormed module over a ring with the
restricted seminorm (`Submodule.seminormedAddCommGroup`, `ClosedSubmodule.seminormedAddCommGroup`),
and equips them with `NormedSpace` when the scalar ring is a normed field
(`Submodule.normedSpace`, `ClosedSubmodule.normedSpace`). More generally, whenever scalars `𝕜`
with a pseudometric act boundedly on a pseudometric `R`-module `M` (`IsBoundedSMul 𝕜 M`)
compatibly with `R` (`IsScalarTower 𝕜 R M`), the restricted action on any submodule or closed
submodule is again bounded (`Submodule.instIsBoundedSMul`, `ClosedSubmodule.instIsBoundedSMul`).
Both specialize `SetLike.instIsBoundedSMul`, which on its own finds only the scalars `R` recorded
by `SMulMemClass`. They also apply to the restricted seminorm of a seminormed module, whose distance
is the restricted distance.

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

variable {𝕜 R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [PseudoMetricSpace M]
  [Zero 𝕜] [PseudoMetricSpace 𝕜] [SMul 𝕜 R] [SMul 𝕜 M] [IsScalarTower 𝕜 R M]
  [IsBoundedSMul 𝕜 M]

/-- A bounded scalar action of `𝕜` on an `R`-module, compatible with `R`, restricts to a bounded
scalar action on any submodule under the subspace distance. -/
instance Submodule.instIsBoundedSMul (S : Submodule R M) : IsBoundedSMul 𝕜 S :=
  haveI := SMulMemClass.ofIsScalarTower (Submodule R M) 𝕜 R M
  SetLike.instIsBoundedSMul S

/-- A bounded scalar action of `𝕜` on an `R`-module, compatible with `R`, restricts to a bounded
scalar action on any closed submodule under the subspace distance. -/
instance ClosedSubmodule.instIsBoundedSMul (S : ClosedSubmodule R M) : IsBoundedSMul 𝕜 S :=
  haveI := SMulMemClass.ofIsScalarTower (ClosedSubmodule R M) 𝕜 R M
  SetLike.instIsBoundedSMul S
