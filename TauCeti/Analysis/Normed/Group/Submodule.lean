/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Submodule
public import Mathlib.Topology.MetricSpace.Algebra

/-!
# Bounded scalar actions on submodules of seminormed modules

Mathlib equips submodules and closed submodules of a seminormed module over a ring with the
restricted seminorm (`Submodule.seminormedAddCommGroup`, `ClosedSubmodule.seminormedAddCommGroup`),
and equips them with `NormedSpace` when the scalar ring is a normed field
(`Submodule.normedSpace`, `ClosedSubmodule.normedSpace`). More generally, whenever scalars `𝕜`
with a pseudometric act boundedly on `M` (`IsBoundedSMul 𝕜 M`) compatibly with `R`
(`IsScalarTower 𝕜 R M`), the restricted action on any submodule or closed submodule is again
bounded (`Submodule.instIsBoundedSMul`, `ClosedSubmodule.instIsBoundedSMul`), because distances
between subtype elements are their ambient distances.

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

variable {𝕜 R M : Type*} [Ring R] [SeminormedAddCommGroup M] [Module R M] [Zero 𝕜]
  [PseudoMetricSpace 𝕜] [SMul 𝕜 R] [SMul 𝕜 M] [IsScalarTower 𝕜 R M] [IsBoundedSMul 𝕜 M]

-- In both instances below, the subspace distance and the restricted action are the ambient ones
-- by definition, so each field is the ambient inequality at the coerced elements.

/-- A bounded scalar action of `𝕜` on a seminormed `R`-module, compatible with `R`, restricts to a
bounded scalar action on any submodule under the subspace norm. -/
instance Submodule.instIsBoundedSMul (S : Submodule R M) : IsBoundedSMul 𝕜 S where
  dist_smul_pair' c x y := dist_smul_pair c (x : M) y
  dist_pair_smul' c₁ c₂ x := dist_pair_smul c₁ c₂ (x : M)

/-- A bounded scalar action of `𝕜` on a seminormed `R`-module, compatible with `R`, restricts to a
bounded scalar action on any closed submodule under the subspace norm. -/
instance ClosedSubmodule.instIsBoundedSMul (S : ClosedSubmodule R M) : IsBoundedSMul 𝕜 S where
  dist_smul_pair' c x y := dist_smul_pair c (x : M) y
  dist_pair_smul' c₁ c₂ x := dist_pair_smul c₁ c₂ (x : M)
