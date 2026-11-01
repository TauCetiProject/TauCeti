/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Projectivization.Action
public import TauCeti.Topology.Algebra.Matrix.SpecialLinearGroup
public import TauCeti.Topology.Algebra.Projectivization

/-!
# Continuous group actions on projective space

A group `G` acting `K`-linearly on `V` acts on the projective space `ℙ K V` by moving lines
(`Projectivization.smul_mk`). When `G` is a topological space acting jointly continuously on `V`,
and scalar multiplication by units of `K` is continuous on `V`, the action on `ℙ K V` is jointly
continuous in the group element and the line. The map
`G × {v : V // v ≠ 0} → G × ℙ K V` is a product of open quotient maps, hence a quotient map, and
the action lifts through it to `(g, v) ↦ [g • v]`.

For matrix groups this gives the jointly continuous actions of `GL(n, K)` and `SL(n, K)` on
`ℙ K (n → K)` over a topological field. The projective special linear group
`PSL(n, K) = SL(n, K) ⧸ Z(SL(n, K))`, with its quotient topology, then acts jointly continuously
as well, because `SL(n, K) → PSL(n, K)` is an open quotient map. Over `ℂ` and `n = 2` these are
the continuous Möbius actions on `ℂℙ¹`, which transport to the Riemann sphere `OnePoint ℂ`
(`OnePoint.instContinuousSMulGL` and `OnePoint.instContinuousSMulPSL`).

## Main results

* `Projectivization.instContinuousSMul`: a jointly continuous linear action on `V` induces a jointly
  continuous action on `ℙ K V`; for instance by `GL n K` or `SL(n, K)` on `ℙ K (n → K)`.
* `Projectivization.instContinuousSMulPSL`: `PSL(n, K)` acts jointly continuously on
  `ℙ K (n → K)`.
-/

public section

open Topology
open scoped LinearAlgebra.Projectivization MatrixGroups

namespace Projectivization

section DivisionRing

variable {G K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] [TopologicalSpace V]
  [ContinuousConstSMul Kˣ V] [Group G] [DistribMulAction G V] [SMulCommClass G K V]
  [TopologicalSpace G] [ContinuousSMul G V]

/-- A group acting `K`-linearly and jointly continuously on `V` acts jointly continuously on the
projective space `ℙ K V`, provided scalar multiplication by units of `K` is continuous on `V`. -/
instance instContinuousSMul : ContinuousSMul G (ℙ K V) where
  continuous_smul := by
    rw [(IsOpenQuotientMap.id.prodMap isOpenQuotientMap_mk').isQuotientMap.continuous_iff]
    -- On representatives the action is `(g, v) ↦ [g • v]` (`Projectivization.smul_mk`).
    exact continuous_mk (continuous_fst.smul (continuous_subtype_val.comp continuous_snd))
      fun p ↦ (smul_ne_zero_iff_ne p.1).2 p.2.2

end DivisionRing

section Field

variable {n K : Type*} [Fintype n] [DecidableEq n] [Field K] [TopologicalSpace K]
  [IsTopologicalRing K]

/-- Over a topological field, the projective special linear group `PSL(n, K)`, with the quotient
topology of `SL(n, K) ⧸ Z(SL(n, K))`, acts jointly continuously on `ℙ K (n → K)`. -/
instance instContinuousSMulPSL :
    ContinuousSMul (Matrix.ProjectiveSpecialLinearGroup n K) (ℙ K (n → K)) where
  continuous_smul := by
    rw [(QuotientGroup.isOpenQuotientMap_mk.prodMap
      IsOpenQuotientMap.id).isQuotientMap.continuous_iff]
    -- The class of `g ∈ SL(n, K)` acts as `g` does
    -- (`Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk`).
    exact continuous_smul (M := Matrix.SpecialLinearGroup n K) (X := ℙ K (n → K))

end Field

end Projectivization
