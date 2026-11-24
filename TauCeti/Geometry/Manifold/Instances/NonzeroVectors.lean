/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Topology.Algebra.MulAction

/-!
# The nonzero vectors of a normed space as a manifold

The nonzero vectors `{v : E // v ≠ 0}` of a normed space `E` over a nontrivially normed field `𝕜`
form an open subset of `E`. Their inclusion into `E` is the single chart of an analytic manifold
modelled on `E`. Mathlib lets the units `𝕜ˣ` act on the nonzero vectors by scalar multiplication
(`Units.nonZeroSubMul`), and this action is by analytic maps. For `𝕜 = ℂ` the nonzero vectors are
the complex manifolds `ℂⁿ ∖ {0}`, `n ≥ 1`, connected by `TauCeti.instConnectedSpaceNonZero` in
`TauCeti.Analysis.Normed.Module.Connected`, whose quotients by free, properly discontinuous groups
of dilations are the Hopf manifolds.

## Main results

* `TauCeti.instChartedSpaceNonZero`, `TauCeti.instIsManifoldNonZero`: the nonzero vectors of `E`
  are an analytic manifold modelled on `E`, charted by the inclusion.
* `TauCeti.contMDiff_val_nonZero`, `TauCeti.contMDiff_nonZero_iff`: the inclusion is analytic, and
  a map into the nonzero vectors is `C^n` exactly when its composite with the inclusion is.
* `TauCeti.instContMDiffConstSMulNonZero`, `TauCeti.instContMDiffConstSMulSubgroupNonZero`: the
  units of `𝕜`, and every subgroup of them, act by analytic maps.
-/

public noncomputable section

open Topology
open scoped Manifold ContDiff

namespace TauCeti

section Topology

variable {E : Type*} [TopologicalSpace E] [Zero E]

/-- A nontrivial type has a nonzero element. -/
instance instNonemptyNonZero [Nontrivial E] : Nonempty {v : E // v ≠ 0} :=
  nonempty_subtype.mpr (exists_ne 0)

variable [T1Space E]

/-- The nonzero vectors are an open subset. -/
theorem isOpenEmbedding_val_nonZero : IsOpenEmbedding (Subtype.val : {v : E // v ≠ 0} → E) :=
  isOpen_ne.isOpenEmbedding_subtypeVal

/-- The nonzero vectors of `E` are charted by their inclusion into `E`. -/
instance instChartedSpaceNonZero [Nontrivial E] : ChartedSpace E {v : E // v ≠ 0} :=
  isOpenEmbedding_val_nonZero.singletonChartedSpace

end Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [Nontrivial E] {n : ℕ∞ω}

/-- The nonzero vectors of `E` are an analytic manifold modelled on `E`. -/
instance instIsManifoldNonZero : IsManifold 𝓘(𝕜, E) n {v : E // v ≠ 0} :=
  isOpenEmbedding_val_nonZero.isManifold_singleton

/-- The inclusion of the nonzero vectors into `E` is analytic. -/
theorem contMDiff_val_nonZero :
    ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E) n (Subtype.val : {v : E // v ≠ 0} → E) :=
  contMDiff_isOpenEmbedding isOpenEmbedding_val_nonZero

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 F H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- A map into the nonzero vectors is `C^n` exactly when it is `C^n` as a map into `E`. -/
theorem contMDiff_nonZero_iff {f : M → {v : E // v ≠ 0}} :
    ContMDiff I 𝓘(𝕜, E) n f ↔ ContMDiff I 𝓘(𝕜, E) n (fun x ↦ (f x : E)) :=
  ⟨contMDiff_val_nonZero.comp, ContMDiff.of_comp_isOpenEmbedding isOpenEmbedding_val_nonZero⟩

/-- The units of `𝕜` act on the nonzero vectors of `E` by analytic maps. -/
instance instContMDiffConstSMulNonZero : ContMDiffConstSMul 𝓘(𝕜, E) n 𝕜ˣ {v : E // v ≠ 0} where
  contMDiff_const_smul a := contMDiff_nonZero_iff.mpr
    ((contDiff_const_smul (a : 𝕜)).contMDiff.comp contMDiff_val_nonZero)

/-- Every subgroup of the units of `𝕜` acts on the nonzero vectors of `E` by analytic maps. -/
instance instContMDiffConstSMulSubgroupNonZero (S : Subgroup 𝕜ˣ) :
    ContMDiffConstSMul 𝓘(𝕜, E) n S {v : E // v ≠ 0} :=
  IsScalarTower.contMDiffConstSMul 𝕜ˣ

omit [Nontrivial E] in
/-- Every subgroup of the units of `𝕜` acts on the nonzero vectors of `E` by homeomorphisms. -/
instance instContinuousConstSMulSubgroupNonZero (S : Subgroup 𝕜ˣ) :
    ContinuousConstSMul S {v : E // v ≠ 0} :=
  IsScalarTower.continuousConstSMul S 𝕜ˣ _

end TauCeti
