/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Topology.Algebra.MulAction
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The nonzero vectors of a normed space as a manifold

The nonzero vectors `{v : E // v ≠ 0}` of a normed space `E` over a nontrivially normed field `𝕜`
form an open subset of `E`. Their inclusion into `E` is the single chart of an analytic manifold
modelled on `E`. Mathlib lets the units `𝕜ˣ` act on the nonzero vectors by scalar multiplication
(`Units.nonZeroSubMul`), and this action is by analytic maps. For `𝕜 = ℂ` the nonzero vectors are
the connected complex manifolds `ℂⁿ ∖ {0}`, `n ≥ 1`, whose quotients by free, properly
discontinuous groups of dilations are the Hopf manifolds.

## Main results

* `TauCeti.instChartedSpaceNonZero`, `TauCeti.instIsManifoldNonZero`: the nonzero vectors of `E`
  are an analytic manifold modelled on `E`, charted by the inclusion.
* `TauCeti.contMDiff_val_nonZero`, `TauCeti.contMDiff_nonZero_iff`: the inclusion is analytic, and
  a map into the nonzero vectors is `C^n` exactly when its composite with the inclusion is.
* `TauCeti.instContMDiffConstSMulNonZero`, `TauCeti.instContMDiffConstSMulSubgroupNonZero`: the
  units of `𝕜`, and every subgroup of them, act by analytic maps.
* `TauCeti.instConnectedSpaceNonZero`: the nonzero vectors of a nontrivial complex normed space are
  connected.
* `Units.norm_coe_zpow_smul`, `Units.exists_zpow_smul_mem_annulus`: the dilation by `cᵏ`
  multiplies norms by `‖c‖ ^ k`, so for `1 < ‖c‖` every orbit meets the closed annulus
  `1 ≤ ‖v‖ ≤ ‖c‖`.
* `Units.coe_zpow_smul_of_eq_algebraMap`: a unit that is the image of a real `r` acts by powers
  of `r`.
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

/-- The nonzero vectors of a nontrivial complex normed space are connected: as a real vector space
it has dimension at least two. -/
instance instConnectedSpaceNonZero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [Nontrivial E] : ConnectedSpace {v : E // v ≠ 0} := by
  have h1 : 1 ≤ Module.rank ℂ E := Cardinal.one_le_iff_pos.mpr rank_pos
  have h : 1 < Module.rank ℝ E := by
    rw [rank_real_of_complex]
    calc (1 : Cardinal) < 2 := Cardinal.one_lt_two
      _ = 2 * 1 := (mul_one 2).symm
      _ ≤ 2 * Module.rank ℂ E := by gcongr
  exact isConnected_iff_connectedSpace.mp (isConnected_compl_singleton_of_one_lt_rank h 0)

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

namespace Units

section Norm

/-! ### Norms of dilated nonzero vectors -/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E]

/-- The dilation by `cᵏ` multiplies the norm of a nonzero vector by `‖c‖ ^ k`. -/
theorem norm_coe_zpow_smul (c : 𝕜ˣ) (k : ℤ) (v : {v : E // v ≠ 0}) :
    ‖((c ^ k • v : {v : E // v ≠ 0}) : E)‖ = ‖(c : 𝕜)‖ ^ k * ‖(v : E)‖ := by
  rw [Units.smul_coe, Units.smul_def, norm_smul, Units.val_zpow_eq_zpow_val, norm_zpow]

/-- For `1 < ‖c‖` every nonzero vector has a multiple by a power of `c` in the closed annulus
`1 ≤ ‖v‖ ≤ ‖c‖`. -/
theorem exists_zpow_smul_mem_annulus {c : 𝕜ˣ} (hc : 1 < ‖(c : 𝕜)‖) (v : {v : E // v ≠ 0}) :
    ∃ k : ℤ, 1 ≤ ‖((c ^ k • v : {v : E // v ≠ 0}) : E)‖ ∧
      ‖((c ^ k • v : {v : E // v ≠ 0}) : E)‖ ≤ ‖(c : 𝕜)‖ := by
  obtain ⟨m, hm₁, hm₂⟩ := exists_mem_Ico_zpow (norm_pos_iff.mpr v.property) hc
  have hpos : 0 < ‖(c : 𝕜)‖ ^ m := zpow_pos (one_pos.trans hc) m
  have hnorm : ‖((c ^ (-m) • v : {v : E // v ≠ 0}) : E)‖ = ‖(v : E)‖ / ‖(c : 𝕜)‖ ^ m := by
    rw [norm_coe_zpow_smul, zpow_neg, inv_mul_eq_div]
  refine ⟨-m, ?_, ?_⟩ <;> rw [hnorm]
  · exact (one_le_div hpos).mpr hm₁
  · rw [div_le_iff₀ hpos, ← zpow_one_add₀ (norm_ne_zero_iff.mpr c.ne_zero), add_comm]
    exact hm₂.le

/-- A power of a unit of a normed `ℝ`-algebra `𝕜` that is the image of a real `r` acts on
nonzero vectors as the real scalar `r ^ k`. -/
theorem coe_zpow_smul_of_eq_algebraMap [NormedAlgebra ℝ 𝕜] [NormedSpace ℝ E]
    [IsScalarTower ℝ 𝕜 E] {c : 𝕜ˣ} {r : ℝ} (hc : (c : 𝕜) = algebraMap ℝ 𝕜 r) (k : ℤ)
    (v : {v : E // v ≠ 0}) : ((c ^ k • v : {v : E // v ≠ 0}) : E) = (r ^ k) • (v : E) := by
  rw [Units.smul_coe, Units.smul_def, Units.val_zpow_eq_zpow_val, hc, ← map_zpow₀,
    algebraMap_smul]

end Norm

end Units
