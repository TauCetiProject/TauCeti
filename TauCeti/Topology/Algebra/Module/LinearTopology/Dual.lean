/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Small.Defs
public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Algebra.Module.LinearMap.DivisionRing
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Logic.Small.Basic
import TauCeti.Topology.Algebra.Module.Quotient

/-!
# Point separation and smallness of the continuous dual under a linear topology

For a `T₁` topological vector space `V : Type v` over a division ring `K` (with any topology on
`K`) whose topology is `K`-linear (`IsLinearTopology K V`), open subspaces have discrete quotients,
so continuous linear functionals separate points (`TauCeti.exists_continuousLinearMap_apply_eq_one`,
`TauCeti.exists_continuousLinearMap_apply_ne_zero`) and `StrongDual K V` is `Small.{v}`
(`TauCeti.small_strongDual`).
-/

public section

open Topology

namespace TauCeti

section DivisionRing

universe u v

variable (K : Type u) {V : Type v} [DivisionRing K] [TopologicalSpace K]
  [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [IsLinearTopology K V] [T1Space V]

/-- **Normalized point separation on a `T₁` linearly topologized vector space over a division
ring** (with any topology on `K`): for any nonzero `v : V`, some continuous linear functional
evaluates to `1` at `v`. -/
theorem exists_continuousLinearMap_apply_eq_one {v : V} (hv : v ≠ 0) :
    ∃ φ : V →L[K] K, φ v = 1 := by
  obtain ⟨U, hU, hUv⟩ := (IsLinearTopology.hasBasis_open_submodule K).mem_iff.mp
    (isClosed_singleton.compl_mem_nhds hv.symm)
  have hvU : v ∉ U := fun h ↦ hUv h (Set.mem_singleton v)
  have := Submodule.Quotient.discreteTopology_of_isOpen U hU
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero K
    fun h ↦ hvU ((Submodule.Quotient.mk_eq_zero U).mp h)
  let g : (V ⧸ U) →ₗ[K] K := (LinearMap.mulRight K (f (U.mkQ v))⁻¹).comp f
  exact ⟨⟨g.comp U.mkQ, (continuous_of_discreteTopology (f := g)).comp continuous_quotient_mk'⟩,
    by simpa [g] using mul_inv_cancel₀ hf⟩

/-- **Continuous linear forms separate points on a `T₁` linearly topologized vector space over a
division ring** (with any topology on `K`). -/
theorem exists_continuousLinearMap_apply_ne_zero {v : V} (hv : v ≠ 0) :
    ∃ φ : V →L[K] K, φ v ≠ 0 :=
  let ⟨φ, hφ⟩ := exists_continuousLinearMap_apply_eq_one K hv
  ⟨φ, hφ.symm ▸ one_ne_zero⟩

variable (V)

/-- The continuous dual `StrongDual K V` of a `T₁` linearly topologized vector space `V : Type v`
over a division ring `K` is `Small.{v}`, regardless of the universe or topology of `K`. -/
theorem small_strongDual : Small.{v} (StrongDual K V) := by
  rcases subsingleton_or_nontrivial V with _ | _
  · infer_instance
  · obtain ⟨v, hv⟩ := exists_ne (0 : V)
    obtain ⟨φ, hφ⟩ := exists_continuousLinearMap_apply_ne_zero K hv
    have : Small.{v} K := small_of_surjective
      (φ.toLinearMap.surjective fun h ↦ hφ (DFunLike.congr_fun h v))
    exact small_of_injective (DFunLike.coe_injective (F := StrongDual K V))

end DivisionRing

end TauCeti
