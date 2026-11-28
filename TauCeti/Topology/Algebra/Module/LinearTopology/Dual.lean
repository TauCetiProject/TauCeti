/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.SeparatingDual
public import Mathlib.Logic.Small.Defs
public import Mathlib.Topology.Algebra.LinearTopology
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Logic.Small.Basic
import TauCeti.Topology.Algebra.Module.Quotient

/-!
# Point separation and smallness of the continuous dual under a linear topology

For a `T₁` topological vector space `V : Type v` over a division ring `K` (with any topology on
`K`) whose topology is `K`-linear (`IsLinearTopology K V`), open subspaces have discrete quotients,
so continuous linear functionals separate points (`TauCeti.separatingDual_of_isLinearTopology`) and
`StrongDual K V` is `Small.{v}` (`TauCeti.small_strongDual`).
-/

public section

open Topology

namespace TauCeti

section DivisionRing

universe u v

variable (K : Type u) (V : Type v) [DivisionRing K] [TopologicalSpace K]
  [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [IsLinearTopology K V] [T1Space V]

/-- **Point separation on a `T₁` linearly topologized vector space over a division ring** (with
any topology on `K`): continuous linear functionals separate points of `V`. -/
theorem separatingDual_of_isLinearTopology : SeparatingDual K V := by
  refine ⟨fun v hv ↦ ?_⟩
  obtain ⟨U, hU, hUv⟩ := (IsLinearTopology.hasBasis_open_submodule K).mem_iff.mp
    (isClosed_singleton.compl_mem_nhds hv.symm)
  have hvU : v ∉ U := fun h ↦ hUv h (Set.mem_singleton v)
  have := Submodule.Quotient.discreteTopology_of_isOpen U hU
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero K
    fun h ↦ hvU ((Submodule.Quotient.mk_eq_zero U).mp h)
  exact ⟨⟨f.comp U.mkQ, (continuous_of_discreteTopology (f := f)).comp continuous_quotient_mk'⟩,
    hf⟩

/-- The continuous dual `StrongDual K V` of a `T₁` linearly topologized vector space `V : Type v`
over a division ring `K` is `Small.{v}`, regardless of the universe or topology of `K`. -/
theorem small_strongDual : Small.{v} (StrongDual K V) := by
  rcases subsingleton_or_nontrivial V with _ | _
  · infer_instance
  · have := separatingDual_of_isLinearTopology K V
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    obtain ⟨φ, hφ⟩ := SeparatingDual.exists_ne_zero (R := K) hv
    have : Small.{v} K := small_of_surjective
      (φ.toLinearMap.surjective fun h ↦ hφ (DFunLike.congr_fun h v))
    exact small_of_injective (DFunLike.coe_injective (F := StrongDual K V))

end DivisionRing

end TauCeti
