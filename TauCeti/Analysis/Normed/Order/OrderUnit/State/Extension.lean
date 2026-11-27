/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Order.OrderUnit.State.Basic
import TauCeti.Analysis.Normed.Module.HahnBanach.Basic

/-!
# Extension of states on order-unit spaces

This file proves norm-preserving extension results for states on order-unit spaces:
every state on the domain of a unit-preserving linear isometry extends to a state on the codomain.

## Main results

* `TauCeti.IsOrderUnitNorm.surjOn_pullbackFunctional_stateSpace`: extension of states along a
  unit-preserving linear isometry via Hahn–Banach.
* `TauCeti.IsOrderUnitNorm.exists_extension_mem_stateSpace`: extension of states from subspaces
  containing `e`.

## References

* Marc A. Rieffel, *Metrics on state spaces*, Doc. Math. 4 (1999), 559–600, Section 1.
* Richard V. Kadison, *A representation theory for commutative topological algebra*,
  Mem. Amer. Math. Soc. 7 (1951).
-/

public section

open Set WeakDual

namespace TauCeti

section Extension

open OrderUnit

/-- **Extension of states along a unit-preserving linear isometry.** Every state on the domain of
a unit-preserving linear isometry between order-unit spaces extends to a state on the codomain. -/
theorem IsOrderUnitNorm.surjOn_pullbackFunctional_stateSpace {E F : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E]
    [SeminormedAddCommGroup F] [NormedSpace ℝ F] [PartialOrder F] [IsOrderedAddMonoid F]
    {e : E} {f : F} (he : IsOrderUnitNorm e) (hf : IsOrderUnitNorm f)
    (T : E →ₗᵢ[ℝ] F) (hTe : T e = f) :
    SurjOn T.toContinuousLinearMap.pullbackFunctional (stateSpace f) (stateSpace e) := by
  intro φ hφ
  let _ : NormedAddCommGroup E :=
    NormedAddCommGroup.ofSeparation fun _ h => he.norm_eq_zero_iff.mp h
  have hφnorm : ‖toStrongDual φ‖ = 1 := he.norm_toStrongDual_of_mem_stateSpace hφ
  obtain ⟨g, hg, hgnorm⟩ := T.exists_extension_norm_eq (toStrongDual φ)
  have hgf : g f = 1 := by
    simpa [hTe, apply_eq_one_of_mem_stateSpace hφ] using DFunLike.congr_fun hg e
  refine ⟨StrongDual.toWeakDual g,
    hf.mem_stateSpace_iff_norm_eq_one_and_apply_eq_one.mpr ⟨hgnorm.trans hφnorm, hgf⟩, ?_⟩
  exact DFunLike.ext _ _ fun x => by simpa using DFunLike.congr_fun hg x

/-- **Extension of states.** Every state of a subspace `p` containing `e` extends to a state of
`E`, by the Hahn–Banach theorem. The extension need not be unique. -/
theorem IsOrderUnitNorm.exists_extension_mem_stateSpace {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E] {e : E}
    [IsOrderedAddMonoid E] (h : IsOrderUnitNorm e) (p : Submodule ℝ E) (hp : e ∈ p)
    {ψ : WeakDual ℝ p} (hψ : ψ ∈ stateSpace (⟨e, hp⟩ : p)) :
    ∃ φ ∈ stateSpace e, ∀ x : p, φ x = ψ x := by
  obtain ⟨φ, hφ, hφψ⟩ :=
    (h.submodule p hp).surjOn_pullbackFunctional_stateSpace h p.subtypeₗᵢ rfl hψ
  refine ⟨φ, hφ, fun x => ?_⟩
  simpa [ContinuousLinearMap.pullbackFunctional_apply] using DFunLike.congr_fun hφψ x

end Extension

end TauCeti
