/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Order.StateSpace
import TauCeti.Analysis.Normed.Module.HahnBanach.Basic

/-!
# Extension of states on order-unit spaces

This file proves norm-preserving extension results for states on order-unit spaces:
every state on the domain of a unit-preserving linear isometry (in particular, a unital subspace)
extends to a state on the codomain.

## Main results

* `TauCeti.IsOrderUnitNorm.surjOn_pullbackFunctional_stateSpace`: extension of states along a
  unit-preserving linear isometry via Hahn–Banach.
* `TauCeti.IsOrderUnitNorm.surjOn_pullbackFunctional_subtypeL`: extension of states from a unital
  subspace.

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

/-- **Extension of states from a unital subspace.** Restriction of states from `E` to a unital
subspace `S` is surjective, by Hahn–Banach. -/
theorem IsOrderUnitNorm.surjOn_pullbackFunctional_subtypeL {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] [PartialOrder E] [IsOrderedAddMonoid E] {e : E} (he : IsOrderUnitNorm e)
    (S : Submodule ℝ E) (heS : e ∈ S) :
    SurjOn S.subtypeL.pullbackFunctional (stateSpace e) (stateSpace (⟨e, heS⟩ : S)) := by
  simpa [Submodule.subtypeₗᵢ_toContinuousLinearMap] using
    (he.submodule S heS).surjOn_pullbackFunctional_stateSpace he S.subtypeₗᵢ rfl

end Extension

end TauCeti
