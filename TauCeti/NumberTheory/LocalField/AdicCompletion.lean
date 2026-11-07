/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.MaximalPrime
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion

/-!
# Completing a local field at its maximal ideal

A nonarchimedean local field is already complete for the adic valuation of the maximal ideal of
its valuation ring. Thus its canonical map to that adic completion is bijective. This allows
results stated over Dedekind adic completions to be transported back to the original local field.
-/

public section

open ValuativeRel

namespace TauCeti

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- A local field maps bijectively to the adic completion at the maximal ideal of its valuation
ring. -/
theorem bijective_algebraMap_adicCompletion_maximalPrime :
    Function.Bijective (algebraMap K ((maximalPrime K).adicCompletion K)) := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  let : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  let v := (maximalPrime K).valuation K
  let e := WithVal.uniformEquiv (v := v) (w := valuation K) rfl
    (isEquiv_valuation_maximalPrime K)
  have : CompleteSpace (WithVal v) := e.completeSpace_iff.mpr inferInstance
  have hs : Function.Surjective ((↑) : WithVal v → UniformSpace.Completion (WithVal v)) := by
    rw [← Set.range_eq_univ,
      ← (UniformSpace.Completion.isUniformInducing_coe
        (WithVal v)).isComplete_range.isClosed.closure_eq]
    exact UniformSpace.Completion.denseRange_coe.closure_range
  refine ⟨(algebraMap K ((maximalPrime K).adicCompletion K)).injective, fun x ↦ ?_⟩
  obtain ⟨y, hy⟩ := hs x.toCompletion
  refine ⟨y.ofVal, ?_⟩
  apply IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext
  rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion_toCompletion]
  exact hy

end TauCeti
