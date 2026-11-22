/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.MaximalPrime
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
import TauCeti.Topology.Algebra.UniformRing

/-!
# Completing a local field at its maximal ideal

A nonarchimedean local field is already complete for the adic valuation of the maximal ideal of
its valuation ring. Thus its canonical map to that adic completion is bijective, and so is the
map from its valuation ring to the ring of integers of the completion. This allows results stated
over Dedekind adic completions to be transported back to the original local field.
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
  have hs : Function.Surjective ((↑) : WithVal v → UniformSpace.Completion (WithVal v)) :=
    UniformSpace.Completion.coe_completeRingEquivSelf_symm (WithVal v) ▸
      (UniformSpace.Completion.completeRingEquivSelf (WithVal v)).symm.surjective
  refine ⟨(algebraMap K ((maximalPrime K).adicCompletion K)).injective, fun x ↦ ?_⟩
  obtain ⟨y, hy⟩ := hs x.toCompletion
  refine ⟨y.ofVal, ?_⟩
  apply IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext
  rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion_toCompletion]
  simpa [UniformSpace.Completion.algebraMap_def, WithVal.algebraMap_right_apply] using hy

/-- The valuation ring of a local field maps bijectively to the ring of integers of the adic
completion at its maximal ideal. -/
theorem bijective_algebraMap_adicCompletionIntegers_maximalPrime :
    Function.Bijective (algebraMap (valuation K).valuationSubring
      ((maximalPrime K).adicCompletionIntegers K)) := by
  set u := maximalPrime K
  have hcomp (a : (valuation K).valuationSubring) :
      ((algebraMap _ (u.adicCompletionIntegers K) a : u.adicCompletionIntegers K) :
        u.adicCompletion K) = algebraMap K (u.adicCompletion K) a := by
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply,
      ValuationSubring.algebraMap_apply,
      IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self_apply]
  have hb := bijective_algebraMap_adicCompletion_maximalPrime K
  refine ⟨fun a b h ↦ Subtype.ext (hb.1 (by rw [← hcomp, ← hcomp, h])), fun x ↦ ?_⟩
  obtain ⟨y, hy⟩ := hb.2 x
  -- `y` is integral, since its image `x` is
  have hy1 : u.valuation K y ≤ 1 := by
    have hy' := hy
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self_apply] at hy'
    rw [← u.valuedAdicCompletion_eq_valuation', hy']
    exact x.property
  have hy2 : y ∈ (valuation K).valuationSubring := by
    rw [← valuationSubring_valuation_maximalPrime K]
    exact hy1
  exact ⟨⟨y, hy2⟩, Subtype.ext ((hcomp _).trans hy)⟩

end TauCeti
