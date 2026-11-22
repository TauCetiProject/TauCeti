/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Measure.Basic
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars

/-!
# Restriction of measure coefficients along an embedding

If a ring homomorphism embeds one topological coefficient ring into another, a measure restricts
along it whenever the integral of every transported test lies in the coefficient image.
This criterion is `RingHom.exists_apply_comp_eq_of_mem_range`.
-/

public section

open ContinuousMap

namespace AbstractMeasure

variable {X : Type*} [TopologicalSpace X]

/-- Restrict a measure through a coefficient embedding when every transported test has its
integral in the coefficient image. -/
theorem _root_.RingHom.exists_apply_comp_eq_of_mem_range {O K : Type*}
    [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
    [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    (j : O →+* K) (hje : Topology.IsEmbedding j)
    (ν : D(X, K))
    (hmem : ∀ f : C(X, O), ν ((⟨j, hje.continuous⟩ : C(O, K)).comp f) ∈ Set.range j) :
    ∃ μ : D(X, O), ∀ f : C(X, O), ν ((⟨j, hje.continuous⟩ : C(O, K)).comp f) = j (μ f) := by
  let := j.toAlgebra
  have halg : algebraMap O K = j := j.algebraMap_toAlgebra
  have hlin : ⇑(Algebra.linearMap O K) = j := by
    funext a
    rw [Algebra.linearMap_apply, halg]
  have hlinj : Function.Injective (Algebra.linearMap O K) := by
    rw [hlin]
    exact hje.injective
  let : ContinuousSMul O K := continuousSMul_of_algebraMap O K (by rw [halg]; exact hje.continuous)
  have hlin_cont : Continuous (Algebra.linearMap O K) := by
    rw [hlin]
    exact hje.continuous
  let J : O →L[O] K := ⟨Algebra.linearMap O K, hlin_cont⟩
  have hJ : ⇑J = j := by
    rw [ContinuousLinearMap.coe_mk', hlin]
  let F : C(X, O) →L[O] K :=
    ((toCLMEquiv ν).restrictScalars O).comp (J.compLeftContinuous O X)
  have hF (f : C(X, O)) : F f = ν ((⟨j, hje.continuous⟩ : C(O, K)).comp f) := by
    have hcomp : J.compLeftContinuous O X f = (⟨j, hje.continuous⟩ : C(O, K)).comp f := by
      have hcomp' := (ContinuousLinearMap.compLeftContinuous_apply O X J f).trans
        (AddMonoidHom.compLeftContinuous_apply X J.toLinearMap.toAddMonoidHom J.continuous f)
      rw [hcomp']
      ext x
      simp only [ContinuousMap.coe_mk, ContinuousMap.comp_apply, LinearMap.toAddMonoidHom_coe,
        ContinuousLinearMap.coe_coe, hJ]
    simp only [F, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
      coe_toCLMEquiv, hcomp]
  have hmem' (f : C(X, O)) : F.toLinearMap f ∈ (Algebra.linearMap O K).range := by
    rw [LinearMap.mem_range]
    obtain ⟨a, ha⟩ := hmem f
    exact ⟨a, by rw [hlin, ContinuousLinearMap.coe_coe, hF]; exact ha⟩
  let L := F.toLinearMap.codRestrictOfInjective (Algebra.linearMap O K) hlinj hmem'
  have hLj (f : C(X, O)) : j (L f) = F f := by
    rw [← hlin]
    exact LinearMap.codRestrictOfInjective_comp_apply F.toLinearMap (Algebra.linearMap O K)
      hlinj hmem' f
  have hL : Continuous L := hje.continuous_iff.mpr <| by
    simpa only [Function.comp_def, hLj] using F.continuous
  exact ⟨toCLMEquiv.symm ⟨L, hL⟩, fun f ↦ by
    rw [coe_symm_toCLMEquiv, ContinuousLinearMap.coe_mk', hLj, hF]⟩

end AbstractMeasure
