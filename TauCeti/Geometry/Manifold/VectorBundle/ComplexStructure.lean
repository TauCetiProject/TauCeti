/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Complex.Structure
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.Notation

/-!
# Differentiable sections of the complex bundle of a complex structure

Let `V` be a real vector bundle over a manifold `B`, with model fibre `F`, and let `J` be a
continuous complex structure on `V` (`TauCeti.Bundle.ContinuousComplexStructure`). Its fibres
with `J` as multiplication by `i` form the complex vector bundle `J.Fiber`, whose trivializations
are those of `V` corrected by the complex linear part `(1 - J' b ∘ J' b₀) / 2` of the identity,
with `J' b` the structure `J b` read in the trivialization of `V` at `b₀`. The two bundles have the
same sections, but their charts differ by this correction.

When `J` is differentiable at `b₀` as a section of the endomorphism bundle of `V`, so is the
correction, and a section of `J.Fiber` that is differentiable at `b₀` in the charts of the complex
bundle is differentiable at `b₀` as a section of `V`
(`TauCeti.Bundle.ContinuousComplexStructure.mdifferentiableAt_totalSpace_fiberEquiv`). This lets
operators defined on sections of `V`, such as normal Cauchy–Riemann operators read through ambient
derivatives, be stated on sections of the complex bundle `J.Fiber`.
-/

public section

noncomputable section

open Bundle Set Module
open scoped Manifold ContDiff Topology

namespace TauCeti.Bundle.ContinuousComplexStructure

variable {EB HB B : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : B → Type*} [∀ b, AddCommGroup (V b)] [∀ b, Module ℝ (V b)] [∀ b, TopologicalSpace (V b)]
  [∀ b, IsTopologicalAddGroup (V b)] [∀ b, ContinuousSMul ℝ (V b)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  (G : Type*) [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [Fact (finrank ℝ F = 2 * finrank ℂ G)]

/-- A section of the complex bundle `J.Fiber` that is differentiable at `b₀` in its complex
charts is differentiable at `b₀` as a section of `V`, provided `J` is differentiable at `b₀` as a
section of the endomorphism bundle of `V`. -/
theorem mdifferentiableAt_totalSpace_fiberEquiv (J : ContinuousComplexStructure F V) {b₀ : B}
    (hJ : MDifferentiableAt IB (IB.prod 𝓘(ℝ, F →L[ℝ] F))
      (fun b ↦ TotalSpace.mk' (F →L[ℝ] F) (E := fun b ↦ V b →L[ℝ] V b) b (J b)) b₀)
    {σ : Π b, J.Fiber b}
    (hσ : MDifferentiableAt IB (IB.prod 𝓘(ℝ, G)) (fun b ↦ TotalSpace.mk' G b (σ b)) b₀) :
    MDifferentiableAt IB (IB.prod 𝓘(ℝ, F)) (fun b ↦ TotalSpace.mk' F b (J.fiberEquiv b (σ b)))
      b₀ := by
  rw [mdifferentiableAt_section] at hσ ⊢
  have hc : MDiffAt (J.coord b₀) b₀ := by
    refine ((mdifferentiableAt_hom_bundle _).1 hJ).2.congr_of_eventuallyEq ?_
    filter_upwards [(trivializationAt F V b₀).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt F V b₀)] with b hb
    ext w
    rw [← (trivializationAt F V b₀).continuousLinearMapAt_symmL (R := ℝ) hb w, J.coord_apply hb,
      (trivializationAt F V b₀).continuousLinearMapAt_symmL (R := ℝ) hb w]
    simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply]
  have hA : MDiffAt (J.complexLinearPart b₀) b₀ := by
    refine ((mdifferentiableAt_const (c := ContinuousLinearMap.id ℝ F)).sub
      (hc.clm_comp (mdifferentiableAt_const (c := J.coord b₀ b₀)))).const_smul
      (2⁻¹ : ℝ) |>.congr_of_eventuallyEq (Filter.Eventually.of_forall fun b ↦ ?_)
    ext w
    simp [complexLinearPart_apply]
  refine (hA.clm_apply ((J.modelEquiv G b₀ : G →L[ℝ] F).mdifferentiableAt.comp b₀ hσ))
    |>.congr_of_eventuallyEq ?_
  have := FiniteDimensional.completeSpace ℝ F
  filter_upwards [(J.isOpen_unitSet b₀).mem_nhds (J.mem_unitSet_self b₀)] with b hb
  have hb' : b ∈ (trivializationAt G J.Fiber b₀).baseSet := by
    rwa [baseSet_trivializationAt]
  -- Both trivializations at `b₀` are read through the inverse of the complex one.
  rw [← (trivializationAt G J.Fiber b₀).symm_apply_apply_mk hb' (σ b),
    J.trivializationAt_symm_apply G hb,
    (trivializationAt F V b₀).apply_mk_symm (J.unitSet_subset b₀ hb)]
  simp only [Function.comp_apply, ContinuousLinearEquiv.coe_coe]

end TauCeti.Bundle.ContinuousComplexStructure
