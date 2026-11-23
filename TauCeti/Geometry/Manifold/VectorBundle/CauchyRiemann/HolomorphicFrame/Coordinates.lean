/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.HolomorphicFrame.Trivialization
import TauCeti.Geometry.Manifold.Complex.Analytic

/-!
# Kernel sections in holomorphic frame coordinates

The coordinates of a differentiable section in a holomorphic kernel frame are holomorphic
exactly when the section is in the kernel of the original operator. The model fibre may be any
rank-one complex normed space. The original total-space topology and real smooth structure of
the bundle are retained.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, Appendix C.1.
-/

public section

noncomputable section

open Bundle Filter Module Set
open scoped ContDiff Manifold Topology TauCeti.ComplexManifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [∀ x, AddCommGroup (V x)] [∀ x, Module ℂ (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, ContinuousSMul ℂ (V x)]
  [VectorBundle ℂ F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, E)]
  {D : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, E) x →L[ℝ] V x}
  {σ : Π x : M, V x} {U : Set M}

namespace IsNonvanishingHolomorphicOn

omit [IsManifold 𝓘(ℂ, E) ∞ M] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, ContinuousSMul ℂ (V x)] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, E)] in
/-- A frame recovers every vector from its sole complex coordinate. -/
theorem eq_coord_smul (hσ : IsNonvanishingHolomorphicOn F D σ U) (b : Basis Unit ℂ F)
    (hU : IsOpen U) {x : M} (hx : x ∈ U) (v : V x) :
    v = b.coord () ((hσ.trivialization b hU ⟨x, v⟩).2) • σ x := by
  let e := hσ.trivialization b hU
  have hxe : x ∈ e.baseSet := by simpa only [e, baseSet_trivialization] using hx
  exact (e.symm_apply_apply_mk hxe v).symm.trans (hσ.trivialization_symm_apply b hU hx _)

end IsNonvanishingHolomorphicOn

namespace IsRealCauchyRiemannOperator

/-- In a holomorphic kernel frame, the coordinates of an originally differentiable section are
holomorphic exactly when the original operator vanishes on that section. -/
theorem mdifferentiableOn_trivialization_iff
    (hD : IsRealCauchyRiemannOperator F
      (SmoothAlmostComplexStructure.ofComplexManifold E M) D)
    (hDℂ : IsComplexLinearOperator F D) (hσ : IsNonvanishingHolomorphicOn F D σ U)
    (b : Basis Unit ℂ F) (hU : IsOpen U) {W : Set M} (hW : IsOpen W)
    (hWU : W ⊆ U) {τ : Π x, V x}
    (hτ : MDifferentiableOn 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F)) (T% τ) W) :
    MDifferentiableOn 𝓘(ℂ, E) 𝓘(ℂ, F)
      (fun x ↦ (hσ.trivialization b hU ⟨x, τ x⟩).2) W ↔ ∀ x ∈ W, D τ x = 0 := by
  have : FiniteDimensional ℂ F := .of_basis b
  let e := hσ.trivialization b hU
  let c : M → F := fun x ↦ (e ⟨x, τ x⟩).2
  let f : M → ℂ := fun x ↦ b.coord () (c x)
  have hc : MDifferentiableOn 𝓘(ℝ, E) 𝓘(ℝ, F) c W :=
    mdifferentiable_snd.comp_mdifferentiableOn
      (((Trivialization.contMDiffOn_of_mem_maximalAtlas
      (hσ.trivialization_mem_maximalAtlas b hU)).mdifferentiableOn (by simp)).comp hτ
        (fun x hx ↦ e.mem_source.mpr (by
          simpa only [e, IsNonvanishingHolomorphicOn.baseSet_trivialization] using hWU hx)))
  have hf : MDifferentiableOn 𝓘(ℝ, E) 𝓘(ℝ, ℂ) f W :=
    ((b.coord ()).toContinuousLinearMap.restrictScalars ℝ).mdifferentiable.comp_mdifferentiableOn hc
  have hτf : ∀ x ∈ W, τ x = f x • σ x := fun x hx ↦ hσ.eq_coord_smul b hU (hWU hx) _
  have hcf : ∀ x ∈ W, c x = f x • b () := fun x _ ↦ by
    simpa only [f, Fintype.sum_unique, Basis.coord_apply] using (b.sum_repr (c x)).symm
  have hker : (∀ x ∈ W, D (f • σ) x = 0) ↔ ∀ x ∈ W, D τ x = 0 := by
    apply forall₂_congr
    intro x hx
    rw [hD.apply_eq_of_eventuallyEq
      (hτ.mdifferentiableAt (hW.mem_nhds hx))]
    exact Filter.mem_of_superset (hW.mem_nhds hx) fun y hy ↦ (hτf y hy).symm
  rw [← hker, hD.forall_apply_smul_eq_zero_iff hDℂ (hσ.mono hWU) hW hf]
  constructor
  · intro h
    exact ((b.coord ()).toContinuousLinearMap.mdifferentiable.comp_mdifferentiableOn h)
  · intro h
    exact (h.smul mdifferentiableOn_const).congr fun x hx ↦ hcf x hx

/-- Changes between actual kernel frames are holomorphic families of complex-linear maps.
Both model bases may be chosen independently. -/
theorem contMDiffOn_coordChangeL_trivialization [FiniteDimensional ℂ E]
    (hD : IsRealCauchyRiemannOperator F
      (SmoothAlmostComplexStructure.ofComplexManifold E M) D)
    (hDℂ : IsComplexLinearOperator F D) (hσ : IsNonvanishingHolomorphicOn F D σ U)
    {σ' : Π x, V x} {U' : Set M} (hσ' : IsNonvanishingHolomorphicOn F D σ' U')
    (b b' : Basis Unit ℂ F) (hU : IsOpen U) (hU' : IsOpen U') :
    ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, F →L[ℂ] F) ω
      (fun x ↦ ((hσ.trivialization b hU).coordChangeL ℂ
        (hσ'.trivialization b' hU') x : F →L[ℂ] F)) (U ∩ U') := by
  have : FiniteDimensional ℂ F := .of_basis b
  have hc := (hD.mdifferentiableOn_trivialization_iff hDℂ hσ' b' hU' (hU.inter hU')
    inter_subset_right ((hσ.contMDiffOn.mono inter_subset_left).mdifferentiableOn (by simp))).2
      (fun x hx ↦ hσ.apply_eq_zero x hx.1)
  have hω : ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, F) ω
      (fun x ↦ (hσ'.trivialization b' hU' ⟨x, σ x⟩).2) (U ∩ U') :=
    hc.contMDiffOn (hU.inter hU')
  refine ((StrongDual.smulRightL ℂ F F
    (b.coord ()).toContinuousLinearMap).contMDiff.comp_contMDiffOn hω).congr ?_
  intro x hx
  ext w
  rw [ContinuousLinearEquiv.coe_coe, Trivialization.coordChangeL_apply]
  · rw [hσ.trivialization_symm_apply b hU hx.1,
      ← (hσ'.trivialization b' hU').continuousLinearMapAt_apply_of_mem (R := ℂ)
        (by simpa only [IsNonvanishingHolomorphicOn.baseSet_trivialization] using hx.2),
      map_smul,
      (hσ'.trivialization b' hU').continuousLinearMapAt_apply_of_mem (R := ℂ)
        (by simpa only [IsNonvanishingHolomorphicOn.baseSet_trivialization] using hx.2)]
    simp only [Function.comp_apply, ContinuousLinearMap.smulRightL_apply_apply,
      ContinuousLinearMap.smulRight_apply, LinearMap.coe_toContinuousLinearMap']
  · simpa only [IsNonvanishingHolomorphicOn.baseSet_trivialization] using hx

end IsRealCauchyRiemannOperator

end TauCeti
