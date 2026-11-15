/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.Barrelled
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Equicontinuity and separately continuous bilinear maps on barrelled spaces

On a barrelled space `E`, every von Neumann bounded set of continuous semilinear maps into a
polynormable space `F` is uniformly equicontinuous (`Bornology.IsVonNBounded.uniformEquicontinuous`)
and hence equicontinuous (`Bornology.IsVonNBounded.equicontinuous`): evaluation at any vector maps a
bounded set of operators to a bounded subset of `F`, so the Banach–Steinhaus theorem
(`PolynormableSpace.banach_steinhaus`) applies.

A bilinear map `B : E × F → G` that is continuous in each variable separately need not be jointly
continuous. It is when `E` is barrelled and both `E` and `F` are first countable, for instance
when `E` and `F` are Fréchet spaces: if `xₘ → 0` and `yₘ → 0`, the continuous linear maps
`B(·, yₘ)` converge pointwise to zero, so they are pointwise bounded, and the Banach–Steinhaus
theorem (`PolynormableSpace.banach_steinhaus`) makes them equicontinuous. Hence
`B(xₘ, yₘ) → 0`, which is continuity at the origin for sequences, and a bilinear map continuous at
the origin and in each variable is continuous.

This is how the continuity of a linear map from test functions to distributions yields a
continuous bilinear form on two spaces of test functions supported in fixed compact sets, and
hence finite-order bounds for it.

## Main results

* `Bornology.IsVonNBounded.uniformEquicontinuous`, `Bornology.IsVonNBounded.equicontinuous`: von
  Neumann bounded families of continuous semilinear maps out of a barrelled space into a
  polynormable space are uniformly equicontinuous and equicontinuous.
* `LinearMap.continuous_uncurry_of_barrelledSpace`: a separately continuous bilinear map on the
  product of a first countable barrelled space and a first countable space is continuous.

## References

* N. Bourbaki, *Topological Vector Spaces*, Chapter III, §4, no. 2, and §5, no. 3, Proposition 6
  and Corollary 1.
* F. Trèves, *Topological Vector Spaces, Distributions and Kernels*, Theorem 34.1 and
  Corollary 1.
-/

public section

open Filter Topology Uniformity

namespace Bornology

section Uniform

variable {𝕜₁ 𝕜₂ E F : Type*} [NontriviallyNormedField 𝕜₁] [NontriviallyNormedField 𝕜₂]
  {σ₁₂ : 𝕜₁ →+* 𝕜₂} [RingHomIsometric σ₁₂]
  [AddCommGroup E] [Module 𝕜₁ E] [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul 𝕜₁ E]
  [BarrelledSpace 𝕜₁ E]
  [AddCommGroup F] [Module 𝕜₂ F] [UniformSpace F] [IsUniformAddGroup F] [PolynormableSpace 𝕜₂ F]

/-- Every von Neumann bounded set of continuous semilinear maps from a barrelled space into a
polynormable space is uniformly equicontinuous: evaluation at each point sends a bounded set of
operators to a bounded subset of the codomain, so the Banach–Steinhaus theorem applies. -/
protected theorem IsVonNBounded.uniformEquicontinuous {S : Set (E →SL[σ₁₂] F)}
    (hS : IsVonNBounded 𝕜₂ S) : UniformEquicontinuous fun f : S ↦ (f.1 : E → F) := by
  refine PolynormableSpace.banach_steinhaus (𝓕 := fun f : S ↦ f.1) fun x ↦ ?_
  refine (ContinuousLinearMap.isVonNBounded_image2_apply hS (isVonNBounded_singleton x)).subset ?_
  rintro _ ⟨f, rfl⟩
  exact ⟨f.1, f.2, x, Set.mem_singleton x, rfl⟩

end Uniform

section Topological

variable {𝕜₁ 𝕜₂ E F : Type*} [NontriviallyNormedField 𝕜₁] [NontriviallyNormedField 𝕜₂]
  {σ₁₂ : 𝕜₁ →+* 𝕜₂} [RingHomIsometric σ₁₂]
  [AddCommGroup E] [Module 𝕜₁ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul 𝕜₁ E] [BarrelledSpace 𝕜₁ E]
  [AddCommGroup F] [Module 𝕜₂ F] [UniformSpace F] [IsUniformAddGroup F] [PolynormableSpace 𝕜₂ F]

/-- Every von Neumann bounded set of continuous semilinear maps from a barrelled topological
vector space into a uniformly topologized polynormable space is equicontinuous. -/
protected theorem IsVonNBounded.equicontinuous {S : Set (E →SL[σ₁₂] F)}
    (hS : IsVonNBounded 𝕜₂ S) : Equicontinuous fun f : S ↦ (f.1 : E → F) := by
  let _ : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  have _ : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  exact hS.uniformEquicontinuous.equicontinuous

end Topological

end Bornology

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul 𝕜 E]
  [BarrelledSpace 𝕜 E] [FirstCountableTopology E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [FirstCountableTopology F]
  [AddCommGroup G] [Module 𝕜 G] [UniformSpace G] [IsUniformAddGroup G] [PolynormableSpace 𝕜 G]

namespace LinearMap

/-- **Separately continuous bilinear maps on barrelled spaces are continuous.** A bilinear map
`B : E × F → G` into a locally convex space, continuous in each variable, is jointly continuous
when `E` is barrelled and `E` and `F` are first countable, for instance when both are Fréchet
spaces. -/
theorem continuous_uncurry_of_barrelledSpace (B : E →ₗ[𝕜] F →ₗ[𝕜] G)
    (h₁ : ∀ y, Continuous fun x ↦ B x y) (h₂ : ∀ x, Continuous (B x)) :
    Continuous fun z : E × F ↦ B z.1 z.2 := by
  -- Continuity at the origin, along sequences.
  have h₀ : Tendsto (fun z : E × F ↦ B z.1 z.2) (𝓝 0) (𝓝 0) := by
    refine tendsto_iff_seq_tendsto.2 fun u hu ↦ ?_
    have hu₁ : Tendsto (fun m ↦ (u m).1) atTop (𝓝 0) := (continuous_fst.tendsto 0).comp hu
    have hu₂ : Tendsto (fun m ↦ (u m).2) atTop (𝓝 0) := (continuous_snd.tendsto 0).comp hu
    -- The continuous linear maps `B(·, yₘ)` tend to zero pointwise, hence are equicontinuous.
    let T : ℕ → E →L[𝕜] G := fun m ↦ ⟨B.flip (u m).2, h₁ (u m).2⟩
    have hT_apply (m : ℕ) (x : E) : T m x = B x (u m).2 := rfl
    have hT : UniformEquicontinuous ((↑) ∘ T) := PolynormableSpace.banach_steinhaus fun x ↦ by
      have : Tendsto (fun m ↦ B x (u m).2) atTop (𝓝 0) := by
        simpa [Function.comp_def] using ((h₂ x).tendsto 0).comp hu₂
      exact this.isVonNBounded_range 𝕜
    rw [nhds_eq_comap_uniformity, tendsto_comap_iff]
    refine fun V hV ↦ (hu₁.eventually (hT.equicontinuous 0 V hV)).mono fun m hm ↦ ?_
    simpa [hT_apply] using hm m
  refine continuous_of_continuousAt_zero₂ (toAddMonoidHom'.comp B.toAddMonoidHom)
    ?_ (fun x ↦ (h₂ x).continuousAt) (fun y ↦ (h₁ y).continuousAt)
  rw [ContinuousAt]
  convert h₀ using 2 <;> simp

end LinearMap
