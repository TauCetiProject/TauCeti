/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.Barrelled
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Separately continuous bilinear maps and evaluation continuity on barrelled spaces

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

Similarly, on any barrelled space `E` (without first countability) and polynormable target `G`,
canonical evaluation `ContinuousLinearMap.applyₗ G σ₁₂` into `(E →SL[σ₁₂] G) →L[𝕜₂] G` is
continuous for the topology of bounded convergence, because every von Neumann bounded family in
`E →SL[σ₁₂] G` is pointwise bounded and hence equicontinuous by Banach–Steinhaus.

## Main results

* `LinearMap.continuous_uncurry_of_barrelledSpace`: a separately continuous bilinear map on the
  product of a first countable barrelled space and a first countable space is continuous.
* `ContinuousLinearMap.continuous_applyₗ`: canonical evaluation `applyₗ G σ₁₂` on a barrelled space
  into `(E →SL[σ₁₂] G) →L[𝕜₂] G` is continuous.

## References

* N. Bourbaki, *Topological Vector Spaces*, Chapter III, §4, no. 2 and §5, no. 3, Proposition 6
  and Corollary 1.
* F. Trèves, *Topological Vector Spaces, Distributions and Kernels*, Theorem 34.1 and
  Corollary 1.
-/

public section

open Filter Topology Uniformity

namespace LinearMap

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul 𝕜 E]
  [BarrelledSpace 𝕜 E] [FirstCountableTopology E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [FirstCountableTopology F]
  [AddCommGroup G] [Module 𝕜 G] [UniformSpace G] [IsUniformAddGroup G] [PolynormableSpace 𝕜 G]

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

namespace ContinuousLinearMap

/-- On a barrelled space `E`, canonical evaluation `applyₗ G σ₁₂` into `(E →SL[σ₁₂] G) →L[𝕜₂] G`
with the topology of bounded convergence is continuous: every von Neumann bounded subset of
`E →SL[σ₁₂] G` is pointwise bounded and hence equicontinuous by Banach–Steinhaus. -/
theorem continuous_applyₗ {𝕜₁ 𝕜₂ E G : Type*} [NontriviallyNormedField 𝕜₁] [NormedField 𝕜₂]
    {σ₁₂ : 𝕜₁ →+* 𝕜₂} [RingHomIsometric σ₁₂]
    [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [Module 𝕜₁ E] [ContinuousSMul 𝕜₁ E] [BarrelledSpace 𝕜₁ E]
    [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [Module 𝕜₂ G] [PolynormableSpace 𝕜₂ G] :
    Continuous (applyₗ G σ₁₂ : E →ₛₗ[σ₁₂] (E →SL[σ₁₂] G) →L[𝕜₂] G) := by
  let : NontriviallyNormedField 𝕜₂ :=
    { ‹NormedField 𝕜₂› with
      non_trivial :=
        let ⟨c, hc⟩ := NontriviallyNormedField.non_trivial (α := 𝕜₁)
        ⟨σ₁₂ c, by rwa [RingHomIsometric.norm_map]⟩ }
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let : UniformSpace G := IsTopologicalAddGroup.rightUniformSpace G
  have : IsUniformAddGroup G := isUniformAddGroup_of_addCommGroup
  refine continuous_of_continuousAt_zero
    (applyₗ G σ₁₂ : E →ₛₗ[σ₁₂] (E →SL[σ₁₂] G) →L[𝕜₂] G).toAddMonoidHom ?_
  rw [ContinuousAt, map_zero]
  refine ContinuousLinearMap.hasBasis_nhds_zero.tendsto_right_iff.2 fun ⟨S, V⟩ ⟨hS, hV⟩ ↦ ?_
  rw [nhds_eq_comap_uniformity] at hV
  obtain ⟨U, hU, hUV⟩ := hV
  have heq := (PolynormableSpace.banach_steinhaus
    (𝓕 := (Subtype.val : S → E →SL[σ₁₂] G)) fun x ↦ ?_).equicontinuous 0 U hU
  · filter_upwards [heq] with x hx f hf
    apply hUV
    simpa using hx ⟨f, hf⟩
  · convert hS.image (applyₗ G σ₁₂ x)
    ext y
    simp

end ContinuousLinearMap
