/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution.Submersion
public import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame.Pullback

/-!
# Pulling back the coordinate frames of a submersion kernel

For a submersion `f`, the differential kernels form its vertical bundle. A normal-form chart
of `f` gives a frame of the vertical bundle by pulling constant vectors in the complement back
through the source chart. Along a map `g` into the source manifold of `f`, evaluating those
vectors at `g y` gives a local frame of the native pullback bundle over the preimage of the chart
source. These vectors lie in `T_(g y) M`, not in the tangent space of the new base at `y`.

The coordinate fields are those of
`Manifold.IsSubmersionAtOfComplement.isDistributionFrameOn_ker_mfderiv`, using the normal form
of a submersion (J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Theorem 4.12).
-/

public section

open Set Bundle Module VectorField TauCeti
open scoped Manifold ContDiff

namespace Manifold.IsSubmersionAtOfComplement

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {EX : Type*} [NormedAddCommGroup EX] [NormedSpace 𝕜 EX]
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {HX : Type*} [TopologicalSpace HX]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' H'}
  {IX : ModelWithCorners 𝕜 EX HX}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {X : Type*} [TopologicalSpace X] [ChartedSpace HX X]
  {m n : ℕ∞ω} [IsManifold I (m + 1) M] {f : M → N} {x : M} {ι : Type*}
  {K : Type*} [FunLike K X M] [ContinuousMapClass K X M]

/-- The submersion-coordinate frame for a complement basis `b` pulls back along `g` to a `C^m`
local frame of the pullback of the kernel bundle of `f`, over the preimage of the source chart.
Here `f` is `C^n` with `m + 1 ≤ n`, and `g` need only be `C^m` on the preimage. The selected chart
and complement come from `h`; the bundle structure comes from the global submersion `hf`. -/
theorem exists_isLocalFrameOn_pullback_ker_mfderiv (h : IsSubmersionAtOfComplement F I J n f x)
    (hf : IsSubmersion I J n f) (b : Basis ι 𝕜 F) (hmn : m + 1 ≤ n)
    (g : K) (hg : ContMDiffOn IX I m g (g ⁻¹' h.domChart.source)) :
    let _ : IsManifold I 1 M := IsManifold.of_le (le_add_self (a := 1) (b := m))
    let _ : CompleteSpace E := by
      have : CompleteSpace 𝕜 := by
        let := IsRCLikeNormedField.rclike 𝕜
        infer_instance
      exact FiniteDimensional.completeSpace 𝕜 E
    let _ : FiniteDimensional 𝕜 E' := Module.Finite.of_injective
      (h.equiv.symm.toLinearMap ∘ₗ LinearMap.inl 𝕜 E' F)
      (h.equiv.symm.injective.comp LinearMap.inl_injective)
    let _ := (hf.isContMDiffDistribution_ker_mfderiv hmn).fiberBundle
    ∃ s : ι → ∀ y : X, (mfderiv I J f (g y)).ker,
      IsLocalFrameOn IX (Fin (finrank 𝕜 E - finrank 𝕜 E') → 𝕜) m
        (V := (g : X → M) *ᵖ fun z ↦ (mfderiv I J f z).ker)
        (fun i y ↦ s i y) (g ⁻¹' h.domChart.source) ∧
      ∀ i y, g y ∈ h.domChart.source → (s i y : TangentSpace I (g y)) =
          mpullback I 𝓘(𝕜, E) (h.domChart.extend I)
            (fun z ↦ (h.equiv.symm (0, b i) : TangentSpace 𝓘(𝕜, E) z)) (g y) := by
  intro _ _ _ _
  let hD := hf.isContMDiffDistribution_ker_mfderiv hmn
  let hframe := h.isDistributionFrameOn_ker_mfderiv b hmn
  exact ⟨_, (hframe.isLocalFrameOn_bundleFrame hD).pullback g hg,
    fun i _ hy ↦ hframe.coe_bundleFrame_apply i hy⟩

end Manifold.IsSubmersionAtOfComplement
