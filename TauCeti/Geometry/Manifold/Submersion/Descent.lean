/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Submersion.Basic
public import TauCeti.Geometry.Manifold.Immersion.Differential

/-!
# Differentials and immersions descended through a submersion

Let `q : M → N` be a `C^n` submersion, `n ≠ 0`, whose source has a boundaryless model. A map
`f : N → P` is differentiable at `q x` exactly when `f ∘ q` is differentiable at `x`
(`Manifold.IsSubmersionAt.mdifferentiableAt_comp_iff`), and `f` and `f ∘ q` have the same tangent
image there (`Manifold.IsSubmersionAt.range_mfderiv_comp`). Neither statement assumes any
regularity of `f`.

Over real or complex scalars, with all three models boundaryless and a finite dimensional target
model, a map out of the target of a surjective `C^n` submersion is a `C^m` immersion,
`1 ≤ m ≤ n`, exactly when its composite with the submersion is `C^m` and kills only vertical
tangent vectors of the submersion (`Manifold.IsSubmersion.isImmersion_iff_ker_mfderiv_comp_le`).
This criterion applies to smooth quotients with positive dimensional fibres, including quotients
removing the excess in composition of correspondences.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Theorems 4.26 and 4.29
  (local sections and passing smoothly to a quotient).
-/

public section

open Function Filter Set Manifold
open scoped Manifold ContDiff Topology

namespace Manifold

section Differential

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F G H H' H'' M N P : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace H']
  {J : ModelWithCorners 𝕜 F H'} [TopologicalSpace N] [ChartedSpace H' N]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [TopologicalSpace H'']
  {K : ModelWithCorners 𝕜 G H''} [TopologicalSpace P] [ChartedSpace H'' P]
  {n : ℕ∞ω} {q : M → N} {f : N → P} {x : M}

/-- **Differentiability descends along a submersion.** If `q` is a `C^n` submersion at `x`,
`n ≠ 0`, with boundaryless source model, then `f` is differentiable at `q x` exactly when
`f ∘ q` is differentiable at `x`. Near `q x`, `f` is `f ∘ q` composed with a local section. -/
theorem IsSubmersionAt.mdifferentiableAt_comp_iff (hq : IsSubmersionAt I J n q x) (hn : n ≠ 0) :
    MDifferentiableAt I K (f ∘ q) x ↔ MDifferentiableAt J K f (q x) := by
  refine ⟨fun hf ↦ ?_, fun hf ↦ hf.comp x (hq.contMDiffAt.mdifferentiableAt hn)⟩
  obtain ⟨U, hU, hxU, s, hsx, hs, hqs⟩ := hq.exists_contMDiffOn_section
  have hfs : MDifferentiableAt J K ((f ∘ q) ∘ s) (q x) :=
    (hsx ▸ hf).comp (q x) ((hs.contMDiffAt (hU.mem_nhds hxU)).mdifferentiableAt hn)
  exact hfs.congr_of_eventuallyEq <| eventually_of_mem (hU.mem_nhds hxU) fun y hy ↦ by
    rw [comp_apply, comp_apply, hqs y hy]

/-- **Tangent images are unchanged by precomposing with a submersion.** If `q` is a `C^n`
submersion at `x`, `n ≠ 0`, with boundaryless source model, then `f ∘ q` and `f` have the same
tangent image at `x` and `q x`. No regularity of `f` is assumed: where `f` is not differentiable,
both differentials vanish. -/
theorem IsSubmersionAt.range_mfderiv_comp (hq : IsSubmersionAt I J n q x) (hn : n ≠ 0) :
    LinearMap.range (mfderiv I K (f ∘ q) x).toLinearMap =
      LinearMap.range (mfderiv J K f (q x)).toLinearMap := by
  by_cases hf : MDifferentiableAt J K f (q x)
  · rw [mfderiv_comp x hf (hq.contMDiffAt.mdifferentiableAt hn),
      ContinuousLinearMap.toLinearMap_comp]
    exact LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.mpr (hq.surjective_mfderiv hn))
  · rw [mfderiv_zero_of_not_mdifferentiableAt hf, mfderiv_zero_of_not_mdifferentiableAt
      (mt (hq.mdifferentiableAt_comp_iff hn).mp hf)]
    simp

end Differential

namespace IsSubmersion

variable {𝕜 : Type*} [RCLike 𝕜]
  {E F G H H' H'' M N P : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace H']
  {J : ModelWithCorners 𝕜 F H'} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H' N]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [FiniteDimensional 𝕜 G]
  [TopologicalSpace H''] {K : ModelWithCorners 𝕜 G H''} [K.Boundaryless]
  [TopologicalSpace P] [ChartedSpace H'' P]
  {m n : ℕ∞ω} [IsManifold J m N] [IsManifold K m P] {q : M → N} {f : N → P}

/-- **Immersions descend along a surjective submersion.** Over real or complex scalars, with
boundaryless models and a finite dimensional target model, let `q` be a surjective `C^n`
submersion and `1 ≤ m ≤ n`. A map `f` out of the target of `q` is a `C^m` immersion exactly when
`f ∘ q` is `C^m` and its differential kills only vertical vectors of `q`. The reverse inclusion
of kernels is automatic. The source of `q` need not be finite dimensional. -/
theorem isImmersion_iff_ker_mfderiv_comp_le (hq : IsSubmersion I J n q)
    (hsurj : Surjective q) (hm : 1 ≤ m) (hmn : m ≤ n) :
    IsImmersion J K m f ↔ ContMDiff I K m (f ∘ q) ∧
      ∀ x, (mfderiv I K (f ∘ q) x).ker ≤ (mfderiv I J q x).ker := by
  have hm0 : m ≠ 0 := ne_of_gt (zero_lt_one.trans_le hm)
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le (hm.trans hmn))
  constructor
  · intro hf
    refine ⟨hf.contMDiff.comp (hq.contMDiff.of_le hmn), fun x ↦ ?_⟩
    rw [mfderiv_comp x (hf.contMDiff.mdifferentiable hm0 _) (hq.contMDiff.mdifferentiable hn0 _),
      ContinuousLinearMap.toLinearMap_comp, LinearMap.ker_comp_of_ker_eq_bot _
        (LinearMap.ker_eq_bot_of_injective (hf.mfderiv_injective hm0 _))]
  · rintro ⟨hfq, hker⟩
    have hf := (hq.contMDiff_comp_iff hsurj hmn).mp hfq
    apply hf.isImmersion_of_injective_mfderiv hm
    intro y
    obtain ⟨x, rfl⟩ := hsurj y
    apply (injective_iff_map_eq_zero _).mpr
    intro v hv
    obtain ⟨u, rfl⟩ := hq.surjective_mfderiv hn0 x v
    have hu : u ∈ (mfderiv I K (f ∘ q) x).ker := by
      rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
        mfderiv_comp x (hf.mdifferentiable hm0 _) (hq.contMDiff.mdifferentiable hn0 _),
        ContinuousLinearMap.comp_apply]
      exact hv
    exact LinearMap.mem_ker.mp (hker x hu)

end IsSubmersion

end Manifold
