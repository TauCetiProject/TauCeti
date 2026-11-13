/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Submersion.Basic
public import TauCeti.Geometry.Manifold.Immersion.Differential

/-!
# Immersions descended through a surjective submersion

A map out of the target of a surjective submersion is smooth exactly when its composite with
the submersion is smooth (`Manifold.IsSubmersion.contMDiff_comp_iff`). If moreover the composite
kills precisely the vertical tangent vectors of the submersion, the descended map is an
immersion. This criterion applies to smooth quotients with positive dimensional fibres,
including quotients removing the excess in composition of correspondences.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Theorems 4.26 and 4.29
  (local sections and passing smoothly to a quotient).
-/

public section

open Function Filter Set Manifold
open scoped Manifold ContDiff Topology

namespace Manifold.IsSubmersion

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
  {n : ℕ∞ω} [IsManifold J n N] [IsManifold K n P] {q : M → N} {f : N → P}

/-- A map descended through a surjective submersion is an immersion exactly when the original
map is smooth and its differential has precisely the vertical kernel. The target model is
finite dimensional; the source of the submersion need not be. -/
theorem isImmersion_iff_ker_mfderiv_comp (hq : IsSubmersion I J n q)
    (hsurj : Surjective q) (hn : 1 ≤ n) :
    IsImmersion J K n f ↔ ContMDiff I K n (f ∘ q) ∧
      ∀ x, (mfderiv I K (f ∘ q) x).ker = (mfderiv I J q x).ker := by
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  constructor
  · intro hf
    refine ⟨hf.contMDiff.comp hq.contMDiff, fun x ↦ ?_⟩
    rw [mfderiv_comp x (hf.contMDiff.mdifferentiable hn0 _) (hq.contMDiff.mdifferentiable hn0 _),
      ContinuousLinearMap.toLinearMap_comp]
    exact LinearMap.ker_comp_of_ker_eq_bot _
      (LinearMap.ker_eq_bot_of_injective (hf.mfderiv_injective hn0 _))
  · rintro ⟨hfq, hker⟩
    have hf := (hq.contMDiff_comp_iff hsurj le_rfl).mp hfq
    apply hf.isImmersion_of_injective_mfderiv hn
    intro y
    obtain ⟨x, rfl⟩ := hsurj y
    apply (injective_iff_map_eq_zero _).mpr
    intro v hv
    obtain ⟨u, rfl⟩ := hq.surjective_mfderiv hn0 x v
    have hu : u ∈ (mfderiv I K (f ∘ q) x).ker := by
      rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
        mfderiv_comp x (hf.mdifferentiable hn0 _) (hq.contMDiff.mdifferentiable hn0 _),
        ContinuousLinearMap.comp_apply]
      exact hv
    exact LinearMap.mem_ker.mp (hker x ▸ hu)

end Manifold.IsSubmersion
