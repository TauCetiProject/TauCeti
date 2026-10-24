/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.GroupAction.GermKernel
public import TauCeti.GroupTheory.GroupAction.Effective

/-!
# Effective reduction of a connected smooth torsion action

The faithful quotient of a torsion group acting by `C¹` maps on a preconnected Hausdorff
boundaryless manifold has trivial germ kernel at every point. Thus quotienting by the global
action kernel really gives an effective chart, rather than just a faithful action. The
identity principle for finite-order smooth actions is essential here.

## References

* A. Adem, J. Leida and Y. Ruan, *Orbifolds and Stringy Topology*, Chapter 1.
-/

public section

open MulAction
open scoped Manifold ContDiff

namespace TauCeti

section Regularity

variable {𝕜 E H M G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
  [Group G] [MulAction G M]

/-- Each element of the quotient action has the same regularity as its representatives. -/
theorem contMDiff_quotientKerToPermHom_smul {n : ℕ∞ω}
    (hsmooth : ∀ g : G, ContMDiff I I n fun x : M ↦ g • x)
    (q : G ⧸ (toPermHom G M).ker) : ContMDiff I I n fun x : M ↦ q • x :=
  QuotientGroup.induction_on q fun g ↦ by
    simpa only [quotientKerToPermHom_mk_smul] using hsmooth g

end Regularity

variable {𝕜 E H M G : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
  [Group G] [MulAction G M]

/-- The faithful quotient of a smooth torsion action on a preconnected Hausdorff boundaryless
manifold is effective: no nonidentity quotient element acts trivially near any point. -/
theorem germKernel_quotientKerToPermHom_eq_bot [I.Boundaryless] [CompleteSpace E]
    [T2Space M] [PreconnectedSpace M]
    (hsmooth : ∀ g : G, ContMDiff I I 1 fun x : M ↦ g • x) (hG : IsMulTorsion G) (x : M) :
    TauCeti.MulAction.germKernel (G ⧸ (toPermHom G M).ker) x = ⊥ := by
  rw [germKernel_eq_ker (contMDiff_quotientKerToPermHom_smul hsmooth)
    (hG.of_surjective (QuotientGroup.mk'_surjective _))]
  exact (MonoidHom.ker_eq_bot_iff _).mpr MulAction.toPerm_injective

end TauCeti
