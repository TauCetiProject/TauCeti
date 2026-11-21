/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Quotient.Picard
public import TauCeti.Topology.Covering.CharacterBundle

/-!
# Duals of character line bundles

Let `p : E → X` be a quotient covering map for a group `G` (`IsQuotientCoveringMap p G`) over a
charted space `X`. Building on `IsQuotientCoveringMap.characterContMDiffCore IB n χ` from
`TauCeti.Geometry.Manifold.Quotient.Picard` and
`IsQuotientCoveringMap.characterFiniteRankCoreInvIso` from
`TauCeti.Topology.Covering.CharacterBundle`, this file provides:

* `IsQuotientCoveringMap.characterContMDiffCoreDualIso` and
  `IsQuotientCoveringMap.characterFiniteRankCoreInvDiffeomorph`: over a complete scalar field, the
  dual `(hp.characterContMDiffCore IB n χ).dual` is canonically isomorphic in
  `ContMDiffFiniteRankBundleCore IB n X` to `hp.characterContMDiffCore IB n χ⁻¹`, with glued
  `C^n` total-space equivalence over `X`.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, Section 2.2.
-/

public section

open TauCeti TauCeti.FiniteRankBundleCore
open scoped Manifold ContDiff

namespace IsQuotientCoveringMap

section Dual

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB}
  {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X] [ChartedSpace HB X]
  [Group G] [MulAction G E] {p : E → X} (hp : IsQuotientCoveringMap p G) {n : ℕ∞ω}

section

variable (IB n) [CompleteSpace 𝕜]

/-- Over a complete scalar field, the dual of `hp.characterContMDiffCore IB n χ` is canonically
isomorphic in `ContMDiffFiniteRankBundleCore IB n X` to `hp.characterContMDiffCore IB n χ⁻¹`. -/
noncomputable def characterContMDiffCoreDualIso (χ : G →* 𝕜ˣ) :
    (hp.characterContMDiffCore IB n χ).dual ≅ hp.characterContMDiffCore IB n χ⁻¹ :=
  ContMDiffFiniteRankBundleCore.constIso
    (A := (hp.characterContMDiffCore IB n χ).dual)
    (D := hp.characterContMDiffCore IB n χ⁻¹)
    (hp.baseSet_dual_characterFiniteRankCore χ) (ContinuousLinearEquiv.refl 𝕜 (Fin 1 → 𝕜))
    (hp.coordChange_characterFiniteRankCore_inv_intertwines χ)

@[simp] theorem characterContMDiffCoreDualIso_hom_toHom (χ : G →* 𝕜ˣ) :
    (hp.characterContMDiffCoreDualIso IB n χ).hom.toHom =
      (hp.characterFiniteRankCoreInvIso χ).hom :=
  (ContMDiffFiniteRankBundleCore.constIso_hom_toHom _ _ _).trans
    (hp.characterFiniteRankCoreInvIso_def χ ▸ rfl)

@[simp] theorem characterContMDiffCoreDualIso_inv_toHom (χ : G →* 𝕜ˣ) :
    (hp.characterContMDiffCoreDualIso IB n χ).inv.toHom =
      (hp.characterFiniteRankCoreInvIso χ).inv :=
  (ContMDiffFiniteRankBundleCore.constIso_inv_toHom _ _ _).trans
    (hp.characterFiniteRankCoreInvIso_def χ ▸ rfl)

end

/-- Over a complete scalar field, the `C^n` bundle equivalence identifying
`(hp.characterFiniteRankCore χ).dual` with `hp.characterFiniteRankCore χ⁻¹` over the identity of
`X`. -/
noncomputable def characterFiniteRankCoreInvDiffeomorph [CompleteSpace 𝕜] (χ : G →* 𝕜ˣ) :
    (hp.characterFiniteRankCore χ).dual.core.TotalSpace ≃ₘ^n⟮
      IB.prod 𝓘(𝕜, Fin (hp.characterFiniteRankCore χ).dual.rank → 𝕜),
      IB.prod 𝓘(𝕜, Fin (hp.characterFiniteRankCore χ⁻¹).rank → 𝕜)⟯
    (hp.characterFiniteRankCore χ⁻¹).core.TotalSpace :=
  constIsoDiffeomorph (A := (hp.characterFiniteRankCore χ).dual)
    (D := hp.characterFiniteRankCore χ⁻¹)
    (hp.baseSet_dual_characterFiniteRankCore χ) (ContinuousLinearEquiv.refl 𝕜 (Fin 1 → 𝕜))
    (hp.coordChange_characterFiniteRankCore_inv_intertwines χ)

@[simp] theorem coe_characterFiniteRankCoreInvDiffeomorph [CompleteSpace 𝕜] (χ : G →* 𝕜ˣ) :
    ⇑(hp.characterFiniteRankCoreInvDiffeomorph (IB := IB) (n := n) χ) =
      (hp.characterFiniteRankCoreInvIso χ).hom.totalSpaceMap := by
  rw [hp.characterFiniteRankCoreInvIso_def χ]
  exact coe_constIsoDiffeomorph (I := IB) (n := n) _ _ _

@[simp] theorem coe_characterFiniteRankCoreInvDiffeomorph_symm [CompleteSpace 𝕜] (χ : G →* 𝕜ˣ) :
    ⇑(hp.characterFiniteRankCoreInvDiffeomorph (IB := IB) (n := n) χ).symm =
      (hp.characterFiniteRankCoreInvIso χ).inv.totalSpaceMap := by
  rw [hp.characterFiniteRankCoreInvIso_def χ]
  exact coe_constIsoDiffeomorph_symm (I := IB) (n := n) _ _ _

end Dual

end IsQuotientCoveringMap
