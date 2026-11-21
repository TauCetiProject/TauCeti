/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Covering.AssociatedBundle
public import TauCeti.Topology.VectorBundle.FiniteRank.Dual

/-!
# Duals of character line bundles

Let `p : E → X` present `X` as the quotient of `E` by a group `G` (`IsQuotientCoveringMap p G`).
For each character `χ : G →* 𝕜ˣ`, `IsQuotientCoveringMap.characterFiniteRankCore χ :
FiniteRankBundleCore 𝕜 X` is the point-indexed rank-one presentation from
`TauCeti.Topology.Covering.AssociatedBundle`.

Building on that foundation, this file provides:

* `IsQuotientCoveringMap.characterFiniteRankCoreInvIso`: over a complete scalar field, the dual
  `(hp.characterFiniteRankCore χ).dual` is canonically isomorphic to
  `hp.characterFiniteRankCore χ⁻¹`.

## References

* Norman Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §§2–3, §8.
* Daniel Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, Section 2.2.
-/

public section

open Bundle CategoryTheory MonoidalCategory ContinuousLinearEquiv ContinuousLinearMap Set
open TauCeti TauCeti.FiniteRankBundleCore VectorBundleCore

namespace IsQuotientCoveringMap

variable {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X] [Group G] [MulAction G E]
  {p : E → X} (hp : IsQuotientCoveringMap p G) {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-! ### Duals of character cores -/

/-- Chart domains of `(hp.characterFiniteRankCore χ).dual` coincide with those of
`hp.characterFiniteRankCore χ⁻¹`. -/
theorem baseSet_dual_characterFiniteRankCore [CompleteSpace 𝕜] (χ : G →* 𝕜ˣ) (x : X) :
    (hp.characterFiniteRankCore χ).dual.core.baseSet x =
      (hp.characterFiniteRankCore χ⁻¹).core.baseSet x := by
  simp [VectorBundleCore.baseSet_at]

/-- On chart overlaps, the dual transition map of `hp.characterFiniteRankCore χ` coincides with the
transition map of `hp.characterFiniteRankCore χ⁻¹`. -/
theorem coordChange_characterFiniteRankCore_inv_intertwines [CompleteSpace 𝕜] (χ : G →* 𝕜ˣ)
    (i j x : X) (hi : x ∈ (hp.characterFiniteRankCore χ).dual.core.baseSet i)
    (hj : x ∈ (hp.characterFiniteRankCore χ).dual.core.baseSet j) :
    (ContinuousLinearEquiv.refl 𝕜 (Fin 1 → 𝕜) : (Fin 1 → 𝕜) →L[𝕜] (Fin 1 → 𝕜)).comp
        ((hp.characterFiniteRankCore χ).dual.core.coordChange i j x) =
      ((hp.characterFiniteRankCore χ⁻¹).core.coordChange i j x).comp
        (ContinuousLinearEquiv.refl 𝕜 (Fin 1 → 𝕜) : (Fin 1 → 𝕜) →L[𝕜] (Fin 1 → 𝕜)) := by
  have hi' : x ∈ (hp.isLocalHomeomorph.localInverseAt (Function.surjInv hp.surjective i)).source :=
    by simpa [VectorBundleCore.baseSet_at] using hi
  have hj' : x ∈ (hp.isLocalHomeomorph.localInverseAt (Function.surjInv hp.surjective j)).source :=
    by simpa [VectorBundleCore.baseSet_at] using hj
  rw [coordChange_dual, hp.characterFiniteRankCore_coordChange χ j i x,
    hp.characterFiniteRankCore_coordChange χ⁻¹ i j x, piTranspose_smul, piTranspose_id,
    hp.deckChange_inv ⟨hi', hj'⟩, map_inv, MonoidHom.inv_apply, ContinuousLinearEquiv.coe_refl]
  exact ContinuousLinearMap.ext fun _ ↦ rfl

/-- Over a complete scalar field, the dual of `hp.characterFiniteRankCore χ` is canonically
isomorphic to `hp.characterFiniteRankCore χ⁻¹`, acting as the identity on every coordinate fibre. -/
noncomputable def characterFiniteRankCoreInvIso [CompleteSpace 𝕜] (χ : G →* 𝕜ˣ) :
    (hp.characterFiniteRankCore χ).dual ≅ hp.characterFiniteRankCore χ⁻¹ :=
  constIso (A := (hp.characterFiniteRankCore χ).dual) (D := hp.characterFiniteRankCore χ⁻¹)
    (hp.baseSet_dual_characterFiniteRankCore χ) (ContinuousLinearEquiv.refl 𝕜 (Fin 1 → 𝕜))
    (hp.coordChange_characterFiniteRankCore_inv_intertwines χ)

/-- `hp.characterFiniteRankCoreInvIso χ` is the constant isomorphism induced by the identity
equivalence on `Fin 1 → 𝕜`. -/
theorem characterFiniteRankCoreInvIso_def [CompleteSpace 𝕜] (χ : G →* 𝕜ˣ) :
    hp.characterFiniteRankCoreInvIso χ =
      constIso (A := (hp.characterFiniteRankCore χ).dual) (D := hp.characterFiniteRankCore χ⁻¹)
        (hp.baseSet_dual_characterFiniteRankCore χ) (ContinuousLinearEquiv.refl 𝕜 (Fin 1 → 𝕜))
        (hp.coordChange_characterFiniteRankCore_inv_intertwines χ) := (rfl)

@[simp]
theorem fiberMap_characterFiniteRankCoreInvIso_hom [CompleteSpace 𝕜] (χ : G →* 𝕜ˣ) (x : X) :
    (hp.characterFiniteRankCoreInvIso χ).hom.fiberMap x = ContinuousLinearMap.id 𝕜 (Fin 1 → 𝕜) :=
  fiberMap_constIso_hom _ _ _ x

@[simp]
theorem fiberMap_characterFiniteRankCoreInvIso_inv [CompleteSpace 𝕜] (χ : G →* 𝕜ˣ) (x : X) :
    (hp.characterFiniteRankCoreInvIso χ).inv.fiberMap x = ContinuousLinearMap.id 𝕜 (Fin 1 → 𝕜) :=
  fiberMap_constIso_inv _ _ _ x

end IsQuotientCoveringMap
