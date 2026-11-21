/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Covering.AssociatedBundle
public import TauCeti.Topology.VectorBundle.FiniteRank.Dual

/-!
# Duals and cocycle twisting for character line bundles

Let `p : E → X` present `X` as the quotient of `E` by a group `G` (`IsQuotientCoveringMap p G`).
For each character `χ : G →* 𝕜ˣ`, `IsQuotientCoveringMap.characterCore χ` is the scalar line-bundle
core over `X` with transitions multiplying by `χ (deckChange e e' x)`, and
`IsQuotientCoveringMap.characterFiniteRankCore χ : FiniteRankBundleCore 𝕜 X` is its point-indexed
rank-one presentation from `TauCeti.Topology.Covering.AssociatedBundle`.

Building on that foundation, this file provides:

* `IsQuotientCoveringMap.deckChange_inv`: inverting the order of local sections inverts the deck
  transformation;
* `IsQuotientCoveringMap.characterFiniteRankCoreInvIso`: over a complete scalar field, the dual
  `(hp.characterFiniteRankCore χ).dual` is canonically isomorphic to
  `hp.characterFiniteRankCore χ⁻¹`;
* `IsQuotientCoveringMap.characterCoreHomEquiv`: twisting chart operators by
  `χ₁⁻¹ (deckChange e e' x)` identifies cocycle morphisms from `hp.characterCore χ₁` to
  `hp.characterCore χ₂` with cocycle morphisms from `hp.characterCore 1` to
  `hp.characterCore (χ₁⁻¹ * χ₂)` while preserving all fibre maps, without completeness assumptions.

## References

* Norman Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §§2–3, §8.
* Daniel Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, Section 2.2.
-/

public section

open Bundle CategoryTheory MonoidalCategory ContinuousLinearEquiv ContinuousLinearMap Set
open TauCeti TauCeti.FiniteRankBundleCore VectorBundleCore

namespace IsQuotientCoveringMap

variable {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X] [Group G] [MulAction G E]
  {p : E → X} (hp : IsQuotientCoveringMap p G)

/-! ### Symmetry of deck transformations and character-core charts -/

/-- Reversing the order of two local sections over a common point of their domains inverts the deck
transformation between them. -/
theorem deckChange_inv {e e' : E} {x : X}
    (h : x ∈ (hp.isLocalHomeomorph.localInverseAt e).source ∩
      (hp.isLocalHomeomorph.localInverseAt e').source) :
    hp.deckChange e' e x = (hp.deckChange e e' x)⁻¹ :=
  mul_eq_one_iff_eq_inv.1 <| by
    rw [hp.deckChange_mul_deckChange ⟨h, h.1⟩, hp.deckChange_self h.1]

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- The chart domain of `hp.characterCore χ` through `e` is the domain of the local section of `p`
through `e`, independently of `χ`. -/
theorem characterCore_baseSet (χ : G →* 𝕜ˣ) (e : E) :
    (hp.characterCore χ).baseSet e = (hp.isLocalHomeomorph.localInverseAt e).source := by
  rw [characterCore_def, associatedCore_baseSet]

@[simp] theorem characterCore_localTriv_baseSet (χ : G →* 𝕜ˣ) (e : E) :
    ((hp.characterCore χ).localTriv e).baseSet =
      (hp.isLocalHomeomorph.localInverseAt e).source := by
  rw [characterCore_def, associatedCore_localTriv_baseSet]

/-- The preferred chart index of `hp.characterCore χ` at `x` is `Function.surjInv hp.surjective x`,
independently of `χ`. -/
@[simp] theorem characterCore_indexAt (χ : G →* 𝕜ˣ) (x : X) :
    (hp.characterCore χ).indexAt x = Function.surjInv hp.surjective x := by
  rw [characterCore_def, associatedCore_indexAt]

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

/-! ### Twisting cocycle morphisms between scalar character cores -/

/-- On the common domain of charts `e` and `e'`, reading a family of fibre maps `ϕ` between
`hp.characterCore χ₁` and `hp.characterCore χ₂` differs from reading `ϕ` between
`hp.characterCore 1` and `hp.characterCore (χ₁⁻¹ * χ₂)` by the locally constant scalar
`χ₁ (hp.deckChange e e' x)`. -/
theorem inChartCoordinates_characterCore_eq_smul (χ₁ χ₂ : G →* 𝕜ˣ) (ϕ : X → 𝕜 →L[𝕜] 𝕜)
    (e e' : E) {x : X}
    (hx : x ∈ (hp.isLocalHomeomorph.localInverseAt e).source ∩
      (hp.isLocalHomeomorph.localInverseAt e').source) :
    (hp.characterCore χ₁).inChartCoordinates (hp.characterCore χ₂) e e' x (ϕ x) =
      (χ₁ (hp.deckChange e e' x) : 𝕜) •
        (hp.characterCore 1).inChartCoordinates (hp.characterCore (χ₁⁻¹ * χ₂)) e e' x (ϕ x) := by
  set i₀ := Function.surjInv hp.surjective x
  have hi₀ : x ∈ (hp.isLocalHomeomorph.localInverseAt i₀).source := by
    simpa only [i₀, Function.surjInv_eq hp.surjective x] using
      hp.isLocalHomeomorph.apply_self_mem_localInverseAt_source (x := i₀)
  have hmul : χ₁ (hp.deckChange e e' x) * (χ₁ (hp.deckChange i₀ e' x))⁻¹ =
      χ₁ (hp.deckChange e i₀ x) := by
    rw [← hp.deckChange_mul_deckChange ⟨⟨hx.1, hi₀⟩, hx.2⟩, map_mul, mul_comm, inv_mul_cancel_left]
  refine ContinuousLinearMap.ext fun v ↦ ?_
  have hmap : ∀ a b : 𝕜, (ϕ x) (a * b) = a * (ϕ x) b := fun a b ↦ (ϕ x).map_smul a b
  simp only [_root_.smul_apply, inChartCoordinates_apply, characterCore_indexAt,
    hp.characterCore_coordChange_apply, hp.characterCore_one_coordChange,
    ContinuousLinearMap.id_apply, smul_eq_mul]
  rw [hmap, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, ← hmul, Units.val_mul]
  ring

/-- Twisting a cocycle morphism `a : CoordinateHom (hp.characterCore χ₁) (hp.characterCore χ₂)` by
`ψ`-multiplying its chart operators yields a cocycle morphism from `hp.characterCore χ₁'` to
`hp.characterCore χ₂'` with the same fibre maps whenever `ψ * χ₁ = χ₁'` and `ψ * χ₂ = χ₂'`. -/
private noncomputable def twistCharacterCoreHom {χ₁ χ₂ χ₁' χ₂' : G →* 𝕜ˣ} (ψ : G →* 𝕜ˣ)
    (h₁ : ψ * χ₁ = χ₁') (h₂ : ψ * χ₂ = χ₂')
    (a : CoordinateHom (hp.characterCore χ₁) (hp.characterCore χ₂)) :
    CoordinateHom (hp.characterCore χ₁') (hp.characterCore χ₂') where
  operator e e' :=
    let re : ↥((hp.characterCore χ₁').baseSet e ∩ (hp.characterCore χ₂').baseSet e') →
        ↥((hp.characterCore χ₁).baseSet e ∩ (hp.characterCore χ₂).baseSet e') :=
      fun x ↦ ⟨x.val, ⟨by simpa using x.property.1, by simpa using x.property.2⟩⟩
    ⟨fun x ↦ (ψ (hp.deckChange e e' x.val) : 𝕜) • a.operator e e' (re x),
      continuous_iff_continuousAt.2 fun x ↦ by
        have hx : x.val ∈ (hp.isLocalHomeomorph.localInverseAt e).source ∩
            (hp.isLocalHomeomorph.localInverseAt e').source := by simpa using x.property
        have hconst : ContinuousAt (fun y : ↥((hp.characterCore χ₁').baseSet e ∩
            (hp.characterCore χ₂').baseSet e') ↦ (ψ (hp.deckChange e e' y.val) : 𝕜)) x :=
          continuousAt_const.congr <| Filter.Eventually.mono
            (continuous_subtypeVal.continuousAt.eventually (hp.eventually_deckChange_eq hx))
            fun y hy ↦ congrArg (fun g ↦ (ψ g : 𝕜)) hy.symm
        exact hconst.smul ((a.operator e e').continuous.comp
          (continuous_subtypeVal.subtype_mk _)).continuousAt⟩
  compatible e₁ e₂ e₁' e₂' x he₁ he₂ he₁' he₂' v := by
    rw [characterCore_baseSet] at he₁ he₂ he₁' he₂'
    have hcompat := a.compatible e₁ e₂ e₁' e₂' x (by simpa using he₁) (by simpa using he₂)
      (by simpa using he₁') (by simpa using he₂') ((ψ (hp.deckChange e₁ e₂ x) : 𝕜) * v)
    rw [← smul_eq_mul, _root_.map_smul, smul_eq_mul, hp.characterCore_coordChange_apply,
      hp.characterCore_coordChange_apply] at hcompat
    have hc : (ψ (hp.deckChange e₁' e₂' x) : 𝕜) * (ψ (hp.deckChange e₁ e₁' x) : 𝕜) =
        (ψ (hp.deckChange e₂ e₂' x) : 𝕜) * (ψ (hp.deckChange e₁ e₂ x) : 𝕜) := by
      exact_mod_cast (by
        rw [← map_mul, ← map_mul, hp.deckChange_mul_deckChange ⟨⟨he₁, he₁'⟩, he₂'⟩,
          hp.deckChange_mul_deckChange ⟨⟨he₁, he₂⟩, he₂'⟩])
    have h₁x : (χ₁' (hp.deckChange e₁ e₂ x) : 𝕜) =
        (ψ (hp.deckChange e₁ e₂ x) : 𝕜) * (χ₁ (hp.deckChange e₁ e₂ x) : 𝕜) := by rw [← h₁]; simp
    have h₂x : (χ₂' (hp.deckChange e₁' e₂' x) : 𝕜) =
        (ψ (hp.deckChange e₁' e₂' x) : 𝕜) * (χ₂ (hp.deckChange e₁' e₂' x) : 𝕜) := by rw [← h₂]; simp
    simp only [ContinuousMap.coe_mk, _root_.smul_apply, smul_eq_mul,
      hp.characterCore_coordChange_apply, h₁x, h₂x]
    calc _ = (ψ (hp.deckChange e₁' e₂' x) : 𝕜) * (ψ (hp.deckChange e₁ e₁' x) : 𝕜) *
            ((χ₂ (hp.deckChange e₁' e₂' x) : 𝕜) * a.operator e₁ e₁' _ v) := by ring
      _ = (ψ (hp.deckChange e₂ e₂' x) : 𝕜) * ((χ₂ (hp.deckChange e₁' e₂' x) : 𝕜) *
            ((ψ (hp.deckChange e₁ e₂ x) : 𝕜) * a.operator e₁ e₁' _ v)) := by rw [hc]; ring
      _ = _ := by rw [hcompat]; congr 2; ring

private theorem fiberMap_twistCharacterCoreHom {χ₁ χ₂ χ₁' χ₂' : G →* 𝕜ˣ} (ψ : G →* 𝕜ˣ)
    (h₁ : ψ * χ₁ = χ₁') (h₂ : ψ * χ₂ = χ₂')
    (a : CoordinateHom (hp.characterCore χ₁) (hp.characterCore χ₂)) (x : X) :
    (hp.twistCharacterCoreHom ψ h₁ h₂ a).fiberMap x = a.fiberMap x := by
  rw [CoordinateHom.fiberMap_def]
  simp only [twistCharacterCoreHom, ContinuousMap.coe_mk, CoordinateHom.operator_eq]
  have hs : x ∈
      (hp.isLocalHomeomorph.localInverseAt (Function.surjInv hp.surjective x)).source := by
    simpa only [Function.surjInv_eq hp.surjective x] using
      hp.isLocalHomeomorph.apply_self_mem_localInverseAt_source
        (x := Function.surjInv hp.surjective x)
  ext; simp [inChartCoordinates_apply, hp.deckChange_self hs]

/-- Cocycle morphisms between `hp.characterCore χ₁` and `hp.characterCore χ₂` correspond
additively to cocycle morphisms between `hp.characterCore 1` and `hp.characterCore (χ₁⁻¹ * χ₂)`
with the exact same fibre maps, without completeness assumptions on `𝕜`. -/
noncomputable def characterCoreHomEquiv (χ₁ χ₂ : G →* 𝕜ˣ) :
    CoordinateHom (hp.characterCore χ₁) (hp.characterCore χ₂) ≃+
      CoordinateHom (hp.characterCore 1) (hp.characterCore (χ₁⁻¹ * χ₂)) where
  toFun := hp.twistCharacterCoreHom χ₁⁻¹ (inv_mul_cancel χ₁) rfl
  invFun := hp.twistCharacterCoreHom χ₁ (mul_one χ₁) (mul_inv_cancel_left χ₁ χ₂)
  left_inv _ := CoordinateHom.fiberMap_injective <| funext fun _ ↦ by
    rw [fiberMap_twistCharacterCoreHom, fiberMap_twistCharacterCoreHom]
  right_inv _ := CoordinateHom.fiberMap_injective <| funext fun _ ↦ by
    rw [fiberMap_twistCharacterCoreHom, fiberMap_twistCharacterCoreHom]
  map_add' _ _ := CoordinateHom.fiberMap_injective <| funext fun _ ↦ by
    simp [CoordinateHom.fiberMap_add, fiberMap_twistCharacterCoreHom]

@[simp] theorem fiberMap_characterCoreHomEquiv (χ₁ χ₂ : G →* 𝕜ˣ)
    (a : CoordinateHom (hp.characterCore χ₁) (hp.characterCore χ₂)) (x : X) :
    (hp.characterCoreHomEquiv χ₁ χ₂ a).fiberMap x = a.fiberMap x :=
  hp.fiberMap_twistCharacterCoreHom χ₁⁻¹ (inv_mul_cancel χ₁) rfl a x

@[simp] theorem fiberMap_characterCoreHomEquiv_symm (χ₁ χ₂ : G →* 𝕜ˣ)
    (b : CoordinateHom (hp.characterCore 1) (hp.characterCore (χ₁⁻¹ * χ₂))) (x : X) :
    ((hp.characterCoreHomEquiv χ₁ χ₂).symm b).fiberMap x = b.fiberMap x :=
  hp.fiberMap_twistCharacterCoreHom χ₁ (mul_one χ₁) (mul_inv_cancel_left χ₁ χ₂) b x

/-- Reading a fibrewise scalar-multiplication map `v ↦ v • s x` from `hp.characterCore 1` to
`hp.characterCore χ` in charts `(e, e')` gives scalar multiplication by the local coordinate of `s`
in the chart `e'`. -/
theorem inChartCoordinates_characterCore_one_smulRight (χ : G →* 𝕜ˣ)
    (s : X → 𝕜) (e e' : E) (x : X) :
    (hp.characterCore 1).inChartCoordinates (hp.characterCore χ) e e' x
        ((ContinuousLinearMap.id 𝕜 𝕜).smulRight (s x)) =
      (ContinuousLinearMap.id 𝕜 𝕜).smulRight
        (((hp.characterCore χ).localTriv e' ⟨x, s x⟩).snd) := by
  refine ContinuousLinearMap.ext fun v ↦ ?_
  rw [inChartCoordinates_apply, hp.characterCore_one_coordChange, ContinuousLinearMap.id_apply,
    smulRight_apply, ContinuousLinearMap.id_apply, _root_.map_smul, localTriv_apply,
    smulRight_apply, ContinuousLinearMap.id_apply]

end IsQuotientCoveringMap
