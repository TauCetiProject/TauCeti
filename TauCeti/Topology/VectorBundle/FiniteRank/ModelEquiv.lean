/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Basic

/-!
# Model-equivalence coordinate changes for vector bundles

Given a vector bundle `V` with model fibre `F`, `TauCeti.FiniteRankBundleCore.ofBundle 𝕜 e V`
presents `V` as a point-indexed `FiniteRankBundleCore 𝕜 B` of rank `r` along a continuous linear
equivalence `e : F ≃L[𝕜] (Fin r → 𝕜)`. Changing the coordinate equivalence from `e₁` to `e₂`
induces a canonical core isomorphism `ofBundleChangeIso e₁ e₂ V` with fibre map `e₂ ∘ e₁⁻¹`,
compatible with the fibre identifications `ofBundleFiberEquiv`.

## References

* Norman Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §2–§3.
* John W. Milnor and James D. Stasheff, *Characteristic Classes*, Princeton University Press, 1974,
  §3.
-/

public section

open Bundle CategoryTheory FiberBundle Set VectorBundleCore

namespace TauCeti.FiniteRankBundleCore

variable {𝕜 B F : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

section ChangeEquiv

variable {r₁ r₂ : ℕ} (e₁ : F ≃L[𝕜] (Fin r₁ → 𝕜)) (e₂ : F ≃L[𝕜] (Fin r₂ → 𝕜)) (V : B → Type*)
  [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- The constant coordinate equivalence `e₂ ∘ e₁⁻¹` intertwines the transition functions of
`ofBundle 𝕜 e₁ V` and `ofBundle 𝕜 e₂ V`. -/
theorem coordChange_ofBundle_intertwines (i j x : B) :
    (e₁.symm.trans e₂).toContinuousLinearMap.comp ((ofBundle 𝕜 e₁ V).core.coordChange i j x) =
      ((ofBundle 𝕜 e₂ V).core.coordChange i j x).comp
        (e₁.symm.trans e₂).toContinuousLinearMap := by
  rw [coordChange_ofBundle, coordChange_ofBundle]
  exact ContinuousLinearMap.ext fun _ ↦
    congrArg e₂ <| (e₁.symm_apply_apply _).trans (congrArg _ (e₂.symm_apply_apply _).symm)

/-- Changing the coordinate equivalence of the model fibre from `e₁` to `e₂` induces a canonical
isomorphism of finite-rank cores with constant fibre map `e₂ ∘ e₁⁻¹`. -/
noncomputable def ofBundleChangeIso :
    ofBundle 𝕜 e₁ V ≅ ofBundle 𝕜 e₂ V :=
  constIso (fun i ↦ ((baseSet_ofBundle e₁ V i).trans (baseSet_ofBundle e₂ V i).symm).le)
    (e₁.symm.trans e₂) fun i j x _ _ ↦ coordChange_ofBundle_intertwines e₁ e₂ V i j x

@[simp]
theorem fiberMap_ofBundleChangeIso_hom (x : B) :
    (ofBundleChangeIso e₁ e₂ V).hom.fiberMap x = (e₁.symm.trans e₂).toContinuousLinearMap :=
  fiberMap_constIso_hom _ _ _ x

@[simp]
theorem fiberMap_ofBundleChangeIso_inv (x : B) :
    (ofBundleChangeIso e₁ e₂ V).inv.fiberMap x = (e₂.symm.trans e₁).toContinuousLinearMap :=
  fiberMap_constIso_inv _ _ _ x

theorem ofBundleChangeIso_inv :
    (ofBundleChangeIso e₁ e₂ V).inv = (ofBundleChangeIso e₂ e₁ V).hom :=
  hom_ext fun x ↦ by
    simp only [fiberMap_ofBundleChangeIso_inv, fiberMap_ofBundleChangeIso_hom]

theorem ofBundleChangeIso_symm :
    (ofBundleChangeIso e₁ e₂ V).symm = ofBundleChangeIso e₂ e₁ V :=
  Iso.ext (ofBundleChangeIso_inv e₁ e₂ V)

/-- Changing the coordinate equivalence commutes with `ofBundleFiberEquiv`. -/
theorem ofBundleFiberEquiv_changeIso (x : B) (v : Fin r₁ → 𝕜) :
    ofBundleFiberEquiv e₂ V x ((ofBundleChangeIso e₁ e₂ V).hom.fiberMap x v) =
      ofBundleFiberEquiv e₁ V x v := by
  rw [fiberMap_ofBundleChangeIso_hom, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.trans_apply, ofBundleFiberEquiv_apply, ofBundleFiberEquiv_apply]
  exact congrArg ((trivializationAt F V x).symm x) (e₂.symm_apply_apply (e₁.symm v))

end ChangeEquiv

end TauCeti.FiniteRankBundleCore
