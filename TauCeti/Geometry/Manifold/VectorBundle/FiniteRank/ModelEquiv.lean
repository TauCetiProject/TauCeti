/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.ModelEquiv
public import TauCeti.Geometry.Manifold.VectorBundle.Core.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.Basic

/-!
# Smooth and holomorphic cores from a coordinate equivalence of the model fibre

This file lifts the coordinate-model constructions of
`TauCeti.Topology.VectorBundle.FiniteRank.ModelEquiv` to `C^n` (and in particular holomorphic, for
`𝕜 = ℂ` and `n = ∞`) vector bundles over a charted space `B`:

* `TauCeti.FiniteRankBundleCore.isContMDiff_ofBundle`: if `V` is a `C^n` vector bundle with
  model fibre `F` and `e : F ≃L[𝕜] (Fin r → 𝕜)`, then `ofBundle 𝕜 e V` is a `C^n` finite-rank
  core;
* `TauCeti.FiniteRankBundleCore.ofBundleTotalSpaceDiffeomorph`: the reconstructed total space
  of `ofBundle 𝕜 e V` is `C^n` diffeomorphic to `TotalSpace F V` over the identity of the base,
  without smoothness or completeness hypotheses;
* `TauCeti.FiniteRankBundleCore.ofBundleChangeDiffeomorph`: changing the coordinate equivalence
  from `e₁` to `e₂` induces a `C^n` diffeomorphism of core total spaces lifting
  `ofBundleChangeIso e₁ e₂ V` and commuting with `ofBundleTotalSpaceDiffeomorph`.

## References

* D. Huybrechts, *Complex Geometry: An Introduction*, §2.2.
* J. W. Milnor and J. D. Stasheff, *Characteristic Classes*, §3.
-/

public section

open Bundle CategoryTheory FiberBundle Set VectorBundleCore
open scoped Manifold ContDiff

namespace TauCeti.FiniteRankBundleCore

variable {𝕜 B F : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  [TopologicalSpace HB] [ChartedSpace HB B] {I : ModelWithCorners 𝕜 EB HB} {n : ℕ∞ω}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

section OfBundle

variable {r : ℕ} (e : F ≃L[𝕜] (Fin r → 𝕜)) (V : B → Type*)
  [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- If `V` is a `C^n` vector bundle with model fibre `F` and `e : F ≃L[𝕜] (Fin r → 𝕜)`, then
`ofBundle 𝕜 e V` is a `C^n` finite-rank core. -/
instance isContMDiff_ofBundle [ContMDiffVectorBundle n F V I] :
    (ofBundle 𝕜 e V).core.IsContMDiff I n where
  contMDiffOn_coordChange i j := by
    rw [baseSet_ofBundle, baseSet_ofBundle]
    exact ((e.arrowCongr e).contDiff.contMDiff.comp_contMDiffOn
      (ContMDiffVectorBundle.contMDiffOn_coordChangeL (IB := I) (n := n)
        (trivializationAt F V i) (trivializationAt F V j))).congr
      fun x _ ↦ coordChange_ofBundle e V i j x

/-- The total-space identification between `(ofBundle 𝕜 e V).core.TotalSpace` and
`TotalSpace F V` is a `C^n` diffeomorphism over the identity of the base, fibrewise `𝕜`-linear via
`ofBundleFiberEquiv`. No smoothness or completeness hypothesis is required. -/
noncomputable def ofBundleTotalSpaceDiffeomorph
    (I : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω) :
    (ofBundle 𝕜 e V).core.TotalSpace ≃ₘ^n⟮I.prod 𝓘(𝕜, Fin (ofBundle 𝕜 e V).rank → 𝕜),
      I.prod 𝓘(𝕜, F)⟯ TotalSpace F V :=
  ((pointIndexedCore 𝕜 F V).congrModelDiffeomorph e I n).symm.trans
    (pointIndexedCoreDiffeomorph 𝕜 F V I n)

@[simp]
theorem ofBundleTotalSpaceDiffeomorph_toHomeomorph :
    (ofBundleTotalSpaceDiffeomorph e V I n).toHomeomorph =
      ofBundleTotalSpaceHomeomorph e V := by
  have h1 : ⇑(pointIndexedCoreDiffeomorph 𝕜 F V I n) = pointIndexedCoreHomeomorph 𝕜 F V := by
    rw [← Diffeomorph.coe_toHomeomorph, pointIndexedCoreDiffeomorph_toHomeomorph]
  have h2 : ⇑((pointIndexedCore 𝕜 F V).congrModelDiffeomorph e I n).symm =
      ((pointIndexedCore 𝕜 F V).congrModelHomeomorph e).symm := by
    rw [← Diffeomorph.coe_toHomeomorph_symm, congrModelDiffeomorph_toHomeomorph]
  refine Homeomorph.ext fun p ↦ ?_
  calc
    (ofBundleTotalSpaceDiffeomorph e V I n).toHomeomorph p
      = (ofBundleTotalSpaceDiffeomorph e V I n) p :=
        congrFun (Diffeomorph.coe_toHomeomorph _) p
    _ = (pointIndexedCoreDiffeomorph 𝕜 F V I n)
          (((pointIndexedCore 𝕜 F V).congrModelDiffeomorph e I n).symm p) :=
        congrFun (Diffeomorph.coe_trans
          ((pointIndexedCore 𝕜 F V).congrModelDiffeomorph e I n).symm
          (pointIndexedCoreDiffeomorph 𝕜 F V I n)) p
    _ = pointIndexedCoreHomeomorph 𝕜 F V
          (((pointIndexedCore 𝕜 F V).congrModelHomeomorph e).symm p) := by
        rw [h1, h2]
    _ = ofBundleTotalSpaceHomeomorph e V p := by
        rw [ofBundleTotalSpaceHomeomorph_def, Homeomorph.trans_apply]

@[simp]
theorem ofBundleTotalSpaceDiffeomorph_apply
    (p : (ofBundle 𝕜 e V).core.TotalSpace) :
    ofBundleTotalSpaceDiffeomorph e V I n p =
      ⟨p.proj, ofBundleFiberEquiv e V p.proj p.snd⟩ :=
  (congrFun (congrArg DFunLike.coe
      (ofBundleTotalSpaceDiffeomorph_toHomeomorph e V (I := I) (n := n))) p).trans
    (ofBundleTotalSpaceHomeomorph_apply e V p)

@[simp]
theorem ofBundleTotalSpaceDiffeomorph_symm_apply (p : TotalSpace F V) :
    (ofBundleTotalSpaceDiffeomorph e V I n).symm p =
      ⟨p.proj, (ofBundleFiberEquiv e V p.proj).symm p.snd⟩ :=
  (congrFun (Diffeomorph.coe_toHomeomorph_symm
      (ofBundleTotalSpaceDiffeomorph e V I n)).symm p).trans <|
    (congrArg (fun h : (ofBundle 𝕜 e V).core.TotalSpace ≃ₜ TotalSpace F V ↦ h.symm p)
        (ofBundleTotalSpaceDiffeomorph_toHomeomorph e V (I := I) (n := n))).trans
      (ofBundleTotalSpaceHomeomorph_symm_apply e V p)

end OfBundle

section ChangeEquiv

variable {r₁ r₂ : ℕ} (e₁ : F ≃L[𝕜] (Fin r₁ → 𝕜)) (e₂ : F ≃L[𝕜] (Fin r₂ → 𝕜)) (V : B → Type*)
  [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- Changing the coordinate equivalence from `e₁` to `e₂` induces a `C^n` diffeomorphism of core
total spaces over the identity of the base, lifting `ofBundleChangeIso e₁ e₂ V` with fibre map
`e₂ ∘ e₁⁻¹`. -/
noncomputable def ofBundleChangeDiffeomorph
    (I : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω) :
    (ofBundle 𝕜 e₁ V).core.TotalSpace ≃ₘ^n⟮I.prod 𝓘(𝕜, Fin (ofBundle 𝕜 e₁ V).rank → 𝕜),
      I.prod 𝓘(𝕜, Fin (ofBundle 𝕜 e₂ V).rank → 𝕜)⟯ (ofBundle 𝕜 e₂ V).core.TotalSpace :=
  isoToDiffeomorphOfConst (ofBundleChangeIso e₁ e₂ V)
    (fun i ↦ (baseSet_ofBundle e₁ V i).trans (baseSet_ofBundle e₂ V i).symm)
    (e₁.symm.trans e₂)
    (fun i j x _ _ ↦ coordChange_ofBundle_intertwines e₁ e₂ V i j x)
    (fiberMap_ofBundleChangeIso_hom e₁ e₂ V)

@[simp]
theorem ofBundleChangeDiffeomorph_apply (p : (ofBundle 𝕜 e₁ V).core.TotalSpace) :
    ofBundleChangeDiffeomorph e₁ e₂ V I n p = ⟨p.proj, e₂ (e₁.symm p.snd)⟩ := by
  rcases p with ⟨x, v⟩
  rw [ofBundleChangeDiffeomorph, coe_isoToDiffeomorphOfConst, CoordinateHom.totalSpaceMap_mk,
    fiberMap_ofBundleChangeIso_hom]
  exact congrArg (TotalSpace.mk x) (ContinuousLinearEquiv.trans_apply e₁.symm e₂ v)

@[simp]
theorem ofBundleChangeDiffeomorph_symm_apply (p : (ofBundle 𝕜 e₂ V).core.TotalSpace) :
    (ofBundleChangeDiffeomorph e₁ e₂ V I n).symm p = ⟨p.proj, e₁ (e₂.symm p.snd)⟩ := by
  rcases p with ⟨x, v⟩
  rw [ofBundleChangeDiffeomorph, coe_isoToDiffeomorphOfConst_symm, CoordinateHom.totalSpaceMap_mk,
    fiberMap_ofBundleChangeIso_inv]
  exact congrArg (TotalSpace.mk x) (ContinuousLinearEquiv.trans_apply e₂.symm e₁ v)

/-- Changing the coordinate equivalence commutes with `ofBundleTotalSpaceDiffeomorph`. -/
theorem ofBundleTotalSpaceDiffeomorph_changeDiffeomorph
    (p : (ofBundle 𝕜 e₁ V).core.TotalSpace) :
    ofBundleTotalSpaceDiffeomorph e₂ V I n (ofBundleChangeDiffeomorph e₁ e₂ V I n p) =
      ofBundleTotalSpaceDiffeomorph e₁ V I n p := by
  rw [ofBundleChangeDiffeomorph_apply, ofBundleTotalSpaceDiffeomorph_apply,
    ofBundleTotalSpaceDiffeomorph_apply]
  have h := ofBundleFiberEquiv_changeIso e₁ e₂ V p.proj p.snd
  rw [fiberMap_ofBundleChangeIso_hom] at h
  exact congrArg (TotalSpace.mk' F p.proj) h

end ChangeEquiv

end TauCeti.FiniteRankBundleCore
