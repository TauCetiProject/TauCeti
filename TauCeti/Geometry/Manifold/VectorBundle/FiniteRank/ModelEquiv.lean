/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.ModelEquiv
public import TauCeti.Geometry.Manifold.VectorBundle.Core.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Hom

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
  from `e₁` to `e₂` induces a `C^n` diffeomorphism of core total spaces commuting with
  `ofBundleTotalSpaceDiffeomorph`;
* `TauCeti.FiniteRankBundleCore.ofBundleDualTotalSpaceDiffeomorph` and
  `TauCeti.FiniteRankBundleCore.ofBundleDualChangeDiffeomorph`: over a complete scalar field,
  the dual core `(ofBundle 𝕜 e V).dual` is `C^n` diffeomorphic to Mathlib's dual bundle
  `fun x ↦ V x →L[𝕜] 𝕜`, compatibly with changes of coordinate equivalence.

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
total spaces over the identity of the base, with fibre map `e₂ ∘ e₁⁻¹`. -/
noncomputable def ofBundleChangeDiffeomorph
    (I : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω) :
    (ofBundle 𝕜 e₁ V).core.TotalSpace ≃ₘ^n⟮I.prod 𝓘(𝕜, Fin (ofBundle 𝕜 e₁ V).rank → 𝕜),
      I.prod 𝓘(𝕜, Fin (ofBundle 𝕜 e₂ V).rank → 𝕜)⟯ (ofBundle 𝕜 e₂ V).core.TotalSpace :=
  constIsoDiffeomorph
    (fun i ↦ (baseSet_ofBundle e₁ V i).trans (baseSet_ofBundle e₂ V i).symm)
    (e₁.symm.trans e₂) fun i j x _ _ ↦ by
      rw [coordChange_ofBundle, coordChange_ofBundle]
      exact ContinuousLinearMap.ext fun _ ↦
        congrArg e₂ <| (e₁.symm_apply_apply _).trans (congrArg _ (e₂.symm_apply_apply _).symm)

@[simp]
theorem ofBundleChangeDiffeomorph_apply (p : (ofBundle 𝕜 e₁ V).core.TotalSpace) :
    ofBundleChangeDiffeomorph e₁ e₂ V I n p = ⟨p.proj, e₂ (e₁.symm p.snd)⟩ := by
  rcases p with ⟨x, v⟩
  rw [ofBundleChangeDiffeomorph, coe_constIsoDiffeomorph, CoordinateHom.totalSpaceMap_mk,
    fiberMap_constIso_hom]
  rfl

@[simp]
theorem ofBundleChangeDiffeomorph_symm_apply (p : (ofBundle 𝕜 e₂ V).core.TotalSpace) :
    (ofBundleChangeDiffeomorph e₁ e₂ V I n).symm p = ⟨p.proj, e₁ (e₂.symm p.snd)⟩ := by
  rcases p with ⟨x, v⟩
  rw [ofBundleChangeDiffeomorph, coe_constIsoDiffeomorph_symm, CoordinateHom.totalSpaceMap_mk,
    fiberMap_constIso_inv]
  rfl

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

section DualBundle

variable [CompleteSpace 𝕜] {r : ℕ} (e : F ≃L[𝕜] (Fin r → 𝕜)) (V : B → Type*)
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- Reading dual-core coordinates as functionals on `V` is `C^n` on total spaces. -/
theorem contMDiff_ofBundleDualFiberEquiv :
    ContMDiff (I.prod 𝓘(𝕜, Fin (ofBundle 𝕜 e V).dual.rank → 𝕜))
      (I.prod 𝓘(𝕜, F →L[𝕜] 𝕜)) n
      (fun p : (ofBundle 𝕜 e V).dual.core.TotalSpace ↦
        TotalSpace.mk' (F →L[𝕜] 𝕜) (E := fun x ↦ V x →L[𝕜] 𝕜) p.proj
          (ofBundleDualFiberEquiv e V p.proj p.snd)) := by
  intro p
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_proj _, ?_⟩
  let L : (Fin (ofBundle 𝕜 e V).dual.rank → 𝕜) →L[𝕜] (F →L[𝕜] 𝕜) :=
    ((ContinuousLinearEquiv.piRing (𝕜 := 𝕜) (E := 𝕜) (Fin r)).symm.trans
      (e.symm.arrowCongr (ContinuousLinearEquiv.refl 𝕜 𝕜))).toContinuousLinearMap
  exact (L.contDiff.comp_contMDiffAt
    ((ofBundle 𝕜 e V).dual.contMDiffAt_localTriv_snd (I := I) (n := n) p)).congr_of_eventuallyEq
      (eventuallyEq_inCoordinates_ofBundleDualFiberEquiv e V p)

/-- The reconstructed total space of `(ofBundle 𝕜 e V).dual` is `C^n` diffeomorphic to Mathlib's
dual bundle `fun x ↦ V x →L[𝕜] 𝕜`, over the identity of the base and fibrewise `𝕜`-linear via
`ofBundleDualFiberEquiv`. No smoothness assumption on `V` is required. -/
noncomputable def ofBundleDualTotalSpaceDiffeomorph
    (I : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω) :
    (ofBundle 𝕜 e V).dual.core.TotalSpace ≃ₘ^n⟮
      I.prod 𝓘(𝕜, Fin (ofBundle 𝕜 e V).dual.rank → 𝕜), I.prod 𝓘(𝕜, F →L[𝕜] 𝕜)⟯
      TotalSpace (F →L[𝕜] 𝕜) (fun x ↦ V x →L[𝕜] 𝕜) :=
  bundleDiffeomorph (ofBundleDualFiberEquiv e V)
    (contMDiff_ofBundleDualFiberEquiv (I := I) (n := n) e V)

@[simp]
theorem ofBundleDualTotalSpaceDiffeomorph_toHomeomorph :
    (ofBundleDualTotalSpaceDiffeomorph e V I n).toHomeomorph =
      ofBundleDualTotalSpaceHomeomorph e V :=
  Homeomorph.ext fun p ↦
    (bundleDiffeomorph_apply _ _ p).trans (ofBundleDualTotalSpaceHomeomorph_apply e V p).symm

@[simp]
theorem ofBundleDualTotalSpaceDiffeomorph_apply
    (p : (ofBundle 𝕜 e V).dual.core.TotalSpace) :
    ofBundleDualTotalSpaceDiffeomorph e V I n p =
      ⟨p.proj, ofBundleDualFiberEquiv e V p.proj p.snd⟩ :=
  bundleDiffeomorph_apply _ _ p

@[simp]
theorem ofBundleDualTotalSpaceDiffeomorph_symm_apply
    (p : TotalSpace (F →L[𝕜] 𝕜) (fun x ↦ V x →L[𝕜] 𝕜)) :
    (ofBundleDualTotalSpaceDiffeomorph e V I n).symm p =
      ⟨p.proj, (ofBundleDualFiberEquiv e V p.proj).symm p.snd⟩ :=
  bundleDiffeomorph_symm_apply _ _ p

end DualBundle

section DualChange

variable [CompleteSpace 𝕜] {r₁ r₂ : ℕ} (e₁ : F ≃L[𝕜] (Fin r₁ → 𝕜)) (e₂ : F ≃L[𝕜] (Fin r₂ → 𝕜))
  (V : B → Type*) [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

private noncomputable def dualChangeFiberEquiv :
    (Fin (ofBundle 𝕜 e₁ V).dual.rank → 𝕜) ≃L[𝕜] (Fin (ofBundle 𝕜 e₂ V).dual.rank → 𝕜) :=
  let T : (Fin r₁ → 𝕜) →L[𝕜] (Fin r₂ → 𝕜) := (e₂.symm.trans e₁).toContinuousLinearMap.piTranspose
  let S : (Fin r₂ → 𝕜) →L[𝕜] (Fin r₁ → 𝕜) := (e₁.symm.trans e₂).toContinuousLinearMap.piTranspose
  { toFun := T
    map_add' := T.map_add
    map_smul' := T.map_smul
    invFun := S
    left_inv := fun v ↦ by
      have hcomp : S.comp T = ContinuousLinearMap.id 𝕜 (Fin r₁ → 𝕜) := by
        rw [← ContinuousLinearMap.piTranspose_comp]
        have h : (e₂.symm.trans e₁).toContinuousLinearMap.comp
            (e₁.symm.trans e₂).toContinuousLinearMap = ContinuousLinearMap.id 𝕜 (Fin r₁ → 𝕜) := by
          ext u; simp
        rw [h, ContinuousLinearMap.piTranspose_id]
      exact congrFun (congrArg DFunLike.coe hcomp) v
    right_inv := fun v ↦ by
      have hcomp : T.comp S = ContinuousLinearMap.id 𝕜 (Fin r₂ → 𝕜) := by
        rw [← ContinuousLinearMap.piTranspose_comp]
        have h : (e₁.symm.trans e₂).toContinuousLinearMap.comp
            (e₂.symm.trans e₁).toContinuousLinearMap = ContinuousLinearMap.id 𝕜 (Fin r₂ → 𝕜) := by
          ext u; simp
        rw [h, ContinuousLinearMap.piTranspose_id]
      exact congrFun (congrArg DFunLike.coe hcomp) v
    continuous_toFun := T.continuous
    continuous_invFun := S.continuous }

/-- Changing the coordinate equivalence from `e₁` to `e₂` induces a `C^n` diffeomorphism of dual
core total spaces, given by the dual morphism `dualMap (ofBundleChangeIso e₂ e₁ V).hom`. -/
noncomputable def ofBundleDualChangeDiffeomorph
    (I : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω) :
    (ofBundle 𝕜 e₁ V).dual.core.TotalSpace ≃ₘ^n⟮
      I.prod 𝓘(𝕜, Fin (ofBundle 𝕜 e₁ V).dual.rank → 𝕜),
      I.prod 𝓘(𝕜, Fin (ofBundle 𝕜 e₂ V).dual.rank → 𝕜)⟯
      (ofBundle 𝕜 e₂ V).dual.core.TotalSpace :=
  constIsoDiffeomorph
    (A := (ofBundle 𝕜 e₁ V).dual) (D := (ofBundle 𝕜 e₂ V).dual)
    (fun i ↦ by
      rw [VectorBundleCore.baseSet_at, VectorBundleCore.baseSet_at, localTriv_baseSet_dual,
        localTriv_baseSet_dual, baseSet_ofBundle, baseSet_ofBundle])
    (dualChangeFiberEquiv e₁ e₂ V)
    fun i j x _ _ ↦ by
      rw [coordChange_dual, coordChange_dual]
      have hcomp : ((e₂.symm.trans e₁).toContinuousLinearMap.piTranspose.comp
            ((ofBundle 𝕜 e₁ V).core.coordChange j i x).piTranspose) =
          ((ofBundle 𝕜 e₂ V).core.coordChange j i x).piTranspose.comp
            (e₂.symm.trans e₁).toContinuousLinearMap.piTranspose := by
        rw [← ContinuousLinearMap.piTranspose_comp, ← ContinuousLinearMap.piTranspose_comp]
        congr 1; ext u
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
          ContinuousLinearEquiv.trans_apply, coordChange_ofBundle,
          ContinuousLinearEquiv.symm_apply_apply]
      ext v : 1
      exact congrFun (congrArg DFunLike.coe hcomp) v

@[simp]
theorem ofBundleDualChangeDiffeomorph_apply
    (p : (ofBundle 𝕜 e₁ V).dual.core.TotalSpace) :
    ofBundleDualChangeDiffeomorph e₁ e₂ V I n p =
      (dualMap (ofBundleChangeIso e₂ e₁ V).hom).totalSpaceMap p := by
  rcases p with ⟨x, v⟩
  rw [ofBundleDualChangeDiffeomorph, coe_constIsoDiffeomorph, CoordinateHom.totalSpaceMap_mk,
    CoordinateHom.totalSpaceMap_mk, fiberMap_constIso_hom, fiberMap_dualMap,
    fiberMap_ofBundleChangeIso_hom]
  rfl

@[simp]
theorem ofBundleDualChangeDiffeomorph_symm_apply
    (p : (ofBundle 𝕜 e₂ V).dual.core.TotalSpace) :
    (ofBundleDualChangeDiffeomorph e₁ e₂ V I n).symm p =
      (dualMap (ofBundleChangeIso e₁ e₂ V).hom).totalSpaceMap p := by
  rcases p with ⟨x, v⟩
  rw [ofBundleDualChangeDiffeomorph, coe_constIsoDiffeomorph_symm, CoordinateHom.totalSpaceMap_mk,
    CoordinateHom.totalSpaceMap_mk, fiberMap_constIso_inv, fiberMap_dualMap,
    fiberMap_ofBundleChangeIso_hom]
  rfl

end DualChange

section DualChangeCompat

variable [CompleteSpace 𝕜] {r₁ r₂ : ℕ} (e₁ : F ≃L[𝕜] (Fin r₁ → 𝕜)) (e₂ : F ≃L[𝕜] (Fin r₂ → 𝕜))
  (V : B → Type*) [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- Changing the coordinate equivalence commutes with `ofBundleDualTotalSpaceDiffeomorph`. -/
theorem ofBundleDualTotalSpaceDiffeomorph_changeDiffeomorph
    (p : (ofBundle 𝕜 e₁ V).dual.core.TotalSpace) :
    ofBundleDualTotalSpaceDiffeomorph e₂ V I n
        (ofBundleDualChangeDiffeomorph e₁ e₂ V I n p) =
      ofBundleDualTotalSpaceDiffeomorph e₁ V I n p := by
  rcases p with ⟨x, v⟩
  rw [ofBundleDualChangeDiffeomorph_apply, ofBundleDualTotalSpaceDiffeomorph_apply,
    ofBundleDualTotalSpaceDiffeomorph_apply, CoordinateHom.totalSpaceMap_mk]
  exact congrArg (TotalSpace.mk' (F →L[𝕜] 𝕜) x)
    (ofBundleDualFiberEquiv_dualMap_changeIso e₁ e₂ V x v)

end DualChangeCompat

end TauCeti.FiniteRankBundleCore
