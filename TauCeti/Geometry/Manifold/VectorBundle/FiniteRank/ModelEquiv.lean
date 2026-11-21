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

* `TauCeti.FiniteRankBundleCore.isContMDiff_ofBundleEquiv`: if `V` is a `C^n` vector bundle with
  model fibre `F` and `e : F ≃L[𝕜] (Fin r → 𝕜)`, then `ofBundleEquiv e V` is a `C^n` finite-rank
  core;
* `TauCeti.FiniteRankBundleCore.ofBundleEquivTotalSpaceDiffeomorph`: the reconstructed total space
  of `ofBundleEquiv e V` is `C^n` diffeomorphic to `TotalSpace F V` over the identity of the base,
  without smoothness or completeness hypotheses;
* `TauCeti.FiniteRankBundleCore.ofBundleEquivChangeDiffeomorph`: changing the coordinate
  equivalence from `e₁` to `e₂` induces a `C^n` diffeomorphism of core total spaces commuting with
  `ofBundleEquivTotalSpaceDiffeomorph`;
* `TauCeti.FiniteRankBundleCore.ofBundleEquivDualTotalSpaceDiffeomorph` and
  `TauCeti.FiniteRankBundleCore.ofBundleEquivDualChangeDiffeomorph`: over a complete scalar field,
  the dual core `(ofBundleEquiv e V).dual` is `C^n` diffeomorphic to Mathlib's dual bundle
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

section OfBundleEquiv

variable {r : ℕ} (e : F ≃L[𝕜] (Fin r → 𝕜)) (V : B → Type*)
  [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- If `V` is a `C^n` vector bundle with model fibre `F` and `e : F ≃L[𝕜] (Fin r → 𝕜)`, then
`ofBundleEquiv e V` is a `C^n` finite-rank core. -/
instance isContMDiff_ofBundleEquiv [ContMDiffVectorBundle n F V I] :
    (ofBundleEquiv e V).core.IsContMDiff I n where
  contMDiffOn_coordChange i j := by
    rw [baseSet_ofBundleEquiv, baseSet_ofBundleEquiv]
    exact ((e.arrowCongr e).contDiff.contMDiff.comp_contMDiffOn
      (ContMDiffVectorBundle.contMDiffOn_coordChangeL (IB := I) (n := n)
        (trivializationAt F V i) (trivializationAt F V j))).congr
      fun x _ ↦ coordChange_ofBundleEquiv e V i j x

/-- The total-space identification between `(ofBundleEquiv e V).core.TotalSpace` and
`TotalSpace F V` is a `C^n` diffeomorphism over the identity of the base, fibrewise `𝕜`-linear via
`ofBundleEquivFiberEquiv`. No smoothness or completeness hypothesis is required. -/
noncomputable def ofBundleEquivTotalSpaceDiffeomorph
    (I : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω) :
    (ofBundleEquiv e V).core.TotalSpace ≃ₘ^n⟮I.prod 𝓘(𝕜, Fin (ofBundleEquiv e V).rank → 𝕜),
      I.prod 𝓘(𝕜, F)⟯ TotalSpace F V :=
  ((pointIndexedCore 𝕜 F V).congrModelDiffeomorph e I n).trans
    (pointIndexedCoreDiffeomorph 𝕜 F V I n)

@[simp]
theorem ofBundleEquivTotalSpaceDiffeomorph_apply
    (p : (ofBundleEquiv e V).core.TotalSpace) :
    ofBundleEquivTotalSpaceDiffeomorph e V I n p =
      ⟨p.proj, ofBundleEquivFiberEquiv e V p.proj p.2⟩ :=
  (congrFun (Diffeomorph.coe_trans ((pointIndexedCore 𝕜 F V).congrModelDiffeomorph e I n)
    (pointIndexedCoreDiffeomorph 𝕜 F V I n)) p).trans <|
    (congrArg (pointIndexedCoreDiffeomorph 𝕜 F V I n)
      (congrModelDiffeomorph_apply (pointIndexedCore 𝕜 F V) e I n p)).trans <|
      (pointIndexedCoreDiffeomorph_apply 𝕜 F V I n _).trans <|
        congrArg (TotalSpace.mk' F p.proj) <|
          (pointIndexedCoreFiberEquiv_apply 𝕜 F V p.proj (e.symm p.2)).trans
            (ofBundleEquivFiberEquiv_apply e V p.proj p.2).symm

@[simp]
theorem ofBundleEquivTotalSpaceDiffeomorph_symm_apply (p : TotalSpace F V) :
    (ofBundleEquivTotalSpaceDiffeomorph e V I n).symm p =
      ⟨p.proj, (ofBundleEquivFiberEquiv e V p.proj).symm p.2⟩ :=
  (congrFun (congrArg DFunLike.coe (Diffeomorph.symm_trans'
    ((pointIndexedCore 𝕜 F V).congrModelDiffeomorph e I n)
    (pointIndexedCoreDiffeomorph 𝕜 F V I n))) p).trans <|
    (congrFun (Diffeomorph.coe_trans (pointIndexedCoreDiffeomorph 𝕜 F V I n).symm
      ((pointIndexedCore 𝕜 F V).congrModelDiffeomorph e I n).symm) p).trans <|
      (congrArg ((pointIndexedCore 𝕜 F V).congrModelDiffeomorph e I n).symm
        (pointIndexedCoreDiffeomorph_symm_apply 𝕜 F V I n p)).trans <|
        (congrModelDiffeomorph_symm_apply (pointIndexedCore 𝕜 F V) e I n _).trans <|
          TotalSpace.ext rfl <| heq_of_eq <|
            (congrArg e (pointIndexedCoreFiberEquiv_symm_apply 𝕜 F V p.proj p.2)).trans
              (ofBundleEquivFiberEquiv_symm_apply e V p.proj p.2).symm

@[simp]
theorem ofBundleEquivTotalSpaceDiffeomorph_toHomeomorph :
    (ofBundleEquivTotalSpaceDiffeomorph e V I n).toHomeomorph =
      ofBundleEquivTotalSpaceHomeomorph e V :=
  Homeomorph.ext fun p ↦
    (ofBundleEquivTotalSpaceDiffeomorph_apply e V p).trans
      (ofBundleEquivTotalSpaceHomeomorph_apply e V p).symm

end OfBundleEquiv

section ChangeEquiv

variable {r₁ r₂ : ℕ} (e₁ : F ≃L[𝕜] (Fin r₁ → 𝕜)) (e₂ : F ≃L[𝕜] (Fin r₂ → 𝕜)) (V : B → Type*)
  [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- Changing the coordinate equivalence from `e₁` to `e₂` induces a `C^n` diffeomorphism of core
total spaces over the identity of the base, with fibre map `e₂ ∘ e₁⁻¹`. -/
noncomputable def ofBundleEquivChangeDiffeomorph
    (I : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω) :
    (ofBundleEquiv e₁ V).core.TotalSpace ≃ₘ^n⟮I.prod 𝓘(𝕜, Fin (ofBundleEquiv e₁ V).rank → 𝕜),
      I.prod 𝓘(𝕜, Fin (ofBundleEquiv e₂ V).rank → 𝕜)⟯ (ofBundleEquiv e₂ V).core.TotalSpace :=
  toDiffeomorphOfConstFiberMap I n
    (ofBundleEquivChangeIso e₁ e₂ V).hom (ofBundleEquivChangeIso e₁ e₂ V).inv
    (ofBundleEquivChangeIso e₁ e₂ V).hom_inv_id (ofBundleEquivChangeIso e₁ e₂ V).inv_hom_id
    (e₁.symm.trans e₂).toContinuousLinearMap (e₂.symm.trans e₁).toContinuousLinearMap
    (fiberMap_ofBundleEquivChangeIso_hom e₁ e₂ V) (fiberMap_ofBundleEquivChangeIso_inv e₁ e₂ V)
    fun _ _ v ↦ by
      rw [coordChange_ofBundleEquiv, coordChange_ofBundleEquiv]
      exact congrArg e₂ <|
        (congrArg _ (e₂.symm_apply_apply (e₁.symm v))).trans (e₁.symm_apply_apply _).symm

@[simp]
theorem ofBundleEquivChangeDiffeomorph_apply (p : (ofBundleEquiv e₁ V).core.TotalSpace) :
    ofBundleEquivChangeDiffeomorph e₁ e₂ V I n p = ⟨p.proj, e₂ (e₁.symm p.2)⟩ :=
  (congrFun (coe_toDiffeomorphOfConstFiberMap ..) p).trans <|
    (congrArg (fun f ↦ f p)
        (CoordinateHom.totalSpaceMap_def (ofBundleEquivChangeIso e₁ e₂ V).hom)).trans <|
      congrArg (TotalSpace.mk' (Fin r₂ → 𝕜) p.proj) <|
        congrArg (fun S : (Fin r₁ → 𝕜) →L[𝕜] (Fin r₂ → 𝕜) ↦ S p.2)
          (fiberMap_ofBundleEquivChangeIso_hom e₁ e₂ V p.proj)

@[simp]
theorem ofBundleEquivChangeDiffeomorph_symm_apply (p : (ofBundleEquiv e₂ V).core.TotalSpace) :
    (ofBundleEquivChangeDiffeomorph e₁ e₂ V I n).symm p = ⟨p.proj, e₁ (e₂.symm p.2)⟩ :=
  (congrFun (coe_toDiffeomorphOfConstFiberMap_symm ..) p).trans <|
    (congrArg (fun f ↦ f p)
        (CoordinateHom.totalSpaceMap_def (ofBundleEquivChangeIso e₁ e₂ V).inv)).trans <|
      congrArg (TotalSpace.mk' (Fin r₁ → 𝕜) p.proj) <|
        congrArg (fun S : (Fin r₂ → 𝕜) →L[𝕜] (Fin r₁ → 𝕜) ↦ S p.2)
          (fiberMap_ofBundleEquivChangeIso_inv e₁ e₂ V p.proj)

/-- Changing the coordinate equivalence commutes with `ofBundleEquivTotalSpaceDiffeomorph`. -/
theorem ofBundleEquivTotalSpaceDiffeomorph_changeDiffeomorph
    (p : (ofBundleEquiv e₁ V).core.TotalSpace) :
    ofBundleEquivTotalSpaceDiffeomorph e₂ V I n (ofBundleEquivChangeDiffeomorph e₁ e₂ V I n p) =
      ofBundleEquivTotalSpaceDiffeomorph e₁ V I n p := by
  rw [ofBundleEquivChangeDiffeomorph_apply, ofBundleEquivTotalSpaceDiffeomorph_apply,
    ofBundleEquivTotalSpaceDiffeomorph_apply]
  have h := ofBundleEquivFiberEquiv_changeIso e₁ e₂ V p.proj p.2
  rw [fiberMap_ofBundleEquivChangeIso_hom] at h
  exact congrArg (TotalSpace.mk' F p.proj) h

end ChangeEquiv

section DualBundle

variable [CompleteSpace 𝕜] {r : ℕ} (e : F ≃L[𝕜] (Fin r → 𝕜)) (V : B → Type*)
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- Reading dual-core coordinates as functionals on `V` is `C^n` on total spaces. -/
theorem contMDiff_ofBundleEquivDualFiberEquiv :
    ContMDiff (I.prod 𝓘(𝕜, Fin (ofBundleEquiv e V).dual.rank → 𝕜))
      (I.prod 𝓘(𝕜, F →L[𝕜] 𝕜)) n
      (fun p : (ofBundleEquiv e V).dual.core.TotalSpace ↦
        TotalSpace.mk' (F →L[𝕜] 𝕜) (E := fun x ↦ V x →L[𝕜] 𝕜) p.proj
          (ofBundleEquivDualFiberEquiv e V p.proj p.2)) := by
  intro p
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_proj _, ?_⟩
  let L : (Fin (ofBundleEquiv e V).dual.rank → 𝕜) →L[𝕜] (F →L[𝕜] 𝕜) :=
    ((ContinuousLinearEquiv.piRing (𝕜 := 𝕜) (E := 𝕜) (Fin r)).symm.trans
      (e.symm.arrowCongr (ContinuousLinearEquiv.refl 𝕜 𝕜))).toContinuousLinearMap
  exact (L.contDiff.comp_contMDiffAt
    ((ofBundleEquiv e V).dual.contMDiffAt_localTriv_snd (I := I) (n := n) p)).congr_of_eventuallyEq
      (eventuallyEq_inCoordinates_ofBundleEquivDualFiberEquiv e V p)

/-- The reconstructed total space of `(ofBundleEquiv e V).dual` is `C^n` diffeomorphic to Mathlib's
dual bundle `fun x ↦ V x →L[𝕜] 𝕜`, over the identity of the base and fibrewise `𝕜`-linear via
`ofBundleEquivDualFiberEquiv`. No smoothness assumption on `V` is required. -/
noncomputable def ofBundleEquivDualTotalSpaceDiffeomorph
    (I : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω) :
    (ofBundleEquiv e V).dual.core.TotalSpace ≃ₘ^n⟮
      I.prod 𝓘(𝕜, Fin (ofBundleEquiv e V).dual.rank → 𝕜), I.prod 𝓘(𝕜, F →L[𝕜] 𝕜)⟯
      TotalSpace (F →L[𝕜] 𝕜) (fun x ↦ V x →L[𝕜] 𝕜) :=
  bundleDiffeomorph (ofBundleEquivDualFiberEquiv e V)
    (contMDiff_ofBundleEquivDualFiberEquiv (I := I) (n := n) e V)

@[simp]
theorem ofBundleEquivDualTotalSpaceDiffeomorph_toHomeomorph :
    (ofBundleEquivDualTotalSpaceDiffeomorph e V I n).toHomeomorph =
      ofBundleEquivDualTotalSpaceHomeomorph e V :=
  Homeomorph.ext fun p ↦
    (bundleDiffeomorph_apply _ _ p).trans (ofBundleEquivDualTotalSpaceHomeomorph_apply e V p).symm

@[simp]
theorem ofBundleEquivDualTotalSpaceDiffeomorph_apply
    (p : (ofBundleEquiv e V).dual.core.TotalSpace) :
    ofBundleEquivDualTotalSpaceDiffeomorph e V I n p =
      ⟨p.proj, ofBundleEquivDualFiberEquiv e V p.proj p.2⟩ :=
  bundleDiffeomorph_apply _ _ p

@[simp]
theorem ofBundleEquivDualTotalSpaceDiffeomorph_symm_apply
    (p : TotalSpace (F →L[𝕜] 𝕜) (fun x ↦ V x →L[𝕜] 𝕜)) :
    (ofBundleEquivDualTotalSpaceDiffeomorph e V I n).symm p =
      ⟨p.proj, (ofBundleEquivDualFiberEquiv e V p.proj).symm p.2⟩ :=
  bundleDiffeomorph_symm_apply _ _ p

end DualBundle

section DualChange

variable [CompleteSpace 𝕜] {r₁ r₂ : ℕ} (e₁ : F ≃L[𝕜] (Fin r₁ → 𝕜)) (e₂ : F ≃L[𝕜] (Fin r₂ → 𝕜))
  (V : B → Type*) [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- Changing the coordinate equivalence from `e₁` to `e₂` induces a `C^n` diffeomorphism of dual
core total spaces, given by the dual morphism `dualMap (ofBundleEquivChangeIso e₂ e₁ V).hom`. -/
noncomputable def ofBundleEquivDualChangeDiffeomorph
    (I : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω) :
    (ofBundleEquiv e₁ V).dual.core.TotalSpace ≃ₘ^n⟮
      I.prod 𝓘(𝕜, Fin (ofBundleEquiv e₁ V).dual.rank → 𝕜),
      I.prod 𝓘(𝕜, Fin (ofBundleEquiv e₂ V).dual.rank → 𝕜)⟯
      (ofBundleEquiv e₂ V).dual.core.TotalSpace :=
  toDiffeomorphOfConstFiberMap I n
    (dualMap (ofBundleEquivChangeIso e₂ e₁ V).hom) (dualMap (ofBundleEquivChangeIso e₁ e₂ V).hom)
    (dualMap_changeIso_comp e₂ e₁ V) (dualMap_changeIso_comp e₁ e₂ V)
    (e₂.symm.trans e₁).toContinuousLinearMap.piTranspose
    (e₁.symm.trans e₂).toContinuousLinearMap.piTranspose
    (fun x ↦ (fiberMap_dualMap _ x).trans (congrArg ContinuousLinearMap.piTranspose
      (fiberMap_ofBundleEquivChangeIso_hom e₂ e₁ V x)))
    (fun x ↦ (fiberMap_dualMap _ x).trans (congrArg ContinuousLinearMap.piTranspose
      (fiberMap_ofBundleEquivChangeIso_hom e₁ e₂ V x)))
    fun x b v ↦ by
      let T₁ : (Fin r₁ → 𝕜) →L[𝕜] (Fin r₁ → 𝕜) := (ofBundleEquiv e₁ V).core.coordChange b x x
      let T₂ : (Fin r₂ → 𝕜) →L[𝕜] (Fin r₂ → 𝕜) := (ofBundleEquiv e₂ V).core.coordChange b x x
      have hcomp : T₂.piTranspose.comp (e₂.symm.trans e₁).toContinuousLinearMap.piTranspose =
          (e₂.symm.trans e₁).toContinuousLinearMap.piTranspose.comp T₁.piTranspose := by
        rw [← ContinuousLinearMap.piTranspose_comp, ← ContinuousLinearMap.piTranspose_comp]
        congr 1; ext u
        simp only [T₁, T₂, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
          ContinuousLinearEquiv.trans_apply, coordChange_ofBundleEquiv,
          ContinuousLinearEquiv.symm_apply_apply]
      exact congrArg (fun S : (Fin r₁ → 𝕜) →L[𝕜] (Fin r₂ → 𝕜) ↦ S v) hcomp

@[simp]
theorem ofBundleEquivDualChangeDiffeomorph_apply
    (p : (ofBundleEquiv e₁ V).dual.core.TotalSpace) :
    ofBundleEquivDualChangeDiffeomorph e₁ e₂ V I n p =
      (dualMap (ofBundleEquivChangeIso e₂ e₁ V).hom).totalSpaceMap p :=
  congrFun (coe_toDiffeomorphOfConstFiberMap ..) p

@[simp]
theorem ofBundleEquivDualChangeDiffeomorph_symm_apply
    (p : (ofBundleEquiv e₂ V).dual.core.TotalSpace) :
    (ofBundleEquivDualChangeDiffeomorph e₁ e₂ V I n).symm p =
      (dualMap (ofBundleEquivChangeIso e₁ e₂ V).hom).totalSpaceMap p :=
  congrFun (coe_toDiffeomorphOfConstFiberMap_symm ..) p

end DualChange

section DualChangeCompat

variable [CompleteSpace 𝕜] {r₁ r₂ : ℕ} (e₁ : F ≃L[𝕜] (Fin r₁ → 𝕜)) (e₂ : F ≃L[𝕜] (Fin r₂ → 𝕜))
  (V : B → Type*) [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- Changing the coordinate equivalence commutes with `ofBundleEquivDualTotalSpaceDiffeomorph`. -/
theorem ofBundleEquivDualTotalSpaceDiffeomorph_changeDiffeomorph
    (p : (ofBundleEquiv e₁ V).dual.core.TotalSpace) :
    ofBundleEquivDualTotalSpaceDiffeomorph e₂ V I n
        (ofBundleEquivDualChangeDiffeomorph e₁ e₂ V I n p) =
      ofBundleEquivDualTotalSpaceDiffeomorph e₁ V I n p := by
  rw [ofBundleEquivDualChangeDiffeomorph_apply, ofBundleEquivDualTotalSpaceDiffeomorph_apply,
    ofBundleEquivDualTotalSpaceDiffeomorph_apply, CoordinateHom.totalSpaceMap_def]
  exact congrArg (TotalSpace.mk' (F →L[𝕜] 𝕜) p.proj)
    (ofBundleEquivDualFiberEquiv_dualMap_changeIso e₁ e₂ V p.proj p.2)

end DualChangeCompat

end TauCeti.FiniteRankBundleCore
