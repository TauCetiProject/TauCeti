/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Determinant
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Hom.Basic

/-!
# Smooth and holomorphic determinant line bundles and top-degree alternating forms

This file lifts the determinant-line identifications of
`TauCeti.Topology.VectorBundle.FiniteRank.Determinant` to `C^n` diffeomorphisms of total spaces
(and in particular biholomorphisms for `𝕜 = ℂ` and `n = ∞`), without smoothness hypotheses on the
underlying cores or bundles:

* `TauCeti.FiniteRankBundleCore.dualDetDiffeomorphDetDual`: canonical `C^n` diffeomorphism
  `A.dual.det.core.TotalSpace ≃ₘ^n A.det.dual.core.TotalSpace` realizing `det(A*) ≅ (det A)*`;
* `TauCeti.FiniteRankBundleCore.ofBundleDualDetTotalSpaceDiffeomorph`: for a vector bundle `V`
  with model fibre `F` and a basis `b : Module.Basis (Fin r) 𝕜 F`, the canonical `C^n`
  diffeomorphism identifying `(ofBundle 𝕜 b.equivFunL V).dual.det.core.TotalSpace` with Mathlib's
  top-degree alternating form bundle `fun x ↦ V x [⋀^Fin r]→L[𝕜] 𝕜`;
* `TauCeti.FiniteRankBundleCore.ofBundleDualDetChangeDiffeomorph`: changing the coordinate
  equivalence from `e₁` to `e₂` induces a `C^n` diffeomorphism of determinant-line total spaces
  lifting `ofBundleDualDetChangeIso e₁ e₂ V`, scaling scalar coordinates by
  `LinearMap.det (e₂.symm.trans e₁).toLinearEquiv.toLinearMap` (and `b₁.det b₂` for bases), and
  commuting strictly with `ofBundleDualDetTotalSpaceDiffeomorph`.

## References

* D. Huybrechts, *Complex Geometry: An Introduction*, §2.2.
* J. W. Milnor and J. D. Stasheff, *Characteristic Classes*, §3.
-/

public section

open Bundle CategoryTheory FiberBundle Set VectorBundleCore
open scoped Manifold ContDiff

namespace TauCeti.FiniteRankBundleCore

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [TopologicalSpace B]
  {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  [TopologicalSpace HB] [ChartedSpace HB B] {I : ModelWithCorners 𝕜 EB HB} {n : ℕ∞ω}

section DualDet

/-- Canonical `C^n` diffeomorphism `det(A*) ≅ (det A)*` on total spaces, lifting
`dualDetIsoDetDual A`. No smoothness assumption on `A` is required. -/
noncomputable def dualDetDiffeomorphDetDual (A : FiniteRankBundleCore 𝕜 B)
    (I : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω) :
    A.dual.det.core.TotalSpace ≃ₘ^n⟮
      I.prod 𝓘(𝕜, Fin A.dual.det.rank → 𝕜), I.prod 𝓘(𝕜, Fin A.det.dual.rank → 𝕜)⟯
      A.det.dual.core.TotalSpace :=
  isoToDiffeomorphOfConst (dualDetIsoDetDual A)
    (fun i ↦ (localTriv_baseSet_det A.dual i).trans (localTriv_baseSet_det A i).symm)
    ((detScalarEquiv A.dual).trans (detScalarEquiv A).symm)
    (fun i j x _ _ ↦ by
      rw [coordChange_det_dual, coordChange_dual_det]
      ext v : 1
      simp only [ContinuousLinearMap.comp_apply, smul_apply,
        ContinuousLinearMap.id_apply, map_smul])
    (fiberMap_dualDetIsoDetDual_hom A)

@[simp]
theorem dualDetDiffeomorphDetDual_apply (A : FiniteRankBundleCore 𝕜 B)
    (p : A.dual.det.core.TotalSpace) :
    dualDetDiffeomorphDetDual A I n p = (dualDetIsoDetDual A).hom.totalSpaceMap p :=
  congrFun (coe_isoToDiffeomorphOfConst _ _ _ _ _) p

@[simp]
theorem dualDetDiffeomorphDetDual_symm_apply (A : FiniteRankBundleCore 𝕜 B)
    (p : A.det.dual.core.TotalSpace) :
    (dualDetDiffeomorphDetDual A I n).symm p = (dualDetIsoDetDual A).inv.totalSpaceMap p :=
  congrFun (coe_isoToDiffeomorphOfConst_symm _ _ _ _ _) p

@[simp]
theorem detScalarEquiv_dualDetDiffeomorphDetDual_snd (A : FiniteRankBundleCore 𝕜 B)
    (p : A.dual.det.core.TotalSpace) :
    detScalarEquiv A (dualDetDiffeomorphDetDual A I n p).snd = detScalarEquiv A.dual p.snd := by
  rcases p with ⟨x, v⟩
  rw [dualDetDiffeomorphDetDual_apply, CoordinateHom.totalSpaceMap_mk]
  exact detScalarEquiv_dualDetIsoDetDual_hom A x v

@[simp]
theorem detScalarEquiv_dualDetDiffeomorphDetDual_symm_snd (A : FiniteRankBundleCore 𝕜 B)
    (p : A.det.dual.core.TotalSpace) :
    detScalarEquiv A.dual ((dualDetDiffeomorphDetDual A I n).symm p).snd =
      detScalarEquiv A p.snd := by
  rcases p with ⟨x, v⟩
  rw [dualDetDiffeomorphDetDual_symm_apply, CoordinateHom.totalSpaceMap_mk]
  exact detScalarEquiv_dualDetIsoDetDual_inv A x v

end DualDet

section TopFormBundle

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {r : ℕ} (b : Module.Basis (Fin r) 𝕜 F) (V : B → Type*)
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- Reading determinant-core coordinates as top-degree alternating forms on `V` is `C^n` on total
spaces, without any smoothness assumption on `V`. -/
theorem contMDiff_ofBundleDualDetFiberEquiv :
    ContMDiff (I.prod 𝓘(𝕜, Fin (ofBundle 𝕜 b.equivFunL V).dual.det.rank → 𝕜))
      (I.prod 𝓘(𝕜, F [⋀^Fin r]→L[𝕜] 𝕜)) n
      (fun p : (ofBundle 𝕜 b.equivFunL V).dual.det.core.TotalSpace ↦
        TotalSpace.mk' (F [⋀^Fin r]→L[𝕜] 𝕜) (E := fun x ↦ V x [⋀^Fin r]→L[𝕜] 𝕜)
          p.proj (ofBundleDualDetFiberEquiv b V p.proj p.snd)) := by
  intro p₀
  rw [Bundle.contMDiffAt_totalSpace_iff]
  refine ⟨(contMDiff_proj _).contMDiffAt, ?_⟩
  let L := (detScalarEquiv (ofBundle 𝕜 b.equivFunL V).dual).trans b.topFormEquiv.symm
  exact (L.contDiff.comp_contMDiffAt
    ((ofBundle 𝕜 b.equivFunL V).dual.det.contMDiffAt_localTriv_snd (I := I) (n := n)
      p₀)).congr_of_eventuallyEq
    (eventuallyEq_trivializationAt_ofBundleDualDetFiberEquiv_snd b V p₀)

/-- The reconstructed total space of `(ofBundle 𝕜 b.equivFunL V).dual.det` is `C^n`
diffeomorphic to Mathlib's top-degree alternating form bundle `fun x ↦ V x [⋀^Fin r]→L[𝕜] 𝕜`, over
the identity of the base and fibrewise `𝕜`-linear via `ofBundleDualDetFiberEquiv`. No smoothness
assumption on `V` is required. -/
noncomputable def ofBundleDualDetTotalSpaceDiffeomorph
    (I : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω) :
    (ofBundle 𝕜 b.equivFunL V).dual.det.core.TotalSpace ≃ₘ^n⟮
      I.prod 𝓘(𝕜, Fin (ofBundle 𝕜 b.equivFunL V).dual.det.rank → 𝕜),
      I.prod 𝓘(𝕜, F [⋀^Fin r]→L[𝕜] 𝕜)⟯
      TotalSpace (F [⋀^Fin r]→L[𝕜] 𝕜) (fun x ↦ V x [⋀^Fin r]→L[𝕜] 𝕜) :=
  bundleDiffeomorph (ofBundleDualDetFiberEquiv b V)
    (contMDiff_ofBundleDualDetFiberEquiv (I := I) (n := n) b V)

@[simp]
theorem ofBundleDualDetTotalSpaceDiffeomorph_toHomeomorph :
    (ofBundleDualDetTotalSpaceDiffeomorph b V I n).toHomeomorph =
      ofBundleDualDetTotalSpaceHomeomorph b V :=
  Homeomorph.ext fun p ↦
    (bundleDiffeomorph_apply _ _ p).trans
      (ofBundleDualDetTotalSpaceHomeomorph_apply b V p).symm

@[simp]
theorem ofBundleDualDetTotalSpaceDiffeomorph_apply
    (p : (ofBundle 𝕜 b.equivFunL V).dual.det.core.TotalSpace) :
    ofBundleDualDetTotalSpaceDiffeomorph b V I n p =
      ⟨p.proj, ofBundleDualDetFiberEquiv b V p.proj p.snd⟩ :=
  bundleDiffeomorph_apply _ _ p

@[simp]
theorem ofBundleDualDetTotalSpaceDiffeomorph_symm_apply
    (p : TotalSpace (F [⋀^Fin r]→L[𝕜] 𝕜) (fun x ↦ V x [⋀^Fin r]→L[𝕜] 𝕜)) :
    (ofBundleDualDetTotalSpaceDiffeomorph b V I n).symm p =
      ⟨p.proj, (ofBundleDualDetFiberEquiv b V p.proj).symm p.snd⟩ :=
  bundleDiffeomorph_symm_apply _ _ p

end TopFormBundle

section EquivChange

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {r : ℕ} (e₁ e₂ : F ≃L[𝕜] (Fin r → 𝕜)) (V : B → Type*)
  [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

private theorem contMDiff_ofBundleDualDetChangeIso_hom :
    ContMDiff (I.prod 𝓘(𝕜, Fin (ofBundle 𝕜 e₁ V).dual.det.rank → 𝕜))
      (I.prod 𝓘(𝕜, Fin (ofBundle 𝕜 e₂ V).dual.det.rank → 𝕜)) n
      (ofBundleDualDetChangeIso e₁ e₂ V).hom.totalSpaceMap := by
  let c : 𝕜 := LinearMap.det (e₂.symm.trans e₁).toLinearEquiv.toLinearMap
  let T : (Fin (ofBundle 𝕜 e₁ V).dual.det.rank → 𝕜) →L[𝕜]
      (Fin (ofBundle 𝕜 e₂ V).dual.det.rank → 𝕜) :=
    (detScalarEquiv (ofBundle 𝕜 e₂ V).dual).symm.toContinuousLinearMap.comp
      ((c • ContinuousLinearMap.id 𝕜 𝕜).comp
        (detScalarEquiv (ofBundle 𝕜 e₁ V).dual).toContinuousLinearMap)
  refine contMDiff_totalSpaceMap_of_fiberMap_eq_const (ofBundleDualDetChangeIso e₁ e₂ V).hom
    (fun i ↦
      (((localTriv_baseSet_det (ofBundle 𝕜 e₁ V).dual i).trans
        (localTriv_baseSet_dual (ofBundle 𝕜 e₁ V) i) |>.trans
          (baseSet_ofBundle e₁ V i)).trans
        ((localTriv_baseSet_det (ofBundle 𝕜 e₂ V).dual i).trans
          (localTriv_baseSet_dual (ofBundle 𝕜 e₂ V) i) |>.trans
            (baseSet_ofBundle e₂ V i)).symm).subset)
    T
    (fun i j x _ _ ↦ by
      rw [coordChange_det_dual_ofBundle, coordChange_det_dual_ofBundle]
      ext v k
      simp only [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply,
        map_smul, ContinuousLinearEquiv.coe_coe, T, smul_eq_mul])
    (fun x ↦ by
      ext v k
      simp only [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply,
        ContinuousLinearEquiv.coe_coe, T, detScalarEquiv_symm_apply, smul_eq_mul]
      exact (det_fiber_apply_eq_detScalarEquiv (ofBundle 𝕜 e₂ V).dual _ k).trans
        (detScalarEquiv_ofBundleDualDetChangeIso_hom e₁ e₂ V x v))

/-- Changing the coordinate equivalence from `e₁` to `e₂` induces a `C^n` diffeomorphism between
the determinant-line total spaces of `(ofBundle 𝕜 e₁ V).dual` and `(ofBundle 𝕜 e₂ V).dual`,
lifting `ofBundleDualDetChangeIso e₁ e₂ V` and scaling scalar coordinates by
`LinearMap.det (e₂.symm.trans e₁).toLinearEquiv.toLinearMap`. -/
noncomputable def ofBundleDualDetChangeDiffeomorph
    (I : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω) :
    (ofBundle 𝕜 e₁ V).dual.det.core.TotalSpace ≃ₘ^n⟮
      I.prod 𝓘(𝕜, Fin (ofBundle 𝕜 e₁ V).dual.det.rank → 𝕜),
      I.prod 𝓘(𝕜, Fin (ofBundle 𝕜 e₂ V).dual.det.rank → 𝕜)⟯
      (ofBundle 𝕜 e₂ V).dual.det.core.TotalSpace :=
  isoToDiffeomorph (ofBundleDualDetChangeIso e₁ e₂ V)
    (contMDiff_ofBundleDualDetChangeIso_hom (I := I) (n := n) e₁ e₂ V)
    ((contMDiff_ofBundleDualDetChangeIso_hom (I := I) (n := n) e₂ e₁ V).congr fun p ↦ by
      rw [ofBundleDualDetChangeIso_inv])

@[simp]
theorem ofBundleDualDetChangeDiffeomorph_apply
    (p : (ofBundle 𝕜 e₁ V).dual.det.core.TotalSpace) :
    ofBundleDualDetChangeDiffeomorph e₁ e₂ V I n p =
      (ofBundleDualDetChangeIso e₁ e₂ V).hom.totalSpaceMap p :=
  congrFun (coe_isoToDiffeomorph _ _ _) p

@[simp]
theorem ofBundleDualDetChangeDiffeomorph_symm_apply
    (p : (ofBundle 𝕜 e₂ V).dual.det.core.TotalSpace) :
    (ofBundleDualDetChangeDiffeomorph e₁ e₂ V I n).symm p =
      (ofBundleDualDetChangeIso e₁ e₂ V).inv.totalSpaceMap p :=
  congrFun (coe_isoToDiffeomorph_symm _ _ _) p

@[simp]
theorem detScalarEquiv_ofBundleDualDetChangeDiffeomorph_snd
    (p : (ofBundle 𝕜 e₁ V).dual.det.core.TotalSpace) :
    detScalarEquiv (ofBundle 𝕜 e₂ V).dual
        (ofBundleDualDetChangeDiffeomorph e₁ e₂ V I n p).snd =
      LinearMap.det (e₂.symm.trans e₁).toLinearEquiv.toLinearMap *
        detScalarEquiv (ofBundle 𝕜 e₁ V).dual p.snd := by
  rcases p with ⟨x, v⟩
  rw [ofBundleDualDetChangeDiffeomorph_apply, CoordinateHom.totalSpaceMap_mk]
  exact detScalarEquiv_ofBundleDualDetChangeIso_hom e₁ e₂ V x v

@[simp]
theorem detScalarEquiv_ofBundleDualDetChangeDiffeomorph_symm_snd
    (p : (ofBundle 𝕜 e₂ V).dual.det.core.TotalSpace) :
    detScalarEquiv (ofBundle 𝕜 e₁ V).dual
        ((ofBundleDualDetChangeDiffeomorph e₁ e₂ V I n).symm p).snd =
      LinearMap.det (e₁.symm.trans e₂).toLinearEquiv.toLinearMap *
        detScalarEquiv (ofBundle 𝕜 e₂ V).dual p.snd := by
  rcases p with ⟨x, v⟩
  rw [ofBundleDualDetChangeDiffeomorph_symm_apply, CoordinateHom.totalSpaceMap_mk]
  exact detScalarEquiv_ofBundleDualDetChangeIso_inv e₁ e₂ V x v

/-- Specialization of `detScalarEquiv_ofBundleDualDetChangeDiffeomorph_snd` to basis
equivalences, where the scaling factor is `b₁.det b₂`. -/
theorem detScalarEquiv_ofBundleDualDetChangeDiffeomorph_basis_snd
    (b₁ b₂ : Module.Basis (Fin r) 𝕜 F)
    (p : (ofBundle 𝕜 b₁.equivFunL V).dual.det.core.TotalSpace) :
    detScalarEquiv (ofBundle 𝕜 b₂.equivFunL V).dual
        (ofBundleDualDetChangeDiffeomorph b₁.equivFunL b₂.equivFunL V I n p).snd =
      b₁.det b₂ * detScalarEquiv (ofBundle 𝕜 b₁.equivFunL V).dual p.snd := by
  rcases p with ⟨x, v⟩
  rw [ofBundleDualDetChangeDiffeomorph_apply, CoordinateHom.totalSpaceMap_mk]
  exact detScalarEquiv_ofBundleDualDetChangeIso_basis_hom b₁ b₂ V x v

/-- Specialization of `detScalarEquiv_ofBundleDualDetChangeDiffeomorph_symm_snd` to basis
equivalences, where the scaling factor is `b₂.det b₁`. -/
theorem detScalarEquiv_ofBundleDualDetChangeDiffeomorph_basis_symm_snd
    (b₁ b₂ : Module.Basis (Fin r) 𝕜 F)
    (p : (ofBundle 𝕜 b₂.equivFunL V).dual.det.core.TotalSpace) :
    detScalarEquiv (ofBundle 𝕜 b₁.equivFunL V).dual
        ((ofBundleDualDetChangeDiffeomorph b₁.equivFunL b₂.equivFunL V I n).symm p).snd =
      b₂.det b₁ * detScalarEquiv (ofBundle 𝕜 b₂.equivFunL V).dual p.snd := by
  rcases p with ⟨x, v⟩
  rw [ofBundleDualDetChangeDiffeomorph_symm_apply, CoordinateHom.totalSpaceMap_mk]
  exact detScalarEquiv_ofBundleDualDetChangeIso_basis_inv b₁ b₂ V x v

end EquivChange

section BasisChangeTopForm

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {r : ℕ} (b₁ b₂ : Module.Basis (Fin r) 𝕜 F) (V : B → Type*)
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- Changing the model basis commutes strictly with `ofBundleDualDetTotalSpaceDiffeomorph`. -/
theorem ofBundleDualDetTotalSpaceDiffeomorph_changeDiffeomorph
    (p : (ofBundle 𝕜 b₁.equivFunL V).dual.det.core.TotalSpace) :
    ofBundleDualDetTotalSpaceDiffeomorph b₂ V I n
        (ofBundleDualDetChangeDiffeomorph b₁.equivFunL b₂.equivFunL V I n p) =
      ofBundleDualDetTotalSpaceDiffeomorph b₁ V I n p := by
  rcases p with ⟨x, v⟩
  rw [ofBundleDualDetChangeDiffeomorph_apply, ofBundleDualDetTotalSpaceDiffeomorph_apply,
    ofBundleDualDetTotalSpaceDiffeomorph_apply, CoordinateHom.totalSpaceMap_mk]
  exact congrArg (TotalSpace.mk' (F [⋀^Fin r]→L[𝕜] 𝕜) x)
    (ofBundleDualDetFiberEquiv_changeIso b₁ b₂ V x v)

end BasisChangeTopForm

end TauCeti.FiniteRankBundleCore
