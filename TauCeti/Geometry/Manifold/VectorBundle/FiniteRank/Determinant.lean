/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Determinant
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.ModelEquiv

/-!
# Smooth and holomorphic determinant line bundles and top-degree alternating forms

This file lifts the determinant-line identifications of
`TauCeti.Topology.VectorBundle.FiniteRank.Determinant` to `C^n` diffeomorphisms of total spaces
(and in particular biholomorphisms for `𝕜 = ℂ` and `n = ∞`), without smoothness hypotheses on the
underlying cores or bundles:

* `TauCeti.FiniteRankBundleCore.dualDetDiffeomorphDetDual`: canonical `C^n` diffeomorphism
  `A.dual.det.core.TotalSpace ≃ₘ^n A.det.dual.core.TotalSpace` realizing `det(A*) ≅ (det A)*`;
* `TauCeti.FiniteRankBundleCore.ofBundleEquivDualDetTotalSpaceDiffeomorph`: for a vector bundle `V`
  with model fibre `F` and a basis `b : Module.Basis (Fin r) 𝕜 F`, the canonical `C^n`
  diffeomorphism identifying `(ofBundleEquiv b.equivFunL V).dual.det.core.TotalSpace` with Mathlib's
  top-degree alternating form bundle `fun x ↦ V x [⋀^Fin r]→L[𝕜] 𝕜`;
* `TauCeti.FiniteRankBundleCore.ofBundleEquivDualDetChangeDiffeomorph`: changing the basis from `b₁`
  to `b₂` induces a `C^n` diffeomorphism of determinant-line total spaces commuting strictly with
  `ofBundleEquivDualDetTotalSpaceDiffeomorph`.

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

/-- Canonical `C^n` diffeomorphism `det(A*) ≅ (det A)*` on total spaces, induced by
`dualDetIsoDetDual A`. No smoothness assumption on `A` is required. -/
noncomputable def dualDetDiffeomorphDetDual (A : FiniteRankBundleCore 𝕜 B)
    (I : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω) :
    A.dual.det.core.TotalSpace ≃ₘ^n⟮
      I.prod 𝓘(𝕜, Fin A.dual.det.rank → 𝕜), I.prod 𝓘(𝕜, Fin A.det.dual.rank → 𝕜)⟯
      A.det.dual.core.TotalSpace :=
  toDiffeomorphOfConstFiberMap I n
    (dualDetIsoDetDual A).hom (dualDetIsoDetDual A).inv
    (dualDetIsoDetDual A).hom_inv_id (dualDetIsoDetDual A).inv_hom_id
    ((detScalarEquiv A.dual).trans (detScalarEquiv A).symm).toContinuousLinearMap
    ((detScalarEquiv A).trans (detScalarEquiv A.dual).symm).toContinuousLinearMap
    (fiberMap_dualDetIsoDetDual_hom A) (fiberMap_dualDetIsoDetDual_inv A)
    fun _ _ _ ↦ by
      rw [coordChange_det_dual, coordChange_dual_det]
      simp only [smul_apply, ContinuousLinearMap.id_apply]
      exact (map_smul _ _ _).symm

@[simp]
theorem dualDetDiffeomorphDetDual_apply (A : FiniteRankBundleCore 𝕜 B)
    (p : A.dual.det.core.TotalSpace) :
    dualDetDiffeomorphDetDual A I n p = (dualDetIsoDetDual A).hom.totalSpaceMap p :=
  congrFun (coe_toDiffeomorphOfConstFiberMap ..) p

@[simp]
theorem dualDetDiffeomorphDetDual_symm_apply (A : FiniteRankBundleCore 𝕜 B)
    (p : A.det.dual.core.TotalSpace) :
    (dualDetDiffeomorphDetDual A I n).symm p = (dualDetIsoDetDual A).inv.totalSpaceMap p :=
  congrFun (coe_toDiffeomorphOfConstFiberMap_symm ..) p

@[simp]
theorem detScalarEquiv_dualDetDiffeomorphDetDual_snd (A : FiniteRankBundleCore 𝕜 B)
    (p : A.dual.det.core.TotalSpace) :
    detScalarEquiv A (dualDetDiffeomorphDetDual A I n p).2 = detScalarEquiv A.dual p.2 := by
  rw [dualDetDiffeomorphDetDual_apply, CoordinateHom.totalSpaceMap_def]
  exact detScalarEquiv_dualDetIsoDetDual_hom A p.proj p.2

@[simp]
theorem detScalarEquiv_dualDetDiffeomorphDetDual_symm_snd (A : FiniteRankBundleCore 𝕜 B)
    (p : A.det.dual.core.TotalSpace) :
    detScalarEquiv A.dual ((dualDetDiffeomorphDetDual A I n).symm p).2 = detScalarEquiv A p.2 := by
  rw [dualDetDiffeomorphDetDual_symm_apply, CoordinateHom.totalSpaceMap_def]
  exact detScalarEquiv_dualDetIsoDetDual_inv A p.proj p.2

end DualDet

section TopFormBundle

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {r : ℕ} (b : Module.Basis (Fin r) 𝕜 F) (V : B → Type*)
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- Reading determinant-core coordinates as top-degree alternating forms on `V` is `C^n` on total
spaces, without any smoothness assumption on `V`. -/
theorem contMDiff_ofBundleEquivDualDetFiberEquiv :
    ContMDiff (I.prod 𝓘(𝕜, Fin (ofBundleEquiv b.equivFunL V).dual.det.rank → 𝕜))
      (I.prod 𝓘(𝕜, F [⋀^Fin r]→L[𝕜] 𝕜)) n
      (fun p : (ofBundleEquiv b.equivFunL V).dual.det.core.TotalSpace ↦
        TotalSpace.mk' (F [⋀^Fin r]→L[𝕜] 𝕜) (E := fun x ↦ V x [⋀^Fin r]→L[𝕜] 𝕜)
          p.proj (ofBundleEquivDualDetFiberEquiv b V p.proj p.2)) := by
  intro p₀
  rw [Bundle.contMDiffAt_totalSpace_iff]
  refine ⟨(contMDiff_proj _).contMDiffAt, ?_⟩
  let L := (detScalarEquiv (ofBundleEquiv b.equivFunL V).dual).trans b.topFormEquiv.symm
  exact (L.contDiff.comp_contMDiffAt
    ((ofBundleEquiv b.equivFunL V).dual.det.contMDiffAt_localTriv_snd (I := I) (n := n)
      p₀)).congr_of_eventuallyEq
    (eventuallyEq_trivializationAt_ofBundleEquivDualDetFiberEquiv_snd b V p₀)

/-- The reconstructed total space of `(ofBundleEquiv b.equivFunL V).dual.det` is `C^n`
diffeomorphic to Mathlib's top-degree alternating form bundle `fun x ↦ V x [⋀^Fin r]→L[𝕜] 𝕜`, over
the identity of the base and fibrewise `𝕜`-linear via `ofBundleEquivDualDetFiberEquiv`. No
smoothness assumption on `V` is required. -/
noncomputable def ofBundleEquivDualDetTotalSpaceDiffeomorph
    (I : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω) :
    (ofBundleEquiv b.equivFunL V).dual.det.core.TotalSpace ≃ₘ^n⟮
      I.prod 𝓘(𝕜, Fin (ofBundleEquiv b.equivFunL V).dual.det.rank → 𝕜),
      I.prod 𝓘(𝕜, F [⋀^Fin r]→L[𝕜] 𝕜)⟯
      TotalSpace (F [⋀^Fin r]→L[𝕜] 𝕜) (fun x ↦ V x [⋀^Fin r]→L[𝕜] 𝕜) :=
  bundleDiffeomorph (ofBundleEquivDualDetFiberEquiv b V)
    (contMDiff_ofBundleEquivDualDetFiberEquiv (I := I) (n := n) b V)

@[simp]
theorem ofBundleEquivDualDetTotalSpaceDiffeomorph_toHomeomorph :
    (ofBundleEquivDualDetTotalSpaceDiffeomorph b V I n).toHomeomorph =
      ofBundleEquivDualDetTotalSpaceHomeomorph b V :=
  Homeomorph.ext fun p ↦
    (bundleDiffeomorph_apply _ _ p).trans
      (ofBundleEquivDualDetTotalSpaceHomeomorph_apply b V p).symm

@[simp]
theorem ofBundleEquivDualDetTotalSpaceDiffeomorph_apply
    (p : (ofBundleEquiv b.equivFunL V).dual.det.core.TotalSpace) :
    ofBundleEquivDualDetTotalSpaceDiffeomorph b V I n p =
      ⟨p.proj, ofBundleEquivDualDetFiberEquiv b V p.proj p.2⟩ :=
  bundleDiffeomorph_apply _ _ p

@[simp]
theorem ofBundleEquivDualDetTotalSpaceDiffeomorph_symm_apply
    (p : TotalSpace (F [⋀^Fin r]→L[𝕜] 𝕜) (fun x ↦ V x [⋀^Fin r]→L[𝕜] 𝕜)) :
    (ofBundleEquivDualDetTotalSpaceDiffeomorph b V I n).symm p =
      ⟨p.proj, (ofBundleEquivDualDetFiberEquiv b V p.proj).symm p.2⟩ :=
  bundleDiffeomorph_symm_apply _ _ p

end TopFormBundle

section BasisChange

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {r : ℕ} (b₁ b₂ : Module.Basis (Fin r) 𝕜 F) (V : B → Type*)
  [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- Changing the model basis from `b₁` to `b₂` induces a `C^n` diffeomorphism between the
determinant-line total spaces of `(ofBundleEquiv b₁.equivFunL V).dual` and
`(ofBundleEquiv b₂.equivFunL V).dual`, scaling scalar coordinates by `b₁.det b₂`. -/
noncomputable def ofBundleEquivDualDetChangeDiffeomorph
    (I : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω) :
    (ofBundleEquiv b₁.equivFunL V).dual.det.core.TotalSpace ≃ₘ^n⟮
      I.prod 𝓘(𝕜, Fin (ofBundleEquiv b₁.equivFunL V).dual.det.rank → 𝕜),
      I.prod 𝓘(𝕜, Fin (ofBundleEquiv b₂.equivFunL V).dual.det.rank → 𝕜)⟯
      (ofBundleEquiv b₂.equivFunL V).dual.det.core.TotalSpace :=
  toDiffeomorphOfConstFiberMap I n
    (ofBundleEquivDualDetChangeIso b₁ b₂ V).hom (ofBundleEquivDualDetChangeIso b₁ b₂ V).inv
    (ofBundleEquivDualDetChangeIso b₁ b₂ V).hom_inv_id
    (ofBundleEquivDualDetChangeIso b₁ b₂ V).inv_hom_id
    (b₁.det b₂ • ((detScalarEquiv (ofBundleEquiv b₁.equivFunL V).dual).trans
      (detScalarEquiv (ofBundleEquiv b₂.equivFunL V).dual).symm).toContinuousLinearMap)
    (b₂.det b₁ • ((detScalarEquiv (ofBundleEquiv b₂.equivFunL V).dual).trans
      (detScalarEquiv (ofBundleEquiv b₁.equivFunL V).dual).symm).toContinuousLinearMap)
    (fun x ↦ ContinuousLinearMap.ext fun v ↦ funext fun i ↦
      (det_fiber_eq_const (ofBundleEquiv b₂.equivFunL V).dual _ i).trans <|
        (detScalarEquiv_ofBundleEquivDualDetChangeIso_hom b₁ b₂ V x v).trans (by simp))
    (fun x ↦ ContinuousLinearMap.ext fun v ↦ funext fun i ↦
      (det_fiber_eq_const (ofBundleEquiv b₁.equivFunL V).dual _ i).trans <|
        (detScalarEquiv_ofBundleEquivDualDetChangeIso_inv b₁ b₂ V x v).trans (by simp))
    fun _ _ _ ↦ by
      rw [coordChange_ofBundleEquiv_dual_det, coordChange_ofBundleEquiv_dual_det]
      simp only [smul_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.map_smul]
      exact smul_comm _ _ _

@[simp]
theorem ofBundleEquivDualDetChangeDiffeomorph_apply
    (p : (ofBundleEquiv b₁.equivFunL V).dual.det.core.TotalSpace) :
    ofBundleEquivDualDetChangeDiffeomorph b₁ b₂ V I n p =
      (ofBundleEquivDualDetChangeIso b₁ b₂ V).hom.totalSpaceMap p :=
  congrFun (coe_toDiffeomorphOfConstFiberMap ..) p

@[simp]
theorem ofBundleEquivDualDetChangeDiffeomorph_symm_apply
    (p : (ofBundleEquiv b₂.equivFunL V).dual.det.core.TotalSpace) :
    (ofBundleEquivDualDetChangeDiffeomorph b₁ b₂ V I n).symm p =
      (ofBundleEquivDualDetChangeIso b₁ b₂ V).inv.totalSpaceMap p :=
  congrFun (coe_toDiffeomorphOfConstFiberMap_symm ..) p

@[simp]
theorem detScalarEquiv_ofBundleEquivDualDetChangeDiffeomorph_snd
    (p : (ofBundleEquiv b₁.equivFunL V).dual.det.core.TotalSpace) :
    detScalarEquiv (ofBundleEquiv b₂.equivFunL V).dual
        (ofBundleEquivDualDetChangeDiffeomorph b₁ b₂ V I n p).2 =
      b₁.det b₂ * detScalarEquiv (ofBundleEquiv b₁.equivFunL V).dual p.2 := by
  rw [ofBundleEquivDualDetChangeDiffeomorph_apply, CoordinateHom.totalSpaceMap_def]
  exact detScalarEquiv_ofBundleEquivDualDetChangeIso_hom b₁ b₂ V p.proj p.2

@[simp]
theorem detScalarEquiv_ofBundleEquivDualDetChangeDiffeomorph_symm_snd
    (p : (ofBundleEquiv b₂.equivFunL V).dual.det.core.TotalSpace) :
    detScalarEquiv (ofBundleEquiv b₁.equivFunL V).dual
        ((ofBundleEquivDualDetChangeDiffeomorph b₁ b₂ V I n).symm p).2 =
      b₂.det b₁ * detScalarEquiv (ofBundleEquiv b₂.equivFunL V).dual p.2 := by
  rw [ofBundleEquivDualDetChangeDiffeomorph_symm_apply, CoordinateHom.totalSpaceMap_def]
  exact detScalarEquiv_ofBundleEquivDualDetChangeIso_inv b₁ b₂ V p.proj p.2

end BasisChange

section BasisChangeTopForm

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {r : ℕ} (b₁ b₂ : Module.Basis (Fin r) 𝕜 F) (V : B → Type*)
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- Changing the model basis commutes strictly with `ofBundleEquivDualDetTotalSpaceDiffeomorph`. -/
theorem ofBundleEquivDualDetTotalSpaceDiffeomorph_changeDiffeomorph
    (p : (ofBundleEquiv b₁.equivFunL V).dual.det.core.TotalSpace) :
    ofBundleEquivDualDetTotalSpaceDiffeomorph b₂ V I n
        (ofBundleEquivDualDetChangeDiffeomorph b₁ b₂ V I n p) =
      ofBundleEquivDualDetTotalSpaceDiffeomorph b₁ V I n p := by
  rw [ofBundleEquivDualDetChangeDiffeomorph_apply,
    ofBundleEquivDualDetTotalSpaceDiffeomorph_apply,
    ofBundleEquivDualDetTotalSpaceDiffeomorph_apply, CoordinateHom.totalSpaceMap_def]
  exact congrArg (TotalSpace.mk' (F [⋀^Fin r]→L[𝕜] 𝕜) p.proj)
    (ofBundleEquivDualDetFiberEquiv_changeIso b₁ b₂ V p.proj p.2)

end BasisChangeTopForm

end TauCeti.FiniteRankBundleCore
