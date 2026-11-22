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
* `TauCeti.FiniteRankBundleCore.ofBundleDualDetTotalSpaceDiffeomorph`: for a vector bundle `V`
  with model fibre `F` and a basis `b : Module.Basis (Fin r) 𝕜 F`, the canonical `C^n`
  diffeomorphism identifying `(ofBundle 𝕜 b.equivFunL V).dual.det.core.TotalSpace` with Mathlib's
  top-degree alternating form bundle `fun x ↦ V x [⋀^Fin r]→L[𝕜] 𝕜`;
* `TauCeti.FiniteRankBundleCore.ofBundleDualDetChangeDiffeomorph`: changing the basis from `b₁` to
  `b₂` induces a `C^n` diffeomorphism of determinant-line total spaces commuting strictly with
  `ofBundleDualDetTotalSpaceDiffeomorph`.

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
  constIsoDiffeomorph
    (A := A.dual.det) (D := A.det.dual)
    (fun i ↦ by
      simp only [VectorBundleCore.baseSet_at, localTriv_baseSet_det, localTriv_baseSet_dual])
    ((detScalarEquiv A.dual).trans (detScalarEquiv A).symm) fun i j x _ _ ↦ by
      rw [coordChange_det_dual, coordChange_dual_det]
      ext v : 1
      simp only [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply, map_smul]

@[simp]
theorem dualDetDiffeomorphDetDual_apply (A : FiniteRankBundleCore 𝕜 B)
    (p : A.dual.det.core.TotalSpace) :
    dualDetDiffeomorphDetDual A I n p = (dualDetIsoDetDual A).hom.totalSpaceMap p := by
  rcases p with ⟨x, v⟩
  rw [dualDetDiffeomorphDetDual, coe_constIsoDiffeomorph, CoordinateHom.totalSpaceMap_mk,
    CoordinateHom.totalSpaceMap_mk, fiberMap_constIso_hom, fiberMap_dualDetIsoDetDual_hom]
  rfl

@[simp]
theorem dualDetDiffeomorphDetDual_symm_apply (A : FiniteRankBundleCore 𝕜 B)
    (p : A.det.dual.core.TotalSpace) :
    (dualDetDiffeomorphDetDual A I n).symm p = (dualDetIsoDetDual A).inv.totalSpaceMap p := by
  rcases p with ⟨x, v⟩
  rw [dualDetDiffeomorphDetDual, coe_constIsoDiffeomorph_symm, CoordinateHom.totalSpaceMap_mk,
    CoordinateHom.totalSpaceMap_mk, fiberMap_constIso_inv, fiberMap_dualDetIsoDetDual_inv]
  rfl

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

section BasisChange

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {r : ℕ} (b₁ b₂ : Module.Basis (Fin r) 𝕜 F) (V : B → Type*)
  [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

private noncomputable def dualDetChangeScaleEquiv : 𝕜 ≃L[𝕜] 𝕜 where
  toFun c := b₁.det b₂ * c
  invFun c := b₂.det b₁ * c
  map_add' x y := mul_add _ x y
  map_smul' a x := by simp [smul_eq_mul, mul_left_comm]
  left_inv c := by dsimp only; rw [← mul_assoc, b₂.det_mul_det, b₂.det_self, one_mul]
  right_inv c := by dsimp only; rw [← mul_assoc, b₁.det_mul_det, b₁.det_self, one_mul]
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

private noncomputable def dualDetChangeFiberEquiv :
    (Fin (ofBundle 𝕜 b₁.equivFunL V).dual.det.rank → 𝕜) ≃L[𝕜]
      (Fin (ofBundle 𝕜 b₂.equivFunL V).dual.det.rank → 𝕜) :=
  (detScalarEquiv (ofBundle 𝕜 b₁.equivFunL V).dual).trans
    ((dualDetChangeScaleEquiv b₁ b₂).trans
      (detScalarEquiv (ofBundle 𝕜 b₂.equivFunL V).dual).symm)

private theorem dualDetChangeFiberEquiv_apply
    (v : Fin (ofBundle 𝕜 b₁.equivFunL V).dual.det.rank → 𝕜)
    (i : Fin (ofBundle 𝕜 b₂.equivFunL V).dual.det.rank) :
    dualDetChangeFiberEquiv b₁ b₂ V v i =
      b₁.det b₂ * detScalarEquiv (ofBundle 𝕜 b₁.equivFunL V).dual v := by
  rw [dualDetChangeFiberEquiv, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.trans_apply, detScalarEquiv_symm_apply]
  rfl

private theorem dualDetChangeFiberEquiv_symm_apply
    (v : Fin (ofBundle 𝕜 b₂.equivFunL V).dual.det.rank → 𝕜)
    (i : Fin (ofBundle 𝕜 b₁.equivFunL V).dual.det.rank) :
    (dualDetChangeFiberEquiv b₁ b₂ V).symm v i =
      b₂.det b₁ * detScalarEquiv (ofBundle 𝕜 b₂.equivFunL V).dual v := by
  rw [dualDetChangeFiberEquiv, ContinuousLinearEquiv.symm_trans_apply,
    ContinuousLinearEquiv.symm_trans_apply, ContinuousLinearEquiv.symm_symm,
    detScalarEquiv_symm_apply]
  rfl

/-- Changing the model basis from `b₁` to `b₂` induces a `C^n` diffeomorphism between the
determinant-line total spaces of `(ofBundle 𝕜 b₁.equivFunL V).dual` and
`(ofBundle 𝕜 b₂.equivFunL V).dual`, scaling scalar coordinates by `b₁.det b₂`. -/
noncomputable def ofBundleDualDetChangeDiffeomorph
    (I : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω) :
    (ofBundle 𝕜 b₁.equivFunL V).dual.det.core.TotalSpace ≃ₘ^n⟮
      I.prod 𝓘(𝕜, Fin (ofBundle 𝕜 b₁.equivFunL V).dual.det.rank → 𝕜),
      I.prod 𝓘(𝕜, Fin (ofBundle 𝕜 b₂.equivFunL V).dual.det.rank → 𝕜)⟯
      (ofBundle 𝕜 b₂.equivFunL V).dual.det.core.TotalSpace :=
  constIsoDiffeomorph
    (A := (ofBundle 𝕜 b₁.equivFunL V).dual.det) (D := (ofBundle 𝕜 b₂.equivFunL V).dual.det)
    (fun i ↦ by
      simp only [VectorBundleCore.baseSet_at, localTriv_baseSet_det, localTriv_baseSet_dual,
        localTriv_baseSet_ofBundle])
    (dualDetChangeFiberEquiv b₁ b₂ V)
    fun i j x _ _ ↦ by
      rw [coordChange_ofBundle_dual_det, coordChange_ofBundle_dual_det]
      ext v : 1
      simp only [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply, map_smul]

@[simp]
theorem ofBundleDualDetChangeDiffeomorph_apply
    (p : (ofBundle 𝕜 b₁.equivFunL V).dual.det.core.TotalSpace) :
    ofBundleDualDetChangeDiffeomorph b₁ b₂ V I n p =
      (ofBundleDualDetChangeIso b₁ b₂ V).hom.totalSpaceMap p := by
  rcases p with ⟨x, v⟩
  rw [ofBundleDualDetChangeDiffeomorph, coe_constIsoDiffeomorph, CoordinateHom.totalSpaceMap_mk,
    CoordinateHom.totalSpaceMap_mk, fiberMap_constIso_hom]
  congr 1; funext i
  refine (dualDetChangeFiberEquiv_apply b₁ b₂ V v i).trans ?_
  refine (detScalarEquiv_ofBundleDualDetChangeIso_hom b₁ b₂ V x v).symm.trans ?_
  exact (det_fiber_eq_const (ofBundle 𝕜 b₂.equivFunL V).dual _ i).symm

@[simp]
theorem ofBundleDualDetChangeDiffeomorph_symm_apply
    (p : (ofBundle 𝕜 b₂.equivFunL V).dual.det.core.TotalSpace) :
    (ofBundleDualDetChangeDiffeomorph b₁ b₂ V I n).symm p =
      (ofBundleDualDetChangeIso b₁ b₂ V).inv.totalSpaceMap p := by
  rcases p with ⟨x, v⟩
  rw [ofBundleDualDetChangeDiffeomorph, coe_constIsoDiffeomorph_symm,
    CoordinateHom.totalSpaceMap_mk, CoordinateHom.totalSpaceMap_mk, fiberMap_constIso_inv]
  congr 1; funext i
  refine (dualDetChangeFiberEquiv_symm_apply b₁ b₂ V v i).trans ?_
  refine (detScalarEquiv_ofBundleDualDetChangeIso_inv b₁ b₂ V x v).symm.trans ?_
  exact (det_fiber_eq_const (ofBundle 𝕜 b₁.equivFunL V).dual _ i).symm

@[simp]
theorem detScalarEquiv_ofBundleDualDetChangeDiffeomorph_snd
    (p : (ofBundle 𝕜 b₁.equivFunL V).dual.det.core.TotalSpace) :
    detScalarEquiv (ofBundle 𝕜 b₂.equivFunL V).dual
        (ofBundleDualDetChangeDiffeomorph b₁ b₂ V I n p).snd =
      b₁.det b₂ * detScalarEquiv (ofBundle 𝕜 b₁.equivFunL V).dual p.snd := by
  rcases p with ⟨x, v⟩
  rw [ofBundleDualDetChangeDiffeomorph_apply, CoordinateHom.totalSpaceMap_mk]
  exact detScalarEquiv_ofBundleDualDetChangeIso_hom b₁ b₂ V x v

@[simp]
theorem detScalarEquiv_ofBundleDualDetChangeDiffeomorph_symm_snd
    (p : (ofBundle 𝕜 b₂.equivFunL V).dual.det.core.TotalSpace) :
    detScalarEquiv (ofBundle 𝕜 b₁.equivFunL V).dual
        ((ofBundleDualDetChangeDiffeomorph b₁ b₂ V I n).symm p).snd =
      b₂.det b₁ * detScalarEquiv (ofBundle 𝕜 b₂.equivFunL V).dual p.snd := by
  rcases p with ⟨x, v⟩
  rw [ofBundleDualDetChangeDiffeomorph_symm_apply, CoordinateHom.totalSpaceMap_mk]
  exact detScalarEquiv_ofBundleDualDetChangeIso_inv b₁ b₂ V x v

end BasisChange

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
        (ofBundleDualDetChangeDiffeomorph b₁ b₂ V I n p) =
      ofBundleDualDetTotalSpaceDiffeomorph b₁ V I n p := by
  rcases p with ⟨x, v⟩
  rw [ofBundleDualDetChangeDiffeomorph_apply, ofBundleDualDetTotalSpaceDiffeomorph_apply,
    ofBundleDualDetTotalSpaceDiffeomorph_apply, CoordinateHom.totalSpaceMap_mk]
  exact congrArg (TotalSpace.mk' (F [⋀^Fin r]→L[𝕜] 𝕜) x)
    (ofBundleDualDetFiberEquiv_changeIso b₁ b₂ V x v)

end BasisChangeTopForm

end TauCeti.FiniteRankBundleCore
