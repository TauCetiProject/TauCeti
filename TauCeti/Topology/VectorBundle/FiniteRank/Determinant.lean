/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.ExteriorPower
public import TauCeti.Topology.VectorBundle.FiniteRank.LinearEquiv
public import TauCeti.Analysis.Normed.Module.Alternating.TopDegree
public import TauCeti.Topology.VectorBundle.ContinuousAlternatingMap
import TauCeti.Topology.Algebra.Module.Determinant

/-!
# Determinant line cores, dual determinants, and top-degree alternating forms

For a finite-rank core `A : FiniteRankBundleCore 𝕜 B` of rank `r`, its determinant line
`A.det = ⋀^r A` has rank `1` and transitions `(A.core.coordChange i j x).det`:

* `detScalarEquiv` identifies `Fin A.det.rank → 𝕜` with `𝕜` at index `0`.
* `detExteriorPowerIso`, `detMap`, and `detIso` transport functoriality of `exteriorPower 𝕜 B r`
  to `A.det` for rank-`r` cores, scaling coordinates by the determinant.
* `coordChange_ofLinearEquiv_det` shows that the determinant transitions of `ofLinearEquiv e V`
  are independent of `e`.
* Over a complete field, `dualDetIso` identifies `(A.dual).det ≅ (A.det).dual`, and
  `dualDetTopFormTotalSpaceHomeomorph` identifies `A.dual.det` with the bundle of top-degree
  continuous alternating forms on `A.core.Fiber`.

## References

* D. Huybrechts, *Complex Geometry: An Introduction*, §2.2.
* J. W. Milnor and J. D. Stasheff, *Characteristic Classes*, §3.
-/

public section

open Bundle CategoryTheory Set VectorBundleCore

namespace TauCeti.FiniteRankBundleCore

section General

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]

/-- The canonical continuous linear equivalence from `Fin A.det.rank → 𝕜` to `𝕜`, evaluating at
index `0`; its inverse sends `c` to `fun _ ↦ c`. -/
noncomputable def detScalarEquiv (A : FiniteRankBundleCore 𝕜 B) :
    (Fin A.det.rank → 𝕜) ≃L[𝕜] 𝕜 :=
  (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ ↦ 𝕜) (finCongr A.rank_det)).trans
    (ContinuousLinearEquiv.funUnique (Fin 1) 𝕜 𝕜)

@[simp] theorem detScalarEquiv_apply (A : FiniteRankBundleCore 𝕜 B) (v : Fin A.det.rank → 𝕜) :
    detScalarEquiv A v = v ⟨0, A.rank_det ▸ Nat.zero_lt_one⟩ := (rfl)

@[simp] theorem detScalarEquiv_symm_apply (A : FiniteRankBundleCore 𝕜 B) (c : 𝕜)
    (i : Fin A.det.rank) :
    (detScalarEquiv A).symm c i = c := (rfl)

/-- Under `detScalarEquiv`, the transition of `A.det` from `i` to `j` at `x` multiplies by the
determinant of `A.core.coordChange i j x`. -/
theorem detScalarEquiv_coordChange_det (A : FiniteRankBundleCore 𝕜 B) (i j x : B)
    (v : Fin A.det.rank → 𝕜) :
    detScalarEquiv A (A.det.core.coordChange i j x v) =
      (A.core.coordChange i j x).det * detScalarEquiv A v := by
  rw [coordChange_det]; simp [detScalarEquiv_apply]

variable (𝕜) in
/-- Scalar evaluation on `Fin (m.choose r) → 𝕜` when `m = r`. -/
noncomputable def topExteriorScalarEquiv {m r : ℕ} (h : m = r) :
    (Fin (m.choose r) → 𝕜) ≃L[𝕜] 𝕜 :=
  (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ ↦ 𝕜)
    (finCongr (h ▸ Nat.choose_self m))).trans
    (ContinuousLinearEquiv.funUnique (Fin 1) 𝕜 𝕜)

@[simp] theorem topExteriorScalarEquiv_apply {m r : ℕ} (h : m = r) (v : Fin (m.choose r) → 𝕜) :
    topExteriorScalarEquiv 𝕜 h v = v ⟨0, h ▸ Nat.choose_self m ▸ Nat.zero_lt_one⟩ := (rfl)

@[simp] theorem topExteriorScalarEquiv_symm_apply {m r : ℕ} (h : m = r) (c : 𝕜)
    (i : Fin (m.choose r)) :
    (topExteriorScalarEquiv 𝕜 h).symm c i = c := (rfl)

/-- Under `topExteriorScalarEquiv`, the top-degree compound matrix `g.exteriorPowerCoords r` acts
by scalar multiplication by `g.det`. -/
theorem topExteriorScalarEquiv_exteriorPowerCoords_self {r : ℕ}
    (g : (Fin r → 𝕜) →L[𝕜] (Fin r → 𝕜)) (w : Fin (r.choose r) → 𝕜) :
    topExteriorScalarEquiv 𝕜 (rfl : r = r) (g.exteriorPowerCoords r w) =
      g.det * topExteriorScalarEquiv 𝕜 (rfl : r = r) w := by
  rw [ContinuousLinearMap.exteriorPowerCoords_self]
  simp [topExteriorScalarEquiv_apply]

/-- The determinant core keeps the same chart domains as the original core. -/
theorem baseSet_det (A : FiniteRankBundleCore 𝕜 B) (i : B) :
    A.det.core.baseSet i = A.core.baseSet i :=
  localTriv_baseSet_det A i

private theorem baseSet_exteriorPower_obj (j : ℕ) (A : FiniteRankBundleCore 𝕜 B) (i : B) :
    ((exteriorPower 𝕜 B j).obj A).core.baseSet i = A.core.baseSet i := (rfl)

/-- Identifying `Fin A.det.rank → 𝕜` with `Fin ((exteriorPower 𝕜 B r).obj A).rank → 𝕜` via
`detScalarEquiv A` and `topExteriorScalarEquiv 𝕜 hr` intertwines the transitions of `A.det` and
`(exteriorPower 𝕜 B r).obj A`. -/
theorem coordChange_comp_detExteriorPower (A : FiniteRankBundleCore 𝕜 B) {r : ℕ} (hr : A.rank = r)
    (i j x : B) :
    (((detScalarEquiv A).trans (topExteriorScalarEquiv 𝕜 hr).symm :
        (Fin A.det.rank → 𝕜) ≃L[𝕜]
          (Fin ((exteriorPower 𝕜 B r).obj A).rank → 𝕜)).toContinuousLinearMap.comp
        (A.det.core.coordChange i j x)) =
      (((exteriorPower 𝕜 B r).obj A).core.coordChange i j x).comp
        (((detScalarEquiv A).trans (topExteriorScalarEquiv 𝕜 hr).symm :
          (Fin A.det.rank → 𝕜) ≃L[𝕜]
            (Fin ((exteriorPower 𝕜 B r).obj A).rank → 𝕜)).toContinuousLinearMap) := by
  subst hr; ext u : 1
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, coordChange_det,
    coordChange_exteriorPower_obj, ContinuousLinearMap.exteriorPowerCoords_self]
  simp only [_root_.smul_apply, ContinuousLinearMap.id_apply]
  exact (map_smul ((detScalarEquiv A).trans (topExteriorScalarEquiv 𝕜 rfl).symm) _ u).symm

/-- For `r = A.rank`, the determinant core `A.det` is canonically isomorphic to the `r`th exterior
power `(exteriorPower 𝕜 B r).obj A`, preserving scalar coordinates. -/
noncomputable def detExteriorPowerIso (A : FiniteRankBundleCore 𝕜 B) {r : ℕ} (hr : A.rank = r) :
    A.det ≅ (exteriorPower 𝕜 B r).obj A :=
  constIso (fun i ↦ baseSet_det A i)
    ((detScalarEquiv A).trans (topExteriorScalarEquiv 𝕜 hr).symm)
    fun i j x _ _ ↦ coordChange_comp_detExteriorPower A hr i j x

/-- Definitional presentation of `detExteriorPowerIso` as a constant-equivalence isomorphism. -/
theorem detExteriorPowerIso_def (A : FiniteRankBundleCore 𝕜 B) {r : ℕ} (hr : A.rank = r) :
    detExteriorPowerIso A hr =
      constIso (D := (exteriorPower 𝕜 B r).obj A) (fun i ↦ baseSet_det A i)
        ((detScalarEquiv A).trans (topExteriorScalarEquiv 𝕜 hr).symm)
        fun i j x _ _ ↦ coordChange_comp_detExteriorPower A hr i j x := (rfl)

/-- The forward map of `detExteriorPowerIso` preserves scalar coordinates. -/
theorem topExteriorScalarEquiv_fiberMap_detExteriorPowerIso_hom
    (A : FiniteRankBundleCore 𝕜 B) {r : ℕ} (hr : A.rank = r) (x : B) (u : Fin A.det.rank → 𝕜) :
    topExteriorScalarEquiv 𝕜 hr ((detExteriorPowerIso A hr).hom.fiberMap x u) =
      detScalarEquiv A u := by
  rw [detExteriorPowerIso]
  exact (congrArg (topExteriorScalarEquiv 𝕜 hr)
    (DFunLike.congr_fun (fiberMap_constIso_hom _ _ _ x) u)).trans
    ((topExteriorScalarEquiv 𝕜 hr).apply_symm_apply _)

/-- The inverse map of `detExteriorPowerIso` preserves scalar coordinates. -/
theorem detScalarEquiv_fiberMap_detExteriorPowerIso_inv
    (A : FiniteRankBundleCore 𝕜 B) {r : ℕ} (hr : A.rank = r) (x : B)
    (w : Fin (((exteriorPower 𝕜 B r).obj A).rank) → 𝕜) :
    detScalarEquiv A ((detExteriorPowerIso A hr).inv.fiberMap x w) =
      topExteriorScalarEquiv 𝕜 hr w := by
  rw [detExteriorPowerIso]
  exact (congrArg (detScalarEquiv A)
    (DFunLike.congr_fun (fiberMap_constIso_inv _ _ _ x) w)).trans
    ((detScalarEquiv A).apply_symm_apply _)

/-- The bundle map on determinant line cores induced by `f : A ⟶ D` between two cores of rank `r`,
transporting `(exteriorPower 𝕜 B r).map f` across `detExteriorPowerIso`. -/
noncomputable def detMap (r : ℕ) {A D : FiniteRankBundleCore 𝕜 B}
    (f : A ⟶ D) (hA : A.rank = r) (hD : D.rank = r) : A.det ⟶ D.det :=
  (detExteriorPowerIso A hA).hom ≫ (exteriorPower 𝕜 B r).map f ≫ (detExteriorPowerIso D hD).inv

theorem detMap_def (r : ℕ) {A D : FiniteRankBundleCore 𝕜 B}
    (f : A ⟶ D) (hA : A.rank = r) (hD : D.rank = r) :
    detMap r f hA hD =
      (detExteriorPowerIso A hA).hom ≫ (exteriorPower 𝕜 B r).map f ≫
        (detExteriorPowerIso D hD).inv := (rfl)

@[simp] theorem detMap_id (r : ℕ) (A : FiniteRankBundleCore 𝕜 B) (hA : A.rank = r) :
    detMap r (𝟙 A) hA hA = 𝟙 A.det := by simp [detMap]

@[simp] theorem detMap_comp (r : ℕ) {A D C : FiniteRankBundleCore 𝕜 B}
    (f : A ⟶ D) (g : D ⟶ C) (hA : A.rank = r) (hD : D.rank = r) (hC : C.rank = r) :
    detMap r (f ≫ g) hA hC = detMap r f hA hD ≫ detMap r g hD hC := by simp [detMap]

/-- Transport the fibre map `f.fiberMap x` along rank equalities `hA : A.rank = r` and
`hD : D.rank = r` to a continuous linear endomorphism of `Fin r → 𝕜`. -/
noncomputable def normalizedFiberMap {r : ℕ} {A D : FiniteRankBundleCore 𝕜 B}
    (f : A ⟶ D) (hA : A.rank = r) (hD : D.rank = r) (x : B) :
    (Fin r → 𝕜) →L[𝕜] (Fin r → 𝕜) :=
  (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ ↦ 𝕜) (finCongr hD)).toContinuousLinearMap.comp
    ((f.fiberMap x).comp
      (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ ↦ 𝕜)
        (finCongr hA)).symm.toContinuousLinearMap)

/-- Pointwise coordinate formula for `normalizedFiberMap f hA hD x`. -/
theorem normalizedFiberMap_apply {r : ℕ} {A D : FiniteRankBundleCore 𝕜 B}
    (f : A ⟶ D) (hA : A.rank = r) (hD : D.rank = r) (x : B)
    (v : Fin r → 𝕜) (i : Fin r) :
    normalizedFiberMap f hA hD x v i =
      f.fiberMap x (fun j ↦ v (Fin.cast hA j)) (Fin.cast hD.symm i) := by
  simp only [normalizedFiberMap, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  rfl

/-- On scalar coordinates, `detMap r f hA hD` multiplies by the determinant of
`normalizedFiberMap f hA hD x`. -/
theorem detScalarEquiv_fiberMap_detMap (r : ℕ) {A D : FiniteRankBundleCore 𝕜 B}
    (f : A ⟶ D) (hA : A.rank = r) (hD : D.rank = r) (x : B) (u : Fin A.det.rank → 𝕜) :
    detScalarEquiv D ((detMap r f hA hD).fiberMap x u) =
      (normalizedFiberMap f hA hD x).det * detScalarEquiv A u := by
  rcases A with ⟨nA, cA, hcA⟩
  rcases D with ⟨nD, cD, hcD⟩
  dsimp only at hA hD
  subst hA hD
  rw [detMap, fiberMap_comp, fiberMap_comp, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, detScalarEquiv_fiberMap_detExteriorPowerIso_inv,
    fiberMap_exteriorPower_map]
  have hnorm : normalizedFiberMap f rfl rfl x = f.fiberMap x := by
    ext v i; simp [normalizedFiberMap_apply]
  rw [hnorm]
  exact (topExteriorScalarEquiv_exteriorPowerCoords_self (f.fiberMap x) _).trans
    (congrArg _ (topExteriorScalarEquiv_fiberMap_detExteriorPowerIso_hom _ _ _ _))

/-- If `f.fiberMap x` acts in normalized `Fin r → 𝕜` coordinates as `T`, then on scalar
coordinates `detMap r f hA hD` multiplies by `T.det`. -/
theorem detScalarEquiv_fiberMap_detMap_of_apply (r : ℕ) {A D : FiniteRankBundleCore 𝕜 B}
    (f : A ⟶ D) (hA : A.rank = r) (hD : D.rank = r) (x : B)
    (T : (Fin r → 𝕜) →L[𝕜] (Fin r → 𝕜))
    (hT : ∀ (v : Fin r → 𝕜) (i : Fin r),
      f.fiberMap x (fun j ↦ v (Fin.cast hA j)) (Fin.cast hD.symm i) = T v i)
    (u : Fin A.det.rank → 𝕜) :
    detScalarEquiv D ((detMap r f hA hD).fiberMap x u) =
      T.det * detScalarEquiv A u := by
  rw [detScalarEquiv_fiberMap_detMap]
  congr 2
  ext v i
  exact (normalizedFiberMap_apply f hA hD x v i).trans (hT v i)

/-- If `f.fiberMap x` acts as the coordinate identity after rank-cast normalization, then
`detMap r f hA hD` preserves scalar coordinates. -/
theorem detScalarEquiv_fiberMap_detMap_of_apply_id (r : ℕ) {A D : FiniteRankBundleCore 𝕜 B}
    (f : A ⟶ D) (hA : A.rank = r) (hD : D.rank = r) (x : B)
    (hf : ∀ (v : Fin r → 𝕜) (i : Fin r),
      f.fiberMap x (fun j ↦ v (Fin.cast hA j)) (Fin.cast hD.symm i) = v i)
    (u : Fin A.det.rank → 𝕜) :
    detScalarEquiv D ((detMap r f hA hD).fiberMap x u) = detScalarEquiv A u := by
  rw [detScalarEquiv_fiberMap_detMap_of_apply r f hA hD x (ContinuousLinearMap.id 𝕜 (Fin r → 𝕜))
    hf u, ContinuousLinearMap.det_id, one_mul]

/-- An isomorphism `e : A ≅ D` between cores of rank `r` induces an isomorphism `A.det ≅ D.det`. -/
noncomputable def detIso (r : ℕ) {A D : FiniteRankBundleCore 𝕜 B}
    (e : A ≅ D) (hA : A.rank = r) (hD : D.rank = r) : A.det ≅ D.det :=
  detExteriorPowerIso A hA ≪≫ (exteriorPower 𝕜 B r).mapIso e ≪≫ (detExteriorPowerIso D hD).symm

@[simp] theorem detIso_hom (r : ℕ) {A D : FiniteRankBundleCore 𝕜 B}
    (e : A ≅ D) (hA : A.rank = r) (hD : D.rank = r) :
    (detIso r e hA hD).hom = detMap r e.hom hA hD := (rfl)

@[simp] theorem detIso_inv (r : ℕ) {A D : FiniteRankBundleCore 𝕜 B}
    (e : A ≅ D) (hA : A.rank = r) (hD : D.rank = r) :
    (detIso r e hA hD).inv = detMap r e.inv hD hA := by
  simp [detIso, detMap, Category.assoc]

section OfLinearEquiv

variable {r : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (e e₁ e₂ : F ≃L[𝕜] (Fin r → 𝕜)) (V : B → Type*)
  [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- The determinant transitions of `ofLinearEquiv e V` depend only on the chart transitions of `V`
on its model fibre `F`, and not on the chosen coordinate equivalence `e`. -/
theorem coordChange_ofLinearEquiv_det (b c x : B) :
    (ofLinearEquiv e V).det.core.coordChange b c x =
      ((trivializationAt F V b).coordChangeL 𝕜 (trivializationAt F V c) x : F →L[𝕜] F).det •
        ContinuousLinearMap.id 𝕜 (Fin (ofLinearEquiv e V).det.rank → 𝕜) := by
  rw [coordChange_det, coordChange_ofLinearEquiv]
  exact congrArg (· • ContinuousLinearMap.id 𝕜 _) (e.det_arrowCongr_self _)

/-- On determinant line cores, the forward map of `ofLinearEquivChangeIso e₁ e₂ V` multiplies scalar
coordinates by the determinant of `e₁.symm.trans e₂`. -/
theorem detScalarEquiv_fiberMap_ofLinearEquivChangeIso_hom (x : B)
    (u : Fin (ofLinearEquiv e₁ V).det.rank → 𝕜) :
    detScalarEquiv (ofLinearEquiv e₂ V)
        ((detIso r (ofLinearEquivChangeIso e₁ e₂ V)
          (rank_ofLinearEquiv e₁ V) (rank_ofLinearEquiv e₂ V)).hom.fiberMap x u) =
      (e₁.symm.trans e₂ : (Fin r → 𝕜) →L[𝕜] (Fin r → 𝕜)).det *
        detScalarEquiv (ofLinearEquiv e₁ V) u := by
  rw [detIso_hom, detScalarEquiv_fiberMap_detMap]
  congr 2
  ext v i
  rw [normalizedFiberMap_apply, fiberMap_ofLinearEquivChangeIso_hom]
  rfl

/-- On determinant line cores, the inverse map of `ofLinearEquivChangeIso e₁ e₂ V` multiplies scalar
coordinates by the determinant of `e₂.symm.trans e₁`. -/
theorem detScalarEquiv_fiberMap_ofLinearEquivChangeIso_inv (x : B)
    (u : Fin (ofLinearEquiv e₂ V).det.rank → 𝕜) :
    detScalarEquiv (ofLinearEquiv e₁ V)
        ((detIso r (ofLinearEquivChangeIso e₁ e₂ V)
          (rank_ofLinearEquiv e₁ V) (rank_ofLinearEquiv e₂ V)).inv.fiberMap x u) =
      (e₂.symm.trans e₁ : (Fin r → 𝕜) →L[𝕜] (Fin r → 𝕜)).det *
        detScalarEquiv (ofLinearEquiv e₂ V) u := by
  rw [detIso_inv, detScalarEquiv_fiberMap_detMap]
  congr 2
  ext v i
  rw [normalizedFiberMap_apply, fiberMap_ofLinearEquivChangeIso_inv]
  rfl

end OfLinearEquiv

end General

/-! ### Dual determinants and top-degree alternating forms -/

section Dual

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [TopologicalSpace B]

/-- The transitions of `(A.dual).det` are multiplication by the determinants of the reverse
transitions of `A`. -/
theorem coordChange_dual_det (A : FiniteRankBundleCore 𝕜 B) (i j x : B) :
    A.dual.det.core.coordChange i j x =
      (A.core.coordChange j i x).det • ContinuousLinearMap.id 𝕜 (Fin A.dual.det.rank → 𝕜) := by
  rw [coordChange_det, coordChange_dual]
  exact congrArg (· • ContinuousLinearMap.id 𝕜 _) (ContinuousLinearMap.det_piTranspose _)

/-- The transitions of `(A.det).dual` are multiplication by the determinants of the reverse
transitions of `A`. -/
theorem coordChange_det_dual (A : FiniteRankBundleCore 𝕜 B) (i j x : B) :
    A.det.dual.core.coordChange i j x =
      (A.core.coordChange j i x).det • ContinuousLinearMap.id 𝕜 (Fin A.det.dual.rank → 𝕜) := by
  rw [coordChange_dual, coordChange_det, ContinuousLinearMap.piTranspose_smul,
    ContinuousLinearMap.piTranspose_id]; rfl

/-- Identifying `Fin A.dual.det.rank → 𝕜` with `Fin A.det.dual.rank → 𝕜` via scalar coordinates
intertwines the transitions of `A.dual.det` and `A.det.dual`. -/
theorem coordChange_comp_dualDet (A : FiniteRankBundleCore 𝕜 B) (i j x : B) :
    (((detScalarEquiv A.dual).trans (detScalarEquiv A).symm :
        (Fin A.dual.det.rank → 𝕜) ≃L[𝕜] (Fin A.det.dual.rank → 𝕜)).toContinuousLinearMap.comp
        (A.dual.det.core.coordChange i j x)) =
      (A.det.dual.core.coordChange i j x).comp
        (((detScalarEquiv A.dual).trans (detScalarEquiv A).symm :
          (Fin A.dual.det.rank → 𝕜) ≃L[𝕜] (Fin A.det.dual.rank → 𝕜)).toContinuousLinearMap) := by
  ext u : 1
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, coordChange_dual_det,
    coordChange_det_dual]
  simp only [_root_.smul_apply, ContinuousLinearMap.id_apply, map_smul]

/-- The determinant of the dual core is canonically isomorphic to the dual of the determinant core,
preserving scalar coordinates. -/
noncomputable def dualDetIso (A : FiniteRankBundleCore 𝕜 B) :
    A.dual.det ≅ A.det.dual :=
  constIso
    (fun i ↦ (baseSet_det A.dual i).trans ((localTriv_baseSet_dual A i).trans
      ((baseSet_det A i).symm.trans (localTriv_baseSet_dual A.det i).symm)))
    ((detScalarEquiv A.dual).trans (detScalarEquiv A).symm)
    fun i j x _ _ ↦ coordChange_comp_dualDet A i j x

/-- Definitional presentation of `dualDetIso` as a constant-equivalence isomorphism. -/
theorem dualDetIso_def (A : FiniteRankBundleCore 𝕜 B) :
    dualDetIso A =
      constIso (D := A.det.dual)
        (fun i ↦ (baseSet_det A.dual i).trans ((localTriv_baseSet_dual A i).trans
          ((baseSet_det A i).symm.trans (localTriv_baseSet_dual A.det i).symm)))
        ((detScalarEquiv A.dual).trans (detScalarEquiv A).symm)
        fun i j x _ _ ↦ coordChange_comp_dualDet A i j x := (rfl)

/-- The forward map of `dualDetIso` preserves scalar coordinates. -/
theorem detScalarEquiv_fiberMap_dualDetIso_hom (A : FiniteRankBundleCore 𝕜 B) (x : B)
    (u : Fin A.dual.det.rank → 𝕜) :
    detScalarEquiv A ((dualDetIso A).hom.fiberMap x u) = detScalarEquiv A.dual u := by
  rw [dualDetIso]
  exact (congrArg (detScalarEquiv A)
    (DFunLike.congr_fun (fiberMap_constIso_hom _
      ((detScalarEquiv A.dual).trans (detScalarEquiv A).symm :
        (Fin A.dual.det.rank → 𝕜) ≃L[𝕜] (Fin A.det.dual.rank → 𝕜))
      (fun i j x _ _ ↦ coordChange_comp_dualDet A i j x) x) u)).trans
    ((detScalarEquiv A).apply_symm_apply _)

/-- The inverse map of `dualDetIso` preserves scalar coordinates. -/
theorem detScalarEquiv_fiberMap_dualDetIso_inv (A : FiniteRankBundleCore 𝕜 B) (x : B)
    (u : Fin A.det.dual.rank → 𝕜) :
    detScalarEquiv A.dual ((dualDetIso A).inv.fiberMap x u) = detScalarEquiv A u := by
  rw [dualDetIso]
  exact (congrArg (detScalarEquiv A.dual)
    (DFunLike.congr_fun (fiberMap_constIso_inv _
      ((detScalarEquiv A.dual).trans (detScalarEquiv A).symm :
        (Fin A.dual.det.rank → 𝕜) ≃L[𝕜] (Fin A.det.dual.rank → 𝕜))
      (fun i j x _ _ ↦ coordChange_comp_dualDet A i j x) x) u)).trans
    ((detScalarEquiv A.dual).apply_symm_apply _)

/-- Each fibre of `A.dual.det` is identified with the space of top-degree scalar-valued continuous
alternating forms on `A.core.Fiber x` via `(Pi.basisFun 𝕜 (Fin A.rank)).continuousDet`. -/
noncomputable def dualDetTopFormFiberEquiv (A : FiniteRankBundleCore 𝕜 B) (x : B) :
    A.dual.det.core.Fiber x ≃L[𝕜] (A.core.Fiber x [⋀^Fin A.rank]→L[𝕜] 𝕜) :=
  (detScalarEquiv A.dual).trans (Pi.basisFun 𝕜 (Fin A.rank)).topFormEquiv.symm

@[simp] theorem dualDetTopFormFiberEquiv_apply (A : FiniteRankBundleCore 𝕜 B) (x : B)
    (u : Fin A.dual.det.rank → 𝕜) (v : Fin A.rank → A.core.Fiber x) :
    dualDetTopFormFiberEquiv A x u v =
      detScalarEquiv A.dual u * (Pi.basisFun 𝕜 (Fin A.rank)).det v :=
  (Pi.basisFun 𝕜 (Fin A.rank)).topFormEquiv_symm_apply (detScalarEquiv A.dual u) v

@[simp] theorem dualDetTopFormFiberEquiv_symm_apply (A : FiniteRankBundleCore 𝕜 B) (x : B)
    (ω : A.core.Fiber x [⋀^Fin A.rank]→L[𝕜] 𝕜) :
    (dualDetTopFormFiberEquiv A x).symm ω =
      (detScalarEquiv A.dual).symm (ω (Pi.basisFun 𝕜 (Fin A.rank))) := by
  apply (dualDetTopFormFiberEquiv A x).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  ext v
  rw [dualDetTopFormFiberEquiv_apply, ContinuousLinearEquiv.apply_symm_apply, mul_comm]
  exact ω.apply_eq_det_mul (Pi.basisFun 𝕜 (Fin A.rank)) v

/-- Over `A`'s chart at `a`, reading `dualDetTopFormFiberEquiv A x u` in the alternating-form
trivialization at `a` gives the top-degree form with scalar coefficient from `localTriv a`. -/
theorem dualDetTopFormFiberEquiv_inCoordinates (A : FiniteRankBundleCore 𝕜 B) (a x : B)
    (hx : x ∈ A.core.baseSet a) (u : Fin A.dual.det.rank → 𝕜) :
    (trivializationAt ((Fin A.rank → 𝕜) [⋀^Fin A.rank]→L[𝕜] 𝕜)
      (fun y ↦ A.core.Fiber y [⋀^Fin A.rank]→L[𝕜] 𝕜) a
      ⟨x, dualDetTopFormFiberEquiv A x u⟩).2 =
      (Pi.basisFun 𝕜 (Fin A.rank)).topFormEquiv.symm
        (detScalarEquiv A.dual ((A.dual.det.core.localTriv a ⟨x, u⟩).2)) := by
  apply (Pi.basisFun 𝕜 (Fin A.rank)).topFormEquiv.injective
  rw [ContinuousLinearEquiv.apply_symm_apply,
    FiberBundle.trivializationAt_continuousAlternatingMap_apply_snd,
    A.core.trivializationAt_symmL (by rwa [A.trivializationAt_core]), A.indexAt_eq, A.indexAt_eq,
    Module.Basis.topFormEquiv_apply]
  let ω₀ : (Fin A.rank → 𝕜) [⋀^Fin A.rank]→L[𝕜] 𝕜 :=
    (Pi.basisFun 𝕜 (Fin A.rank)).topFormEquiv.symm (detScalarEquiv A.dual u)
  refine (ω₀.compContinuousLinearMap_apply_basis (Pi.basisFun 𝕜 (Fin A.rank))
    (A.core.coordChange a x x)).trans ?_
  have hu : ω₀ (Pi.basisFun 𝕜 (Fin A.rank)) = detScalarEquiv A.dual u :=
    ((Pi.basisFun 𝕜 (Fin A.rank)).topFormEquiv_apply ω₀).symm.trans
      ((Pi.basisFun 𝕜 (Fin A.rank)).topFormEquiv.apply_symm_apply _)
  rw [hu, VectorBundleCore.localTriv_apply]; dsimp only
  rw [A.dual.det.indexAt_eq, detScalarEquiv_coordChange_det, coordChange_dual]
  exact congrArg (· * detScalarEquiv A.dual u) (ContinuousLinearMap.det_piTranspose _).symm

/-- Reading `A.dual.det` vectors as top-degree alternating forms on the fibres of `A` is continuous
on total spaces. -/
theorem continuous_dualDetTopFormFiberEquiv (A : FiniteRankBundleCore 𝕜 B) :
    Continuous fun p : A.dual.det.core.TotalSpace ↦
      TotalSpace.mk' ((Fin A.rank → 𝕜) [⋀^Fin A.rank]→L[𝕜] 𝕜)
        (E := fun x ↦ A.core.Fiber x [⋀^Fin A.rank]→L[𝕜] 𝕜) p.proj
        (dualDetTopFormFiberEquiv A p.proj p.snd) :=
  continuous_of_localTriv_snd_of_mem_baseSet A.dual.det _ (fun _ ↦ rfl)
    ((detScalarEquiv A.dual).trans
      (Pi.basisFun 𝕜 (Fin A.rank)).topFormEquiv.symm).toContinuousLinearMap
    fun b ⟨x, u⟩ hx ↦
      dualDetTopFormFiberEquiv_inCoordinates A b x (by simpa [baseSet_det] using hx) u

/-- The reconstructed total space of `A.dual.det` is canonically homeomorphic over `B` to Mathlib's
bundle of top-degree scalar-valued continuous alternating forms on `A.core.Fiber`. -/
noncomputable def dualDetTopFormTotalSpaceHomeomorph (A : FiniteRankBundleCore 𝕜 B) :
    A.dual.det.core.TotalSpace ≃ₜ
      TotalSpace ((Fin A.rank → 𝕜) [⋀^Fin A.rank]→L[𝕜] 𝕜)
        (fun x ↦ A.core.Fiber x [⋀^Fin A.rank]→L[𝕜] 𝕜) :=
  bundleHomeomorph (dualDetTopFormFiberEquiv A) (continuous_dualDetTopFormFiberEquiv A)

@[simp] theorem dualDetTopFormTotalSpaceHomeomorph_apply (A : FiniteRankBundleCore 𝕜 B)
    (p : A.dual.det.core.TotalSpace) :
    dualDetTopFormTotalSpaceHomeomorph A p = ⟨p.proj, dualDetTopFormFiberEquiv A p.proj p.snd⟩ :=
  bundleHomeomorph_apply _ _ p

@[simp] theorem dualDetTopFormTotalSpaceHomeomorph_symm_apply (A : FiniteRankBundleCore 𝕜 B)
    (p : TotalSpace ((Fin A.rank → 𝕜) [⋀^Fin A.rank]→L[𝕜] 𝕜)
      (fun x ↦ A.core.Fiber x [⋀^Fin A.rank]→L[𝕜] 𝕜)) :
    (dualDetTopFormTotalSpaceHomeomorph A).symm p =
      ⟨p.proj, (dualDetTopFormFiberEquiv A p.proj).symm p.snd⟩ :=
  bundleHomeomorph_symm_apply _ _ p

end Dual

end TauCeti.FiniteRankBundleCore
