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

For a finite-rank vector-bundle core `A : FiniteRankBundleCore 𝕜 B` of rank `r`, its determinant
line `A.det = ⋀^r A` (`FiniteRankBundleCore.det`) has rank `1` and transition functions given by
scalar multiplication by `(A.core.coordChange i j x).det`. This file develops the scalar-coordinate,
functorial, dual, and alternating-form interfaces for `A.det`:

* `FiniteRankBundleCore.detScalarEquiv` identifies the coordinate line `Fin A.det.rank → 𝕜` with
  `𝕜` by evaluating at the single basis index `0` (`e₀ ∧ ⋯ ∧ e_{r-1}`).
* `FiniteRankBundleCore.detExteriorPowerIso`, `FiniteRankBundleCore.detMap`, and
  `FiniteRankBundleCore.detIso` transport the functoriality of `exteriorPower 𝕜 B r` onto `A.det`
  for cores of rank `r`, acting on scalar coordinates by the determinant of the fibre map.
* `FiniteRankBundleCore.coordChange_ofLinearEquiv_det` shows that the determinant transitions of
  `ofLinearEquiv e V` are the determinants of the chart transitions of `V` on its model fibre `F`,
  independent of the coordinate equivalence `e`.
* Over a complete scalar field, `FiniteRankBundleCore.dualDetIso` identifies `(A.dual).det` with
  `(A.det).dual` (both having transitions `(A.core.coordChange j i x).det`), and
  `FiniteRankBundleCore.dualDetTopFormTotalSpaceHomeomorph` identifies the reconstructed total space
  of `A.dual.det` with Mathlib's bundle `fun x ↦ A.core.Fiber x [⋀^Fin A.rank]→L[𝕜] 𝕜` of
  top-degree continuous alternating forms via `(Pi.basisFun 𝕜 (Fin A.rank)).topFormEquiv.symm`.

## References

* D. Huybrechts, *Complex Geometry: An Introduction*, §2.2.
* J. W. Milnor and J. D. Stasheff, *Characteristic Classes*, §3.
-/

public section

open Bundle CategoryTheory Set VectorBundleCore

namespace TauCeti.FiniteRankBundleCore

section General

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]

/-- The canonical continuous linear equivalence from the coordinate model `Fin A.det.rank → 𝕜` of
the determinant line `A.det` to `𝕜`, evaluating at the unique basis index `0` (`e₀ ∧ ⋯ ∧ e_{r-1}`).
Its inverse sends `c : 𝕜` to the constant tuple `fun _ ↦ c`. -/
noncomputable def detScalarEquiv (A : FiniteRankBundleCore 𝕜 B) :
    (Fin A.det.rank → 𝕜) ≃L[𝕜] 𝕜 where
  toLinearEquiv :=
    { toFun := fun v ↦ v ⟨0, A.rank_det ▸ Nat.zero_lt_one⟩
      invFun := fun c _ ↦ c
      left_inv := fun v ↦ by
        ext ⟨i, hi⟩
        have hi' : i < 1 := A.rank_det ▸ hi
        obtain rfl : i = 0 := Nat.lt_one_iff.1 hi'
        rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  continuous_toFun := continuous_apply _
  continuous_invFun := continuous_pi fun _ ↦ continuous_id

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
  rw [coordChange_det]
  simp [detScalarEquiv_apply]

variable (𝕜) in
/-- Scalar evaluation on `Fin (m.choose r) → 𝕜` when `m = r`. -/
noncomputable def topExteriorScalarEquiv {m r : ℕ} (h : m = r) :
    (Fin (m.choose r) → 𝕜) ≃L[𝕜] 𝕜 where
  toLinearEquiv :=
    { toFun := fun v ↦ v ⟨0, h ▸ Nat.choose_self m ▸ Nat.zero_lt_one⟩
      invFun := fun c _ ↦ c
      left_inv := fun v ↦ by
        ext ⟨i, hi⟩
        have hi' : i < 1 := Nat.choose_self m ▸ h ▸ hi
        obtain rfl : i = 0 := Nat.lt_one_iff.1 hi'
        rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  continuous_toFun := continuous_apply _
  continuous_invFun := continuous_pi fun _ ↦ continuous_id

@[simp] theorem topExteriorScalarEquiv_apply {m r : ℕ} (h : m = r)
    (v : Fin (m.choose r) → 𝕜) :
    topExteriorScalarEquiv 𝕜 h v = v ⟨0, h ▸ Nat.choose_self m ▸ Nat.zero_lt_one⟩ := (rfl)

@[simp] theorem topExteriorScalarEquiv_symm_apply {m r : ℕ} (h : m = r) (c : 𝕜)
    (i : Fin (m.choose r)) :
    (topExteriorScalarEquiv 𝕜 h).symm c i = c := (rfl)

theorem topExteriorScalarEquiv_exteriorPowerCoords_self {r : ℕ}
    (g : (Fin r → 𝕜) →L[𝕜] (Fin r → 𝕜)) (w : Fin (r.choose r) → 𝕜) :
    topExteriorScalarEquiv 𝕜 (rfl : r = r) (g.exteriorPowerCoords r w) =
      g.det * topExteriorScalarEquiv 𝕜 (rfl : r = r) w := by
  rw [ContinuousLinearMap.exteriorPowerCoords_self]
  simp [topExteriorScalarEquiv]

theorem baseSet_det (A : FiniteRankBundleCore 𝕜 B) (i : B) :
    A.det.core.baseSet i = A.core.baseSet i :=
  localTriv_baseSet_det A i

private theorem baseSet_exteriorPower_obj (j : ℕ) (A : FiniteRankBundleCore 𝕜 B) (i : B) :
    ((exteriorPower 𝕜 B j).obj A).core.baseSet i = A.core.baseSet i := (rfl)

/-- For `r = A.rank`, the determinant core `A.det` is canonically isomorphic to the `r`th exterior
power `(exteriorPower 𝕜 B r).obj A`, preserving scalar coordinates. -/
noncomputable def detExteriorPowerIso (A : FiniteRankBundleCore 𝕜 B) {r : ℕ} (hr : A.rank = r) :
    A.det ≅ (exteriorPower 𝕜 B r).obj A :=
  constIso (fun i ↦ (baseSet_det A i).trans (baseSet_exteriorPower_obj r A i).symm)
    ((detScalarEquiv A).trans (topExteriorScalarEquiv 𝕜 hr).symm)
    fun i j x _ _ ↦ by
      subst hr
      ext u : 1
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, coordChange_det,
        coordChange_exteriorPower_obj, ContinuousLinearMap.exteriorPowerCoords_self]
      simp only [_root_.smul_apply, ContinuousLinearMap.id_apply]
      exact (map_smul ((detScalarEquiv A).trans (topExteriorScalarEquiv 𝕜 rfl).symm)
        (A.core.coordChange i j x).det u).symm

theorem topExteriorScalarEquiv_fiberMap_detExteriorPowerIso_hom
    (A : FiniteRankBundleCore 𝕜 B) {r : ℕ} (hr : A.rank = r) (x : B) (u : Fin A.det.rank → 𝕜) :
    topExteriorScalarEquiv 𝕜 hr ((detExteriorPowerIso A hr).hom.fiberMap x u) =
      detScalarEquiv A u := by
  rw [detExteriorPowerIso, fiberMap_constIso_hom]
  exact (topExteriorScalarEquiv 𝕜 hr).apply_symm_apply (detScalarEquiv A u)

theorem detScalarEquiv_fiberMap_detExteriorPowerIso_inv
    (A : FiniteRankBundleCore 𝕜 B) {r : ℕ} (hr : A.rank = r) (x : B)
    (w : Fin (((exteriorPower 𝕜 B r).obj A).rank) → 𝕜) :
    detScalarEquiv A ((detExteriorPowerIso A hr).inv.fiberMap x w) =
      topExteriorScalarEquiv 𝕜 hr w := by
  rw [detExteriorPowerIso, fiberMap_constIso_inv]
  exact (detScalarEquiv A).apply_symm_apply (topExteriorScalarEquiv 𝕜 hr w)

/-- The bundle map on determinant line cores induced by a bundle map `f : A ⟶ D` between two cores
of rank `r`, transporting `(exteriorPower 𝕜 B r).map f` across `detExteriorPowerIso`. -/
noncomputable def detMap (r : ℕ) {A D : FiniteRankBundleCore 𝕜 B}
    (f : A ⟶ D) (hA : A.rank = r) (hD : D.rank = r) : A.det ⟶ D.det :=
  (detExteriorPowerIso A hA).hom ≫ (exteriorPower 𝕜 B r).map f ≫ (detExteriorPowerIso D hD).inv

theorem detMap_def (r : ℕ) {A D : FiniteRankBundleCore 𝕜 B}
    (f : A ⟶ D) (hA : A.rank = r) (hD : D.rank = r) :
    detMap r f hA hD =
      (detExteriorPowerIso A hA).hom ≫ (exteriorPower 𝕜 B r).map f ≫
        (detExteriorPowerIso D hD).inv := (rfl)

@[simp] theorem detMap_id (r : ℕ) (A : FiniteRankBundleCore 𝕜 B) (hA : A.rank = r) :
    detMap r (𝟙 A) hA hA = 𝟙 A.det := by
  simp [detMap]

@[simp] theorem detMap_comp (r : ℕ) {A D C : FiniteRankBundleCore 𝕜 B}
    (f : A ⟶ D) (g : D ⟶ C) (hA : A.rank = r) (hD : D.rank = r) (hC : C.rank = r) :
    detMap r (f ≫ g) hA hC = detMap r f hA hD ≫ detMap r g hD hC := by
  simp [detMap]

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

/-- The determinant transitions of `ofLinearEquiv e V` depend only on the chart transitions of `V`
on its model fibre `F`, and not on the chosen coordinate equivalence `e`. -/
theorem coordChange_ofLinearEquiv_det {r : ℕ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] (e : F ≃L[𝕜] (Fin r → 𝕜)) (V : B → Type*)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
    [FiberBundle F V] [VectorBundle 𝕜 F V] (b c x : B) :
    (ofLinearEquiv e V).det.core.coordChange b c x =
      ((trivializationAt F V b).coordChangeL 𝕜 (trivializationAt F V c) x : F →L[𝕜] F).det •
        ContinuousLinearMap.id 𝕜 (Fin (ofLinearEquiv e V).det.rank → 𝕜) := by
  rw [coordChange_det, coordChange_ofLinearEquiv]
  exact congrArg (· • ContinuousLinearMap.id 𝕜 _) (e.det_arrowCongr_self _)

/-- On determinant line cores, the coordinate-change isomorphism `ofLinearEquivChangeIso e₁ e₂ V`
multiplies scalar coordinates by the determinant of `e₁.symm.trans e₂`. -/
theorem detScalarEquiv_fiberMap_ofLinearEquivChangeIso {r : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (e₁ e₂ : F ≃L[𝕜] (Fin r → 𝕜)) (V : B → Type*)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
    [FiberBundle F V] [VectorBundle 𝕜 F V] (x : B)
    (u : Fin (ofLinearEquiv e₁ V).det.rank → 𝕜) :
    detScalarEquiv (ofLinearEquiv e₂ V)
        ((detIso r (ofLinearEquivChangeIso e₁ e₂ V)
          (rank_ofLinearEquiv e₁ V) (rank_ofLinearEquiv e₂ V)).hom.fiberMap x u) =
      (e₁.symm.trans e₂ : (Fin r → 𝕜) →L[𝕜] (Fin r → 𝕜)).det *
        detScalarEquiv (ofLinearEquiv e₁ V) u := by
  rw [detIso_hom, detMap, fiberMap_comp, fiberMap_comp, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, detScalarEquiv_fiberMap_detExteriorPowerIso_inv,
    fiberMap_exteriorPower_map, fiberMap_ofLinearEquivChangeIso_hom]
  exact (topExteriorScalarEquiv_exteriorPowerCoords_self
    (e₁.symm.trans e₂ : (Fin r → 𝕜) →L[𝕜] (Fin r → 𝕜)) _).trans
    (congrArg _ (topExteriorScalarEquiv_fiberMap_detExteriorPowerIso_hom _ _ _ _))

end General

/-! ### Dual determinants and top-degree alternating forms -/

section Dual

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [TopologicalSpace B]

/-- The transitions of `(A.dual).det` are multiplication by the determinants of the reverse
transitions of `A`, since transposition preserves determinants. -/
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
    ContinuousLinearMap.piTranspose_id]
  rfl

/-- The determinant of the dual core is canonically isomorphic to the dual of the determinant core:
both have transitions `(A.core.coordChange j i x).det`, intertwined by preserving scalar
coordinates. -/
noncomputable def dualDetIso (A : FiniteRankBundleCore 𝕜 B) :
    A.dual.det ≅ A.det.dual :=
  constIso
    (fun i ↦ (baseSet_det A.dual i).trans ((localTriv_baseSet_dual A i).trans
      ((baseSet_det A i).symm.trans (localTriv_baseSet_dual A.det i).symm)))
    ((detScalarEquiv A.dual).trans (detScalarEquiv A).symm)
    fun i j x _ _ ↦ by
      ext u : 1
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, coordChange_dual_det,
        coordChange_det_dual]
      simp only [_root_.smul_apply, ContinuousLinearMap.id_apply, map_smul]

theorem detScalarEquiv_fiberMap_dualDetIso_hom (A : FiniteRankBundleCore 𝕜 B) (x : B)
    (u : Fin A.dual.det.rank → 𝕜) :
    detScalarEquiv A ((dualDetIso A).hom.fiberMap x u) = detScalarEquiv A.dual u := by
  rw [dualDetIso, fiberMap_constIso_hom]
  exact (detScalarEquiv A).apply_symm_apply (detScalarEquiv A.dual u)

theorem detScalarEquiv_fiberMap_dualDetIso_inv (A : FiniteRankBundleCore 𝕜 B) (x : B)
    (u : Fin A.det.dual.rank → 𝕜) :
    detScalarEquiv A.dual ((dualDetIso A).inv.fiberMap x u) = detScalarEquiv A u := by
  rw [dualDetIso, fiberMap_constIso_inv]
  exact (detScalarEquiv A.dual).apply_symm_apply (detScalarEquiv A u)

/-- Each fibre of `A.dual.det` is canonically identified with the space of top-degree scalar-valued
continuous alternating forms on `A.core.Fiber x` by multiplying the standard determinant form
`(Pi.basisFun 𝕜 (Fin A.rank)).continuousDet` by `detScalarEquiv A.dual`. -/
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
      (detScalarEquiv A.dual).symm (ω (Pi.basisFun 𝕜 (Fin A.rank))) :=
  (dualDetTopFormFiberEquiv A x).injective <|
    ((dualDetTopFormFiberEquiv A x).apply_symm_apply ω).trans <|
      ContinuousAlternatingMap.ext fun v ↦
        (ω.apply_eq_det_mul (Pi.basisFun 𝕜 (Fin A.rank)) v).trans <|
          (mul_comm _ _).trans <|
            (congrArg (· * _) ((detScalarEquiv A.dual).apply_symm_apply _)).symm.trans
              (dualDetTopFormFiberEquiv_apply A x _ v).symm

/-- Over `A`'s chart at `a`, reading `dualDetTopFormFiberEquiv A x u` in the alternating-form
bundle trivialization at `a` gives the top-degree form whose scalar coefficient on the standard
basis is the `a`-chart coordinate of `u` in `A.dual.det`. -/
theorem dualDetTopFormFiberEquiv_inCoordinates (A : FiniteRankBundleCore 𝕜 B) (a x : B)
    (hx : x ∈ A.core.baseSet a) (u : Fin A.dual.det.rank → 𝕜) :
    (trivializationAt ((Fin A.rank → 𝕜) [⋀^Fin A.rank]→L[𝕜] 𝕜)
      (fun y ↦ A.core.Fiber y [⋀^Fin A.rank]→L[𝕜] 𝕜) a
      ⟨x, dualDetTopFormFiberEquiv A x u⟩).2 =
      (Pi.basisFun 𝕜 (Fin A.rank)).topFormEquiv.symm
        (detScalarEquiv A.dual ((A.dual.det.core.localTriv a ⟨x, u⟩).2)) := by
  apply (Pi.basisFun 𝕜 (Fin A.rank)).topFormEquiv.injective
  rw [ContinuousLinearEquiv.apply_symm_apply,
    FiberBundle.trivializationAt_continuousAlternatingMap_apply_snd]
  have hb : x ∈ (trivializationAt (Fin A.rank → 𝕜) A.core.Fiber a).baseSet := by
    rwa [A.trivializationAt_core]
  rw [A.core.trivializationAt_symmL hb, A.indexAt_eq, A.indexAt_eq,
    Module.Basis.topFormEquiv_apply]
  let ω₀ : (Fin A.rank → 𝕜) [⋀^Fin A.rank]→L[𝕜] 𝕜 :=
    (Pi.basisFun 𝕜 (Fin A.rank)).topFormEquiv.symm (detScalarEquiv A.dual u)
  refine (ω₀.compContinuousLinearMap_apply_basis (Pi.basisFun 𝕜 (Fin A.rank))
    (A.core.coordChange a x x)).trans ?_
  have hu : ω₀ (Pi.basisFun 𝕜 (Fin A.rank)) = detScalarEquiv A.dual u :=
    ((Pi.basisFun 𝕜 (Fin A.rank)).topFormEquiv_apply ω₀).symm.trans
      ((Pi.basisFun 𝕜 (Fin A.rank)).topFormEquiv.apply_symm_apply (detScalarEquiv A.dual u))
  rw [hu, VectorBundleCore.localTriv_apply]
  dsimp only
  rw [A.dual.det.indexAt_eq, detScalarEquiv_coordChange_det, coordChange_dual]
  exact congrArg (· * detScalarEquiv A.dual u) (ContinuousLinearMap.det_piTranspose _).symm

/-- Reading `A.dual.det` vectors as top-degree alternating forms on the fibres of `A` is continuous
on total spaces. -/
theorem continuous_dualDetTopFormFiberEquiv (A : FiniteRankBundleCore 𝕜 B) :
    Continuous fun p : A.dual.det.core.TotalSpace ↦
      TotalSpace.mk' ((Fin A.rank → 𝕜) [⋀^Fin A.rank]→L[𝕜] 𝕜)
        (E := fun x ↦ A.core.Fiber x [⋀^Fin A.rank]→L[𝕜] 𝕜) p.proj
        (dualDetTopFormFiberEquiv A p.proj p.2) := by
  refine continuous_iff_continuousAt.2 fun p ↦ ?_
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨A.dual.det.core.continuous_proj.continuousAt, ?_⟩
  have hp : p ∈ (A.dual.det.core.localTriv p.proj).source :=
    (A.dual.det.core.mem_localTriv_source p.proj p).2 (A.dual.det.mem_baseSet_self p.proj)
  have hU := (A.dual.det.core.localTriv p.proj).open_source.mem_nhds hp
  have hc := (((Pi.basisFun 𝕜 (Fin A.rank)).topFormEquiv.symm.continuous.comp
    (detScalarEquiv A.dual).continuous).continuousAt.comp
    (((A.dual.det.core.localTriv p.proj).continuousOn.continuousAt hU).snd))
  refine hc.congr_of_eventuallyEq ?_
  filter_upwards [hU] with ⟨x, u⟩ hq
  have hq' : x ∈ A.core.baseSet p.proj := by
    have hmem := (A.dual.det.core.mem_localTriv_source p.proj ⟨x, u⟩).1 hq
    rwa [baseSet_det] at hmem
  exact dualDetTopFormFiberEquiv_inCoordinates A p.proj x hq' u

/-- The reconstructed total space of `A.dual.det` is canonically homeomorphic over `B` to Mathlib's
bundle of top-degree scalar-valued continuous alternating forms on `A.core.Fiber`. -/
noncomputable def dualDetTopFormTotalSpaceHomeomorph (A : FiniteRankBundleCore 𝕜 B) :
    A.dual.det.core.TotalSpace ≃ₜ
      TotalSpace ((Fin A.rank → 𝕜) [⋀^Fin A.rank]→L[𝕜] 𝕜)
        (fun x ↦ A.core.Fiber x [⋀^Fin A.rank]→L[𝕜] 𝕜) :=
  bundleHomeomorph (dualDetTopFormFiberEquiv A) (continuous_dualDetTopFormFiberEquiv A)

@[simp] theorem dualDetTopFormTotalSpaceHomeomorph_apply (A : FiniteRankBundleCore 𝕜 B)
    (p : A.dual.det.core.TotalSpace) :
    dualDetTopFormTotalSpaceHomeomorph A p =
      ⟨p.proj, dualDetTopFormFiberEquiv A p.proj p.2⟩ :=
  bundleHomeomorph_apply _ _ p

@[simp] theorem dualDetTopFormTotalSpaceHomeomorph_symm_apply (A : FiniteRankBundleCore 𝕜 B)
    (p : TotalSpace ((Fin A.rank → 𝕜) [⋀^Fin A.rank]→L[𝕜] 𝕜)
      (fun x ↦ A.core.Fiber x [⋀^Fin A.rank]→L[𝕜] 𝕜)) :
    (dualDetTopFormTotalSpaceHomeomorph A).symm p =
      ⟨p.proj, (dualDetTopFormFiberEquiv A p.proj).symm p.2⟩ :=
  bundleHomeomorph_symm_apply _ _ p

end Dual

end TauCeti.FiniteRankBundleCore
