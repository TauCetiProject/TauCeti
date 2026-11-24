/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Dual
public import TauCeti.Topology.VectorBundle.Hom

/-!
# Coordinate changes and duals for `FiniteRankBundleCore.ofLinearEquiv`

Given a continuous linear equivalence `e : F ≃L[𝕜] (Fin r → 𝕜)`,
`FiniteRankBundleCore.ofLinearEquiv e V` (defined in
`TauCeti.Topology.VectorBundle.FiniteRank.Basic`) presents a vector bundle `V` with model fibre
`F` as a point-indexed finite-rank core.

* `ofLinearEquivChangeIso` relates two coordinate equivalences `e₁`, `e₂` via `e₁.symm.trans e₂`,
  commuting with `ofLinearEquivTotalSpaceHomeomorph`.
* Over a complete field, `dualCoords e` gives dual coordinates on `F →L[𝕜] 𝕜` and
  `ofLinearEquivDualIso e V` identifies `(ofLinearEquiv e V).dual` with the core of
  `fun x ↦ V x →L[𝕜] 𝕜`.
-/

public section

open Bundle CategoryTheory Set VectorBundleCore

namespace TauCeti.FiniteRankBundleCore

universe u v w z

section General

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜]
  {B : Type u} [TopologicalSpace B]
  {F : Type w} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-! ### Change of model coordinates -/

section Change

variable {r₁ r₂ r₃ : ℕ} (e₁ : F ≃L[𝕜] (Fin r₁ → 𝕜)) (e₂ : F ≃L[𝕜] (Fin r₂ → 𝕜))
  (e₃ : F ≃L[𝕜] (Fin r₃ → 𝕜)) (V : B → Type z)
  [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- Changing model coordinates from `e₁` to `e₂` intertwines the transition maps of
`ofLinearEquiv e₁ V` and `ofLinearEquiv e₂ V`. -/
theorem coordChange_comp_ofLinearEquiv_change (b c x : B) :
    ((e₁.symm.trans e₂).toContinuousLinearMap.comp
        ((ofLinearEquiv e₁ V).core.coordChange b c x)) =
      ((ofLinearEquiv e₂ V).core.coordChange b c x).comp
        (e₁.symm.trans e₂).toContinuousLinearMap :=
  ContinuousLinearMap.ext fun u ↦
    let T := (trivializationAt F V b).coordChangeL 𝕜 (trivializationAt F V c) x
    congrArg e₂ ((e₁.symm_apply_apply (T (e₁.symm u))).trans
      (congrArg T (e₂.symm_apply_apply (e₁.symm u)).symm))

/-- Changing the model-fibre coordinate equivalence from `e₁` to `e₂` induces a constant-matrix
isomorphism of finite-rank cores with fibre map `e₁.symm.trans e₂`. -/
noncomputable def ofLinearEquivChangeIso :
    ofLinearEquiv e₁ V ≅ ofLinearEquiv e₂ V :=
  constIso (fun _ ↦ rfl) (e₁.symm.trans e₂) fun b c x _ _ ↦
    coordChange_comp_ofLinearEquiv_change e₁ e₂ V b c x

@[simp] theorem fiberMap_ofLinearEquivChangeIso_hom (x : B) :
    (ofLinearEquivChangeIso e₁ e₂ V).hom.fiberMap x =
      (e₁.symm.trans e₂ : (Fin r₁ → 𝕜) →L[𝕜] (Fin r₂ → 𝕜)) :=
  fiberMap_constIso_hom _ _ _ x

@[simp] theorem fiberMap_ofLinearEquivChangeIso_inv (x : B) :
    (ofLinearEquivChangeIso e₁ e₂ V).inv.fiberMap x =
      (e₂.symm.trans e₁ : (Fin r₂ → 𝕜) →L[𝕜] (Fin r₁ → 𝕜)) :=
  fiberMap_constIso_inv _ _ _ x

/-- Changing from a coordinate equivalence to itself is the identity isomorphism. -/
@[simp] theorem ofLinearEquivChangeIso_self :
    ofLinearEquivChangeIso e₁ e₁ V = Iso.refl (ofLinearEquiv e₁ V) :=
  Iso.ext <| hom_ext fun x ↦ by
    ext v
    simp [fiberMap_ofLinearEquivChangeIso_hom]
    -- `(ofLinearEquiv e₁ V).rank` reduces definitionally to `r₁`.
    rfl

/-- Inverting a coordinate-change isomorphism reverses the two coordinate equivalences. -/
@[simp] theorem ofLinearEquivChangeIso_symm :
    (ofLinearEquivChangeIso e₁ e₂ V).symm = ofLinearEquivChangeIso e₂ e₁ V :=
  Iso.ext <| hom_ext fun x ↦ by
    rw [Iso.symm_hom, fiberMap_ofLinearEquivChangeIso_inv, fiberMap_ofLinearEquivChangeIso_hom]

/-- Composing the forward maps of successive coordinate changes yields the direct coordinate
change. -/
@[simp] theorem ofLinearEquivChangeIso_hom_comp :
    (ofLinearEquivChangeIso e₁ e₂ V).hom ≫ (ofLinearEquivChangeIso e₂ e₃ V).hom =
      (ofLinearEquivChangeIso e₁ e₃ V).hom :=
  hom_ext fun x ↦ by
    ext v
    simp [fiberMap_ofLinearEquivChangeIso_hom]

/-- Composing the inverse maps of successive coordinate changes yields the direct inverse
coordinate change. -/
@[simp] theorem ofLinearEquivChangeIso_inv_comp :
    (ofLinearEquivChangeIso e₂ e₃ V).inv ≫ (ofLinearEquivChangeIso e₁ e₂ V).inv =
      (ofLinearEquivChangeIso e₁ e₃ V).inv := by
  simpa only [← Iso.symm_hom, ofLinearEquivChangeIso_symm] using
    ofLinearEquivChangeIso_hom_comp e₃ e₂ e₁ V

/-- Composing two coordinate-change isomorphisms yields the direct coordinate-change
isomorphism. -/
@[simp] theorem ofLinearEquivChangeIso_trans :
    (ofLinearEquivChangeIso e₁ e₂ V).trans (ofLinearEquivChangeIso e₂ e₃ V) =
      ofLinearEquivChangeIso e₁ e₃ V :=
  Iso.ext (ofLinearEquivChangeIso_hom_comp e₁ e₂ e₃ V)

/-- The coordinate-change isomorphism commutes with the reconstruction homeomorphisms onto
`TotalSpace F V`. -/
theorem ofLinearEquivTotalSpaceHomeomorph_changeIso_hom
    (p : (ofLinearEquiv e₁ V).core.TotalSpace) :
    ofLinearEquivTotalSpaceHomeomorph e₂ V
        ((ofLinearEquivChangeIso e₁ e₂ V).hom.totalSpaceMap p) =
      ofLinearEquivTotalSpaceHomeomorph e₁ V p := by
  rcases p with ⟨x, u⟩
  rw [CoordinateHom.totalSpaceMap_mk, fiberMap_ofLinearEquivChangeIso_hom,
    ofLinearEquivTotalSpaceHomeomorph_apply, ofLinearEquivTotalSpaceHomeomorph_apply]
  -- `u : (ofLinearEquiv e₁ V).core.Fiber x` is definitionally `Fin r₁ → 𝕜`.
  let u' : Fin r₁ → 𝕜 := u
  change TotalSpace.mk' F x (ofLinearEquivFiberEquiv e₂ V x
      ((e₁.symm.trans e₂ : (Fin r₁ → 𝕜) →L[𝕜] (Fin r₂ → 𝕜)) u')) =
    TotalSpace.mk' F x (ofLinearEquivFiberEquiv e₁ V x u')
  simp

end Change

end General

/-! ### Dual model coordinates -/

section Dual

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {B : Type u} [TopologicalSpace B]
  {F : Type w} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The dual coordinate equivalence on `F →L[𝕜] 𝕜` associated to `e : F ≃L[𝕜] (Fin r → 𝕜)`,
sending `p` to `i ↦ p (e.symm (Pi.single i 1))`. -/
noncomputable def dualCoords {r : ℕ} (e : F ≃L[𝕜] (Fin r → 𝕜)) :
    (F →L[𝕜] 𝕜) ≃L[𝕜] (Fin r → 𝕜) :=
  (e.arrowCongr (.refl 𝕜 𝕜)).trans (ContinuousLinearEquiv.piRing (𝕜 := 𝕜) (E := 𝕜) (Fin r))

@[simp] theorem dualCoords_apply {r : ℕ} (e : F ≃L[𝕜] (Fin r → 𝕜)) (p : F →L[𝕜] 𝕜) (i : Fin r) :
    dualCoords e p i = p (e.symm (Pi.single i 1)) := by simp [dualCoords]

@[simp] theorem dualCoords_symm_apply {r : ℕ} (e : F ≃L[𝕜] (Fin r → 𝕜)) (w : Fin r → 𝕜) (v : F) :
    (dualCoords e).symm w v = ∑ i, e v i * w i := by simp [dualCoords]

/-- Pairing a coordinate vector `v` against `dualCoords e p` evaluates `p` on `e.symm v`. -/
theorem sum_mul_dualCoords_apply {r : ℕ} (e : F ≃L[𝕜] (Fin r → 𝕜)) (p : F →L[𝕜] 𝕜)
    (v : Fin r → 𝕜) :
    ∑ i, v i * dualCoords e p i = p (e.symm v) := by
  have hv : (∑ i, v i • Pi.single i (1 : 𝕜)) = v := by ext j; simp [Pi.single_apply]
  calc ∑ i, v i * dualCoords e p i
      = p (e.symm (∑ i, v i • Pi.single i 1)) := by simp [← smul_eq_mul, map_sum, map_smul]
    _ = p (e.symm v) := by rw [hv]

/-- Changing dual coordinates from `e₁` to `e₂` is the transpose of changing primal coordinates from
`e₂` to `e₁`. -/
theorem dualCoords_symm_trans_dualCoords {r₁ r₂ : ℕ}
    (e₁ : F ≃L[𝕜] (Fin r₁ → 𝕜)) (e₂ : F ≃L[𝕜] (Fin r₂ → 𝕜)) :
    ((dualCoords e₁).symm.trans (dualCoords e₂) : (Fin r₁ → 𝕜) →L[𝕜] (Fin r₂ → 𝕜)) =
      (e₂.symm.trans e₁ : (Fin r₂ → 𝕜) →L[𝕜] (Fin r₁ → 𝕜)).piTranspose := by
  refine (ContinuousLinearMap.eq_piTranspose_iff _ _).2 fun v w ↦ ?_
  exact (sum_mul_dualCoords_apply e₂ ((dualCoords e₁).symm w) v).trans
    (dualCoords_symm_apply e₁ w (e₂.symm v))

/-- In `dualCoords b.equivFunL`, the `i`th coordinate of `p : F →L[𝕜] 𝕜` is `p (b i)`. -/
theorem dualCoords_equivFunL_apply {r : ℕ} (b : Module.Basis (Fin r) 𝕜 F)
    (p : F →L[𝕜] 𝕜) (i : Fin r) :
    dualCoords b.equivFunL p i = p (b i) :=
  (dualCoords_apply b.equivFunL p i).trans (congrArg p (b.equivFunL.injective (by simp)))

/-- Reconstructing a functional from its dual coordinates `w` pairs `v : F` with `w` against
`b.equivFun v`. -/
theorem dualCoords_equivFunL_symm_apply {r : ℕ} (b : Module.Basis (Fin r) 𝕜 F)
    (w : Fin r → 𝕜) (v : F) :
    (dualCoords b.equivFunL).symm w v = ∑ i, b.equivFun v i * w i :=
  dualCoords_symm_apply b.equivFunL w v

/-- Changing dual coordinates from `b₁` to `b₂` has determinant `b₁.det b₂`. -/
theorem det_dualCoords_equivFunL_symm_trans {r : ℕ} (b₁ b₂ : Module.Basis (Fin r) 𝕜 F) :
    (((dualCoords b₁.equivFunL).symm.trans
      (dualCoords b₂.equivFunL)).toContinuousLinearMap).det = b₁.det b₂ := by
  rw [dualCoords_symm_trans_dualCoords, ContinuousLinearMap.det_piTranspose]
  have hconj : ((b₂.equivFunL.symm.trans b₁.equivFunL : (Fin r → 𝕜) →L[𝕜] (Fin r → 𝕜)) :
      (Fin r → 𝕜) →ₗ[𝕜] (Fin r → 𝕜)) =
      b₁.equivFun.toLinearMap ∘ₗ (b₁.equiv b₂ (Equiv.refl (Fin r))).toLinearMap ∘ₗ
        b₁.equivFun.symm.toLinearMap :=
    LinearMap.ext fun v ↦ by simp [Module.Basis.equivFun_symm_apply, map_sum, map_smul]
  rw [ContinuousLinearMap.det, hconj, LinearMap.det_conj _ b₁.equivFun, b₂.det_basis b₁]

variable {r : ℕ} (e : F ≃L[𝕜] (Fin r → 𝕜)) (V : B → Type z)
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- On the overlap of two chart domains, the transition of `fun x ↦ V x →L[𝕜] 𝕜` in `dualCoords e`
equals the transposed reverse transition of `ofLinearEquiv e V`. -/
theorem coordChange_ofLinearEquiv_dualCoords {i j x : B}
    (hi : x ∈ (trivializationAt F V i).baseSet) (hj : x ∈ (trivializationAt F V j).baseSet) :
    (ofLinearEquiv (dualCoords e) (fun y ↦ V y →L[𝕜] 𝕜)).core.coordChange i j x =
      (ofLinearEquiv e V).dual.core.coordChange i j x := by
  rw [coordChange_ofLinearEquiv, coordChange_dual, coordChange_ofLinearEquiv]
  -- Pass `Fin r` explicitly so `Fintype` resolves to `Fin.fintype r` rather than
  -- `Fin.fintype (ofLinearEquiv e V).rank` (defeq via `@[expose]` on `ofLinearEquiv`).
  refine (ContinuousLinearMap.eq_piTranspose_iff (ι := Fin r) (κ := Fin r) _ _).2 fun v w ↦ ?_
  simp only [ContinuousLinearEquiv.arrowCongr_apply, ContinuousLinearEquiv.coe_coe]
  rw [sum_mul_dualCoords_apply, trivializationAt_dual_coordChangeL V hi hj,
    ContinuousLinearMap.comp_apply, dualCoords_symm_apply, ContinuousLinearEquiv.coe_coe]

/-- The chart domain of `(ofLinearEquiv e V).dual` at `i` is `(trivializationAt F V i).baseSet`. -/
theorem baseSet_ofLinearEquiv_dual (i : B) :
    (ofLinearEquiv e V).dual.core.baseSet i = (trivializationAt F V i).baseSet :=
  (localTriv_baseSet_dual (ofLinearEquiv e V) i).trans (baseSet_ofLinearEquiv e V i)

/-- On the overlap of two chart domains, the identity intertwines the transitions of
`(ofLinearEquiv e V).dual` and `ofLinearEquiv (dualCoords e) (fun y ↦ V y →L[𝕜] 𝕜)`. -/
theorem coordChange_comp_ofLinearEquiv_dual {i j x : B}
    (hi : x ∈ (ofLinearEquiv e V).dual.core.baseSet i)
    (hj : x ∈ (ofLinearEquiv e V).dual.core.baseSet j) :
    (ContinuousLinearMap.id 𝕜 (Fin (ofLinearEquiv e V).dual.rank → 𝕜)).comp
        ((ofLinearEquiv e V).dual.core.coordChange i j x) =
      ((ofLinearEquiv (dualCoords e) (fun y ↦ V y →L[𝕜] 𝕜)).core.coordChange i j x).comp
        (ContinuousLinearMap.id 𝕜 (Fin (ofLinearEquiv e V).dual.rank → 𝕜)) := by
  rw [baseSet_ofLinearEquiv_dual] at hi hj
  exact ContinuousLinearMap.ext fun (w : Fin r → 𝕜) ↦
    congrFun (congrArg DFunLike.coe (coordChange_ofLinearEquiv_dualCoords e V hi hj).symm) w

/-- On the overlap of two chart domains, the identity intertwines the transitions of
`ofLinearEquiv (dualCoords e) (fun y ↦ V y →L[𝕜] 𝕜)` and `(ofLinearEquiv e V).dual`. -/
theorem coordChange_comp_ofLinearEquiv_dual_symm {i j x : B}
    (hi : x ∈ (ofLinearEquiv (dualCoords e) (fun y ↦ V y →L[𝕜] 𝕜)).core.baseSet i)
    (hj : x ∈ (ofLinearEquiv (dualCoords e) (fun y ↦ V y →L[𝕜] 𝕜)).core.baseSet j) :
    (ContinuousLinearMap.id 𝕜
        (Fin (ofLinearEquiv (dualCoords e) (fun y ↦ V y →L[𝕜] 𝕜)).rank → 𝕜)).comp
        ((ofLinearEquiv (dualCoords e) (fun y ↦ V y →L[𝕜] 𝕜)).core.coordChange i j x) =
      ((ofLinearEquiv e V).dual.core.coordChange i j x).comp
        (ContinuousLinearMap.id 𝕜
          (Fin (ofLinearEquiv (dualCoords e) (fun y ↦ V y →L[𝕜] 𝕜)).rank → 𝕜)) := by
  rw [baseSet_ofLinearEquiv] at hi hj
  exact ContinuousLinearMap.ext fun (w : Fin r → 𝕜) ↦
    congrFun (congrArg DFunLike.coe
      (coordChange_ofLinearEquiv_dualCoords e V (by simpa using hi) (by simpa using hj))) w

/-- The dual of `ofLinearEquiv e V` is canonically isomorphic to the core of Mathlib's dual bundle
`fun x ↦ V x →L[𝕜] 𝕜` in `dualCoords e`, by the identity on every coordinate fibre. -/
noncomputable def ofLinearEquivDualIso :
    (ofLinearEquiv e V).dual ≅ ofLinearEquiv (dualCoords e) (fun y ↦ V y →L[𝕜] 𝕜) :=
  constIso (fun i ↦ (baseSet_ofLinearEquiv_dual e V i).trans
      (by rw [baseSet_ofLinearEquiv]; simp))
    (ContinuousLinearEquiv.refl 𝕜 (Fin r → 𝕜))
    fun _ _ _ hi hj ↦ coordChange_comp_ofLinearEquiv_dual e V hi hj

@[simp] theorem fiberMap_ofLinearEquivDualIso_hom (x : B) :
    (ofLinearEquivDualIso e V).hom.fiberMap x = ContinuousLinearMap.id 𝕜 (Fin r → 𝕜) :=
  fiberMap_constIso_hom _ _ _ x

@[simp] theorem fiberMap_ofLinearEquivDualIso_inv (x : B) :
    (ofLinearEquivDualIso e V).inv.fiberMap x = ContinuousLinearMap.id 𝕜 (Fin r → 𝕜) :=
  fiberMap_constIso_inv _ _ _ x

/-- Under `ofLinearEquivFiberEquiv`, a dual coordinate vector in `dualCoords e` represents the same
functional on `V x` as `dualFiberEquiv (ofLinearEquiv e V) x` precomposed with
`(ofLinearEquivFiberEquiv e V x).symm`. -/
theorem ofLinearEquivFiberEquiv_dualCoords_apply (x : B) (w : Fin r → 𝕜) :
    ofLinearEquivFiberEquiv (dualCoords e) (fun y ↦ V y →L[𝕜] 𝕜) x w =
      (dualFiberEquiv (ofLinearEquiv e V) x w).comp
        (ofLinearEquivFiberEquiv e V x).symm.toContinuousLinearMap := by
  rw [ofLinearEquivFiberEquiv_apply,
    trivializationAt_dual_symm_eq V (mem_baseSet_trivializationAt F V x)]
  ext v
  simp only [ContinuousLinearMap.comp_apply, dualCoords_symm_apply,
    Trivialization.continuousLinearMapAt_apply_of_mem 𝕜 _ (mem_baseSet_trivializationAt F V x),
    ContinuousLinearEquiv.coe_coe, ofLinearEquivFiberEquiv_symm_apply]
  exact (dualFiberEquiv_apply_apply (ofLinearEquiv e V) x w _).symm

end Dual

end TauCeti.FiniteRankBundleCore
