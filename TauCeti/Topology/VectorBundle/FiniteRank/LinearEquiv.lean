/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Dual
public import TauCeti.Topology.VectorBundle.Hom

/-!
# Presenting vector bundles as finite-rank cores via model-fibre coordinates

`FiniteRankBundleCore.ofBundle` presents a vector bundle whose model fibre is already a coordinate
space `Fin r → 𝕜`. Geometric vector bundles—such as tangent, cotangent, and tensor bundles—usually
carry an abstract finite-dimensional normed space `F` as model fibre instead. Given any continuous
linear equivalence `e : F ≃L[𝕜] (Fin r → 𝕜)` (for example `b.equivFunL` of a basis `b` of `F`),
`FiniteRankBundleCore.ofLinearEquiv e V` conjugates the point-indexed transitions of `V` by `e` to
produce an object of `FiniteRankBundleCore 𝕜 B` in the base universe, independent of the fibre
universe of `V`.

* `FiniteRankBundleCore.ofLinearEquivFiberEquiv` and
  `FiniteRankBundleCore.ofLinearEquivTotalSpaceHomeomorph` identify the reconstructed bundle of
  `ofLinearEquiv e V` with `V` over the identity of `B`, without completeness or separation
  assumptions.
* `FiniteRankBundleCore.ofLinearEquivChangeIso` shows that two model-coordinate equivalences
  `e₁` and `e₂` on `F` give canonically isomorphic cores via the constant transition
  `e₁.symm.trans e₂`, commuting with the reconstruction homeomorphisms onto `TotalSpace F V`.
* Over a complete scalar field, `FiniteRankBundleCore.dualCoords e` equips the continuous dual
  `F →L[𝕜] 𝕜` with the dual coordinate map `p ↦ fun i ↦ p (e.symm (Pi.single i 1))`, and
  `FiniteRankBundleCore.ofLinearEquivDualIso e V` identifies `(ofLinearEquiv e V).dual` with the
  core of Mathlib's dual bundle `fun x ↦ V x →L[𝕜] 𝕜` by the identity on every coordinate fibre.
-/

public section

open Bundle CategoryTheory Set VectorBundleCore

namespace TauCeti.FiniteRankBundleCore

universe u v w z

section General

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜]
  {B : Type u} [TopologicalSpace B]
  {F : Type w} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Present a vector bundle `V` with model fibre `F` as a point-indexed finite-rank core by
conjugating its preferred chart transitions through a continuous linear equivalence
`e : F ≃L[𝕜] (Fin r → 𝕜)`. Neither `F` nor the fibre universe of `V` occurs in the result type. -/
-- Expose the rank projection so dependent coordinate spaces reduce to `Fin r → 𝕜`.
@[expose]
noncomputable def ofLinearEquiv {r : ℕ} (e : F ≃L[𝕜] (Fin r → 𝕜)) (V : B → Type z)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
    [FiberBundle F V] [VectorBundle 𝕜 F V] :
    FiniteRankBundleCore 𝕜 B where
  rank := r
  core :=
    { baseSet := fun b ↦ (trivializationAt F V b).baseSet
      isOpen_baseSet := fun b ↦ (trivializationAt F V b).open_baseSet
      indexAt := id
      mem_baseSet_at := fun b ↦ mem_baseSet_trivializationAt F V b
      coordChange := fun b c x ↦
        e.arrowCongr e ((trivializationAt F V b).coordChangeL 𝕜 (trivializationAt F V c) x)
      coordChange_self := fun b x hx u ↦ by
        rw [ContinuousLinearEquiv.arrowCongr_apply]
        simp only [ContinuousLinearEquiv.coe_coe]
        rw [Trivialization.coe_coordChangeL (R := 𝕜) _ _ ⟨hx, hx⟩, LinearEquiv.trans_apply,
          LinearEquiv.apply_symm_apply, e.apply_symm_apply]
      continuousOn_coordChange := fun b c ↦
        (e.arrowCongr e).continuous.comp_continuousOn (continuousOn_coordChange 𝕜 _ _)
      coordChange_comp := fun b c d x hx u ↦ by
        simp only [ContinuousLinearEquiv.arrowCongr_apply, ContinuousLinearEquiv.symm_apply_apply,
          ContinuousLinearEquiv.coe_coe]
        rw [Trivialization.coe_coordChangeL _ _ ⟨hx.1.1, hx.1.2⟩,
          Trivialization.coe_coordChangeL _ _ ⟨hx.1.2, hx.2⟩,
          Trivialization.coe_coordChangeL _ _ ⟨hx.1.1, hx.2⟩]
        simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] }
  indexAt_eq := fun _ ↦ rfl

section Basic

variable {r : ℕ} (e : F ≃L[𝕜] (Fin r → 𝕜)) (V : B → Type z)
  [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

@[simp] theorem rank_ofLinearEquiv : (ofLinearEquiv e V).rank = r := (rfl)

theorem baseSet_ofLinearEquiv (b : B) :
    (ofLinearEquiv e V).core.baseSet b = (trivializationAt F V b).baseSet := (rfl)

@[simp] theorem localTriv_baseSet_ofLinearEquiv (b : B) :
    ((ofLinearEquiv e V).core.localTriv b).baseSet = (trivializationAt F V b).baseSet := (rfl)

@[simp] theorem coordChange_ofLinearEquiv (b c x : B) :
    (ofLinearEquiv e V).core.coordChange b c x =
      e.arrowCongr e ((trivializationAt F V b).coordChangeL 𝕜 (trivializationAt F V c) x) :=
  (rfl)

/-- For the identity coordinate equivalence on `Fin r → 𝕜`, `ofLinearEquiv` is canonically
isomorphic to `ofBundle` by the identity on every coordinate fibre. -/
noncomputable def ofLinearEquivReflIso (r : ℕ) (W : B → Type z)
    [∀ x, AddCommMonoid (W x)] [∀ x, Module 𝕜 (W x)]
    [∀ x, TopologicalSpace (W x)] [TopologicalSpace (TotalSpace (Fin r → 𝕜) W)]
    [FiberBundle (Fin r → 𝕜) W] [VectorBundle 𝕜 (Fin r → 𝕜) W] :
    ofLinearEquiv (ContinuousLinearEquiv.refl 𝕜 (Fin r → 𝕜)) W ≅ ofBundle 𝕜 r W :=
  constIso (fun b ↦ ((pointIndexedCore_localTriv_baseSet 𝕜 (Fin r → 𝕜) W b).symm))
    (ContinuousLinearEquiv.refl 𝕜 (Fin r → 𝕜)) fun b c x _ _ ↦
      ContinuousLinearMap.ext fun u ↦
        DFunLike.congr_fun (pointIndexedCore_coordChange 𝕜 (Fin r → 𝕜) W b c x).symm u

/-- The continuous linear equivalence identifying the reconstructed fibre of `ofLinearEquiv e V` at
`x` with `V x`, via `e.symm` followed by the inverse of `trivializationAt F V x`. -/
noncomputable def ofLinearEquivFiberEquiv (x : B) :
    (ofLinearEquiv e V).core.Fiber x ≃L[𝕜] V x :=
  e.symm.trans (VectorBundle.continuousLinearEquivAt 𝕜 F V x).symm

@[simp] theorem ofLinearEquivFiberEquiv_apply (x : B) (u : Fin r → 𝕜) :
    ofLinearEquivFiberEquiv e V x u = (trivializationAt F V x).symm x (e.symm u) := (rfl)

@[simp] theorem ofLinearEquivFiberEquiv_symm_apply (x : B) (v : V x) :
    (ofLinearEquivFiberEquiv e V x).symm v = e ((trivializationAt F V x ⟨x, v⟩).2) := (rfl)

private noncomputable def ofLinearEquivTotalEquiv :
    (ofLinearEquiv e V).core.TotalSpace ≃ TotalSpace F V where
  toFun p := ⟨p.proj, ofLinearEquivFiberEquiv e V p.proj p.2⟩
  invFun p := ⟨p.proj, (ofLinearEquivFiberEquiv e V p.proj).symm p.2⟩
  left_inv p := by
    dsimp only
    rw [ContinuousLinearEquiv.symm_apply_apply]
  right_inv p := by
    dsimp only
    rw [ContinuousLinearEquiv.apply_symm_apply]

private theorem trivializationAt_ofLinearEquivTotalEquiv (b : B)
    (p : (ofLinearEquiv e V).core.TotalSpace)
    (hp : p.proj ∈ (trivializationAt F V b).baseSet) :
    (trivializationAt F V b) (ofLinearEquivTotalEquiv e V p) =
      (p.proj, e.symm (((ofLinearEquiv e V).core.localTriv b p).2)) := by
  have h := ((trivializationAt F V p.proj).mk_coordChangeL (R := 𝕜) (trivializationAt F V b)
    ⟨mem_baseSet_trivializationAt F V p.proj, hp⟩ (e.symm p.2)).symm
  refine h.trans (Prod.ext rfl ?_)
  rw [VectorBundleCore.localTriv_apply]
  exact (e.symm_apply_apply
    ((trivializationAt F V p.proj).coordChangeL 𝕜
      (trivializationAt F V b) p.proj (e.symm p.2))).symm

private theorem continuous_ofLinearEquivTotalEquiv :
    Continuous (ofLinearEquivTotalEquiv e V) := by
  refine continuous_iff_continuousAt.2 fun p ↦ ?_
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨(ofLinearEquiv e V).core.continuous_proj.continuousAt, ?_⟩
  have hp : p ∈ ((ofLinearEquiv e V).core.localTriv p.proj).source :=
    (ofLinearEquiv e V).core.mem_source_at p.proj p.2
  have hU := ((ofLinearEquiv e V).core.localTriv p.proj).open_source.mem_nhds hp
  have hc := e.symm.continuous.continuousAt.comp
    (((ofLinearEquiv e V).core.localTriv p.proj).continuousOn.continuousAt hU).snd
  refine hc.congr_of_eventuallyEq ?_
  filter_upwards [hU] with q hq
  exact congrArg Prod.snd (trivializationAt_ofLinearEquivTotalEquiv e V p.proj q
    (((ofLinearEquiv e V).core.localTriv p.proj).mem_source.1 hq))

private theorem continuous_ofLinearEquivTotalEquiv_symm :
    Continuous (ofLinearEquivTotalEquiv e V).symm := by
  refine continuous_iff_continuousAt.2 fun p ↦ ?_
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨(FiberBundle.continuous_proj F V).continuousAt, ?_⟩
  have hp := FiberBundle.mem_trivializationAt_proj_source (x := p)
  have hU := (trivializationAt F V p.proj).open_source.mem_nhds hp
  have hc := e.continuous.continuousAt.comp
    ((trivializationAt F V p.proj).continuousOn.continuousAt hU).snd
  refine hc.congr_of_eventuallyEq ?_
  filter_upwards [hU] with q hq
  rw [(ofLinearEquiv e V).trivializationAt_core]
  have hproj : ((ofLinearEquivTotalEquiv e V).symm p).proj = p.proj := rfl
  rw [hproj]
  have htriv := congrArg (fun z ↦ e z.2) (trivializationAt_ofLinearEquivTotalEquiv e V p.proj
    ((ofLinearEquivTotalEquiv e V).symm q)
    ((trivializationAt F V p.proj).mem_source.1 hq))
  rw [Equiv.apply_symm_apply] at htriv
  exact ((e.apply_symm_apply _).symm.trans htriv.symm)

/-- The reconstructed total space of `ofLinearEquiv e V` is homeomorphic to `TotalSpace F V` over
the identity of `B`, acting on each fibre by `ofLinearEquivFiberEquiv e V`. -/
noncomputable def ofLinearEquivTotalSpaceHomeomorph :
    (ofLinearEquiv e V).core.TotalSpace ≃ₜ TotalSpace F V where
  toEquiv := ofLinearEquivTotalEquiv e V
  continuous_toFun := continuous_ofLinearEquivTotalEquiv e V
  continuous_invFun := continuous_ofLinearEquivTotalEquiv_symm e V

@[simp] theorem ofLinearEquivTotalSpaceHomeomorph_apply
    (p : (ofLinearEquiv e V).core.TotalSpace) :
    ofLinearEquivTotalSpaceHomeomorph e V p =
      ⟨p.proj, ofLinearEquivFiberEquiv e V p.proj p.2⟩ := (rfl)

@[simp] theorem ofLinearEquivTotalSpaceHomeomorph_symm_apply (p : TotalSpace F V) :
    (ofLinearEquivTotalSpaceHomeomorph e V).symm p =
      ⟨p.proj, (ofLinearEquivFiberEquiv e V p.proj).symm p.2⟩ := (rfl)

/-- Over `b`'s chart domain, `ofLinearEquivTotalSpaceHomeomorph` intertwines the core chart at `b`
with `trivializationAt F V b` through `e.symm` on the fibre coordinate. -/
theorem trivializationAt_ofLinearEquivTotalSpaceHomeomorph (b : B)
    (p : (ofLinearEquiv e V).core.TotalSpace)
    (hp : p.proj ∈ (trivializationAt F V b).baseSet) :
    (trivializationAt F V b) (ofLinearEquivTotalSpaceHomeomorph e V p) =
      (p.proj, e.symm (((ofLinearEquiv e V).core.localTriv b p).2)) :=
  trivializationAt_ofLinearEquivTotalEquiv e V b p hp

end Basic

/-! ### Change of model coordinates -/

/-- Changing the model-fibre coordinate equivalence from `e₁` to `e₂` induces a constant-matrix
isomorphism of finite-rank cores with fibre map `e₁.symm.trans e₂`. -/
noncomputable def ofLinearEquivChangeIso {r₁ r₂ : ℕ}
    (e₁ : F ≃L[𝕜] (Fin r₁ → 𝕜)) (e₂ : F ≃L[𝕜] (Fin r₂ → 𝕜)) (V : B → Type z)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
    [FiberBundle F V] [VectorBundle 𝕜 F V] :
    ofLinearEquiv e₁ V ≅ ofLinearEquiv e₂ V :=
  constIso (fun _ ↦ rfl) (e₁.symm.trans e₂) fun b c x _ _ ↦
    ContinuousLinearMap.ext fun u ↦
      let T := (trivializationAt F V b).coordChangeL 𝕜 (trivializationAt F V c) x
      congrArg e₂ ((e₁.symm_apply_apply (T (e₁.symm u))).trans
        (congrArg T (e₂.symm_apply_apply (e₁.symm u)).symm))

@[simp] theorem fiberMap_ofLinearEquivChangeIso_hom {r₁ r₂ : ℕ}
    (e₁ : F ≃L[𝕜] (Fin r₁ → 𝕜)) (e₂ : F ≃L[𝕜] (Fin r₂ → 𝕜)) (V : B → Type z)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
    [FiberBundle F V] [VectorBundle 𝕜 F V] (x : B) :
    (ofLinearEquivChangeIso e₁ e₂ V).hom.fiberMap x =
      (e₁.symm.trans e₂ : (Fin r₁ → 𝕜) →L[𝕜] (Fin r₂ → 𝕜)) :=
  fiberMap_constIso_hom _ _ _ x

@[simp] theorem fiberMap_ofLinearEquivChangeIso_inv {r₁ r₂ : ℕ}
    (e₁ : F ≃L[𝕜] (Fin r₁ → 𝕜)) (e₂ : F ≃L[𝕜] (Fin r₂ → 𝕜)) (V : B → Type z)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
    [FiberBundle F V] [VectorBundle 𝕜 F V] (x : B) :
    (ofLinearEquivChangeIso e₁ e₂ V).inv.fiberMap x =
      (e₂.symm.trans e₁ : (Fin r₂ → 𝕜) →L[𝕜] (Fin r₁ → 𝕜)) :=
  fiberMap_constIso_inv _ _ _ x

/-- The coordinate-change isomorphism commutes with the reconstruction homeomorphisms onto
`TotalSpace F V`. -/
theorem ofLinearEquivTotalSpaceHomeomorph_changeIso_hom {r₁ r₂ : ℕ}
    (e₁ : F ≃L[𝕜] (Fin r₁ → 𝕜)) (e₂ : F ≃L[𝕜] (Fin r₂ → 𝕜)) (V : B → Type z)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
    [FiberBundle F V] [VectorBundle 𝕜 F V]
    (p : (ofLinearEquiv e₁ V).core.TotalSpace) :
    ofLinearEquivTotalSpaceHomeomorph e₂ V
        ((ofLinearEquivChangeIso e₁ e₂ V).hom.totalSpaceMap p) =
      ofLinearEquivTotalSpaceHomeomorph e₁ V p := by
  rcases p with ⟨x, u⟩
  rw [CoordinateHom.totalSpaceMap_mk, fiberMap_ofLinearEquivChangeIso_hom,
    ofLinearEquivTotalSpaceHomeomorph_apply, ofLinearEquivTotalSpaceHomeomorph_apply]
  exact congrArg (TotalSpace.mk' F x)
    (congrArg (VectorBundle.continuousLinearEquivAt 𝕜 F V x).symm (e₂.symm_apply_apply (e₁.symm u)))

end General

/-! ### Dual model coordinates -/

section Dual

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {B : Type u} [TopologicalSpace B]
  {F : Type w} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The dual coordinate equivalence on `F →L[𝕜] 𝕜` associated to `e : F ≃L[𝕜] (Fin r → 𝕜)`: a
functional `p` is sent to its values `i ↦ p (e.symm (Pi.single i 1))` on the basis vectors of `e`,
so that `(dualCoords e).symm w` pairs `v : F` with `w` by `∑ i, e v i * w i`. -/
noncomputable def dualCoords {r : ℕ} (e : F ≃L[𝕜] (Fin r → 𝕜)) :
    (F →L[𝕜] 𝕜) ≃L[𝕜] (Fin r → 𝕜) :=
  (e.arrowCongr (.refl 𝕜 𝕜)).trans (ContinuousLinearEquiv.piRing (𝕜 := 𝕜) (E := 𝕜) (Fin r))

@[simp] theorem dualCoords_apply {r : ℕ} (e : F ≃L[𝕜] (Fin r → 𝕜))
    (p : F →L[𝕜] 𝕜) (i : Fin r) :
    dualCoords e p i = p (e.symm (Pi.single i 1)) := by
  simp [dualCoords]

@[simp] theorem dualCoords_symm_apply {r : ℕ} (e : F ≃L[𝕜] (Fin r → 𝕜))
    (w : Fin r → 𝕜) (v : F) :
    (dualCoords e).symm w v = ∑ i, e v i * w i := by
  simp [dualCoords]

/-- Changing dual coordinates from `e₁` to `e₂` is the transpose of changing primal coordinates from
`e₂` to `e₁`. -/
theorem dualCoords_symm_trans_dualCoords {r₁ r₂ : ℕ}
    (e₁ : F ≃L[𝕜] (Fin r₁ → 𝕜)) (e₂ : F ≃L[𝕜] (Fin r₂ → 𝕜)) :
    ((dualCoords e₁).symm.trans (dualCoords e₂) : (Fin r₁ → 𝕜) →L[𝕜] (Fin r₂ → 𝕜)) =
      (e₂.symm.trans e₁ : (Fin r₂ → 𝕜) →L[𝕜] (Fin r₁ → 𝕜)).piTranspose := by
  refine (ContinuousLinearMap.eq_piTranspose_iff _ _).2 fun v w ↦ ?_
  have hv : (∑ i, v i • Pi.single i (1 : 𝕜)) = v := by
    ext j
    simp [Pi.single_apply]
  calc ∑ i, v i * dualCoords e₂ ((dualCoords e₁).symm w) i
      = ∑ i, v i * (dualCoords e₁).symm w (e₂.symm (Pi.single i 1)) := by simp
    _ = (dualCoords e₁).symm w (e₂.symm (∑ i, v i • Pi.single i 1)) := by
        simp_rw [← smul_eq_mul, ← map_smul, ← map_sum]
    _ = ∑ j, (e₂.symm.trans e₁ : (Fin r₂ → 𝕜) →L[𝕜] (Fin r₁ → 𝕜)) v j * w j := by
        rw [hv, dualCoords_symm_apply]
        rfl

/-- In `dualCoords b.equivFunL`, the `i`th coordinate of a functional `p : F →L[𝕜] 𝕜` is its value
`p (b i)` on the `i`th basis vector. -/
theorem dualCoords_equivFunL_apply {r : ℕ} (b : Module.Basis (Fin r) 𝕜 F)
    (p : F →L[𝕜] 𝕜) (i : Fin r) :
    dualCoords b.equivFunL p i = p (b i) := by
  rw [dualCoords_apply]
  exact congrArg p (b.equivFunL.injective (by simp))

/-- Reconstructing a functional from its dual coordinates `w` pairs `v : F` with `w` against the
primal coordinates `b.equivFun v`. -/
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
        b₁.equivFun.symm.toLinearMap := by
    refine LinearMap.ext fun v ↦ ?_
    simp [Module.Basis.equivFun_symm_apply, map_sum, map_smul]
  rw [ContinuousLinearMap.det, hconj, LinearMap.det_conj _ b₁.equivFun, b₂.det_basis b₁]

variable {r : ℕ} (e : F ≃L[𝕜] (Fin r → 𝕜)) (V : B → Type z)
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- On the overlap of two chart domains, the transition of the dual bundle `fun x ↦ V x →L[𝕜] 𝕜` in
`dualCoords e` equals the transposed reverse transition of `ofLinearEquiv e V`. -/
theorem coordChange_ofLinearEquiv_dualCoords {i j x : B}
    (hi : x ∈ (trivializationAt F V i).baseSet) (hj : x ∈ (trivializationAt F V j).baseSet) :
    (ofLinearEquiv (dualCoords e) (fun y ↦ V y →L[𝕜] 𝕜)).core.coordChange i j x =
      (ofLinearEquiv e V).dual.core.coordChange i j x := by
  rw [coordChange_ofLinearEquiv, coordChange_dual, coordChange_ofLinearEquiv]
  -- Reduce the exposed `.rank` projections to `r` so `Fin`-indexed sums match at `implicit`
  -- transparency during subsequent `rw` steps.
  change (dualCoords e).arrowCongr (dualCoords e)
      ((trivializationAt (F →L[𝕜] 𝕜) (fun y ↦ V y →L[𝕜] 𝕜) i).coordChangeL 𝕜
        (trivializationAt (F →L[𝕜] 𝕜) (fun y ↦ V y →L[𝕜] 𝕜) j) x) =
    (e.arrowCongr e
      ((trivializationAt F V j).coordChangeL 𝕜 (trivializationAt F V i) x)).piTranspose
  refine (ContinuousLinearMap.eq_piTranspose_iff _ _).2 fun v w ↦ ?_
  let ed (b : B) := trivializationAt (F →L[𝕜] 𝕜) (fun y ↦ V y →L[𝕜] 𝕜) b
  have hdi : x ∈ (ed i).baseSet := by simp [ed, hi]
  have hdj : x ∈ (ed j).baseSet := by simp [ed, hj]
  have hpair : ∑ k, v k *
      (dualCoords e).arrowCongr (dualCoords e) ((ed i).coordChangeL 𝕜 (ed j) x) w k =
      ((ed i).coordChangeL 𝕜 (ed j) x ((dualCoords e).symm w)) (e.symm v) := by
    conv_lhs =>
      arg 2
      ext k
      rw [← congrFun (e.apply_symm_apply v) k]
    rw [← dualCoords_symm_apply e _ (e.symm v)]
    simp [ed]
  rw [hpair, Trivialization.coordChangeL_apply _ _ ⟨hdi, hdj⟩]
  have hsymm : (ed i).symm x ((dualCoords e).symm w) =
      ((dualCoords e).symm w).comp ((trivializationAt F V i).continuousLinearMapAt 𝕜 x) := by
    rw [← (ed i).symmL_apply (R := 𝕜) hdi]
    exact (Bundle.Trivialization.continuousLinearMap_symmL (trivializationAt F V i)
      (trivializationAt 𝕜 (Bundle.Trivial B 𝕜) i) x ((dualCoords e).symm w)).trans
        (by simp [Trivial.eq_trivialization B 𝕜])
  rw [hsymm]
  simp only [ed, hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
    Trivial.fiberBundle_trivializationAt', Trivial.continuousLinearMapAt_trivialization,
    ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_apply]
  have hji : (trivializationAt F V i).continuousLinearMapAt 𝕜 x
      ((trivializationAt F V j).symmL 𝕜 x (e.symm v)) =
      (trivializationAt F V j).coordChangeL 𝕜 (trivializationAt F V i) x (e.symm v) := by
    rw [Trivialization.coordChangeL_apply _ _ ⟨hj, hi⟩,
      Trivialization.symmL_apply _ hj,
      Trivialization.continuousLinearMapAt_apply_of_mem _ _ hi]
  rw [hji, dualCoords_symm_apply]
  rfl

private theorem baseSet_ofLinearEquiv_dual (i : B) :
    (ofLinearEquiv e V).dual.core.baseSet i = (trivializationAt F V i).baseSet :=
  (localTriv_baseSet_dual (ofLinearEquiv e V) i).trans (baseSet_ofLinearEquiv e V i)

/-- The dual of `ofLinearEquiv e V` is canonically isomorphic to the core of Mathlib's dual bundle
`fun x ↦ V x →L[𝕜] 𝕜` in `dualCoords e`, by the identity on every coordinate fibre. -/
noncomputable def ofLinearEquivDualIso :
    (ofLinearEquiv e V).dual ≅ ofLinearEquiv (dualCoords e) (fun y ↦ V y →L[𝕜] 𝕜) :=
  constIso (fun i ↦ (baseSet_ofLinearEquiv_dual e V i).trans (by simp))
    (ContinuousLinearEquiv.refl 𝕜 (Fin r → 𝕜))
    fun i j x hi hj ↦ by
      rw [baseSet_ofLinearEquiv_dual] at hi hj
      ext (w : Fin r → 𝕜) : 1
      have h := congrFun (congrArg DFunLike.coe
        (coordChange_ofLinearEquiv_dualCoords e V hi hj).symm) w
      exact h

@[simp] theorem fiberMap_ofLinearEquivDualIso_hom (x : B) :
    (ofLinearEquivDualIso e V).hom.fiberMap x = ContinuousLinearMap.id 𝕜 (Fin r → 𝕜) :=
  fiberMap_constIso_hom _ _ _ x

@[simp] theorem fiberMap_ofLinearEquivDualIso_inv (x : B) :
    (ofLinearEquivDualIso e V).inv.fiberMap x = ContinuousLinearMap.id 𝕜 (Fin r → 𝕜) :=
  fiberMap_constIso_inv _ _ _ x

/-- Under `ofLinearEquivFiberEquiv`, a dual coordinate vector in `dualCoords e` represents the same
functional on `V x` as `dualFiberEquiv (ofLinearEquiv e V) x` precomposed with the inverse of
`ofLinearEquivFiberEquiv e V x`. -/
theorem ofLinearEquivFiberEquiv_dualCoords_apply (x : B) (w : Fin r → 𝕜) :
    ofLinearEquivFiberEquiv (dualCoords e) (fun y ↦ V y →L[𝕜] 𝕜) x w =
      (dualFiberEquiv (ofLinearEquiv e V) x w).comp
        (ofLinearEquivFiberEquiv e V x).symm.toContinuousLinearMap := by
  have hx : x ∈ (trivializationAt (F →L[𝕜] 𝕜) (fun y ↦ V y →L[𝕜] 𝕜) x).baseSet :=
    mem_baseSet_trivializationAt _ _ x
  rw [ofLinearEquivFiberEquiv_apply, ← Trivialization.symmL_apply (R := 𝕜) _ hx]
  refine (Bundle.Trivialization.continuousLinearMap_symmL (trivializationAt F V x)
    (trivializationAt 𝕜 (Bundle.Trivial B 𝕜) x) x ((dualCoords e).symm w)).trans ?_
  ext v
  simp only [Trivial.eq_trivialization B 𝕜, Trivial.symmL_trivialization,
    ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_apply, dualCoords_symm_apply,
    Trivialization.continuousLinearMapAt_apply_of_mem 𝕜 _ (mem_baseSet_trivializationAt F V x),
    ContinuousLinearEquiv.coe_coe, ofLinearEquivFiberEquiv_symm_apply]
  exact (dualFiberEquiv_apply_apply (ofLinearEquiv e V) x w _).symm

end Dual

end TauCeti.FiniteRankBundleCore
