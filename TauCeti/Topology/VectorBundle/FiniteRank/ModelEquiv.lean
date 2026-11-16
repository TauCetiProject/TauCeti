/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Dual

/-!
# Finite-rank cores from a coordinate equivalence of the model fibre

Given a vector bundle `V` with model fibre `F` and a continuous linear equivalence
`e : F ≃L[𝕜] (Fin r → 𝕜)`, `TauCeti.FiniteRankBundleCore.ofBundleEquiv e V` presents `V` as a
point-indexed `FiniteRankBundleCore 𝕜 B` of rank `r` with the same chart domains as
`trivializationAt F V` and with the transition maps of `V` conjugated by `e`.

This generalizes `TauCeti.FiniteRankBundleCore.ofBundle`, which requires the model fibre to be
literally `Fin r → 𝕜`. The fibrewise linear equivalence `ofBundleEquivFiberEquiv e V x` glues to a
homeomorphism `ofBundleEquivTotalSpaceHomeomorph e V` between `(ofBundleEquiv e V).core.TotalSpace`
and `TotalSpace F V` over the identity of the base, requiring no completeness assumption on `𝕜`.
Changing the coordinate equivalence from `e₁` to `e₂` induces a canonical core isomorphism
`ofBundleEquivChangeIso e₁ e₂ V` with fibre map `e₂ ∘ e₁⁻¹`, compatible with the total-space
identifications.

Over a complete scalar field, the dual core `(ofBundleEquiv e V).dual` is identified fibrewise
linearly and homeomorphically with Mathlib's dual bundle `fun x ↦ V x →L[𝕜] 𝕜`
(`ofBundleEquivDualTotalSpaceHomeomorph e V`). Under this dual convention, a dual coordinate vector
`w : Fin r → 𝕜` represents the functional sending a vector with model coordinates `u : F` in the
preferred trivialization at `x` to `∑ k, e u k * w k`; in particular, the `i`th standard basis
vector `Pi.single i 1` represents the `i`th coordinate functional `u ↦ e u i`. Changing `e₁` to
`e₂` acts contravariantly by `dualMap (ofBundleEquivChangeIso e₂ e₁ V).hom` and commutes with the
identification to `fun x ↦ V x →L[𝕜] 𝕜`.

## References

* Norman Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §2–§3.
* John W. Milnor and James D. Stasheff, *Characteristic Classes*, Princeton University Press, 1974,
  §3.
-/

public section

open Bundle CategoryTheory FiberBundle Set VectorBundleCore

namespace TauCeti.FiniteRankBundleCore

variable {𝕜 B F : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

section OfBundleEquiv

variable {r : ℕ} (e : F ≃L[𝕜] (Fin r → 𝕜)) (V : B → Type*)
  [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- Present a vector bundle `V` with model fibre `F` as a point-indexed finite-rank core of rank
`r`, by transporting the model fibre along `e : F ≃L[𝕜] (Fin r → 𝕜)`. The charts have the same base
sets as `trivializationAt F V`, and the transitions are those of `V` conjugated by `e`. -/
-- Expose the rank projection so the dependent fibre model reduces to `Fin r → 𝕜`.
@[expose]
noncomputable def ofBundleEquiv : FiniteRankBundleCore 𝕜 B where
  rank := r
  core :=
    { baseSet := fun x ↦ (trivializationAt F V x).baseSet
      isOpen_baseSet := fun x ↦ (trivializationAt F V x).open_baseSet
      indexAt := id
      mem_baseSet_at := fun x ↦ mem_baseSet_trivializationAt F V x
      coordChange := fun i j x ↦
        e.toContinuousLinearMap.comp
          (((trivializationAt F V i).coordChangeL 𝕜 (trivializationAt F V j) x : F →L[𝕜] F).comp
            e.symm.toContinuousLinearMap)
      coordChange_self := fun i x hx v ↦ by
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
        rw [Trivialization.coe_coordChangeL (R := 𝕜) _ _ ⟨hx, hx⟩]
        simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
          ContinuousLinearEquiv.apply_symm_apply]
      continuousOn_coordChange := fun i j ↦
        (e.arrowCongr e).continuous.comp_continuousOn
          (continuousOn_coordChange 𝕜 (trivializationAt F V i)
            (trivializationAt F V j))
      coordChange_comp := fun i j k x hx v ↦ by
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
          ContinuousLinearEquiv.symm_apply_apply]
        rw [Trivialization.coe_coordChangeL (R := 𝕜) _ _ ⟨hx.1.1, hx.1.2⟩,
          Trivialization.coe_coordChangeL (R := 𝕜) _ _ ⟨hx.1.2, hx.2⟩,
          Trivialization.coe_coordChangeL (R := 𝕜) _ _ ⟨hx.1.1, hx.2⟩]
        simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] }
  indexAt_eq := fun _ ↦ rfl

@[simp]
theorem rank_ofBundleEquiv : (ofBundleEquiv e V).rank = r := (rfl)

@[simp]
theorem localTriv_baseSet_ofBundleEquiv (b : B) :
    ((ofBundleEquiv e V).core.localTriv b).baseSet = (trivializationAt F V b).baseSet := (rfl)

@[simp]
theorem coordChange_ofBundleEquiv (i j x : B) :
    (ofBundleEquiv e V).core.coordChange i j x =
      e.toContinuousLinearMap.comp
        (((trivializationAt F V i).coordChangeL 𝕜 (trivializationAt F V j) x : F →L[𝕜] F).comp
          e.symm.toContinuousLinearMap) := (rfl)

/-- On the fibre over `x`, identify the coordinate fibre `Fin r → 𝕜` of `ofBundleEquiv e V` with
`V x` by sending `v` to `(trivializationAt F V x).symm x (e.symm v)`. -/
noncomputable def ofBundleEquivFiberEquiv (x : B) :
    (ofBundleEquiv e V).core.Fiber x ≃L[𝕜] V x :=
  e.symm.trans (VectorBundle.continuousLinearEquivAt 𝕜 F V x).symm

@[simp]
theorem ofBundleEquivFiberEquiv_apply (x : B) (v : Fin r → 𝕜) :
    ofBundleEquivFiberEquiv e V x v = (trivializationAt F V x).symm x (e.symm v) := (rfl)

@[simp]
theorem ofBundleEquivFiberEquiv_symm_apply (x : B) (v : V x) :
    (ofBundleEquivFiberEquiv e V x).symm v = e ((trivializationAt F V x) ⟨x, v⟩).2 := (rfl)

/-- On the base set of the preferred trivialization of `V` at `b`, `ofBundleEquivFiberEquiv`
intertwines the core chart at `b` with `trivializationAt F V b` via `e.symm`. -/
theorem trivializationAt_ofBundleEquivFiberEquiv_snd (b : B) {x : B}
    (hx : x ∈ (trivializationAt F V b).baseSet) (v : Fin r → 𝕜) :
    (trivializationAt F V b ⟨x, ofBundleEquivFiberEquiv e V x v⟩).2 =
      e.symm (((ofBundleEquiv e V).core.localTriv b ⟨x, v⟩).2) := by
  have h1 : ((ofBundleEquiv e V).core.localTriv b ⟨x, v⟩).2 =
      e ((trivializationAt F V x).coordChangeL 𝕜 (trivializationAt F V b) x (e.symm v)) := by
    rw [VectorBundleCore.localTriv_apply]
    rfl
  rw [h1, e.symm_apply_apply, ofBundleEquivFiberEquiv_apply]
  exact (congrArg Prod.snd ((trivializationAt F V x).mk_coordChangeL (R := 𝕜)
    (trivializationAt F V b) ⟨mem_baseSet_trivializationAt F V x, hx⟩ (e.symm v))).symm

private noncomputable def ofBundleEquivTotalEquiv :
    (ofBundleEquiv e V).core.TotalSpace ≃ TotalSpace F V where
  toFun p := ⟨p.proj, ofBundleEquivFiberEquiv e V p.proj p.2⟩
  invFun p := ⟨p.proj, (ofBundleEquivFiberEquiv e V p.proj).symm p.2⟩
  left_inv p := by
    dsimp only
    rw [ContinuousLinearEquiv.symm_apply_apply]
  right_inv p := by
    dsimp only
    rw [ContinuousLinearEquiv.apply_symm_apply]

private theorem continuous_ofBundleEquivTotalEquiv :
    Continuous (ofBundleEquivTotalEquiv e V) := by
  refine continuous_iff_continuousAt.2 fun p ↦ ?_
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨(ofBundleEquiv e V).core.continuous_proj.continuousAt, ?_⟩
  have hp : p ∈ ((ofBundleEquiv e V).core.localTriv p.proj).source :=
    ((ofBundleEquiv e V).core.mem_localTriv_source p.proj p).2
      (mem_baseSet_trivializationAt F V p.proj)
  have hU := ((ofBundleEquiv e V).core.localTriv p.proj).open_source.mem_nhds hp
  have hc := (((ofBundleEquiv e V).core.localTriv p.proj).continuousOn.continuousAt hU).snd
  refine (e.symm.continuous.continuousAt.comp hc).congr_of_eventuallyEq ?_
  filter_upwards [hU] with q hq
  exact trivializationAt_ofBundleEquivFiberEquiv_snd e V p.proj
    (((ofBundleEquiv e V).core.mem_localTriv_source p.proj q).1 hq) q.2

private theorem continuous_ofBundleEquivTotalEquiv_symm :
    Continuous (ofBundleEquivTotalEquiv e V).symm := by
  refine continuous_iff_continuousAt.2 fun p ↦ ?_
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨(FiberBundle.continuous_proj F V).continuousAt, ?_⟩
  have hp : p ∈ (trivializationAt F V p.proj).source :=
    FiberBundle.mem_trivializationAt_proj_source (x := p)
  have hU := (trivializationAt F V p.proj).open_source.mem_nhds hp
  have hc := ((trivializationAt F V p.proj).continuousOn.continuousAt hU).snd
  refine (e.continuous.continuousAt.comp hc).congr_of_eventuallyEq ?_
  filter_upwards [hU] with q hq
  rw [(ofBundleEquiv e V).trivializationAt_core]
  have hq' := trivializationAt_ofBundleEquivFiberEquiv_snd e V p.proj
    ((trivializationAt F V p.proj).mem_source.1 hq)
    ((ofBundleEquivFiberEquiv e V q.proj).symm q.2)
  have happly : (⟨q.proj, ofBundleEquivFiberEquiv e V q.proj
      ((ofBundleEquivFiberEquiv e V q.proj).symm q.2)⟩ : TotalSpace F V) = q := by
    rw [ContinuousLinearEquiv.apply_symm_apply]
  rw [happly] at hq'
  exact ((congrArg e hq').trans (e.apply_symm_apply _)).symm

/-- Reconstruction of `ofBundleEquiv e V` is homeomorphic to the original vector bundle `V`, over
the identity of the base and by `ofBundleEquivFiberEquiv e V x` on each fibre. -/
noncomputable def ofBundleEquivTotalSpaceHomeomorph :
    (ofBundleEquiv e V).core.TotalSpace ≃ₜ TotalSpace F V where
  toEquiv := ofBundleEquivTotalEquiv e V
  continuous_toFun := continuous_ofBundleEquivTotalEquiv e V
  continuous_invFun := continuous_ofBundleEquivTotalEquiv_symm e V

@[simp]
theorem ofBundleEquivTotalSpaceHomeomorph_apply (p : (ofBundleEquiv e V).core.TotalSpace) :
    ofBundleEquivTotalSpaceHomeomorph e V p = ⟨p.proj, ofBundleEquivFiberEquiv e V p.proj p.2⟩ :=
  (rfl)

@[simp]
theorem ofBundleEquivTotalSpaceHomeomorph_symm_apply (p : TotalSpace F V) :
    (ofBundleEquivTotalSpaceHomeomorph e V).symm p =
      ⟨p.proj, (ofBundleEquivFiberEquiv e V p.proj).symm p.2⟩ := (rfl)

/-- On the base set of `trivializationAt F V b`, `ofBundleEquivTotalSpaceHomeomorph` intertwines
the core chart at `b` with `trivializationAt F V b` via `e.symm`. -/
theorem trivializationAt_ofBundleEquivTotalSpaceHomeomorph_snd (b : B)
    (p : (ofBundleEquiv e V).core.TotalSpace) (hp : p.proj ∈ (trivializationAt F V b).baseSet) :
    (trivializationAt F V b (ofBundleEquivTotalSpaceHomeomorph e V p)).2 =
      e.symm (((ofBundleEquiv e V).core.localTriv b p).2) :=
  trivializationAt_ofBundleEquivFiberEquiv_snd e V b hp p.2

end OfBundleEquiv

section ChangeEquiv

variable {r₁ r₂ : ℕ} (e₁ : F ≃L[𝕜] (Fin r₁ → 𝕜)) (e₂ : F ≃L[𝕜] (Fin r₂ → 𝕜)) (V : B → Type*)
  [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- Changing the coordinate equivalence of the model fibre from `e₁` to `e₂` induces a canonical
isomorphism of finite-rank cores with constant fibre map `e₂ ∘ e₁⁻¹`. -/
noncomputable def ofBundleEquivChangeIso :
    ofBundleEquiv e₁ V ≅ ofBundleEquiv e₂ V :=
  constIso (fun _ ↦ rfl) (e₁.symm.trans e₂) fun _ _ _ _ _ ↦
    ContinuousLinearMap.ext fun _ ↦
      congrArg e₂ <| (e₁.symm_apply_apply _).trans (congrArg _ (e₂.symm_apply_apply _).symm)

@[simp]
theorem fiberMap_ofBundleEquivChangeIso_hom (x : B) :
    (ofBundleEquivChangeIso e₁ e₂ V).hom.fiberMap x = (e₁.symm.trans e₂).toContinuousLinearMap :=
  fiberMap_constIso_hom _ _ _ x

@[simp]
theorem fiberMap_ofBundleEquivChangeIso_inv (x : B) :
    (ofBundleEquivChangeIso e₁ e₂ V).inv.fiberMap x = (e₂.symm.trans e₁).toContinuousLinearMap :=
  fiberMap_constIso_inv _ _ _ x

/-- Changing the coordinate equivalence commutes with `ofBundleEquivFiberEquiv`. -/
theorem ofBundleEquivFiberEquiv_changeIso (x : B) (v : Fin r₁ → 𝕜) :
    ofBundleEquivFiberEquiv e₂ V x ((ofBundleEquivChangeIso e₁ e₂ V).hom.fiberMap x v) =
      ofBundleEquivFiberEquiv e₁ V x v := by
  rw [fiberMap_ofBundleEquivChangeIso_hom]
  exact congrArg ((trivializationAt F V x).symm x) (e₂.symm_apply_apply (e₁.symm v))

end ChangeEquiv

section DualBundle

variable [CompleteSpace 𝕜] {r : ℕ} (e : F ≃L[𝕜] (Fin r → 𝕜)) (V : B → Type*)
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- On the fibre over `x`, identify a dual coordinate vector `w : Fin r → 𝕜` of
`(ofBundleEquiv e V).dual` with the continuous linear functional on `V x` pairing a vector with
coordinates `u = e ((trivializationAt F V x) ⟨x, v⟩).2` to `∑ k, u k * w k`. -/
noncomputable def ofBundleEquivDualFiberEquiv (x : B) :
    (ofBundleEquiv e V).dual.core.Fiber x ≃L[𝕜] (V x →L[𝕜] 𝕜) :=
  (dualFiberEquiv (ofBundleEquiv e V) x).trans
    ((ofBundleEquivFiberEquiv e V x).arrowCongr (ContinuousLinearEquiv.refl 𝕜 𝕜))

/-- Explicit dual pairing convention: a dual coordinate vector `w` evaluates on `v : V x` by
pairing the `e`-coordinates of `v` in `trivializationAt F V x` with `w`. -/
@[simp]
theorem ofBundleEquivDualFiberEquiv_apply_apply (x : B) (w : Fin r → 𝕜) (v : V x) :
    ofBundleEquivDualFiberEquiv e V x w v =
      ∑ k, e ((trivializationAt F V x) ⟨x, v⟩).2 k * w k :=
  dualFiberEquiv_apply_apply (ofBundleEquiv e V) x w
    (e ((trivializationAt F V x) ⟨x, v⟩).2)

/-- Evaluated on a vector `(trivializationAt F V x).symm x u` of the preferred trivialization at
`x`, a dual coordinate vector `w` pairs `e u` with `w`. -/
theorem ofBundleEquivDualFiberEquiv_apply_symm (x : B) (w : Fin r → 𝕜) (u : F) :
    ofBundleEquivDualFiberEquiv e V x w ((trivializationAt F V x).symm x u) =
      ∑ k, e u k * w k := by
  rw [ofBundleEquivDualFiberEquiv_apply_apply,
    (trivializationAt F V x).apply_mk_symm (mem_baseSet_trivializationAt F V x) u]

/-- The `i`th standard basis vector `Pi.single i 1` of the dual core corresponds to the `i`th
coordinate functional `u ↦ e u i` on the preferred trivialization at `x`. -/
theorem ofBundleEquivDualFiberEquiv_single_apply_symm (x : B) (i : Fin r) (u : F) :
    ofBundleEquivDualFiberEquiv e V x (Pi.single i 1) ((trivializationAt F V x).symm x u) =
      e u i :=
  (ofBundleEquivDualFiberEquiv_apply_symm e V x (Pi.single i 1) u).trans
    (by simp [Pi.single_apply])

/-- The dual coordinates of a functional `α : V x →L[𝕜] 𝕜` are its values on the basis vectors
`(trivializationAt F V x).symm x (e.symm (Pi.single i 1))`. -/
@[simp]
theorem ofBundleEquivDualFiberEquiv_symm_apply (x : B) (α : V x →L[𝕜] 𝕜) (i : Fin r) :
    (ofBundleEquivDualFiberEquiv e V x).symm α i =
      α ((trivializationAt F V x).symm x (e.symm (Pi.single i 1))) :=
  dualFiberEquiv_symm_apply (ofBundleEquiv e V) x _ i

/-- In the preferred Hom-bundle chart at `a`, `ofBundleEquivDualFiberEquiv` reads a dual-core
coordinate vector through the constant continuous linear equivalence
`w ↦ (ContinuousLinearEquiv.piRing.symm w) ∘L e`. -/
theorem ofBundleEquivDualFiberEquiv_inCoordinates (a : B) {x : B}
    (hx : x ∈ (trivializationAt F V a).baseSet) (w : Fin r → 𝕜) :
    ContinuousLinearMap.inCoordinates F V 𝕜 (Trivial B 𝕜) a x a x
        (ofBundleEquivDualFiberEquiv e V x w) =
      ((ContinuousLinearEquiv.piRing (𝕜 := 𝕜) (E := 𝕜) (Fin r)).symm
        (((ofBundleEquiv e V).dual.core.localTriv a ⟨x, w⟩).2)).comp e.toContinuousLinearMap := by
  have hx' : x ∈ (trivializationAt F V x).baseSet := mem_baseSet_trivializationAt F V x
  have hpi : (ContinuousLinearEquiv.piRing (𝕜 := 𝕜) (E := 𝕜) (Fin r)).symm
        (((ofBundleEquiv e V).dual.core.localTriv a ⟨x, w⟩).2) =
      ((ContinuousLinearEquiv.piRing (𝕜 := 𝕜) (E := 𝕜) (Fin r)).symm w).comp
        ((ofBundleEquiv e V).core.coordChange a x x) := by
    rw [VectorBundleCore.localTriv_apply, (ofBundleEquiv e V).dual.indexAt_eq, coordChange_dual]
    exact ContinuousLinearMap.piRing_symm_piTranspose _ w
  rw [hpi]
  ext u
  have hL : ContinuousLinearMap.inCoordinates F V 𝕜 (Trivial B 𝕜) a x a x
      (ofBundleEquivDualFiberEquiv e V x w) u =
      ∑ k, e ((trivializationAt F V x) ⟨x, (trivializationAt F V a).symmL 𝕜 x u⟩).2 k * w k :=
    (congrArg (fun f : 𝕜 →L[𝕜] 𝕜 ↦ f _)
        (Trivial.continuousLinearMapAt_trivialization 𝕜 B 𝕜 x)).trans
      (ofBundleEquivDualFiberEquiv_apply_apply e V x w ((trivializationAt F V a).symmL 𝕜 x u))
  have hc : (ofBundleEquiv e V).core.coordChange a x x (e u) =
      e ((trivializationAt F V a).coordChangeL 𝕜 (trivializationAt F V x) x u) :=
    congrArg e (congrArg _ (e.symm_apply_apply u))
  have hR : (((ContinuousLinearEquiv.piRing (𝕜 := 𝕜) (E := 𝕜) (Fin r)).symm w).comp
      ((ofBundleEquiv e V).core.coordChange a x x)).comp e.toContinuousLinearMap u =
      ∑ k, e ((trivializationAt F V a).coordChangeL 𝕜 (trivializationAt F V x) x u) k * w k :=
    (congrArg ((ContinuousLinearEquiv.piRing (𝕜 := 𝕜) (E := 𝕜) (Fin r)).symm w) hc).trans <|
      (ContinuousLinearEquiv.piRing_symm_apply (𝕜 := 𝕜) w _).trans (by simp only [smul_eq_mul])
  refine hL.trans <| (Finset.sum_congr rfl fun k _ ↦ ?_).trans hR.symm
  congr 2
  rw [(trivializationAt F V a).symmL_apply hx,
    ← (trivializationAt F V a).mk_coordChangeL (R := 𝕜) (trivializationAt F V x) ⟨hx, hx'⟩ u]

/-- Reading dual-core coordinates as functionals on `V` is continuous on total spaces. -/
theorem continuous_ofBundleEquivDualFiberEquiv :
    Continuous fun p : (ofBundleEquiv e V).dual.core.TotalSpace ↦
      TotalSpace.mk' (F →L[𝕜] 𝕜) (E := fun x ↦ V x →L[𝕜] 𝕜) p.proj
        (ofBundleEquivDualFiberEquiv e V p.proj p.2) := by
  refine continuous_iff_continuousAt.2 fun p ↦ ?_
  rw [continuousAt_hom_bundle]
  refine ⟨(ofBundleEquiv e V).dual.core.continuous_proj.continuousAt, ?_⟩
  have hp : p ∈ ((ofBundleEquiv e V).dual.core.localTriv p.proj).source :=
    ((ofBundleEquiv e V).dual.core.mem_localTriv_source p.proj p).2
      (mem_baseSet_trivializationAt F V p.proj)
  have hU := ((ofBundleEquiv e V).dual.core.localTriv p.proj).open_source.mem_nhds hp
  have hc := (((ofBundleEquiv e V).dual.core.localTriv p.proj).continuousOn.continuousAt hU).snd
  let L : (Fin r → 𝕜) →L[𝕜] (F →L[𝕜] 𝕜) :=
    ((ContinuousLinearEquiv.piRing (𝕜 := 𝕜) (E := 𝕜) (Fin r)).symm.trans
      (e.symm.arrowCongr (ContinuousLinearEquiv.refl 𝕜 𝕜))).toContinuousLinearMap
  refine (L.continuous.continuousAt.comp hc).congr_of_eventuallyEq ?_
  filter_upwards [hU] with q hq
  refine (ofBundleEquivDualFiberEquiv_inCoordinates e V p.proj
    (((ofBundleEquiv e V).dual.core.mem_localTriv_source p.proj q).1 hq) q.2).trans ?_
  ext u
  rfl

/-- The reconstructed total space of `(ofBundleEquiv e V).dual` is homeomorphic to Mathlib's dual
bundle `fun x ↦ V x →L[𝕜] 𝕜`, over the identity of the base and by `ofBundleEquivDualFiberEquiv` on
each fibre. -/
noncomputable def ofBundleEquivDualTotalSpaceHomeomorph :
    (ofBundleEquiv e V).dual.core.TotalSpace ≃ₜ
      TotalSpace (F →L[𝕜] 𝕜) (fun x ↦ V x →L[𝕜] 𝕜) :=
  bundleHomeomorph (𝕜 := 𝕜) (ofBundleEquivDualFiberEquiv e V)
    (continuous_ofBundleEquivDualFiberEquiv e V)

@[simp]
theorem ofBundleEquivDualTotalSpaceHomeomorph_apply
    (p : (ofBundleEquiv e V).dual.core.TotalSpace) :
    ofBundleEquivDualTotalSpaceHomeomorph e V p =
      ⟨p.proj, ofBundleEquivDualFiberEquiv e V p.proj p.2⟩ :=
  bundleHomeomorph_apply (𝕜 := 𝕜) (ofBundleEquivDualFiberEquiv e V)
    (continuous_ofBundleEquivDualFiberEquiv e V) p

@[simp]
theorem ofBundleEquivDualTotalSpaceHomeomorph_symm_apply
    (p : TotalSpace (F →L[𝕜] 𝕜) (fun x ↦ V x →L[𝕜] 𝕜)) :
    (ofBundleEquivDualTotalSpaceHomeomorph e V).symm p =
      ⟨p.proj, (ofBundleEquivDualFiberEquiv e V p.proj).symm p.2⟩ :=
  bundleHomeomorph_symm_apply (𝕜 := 𝕜) (ofBundleEquivDualFiberEquiv e V)
    (continuous_ofBundleEquivDualFiberEquiv e V) p

end DualBundle

section DualChange

variable [CompleteSpace 𝕜] {r₁ r₂ : ℕ} (e₁ : F ≃L[𝕜] (Fin r₁ → 𝕜)) (e₂ : F ≃L[𝕜] (Fin r₂ → 𝕜))
  (V : B → Type*) [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- Changing the coordinate equivalence acts contravariantly on the dual core and commutes with the
identification `ofBundleEquivDualFiberEquiv` to `V x →L[𝕜] 𝕜`. -/
theorem ofBundleEquivDualFiberEquiv_dualMap_changeIso (x : B) (w : Fin r₁ → 𝕜) :
    ofBundleEquivDualFiberEquiv e₂ V x
        ((dualMap (ofBundleEquivChangeIso e₂ e₁ V).hom).fiberMap x w) =
      ofBundleEquivDualFiberEquiv e₁ V x w := by
  have hmap : ((dualMap (ofBundleEquivChangeIso e₂ e₁ V).hom).fiberMap x w : Fin r₂ → 𝕜) =
      (e₂.symm.trans e₁).toContinuousLinearMap.piTranspose w :=
    congrArg (fun S : (Fin r₁ → 𝕜) →L[𝕜] (Fin r₂ → 𝕜) ↦ S w) <|
      (fiberMap_dualMap _ x).trans (congrArg ContinuousLinearMap.piTranspose
        (fiberMap_ofBundleEquivChangeIso_hom e₂ e₁ V x))
  ext v
  rw [hmap, ofBundleEquivDualFiberEquiv_apply_apply, ofBundleEquivDualFiberEquiv_apply_apply]
  have h := ContinuousLinearMap.sum_mul_piTranspose
    (e₂.symm.trans e₁).toContinuousLinearMap
    (e₂ ((trivializationAt F V x) ⟨x, v⟩).2) w
  simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.symm_apply_apply] using h

end DualChange

end TauCeti.FiniteRankBundleCore
