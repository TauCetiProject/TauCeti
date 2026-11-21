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

This builds on `TauCeti.pointIndexedCore` and `VectorBundleCore.congrModel`, generalizing the
trivial-model case. The fibrewise linear equivalence `ofBundleEquivFiberEquiv e V x` glues to a
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
  core := (pointIndexedCore 𝕜 F V).congrModel e
  indexAt_eq x := (congrModel_indexAt (pointIndexedCore 𝕜 F V) e x).trans
    (pointIndexedCore_indexAt 𝕜 F V x)

@[simp]
theorem rank_ofBundleEquiv : (ofBundleEquiv e V).rank = r := (rfl)

theorem baseSet_ofBundleEquiv (b : B) :
    (ofBundleEquiv e V).core.baseSet b = (trivializationAt F V b).baseSet :=
  (congrModel_baseSet (pointIndexedCore 𝕜 F V) e b).trans
    (pointIndexedCore_localTriv_baseSet 𝕜 F V b)

@[simp]
theorem localTriv_baseSet_ofBundleEquiv (b : B) :
    ((ofBundleEquiv e V).core.localTriv b).baseSet = (trivializationAt F V b).baseSet :=
  baseSet_ofBundleEquiv e V b

@[simp]
theorem coordChange_ofBundleEquiv (i j x : B) :
    (ofBundleEquiv e V).core.coordChange i j x =
      e.toContinuousLinearMap.comp
        (((trivializationAt F V i).coordChangeL 𝕜 (trivializationAt F V j) x : F →L[𝕜] F).comp
          e.symm.toContinuousLinearMap) :=
  (congrModel_coordChange (pointIndexedCore 𝕜 F V) e i j x).trans <| by
    rw [pointIndexedCore_coordChange]

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
      e (((pointIndexedCore 𝕜 F V).localTriv b ⟨x, e.symm v⟩).2) :=
    localTriv_congrModel_snd (pointIndexedCore 𝕜 F V) e b ⟨x, v⟩
  have h2 := congrArg Prod.snd
    (trivializationAt_pointIndexedCoreHomeomorph 𝕜 F V b ⟨x, e.symm v⟩ hx)
  rw [pointIndexedCoreHomeomorph_apply, pointIndexedCoreFiberEquiv_apply] at h2
  rw [h1, e.symm_apply_apply]
  exact h2

/-- Reconstruction of `ofBundleEquiv e V` is homeomorphic to the original vector bundle `V`, over
the identity of the base and by `ofBundleEquivFiberEquiv e V x` on each fibre. -/
noncomputable def ofBundleEquivTotalSpaceHomeomorph :
    (ofBundleEquiv e V).core.TotalSpace ≃ₜ TotalSpace F V :=
  ((pointIndexedCore 𝕜 F V).congrModelHomeomorph e).trans (pointIndexedCoreHomeomorph 𝕜 F V)

@[simp]
theorem ofBundleEquivTotalSpaceHomeomorph_apply (p : (ofBundleEquiv e V).core.TotalSpace) :
    ofBundleEquivTotalSpaceHomeomorph e V p = ⟨p.proj, ofBundleEquivFiberEquiv e V p.proj p.2⟩ :=
  (Homeomorph.trans_apply ((pointIndexedCore 𝕜 F V).congrModelHomeomorph e)
    (pointIndexedCoreHomeomorph 𝕜 F V) p).trans <|
    (congrArg (pointIndexedCoreHomeomorph 𝕜 F V)
      (congrModelHomeomorph_apply (pointIndexedCore 𝕜 F V) e p)).trans <|
      (pointIndexedCoreHomeomorph_apply 𝕜 F V _).trans <|
        congrArg (TotalSpace.mk' F p.proj) <|
          (pointIndexedCoreFiberEquiv_apply 𝕜 F V p.proj (e.symm p.2)).trans
            (ofBundleEquivFiberEquiv_apply e V p.proj p.2).symm

@[simp]
theorem ofBundleEquivTotalSpaceHomeomorph_symm_apply (p : TotalSpace F V) :
    (ofBundleEquivTotalSpaceHomeomorph e V).symm p =
      ⟨p.proj, (ofBundleEquivFiberEquiv e V p.proj).symm p.2⟩ :=
  (Homeomorph.symm_trans_apply ((pointIndexedCore 𝕜 F V).congrModelHomeomorph e)
    (pointIndexedCoreHomeomorph 𝕜 F V) p).trans <|
    (congrArg ((pointIndexedCore 𝕜 F V).congrModelHomeomorph e).symm
      (pointIndexedCoreHomeomorph_symm_apply 𝕜 F V p)).trans <|
      (congrModelHomeomorph_symm_apply (pointIndexedCore 𝕜 F V) e _).trans <|
        TotalSpace.ext rfl <| heq_of_eq <|
          (congrArg e (pointIndexedCoreFiberEquiv_symm_apply 𝕜 F V p.proj p.2)).trans
            (ofBundleEquivFiberEquiv_symm_apply e V p.proj p.2).symm

/-- On the base set of `trivializationAt F V b`, `ofBundleEquivTotalSpaceHomeomorph` intertwines
the core chart at `b` with `trivializationAt F V b` via `e.symm`. -/
theorem trivializationAt_ofBundleEquivTotalSpaceHomeomorph_snd (b : B)
    (p : (ofBundleEquiv e V).core.TotalSpace) (hp : p.proj ∈ (trivializationAt F V b).baseSet) :
    (trivializationAt F V b (ofBundleEquivTotalSpaceHomeomorph e V p)).2 =
      e.symm (((ofBundleEquiv e V).core.localTriv b p).2) := by
  rw [ofBundleEquivTotalSpaceHomeomorph_apply]
  exact trivializationAt_ofBundleEquivFiberEquiv_snd e V b hp p.2

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
  constIso (fun i ↦ (baseSet_ofBundleEquiv e₁ V i).trans (baseSet_ofBundleEquiv e₂ V i).symm)
    (e₁.symm.trans e₂) fun i j x _ _ ↦ by
      rw [coordChange_ofBundleEquiv, coordChange_ofBundleEquiv]
      exact ContinuousLinearMap.ext fun _ ↦
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
  dualFiberEquiv_apply_apply (ofBundleEquiv e V) x w (e ((trivializationAt F V x) ⟨x, v⟩).2)

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

/-- Evaluating the continuous linear equivalence
`piRing.symm.trans (e.symm.arrowCongr (ContinuousLinearEquiv.refl 𝕜 𝕜))` on `w` gives
`(piRing.symm w).comp e`. -/
theorem piRing_symm_trans_arrowCongr_apply (w : Fin r → 𝕜) :
    ((ContinuousLinearEquiv.piRing (𝕜 := 𝕜) (E := 𝕜) (Fin r)).symm.trans
        (e.symm.arrowCongr (ContinuousLinearEquiv.refl 𝕜 𝕜))).toContinuousLinearMap w =
      ((ContinuousLinearEquiv.piRing (𝕜 := 𝕜) (E := 𝕜) (Fin r)).symm w).comp
        e.toContinuousLinearMap :=
  ContinuousLinearMap.ext fun _ ↦ (rfl)

/-- In the preferred Hom-bundle chart at `a`, `ofBundleEquivDualFiberEquiv` reads a dual-core
coordinate vector through the constant continuous linear equivalence
`w ↦ (ContinuousLinearEquiv.piRing.symm w) ∘L e`. -/
theorem ofBundleEquivDualFiberEquiv_inCoordinates (a : B) {x : B}
    (hx : x ∈ (trivializationAt F V a).baseSet) (w : Fin r → 𝕜) :
    ContinuousLinearMap.inCoordinates F V 𝕜 (Trivial B 𝕜) a x a x
        (ofBundleEquivDualFiberEquiv e V x w) =
      ((ContinuousLinearEquiv.piRing (𝕜 := 𝕜) (E := 𝕜) (Fin r)).symm
        (((ofBundleEquiv e V).dual.core.localTriv a ⟨x, w⟩).2)).comp e.toContinuousLinearMap := by
  have hpi : (ContinuousLinearEquiv.piRing (𝕜 := 𝕜) (E := 𝕜) (Fin r)).symm
        (((ofBundleEquiv e V).dual.core.localTriv a ⟨x, w⟩).2) =
      ((ContinuousLinearEquiv.piRing (𝕜 := 𝕜) (E := 𝕜) (Fin r)).symm w).comp
        ((ofBundleEquiv e V).core.coordChange a x x) := by
    rw [VectorBundleCore.localTriv_apply, (ofBundleEquiv e V).dual.indexAt_eq, coordChange_dual]
    exact ContinuousLinearMap.piRing_symm_piTranspose _ w
  rw [hpi, coordChange_ofBundleEquiv]
  ext u
  have hR : (((ContinuousLinearEquiv.piRing (𝕜 := 𝕜) (E := 𝕜) (Fin r)).symm w).comp
      (e.toContinuousLinearMap.comp
        (((trivializationAt F V a).coordChangeL 𝕜 (trivializationAt F V x) x : F →L[𝕜] F).comp
          e.symm.toContinuousLinearMap))).comp e.toContinuousLinearMap u =
      ∑ k, e ((trivializationAt F V a).coordChangeL 𝕜 (trivializationAt F V x) x u) k * w k :=
    (congrArg ((ContinuousLinearEquiv.piRing (𝕜 := 𝕜) (E := 𝕜) (Fin r)).symm w)
        (congrArg e (congrArg _ (e.symm_apply_apply u)))).trans <|
      (ContinuousLinearEquiv.piRing_symm_apply (𝕜 := 𝕜) w _).trans (by simp only [smul_eq_mul]; rfl)
  refine (congrArg (fun f : 𝕜 →L[𝕜] 𝕜 ↦ f _)
      (Trivial.continuousLinearMapAt_trivialization 𝕜 B 𝕜 x)).trans <|
    (ofBundleEquivDualFiberEquiv_apply_apply e V x w ((trivializationAt F V a).symmL 𝕜 x u)).trans
      ((Finset.sum_congr rfl fun k _ ↦ ?_).trans hR.symm)
  congr 2
  rw [(trivializationAt F V a).symmL_apply hx,
    ← (trivializationAt F V a).mk_coordChangeL (R := 𝕜) (trivializationAt F V x)
      ⟨hx, mem_baseSet_trivializationAt F V x⟩ u]

/-- Near any `p₀`, reading `ofBundleEquivDualFiberEquiv` in the Hom-bundle chart at `p₀.proj`
eventually agrees with a fixed continuous linear equivalence applied to the dual core chart at
`p₀.proj`. -/
theorem eventuallyEq_inCoordinates_ofBundleEquivDualFiberEquiv
    (p₀ : (ofBundleEquiv e V).dual.core.TotalSpace) :
    (fun q : (ofBundleEquiv e V).dual.core.TotalSpace ↦
        ContinuousLinearMap.inCoordinates F V 𝕜 (Trivial B 𝕜) p₀.proj q.proj p₀.proj q.proj
          (ofBundleEquivDualFiberEquiv e V q.proj q.2)) =ᶠ[nhds p₀]
      fun q ↦
        ((ContinuousLinearEquiv.piRing (𝕜 := 𝕜) (E := 𝕜) (Fin r)).symm.trans
          (e.symm.arrowCongr (ContinuousLinearEquiv.refl 𝕜 𝕜))).toContinuousLinearMap
          (((ofBundleEquiv e V).dual.core.localTriv p₀.proj q).2) := by
  have hU := ((ofBundleEquiv e V).dual.core.localTriv p₀.proj).open_source.mem_nhds <|
    ((ofBundleEquiv e V).dual.core.mem_localTriv_source p₀.proj p₀).2
      ((baseSet_ofBundleEquiv e V p₀.proj).symm ▸ mem_baseSet_trivializationAt F V p₀.proj)
  filter_upwards [hU] with q hq
  exact (ofBundleEquivDualFiberEquiv_inCoordinates e V p₀.proj
    ((baseSet_ofBundleEquiv e V p₀.proj) ▸
      ((ofBundleEquiv e V).dual.core.mem_localTriv_source p₀.proj q).1 hq) q.2).trans
    (piRing_symm_trans_arrowCongr_apply e _).symm

/-- Reading dual-core coordinates as functionals on `V` is continuous on total spaces. -/
theorem continuous_ofBundleEquivDualFiberEquiv :
    Continuous fun p : (ofBundleEquiv e V).dual.core.TotalSpace ↦
      TotalSpace.mk' (F →L[𝕜] 𝕜) (E := fun x ↦ V x →L[𝕜] 𝕜) p.proj
        (ofBundleEquivDualFiberEquiv e V p.proj p.2) := by
  refine continuous_iff_continuousAt.2 fun p ↦ ?_
  rw [continuousAt_hom_bundle]
  refine ⟨(ofBundleEquiv e V).dual.core.continuous_proj.continuousAt, ?_⟩
  have hU := ((ofBundleEquiv e V).dual.core.localTriv p.proj).open_source.mem_nhds <|
    ((ofBundleEquiv e V).dual.core.mem_localTriv_source p.proj p).2
      ((baseSet_ofBundleEquiv e V p.proj).symm ▸ mem_baseSet_trivializationAt F V p.proj)
  have hc := (((ofBundleEquiv e V).dual.core.localTriv p.proj).continuousOn.continuousAt hU).snd
  let L : (Fin r → 𝕜) →L[𝕜] (F →L[𝕜] 𝕜) :=
    ((ContinuousLinearEquiv.piRing (𝕜 := 𝕜) (E := 𝕜) (Fin r)).symm.trans
      (e.symm.arrowCongr (ContinuousLinearEquiv.refl 𝕜 𝕜))).toContinuousLinearMap
  exact (L.continuous.continuousAt.comp hc).congr_of_eventuallyEq
    (eventuallyEq_inCoordinates_ofBundleEquivDualFiberEquiv e V p)

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
  bundleHomeomorph_apply _ _ p

@[simp]
theorem ofBundleEquivDualTotalSpaceHomeomorph_symm_apply
    (p : TotalSpace (F →L[𝕜] 𝕜) (fun x ↦ V x →L[𝕜] 𝕜)) :
    (ofBundleEquivDualTotalSpaceHomeomorph e V).symm p =
      ⟨p.proj, (ofBundleEquivDualFiberEquiv e V p.proj).symm p.2⟩ :=
  bundleHomeomorph_symm_apply _ _ p

end DualBundle

section DualChange

variable [CompleteSpace 𝕜] {r₁ r₂ : ℕ} (e₁ : F ≃L[𝕜] (Fin r₁ → 𝕜)) (e₂ : F ≃L[𝕜] (Fin r₂ → 𝕜))
  (V : B → Type*) [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- Composing the dual change-of-coordinates maps `e₁ ↦ e₂` and `e₂ ↦ e₁` yields the identity
morphism on `(ofBundleEquiv e₂ V).dual`. -/
theorem dualMap_changeIso_comp :
    (dualMap (ofBundleEquivChangeIso e₁ e₂ V).hom) ≫
        (dualMap (ofBundleEquivChangeIso e₂ e₁ V).hom) =
      𝟙 (ofBundleEquiv e₂ V).dual := by
  rw [← dualMap_comp]
  have h : (ofBundleEquivChangeIso e₂ e₁ V).hom ≫ (ofBundleEquivChangeIso e₁ e₂ V).hom =
      𝟙 (ofBundleEquiv e₂ V) := hom_ext fun x ↦
    (fiberMap_comp _ _ x).trans <|
      (congrArg₂ ContinuousLinearMap.comp
        (fiberMap_ofBundleEquivChangeIso_hom e₁ e₂ V x)
        (fiberMap_ofBundleEquivChangeIso_hom e₂ e₁ V x)).trans <|
      (show (e₁.symm.trans e₂).toContinuousLinearMap.comp
            (e₂.symm.trans e₁).toContinuousLinearMap =
          ContinuousLinearMap.id 𝕜 (Fin r₂ → 𝕜) from
        ContinuousLinearMap.ext fun v ↦
          (congrArg e₂ (e₁.symm_apply_apply (e₂.symm v))).trans
            (e₂.apply_symm_apply v)).trans (fiberMap_id (ofBundleEquiv e₂ V) x).symm
  rw [h, dualMap_id]

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
  simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.symm_apply_apply] using
    ContinuousLinearMap.sum_mul_piTranspose (e₂.symm.trans e₁).toContinuousLinearMap
      (e₂ ((trivializationAt F V x) ⟨x, v⟩).2) w

end DualChange

end TauCeti.FiniteRankBundleCore
