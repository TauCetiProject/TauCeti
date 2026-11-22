/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Dual
import TauCeti.Analysis.Normed.Module.FiniteDimension

/-!
# Model-equivalence coordinate changes and dual cores of vector bundles

Given a vector bundle `V` with model fibre `F`, `TauCeti.FiniteRankBundleCore.ofBundle 𝕜 e V`
presents `V` as a point-indexed `FiniteRankBundleCore 𝕜 B` of rank `r` along a continuous linear
equivalence `e : F ≃L[𝕜] (Fin r → 𝕜)`. Changing the coordinate equivalence from `e₁` to `e₂`
induces a canonical core isomorphism `ofBundleChangeIso e₁ e₂ V` with fibre map `e₂ ∘ e₁⁻¹`,
compatible with the fibre identifications `ofBundleFiberEquiv`.

Over a complete scalar field, the dual core `(ofBundle 𝕜 e V).dual` is identified fibrewise
linearly and homeomorphically with Mathlib's dual bundle `fun x ↦ V x →L[𝕜] 𝕜`
(`ofBundleDualTotalSpaceHomeomorph e V`). Under this dual convention, a dual coordinate vector
`w : Fin r → 𝕜` represents the functional sending a vector with model coordinates `u : F` in the
preferred trivialization at `x` to `∑ k, e u k * w k`; in particular, the `i`th standard basis
vector `Pi.single i 1` represents the `i`th coordinate functional `u ↦ e u i`. Changing `e₁` to
`e₂` acts contravariantly by `dualMap (ofBundleChangeIso e₂ e₁ V).hom` and commutes with the
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

section ChangeEquiv

variable {r₁ r₂ : ℕ} (e₁ : F ≃L[𝕜] (Fin r₁ → 𝕜)) (e₂ : F ≃L[𝕜] (Fin r₂ → 𝕜)) (V : B → Type*)
  [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- Changing the coordinate equivalence of the model fibre from `e₁` to `e₂` induces a canonical
isomorphism of finite-rank cores with constant fibre map `e₂ ∘ e₁⁻¹`. -/
noncomputable def ofBundleChangeIso :
    ofBundle 𝕜 e₁ V ≅ ofBundle 𝕜 e₂ V :=
  constIso (fun i ↦ (baseSet_ofBundle e₁ V i).trans (baseSet_ofBundle e₂ V i).symm)
    (e₁.symm.trans e₂) fun i j x _ _ ↦ by
      rw [coordChange_ofBundle, coordChange_ofBundle]
      exact ContinuousLinearMap.ext fun _ ↦
        congrArg e₂ <| (e₁.symm_apply_apply _).trans (congrArg _ (e₂.symm_apply_apply _).symm)

@[simp]
theorem fiberMap_ofBundleChangeIso_hom (x : B) :
    (ofBundleChangeIso e₁ e₂ V).hom.fiberMap x = (e₁.symm.trans e₂).toContinuousLinearMap :=
  fiberMap_constIso_hom _ _ _ x

@[simp]
theorem fiberMap_ofBundleChangeIso_inv (x : B) :
    (ofBundleChangeIso e₁ e₂ V).inv.fiberMap x = (e₂.symm.trans e₁).toContinuousLinearMap :=
  fiberMap_constIso_inv _ _ _ x

theorem ofBundleChangeIso_inv :
    (ofBundleChangeIso e₁ e₂ V).inv = (ofBundleChangeIso e₂ e₁ V).hom :=
  hom_ext fun x ↦ by
    simp only [fiberMap_ofBundleChangeIso_inv, fiberMap_ofBundleChangeIso_hom]

/-- Changing the coordinate equivalence commutes with `ofBundleFiberEquiv`. -/
theorem ofBundleFiberEquiv_changeIso (x : B) (v : Fin r₁ → 𝕜) :
    ofBundleFiberEquiv e₂ V x ((ofBundleChangeIso e₁ e₂ V).hom.fiberMap x v) =
      ofBundleFiberEquiv e₁ V x v := by
  rw [fiberMap_ofBundleChangeIso_hom, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.trans_apply, ofBundleFiberEquiv_apply, ofBundleFiberEquiv_apply]
  exact congrArg ((trivializationAt F V x).symm x) (e₂.symm_apply_apply (e₁.symm v))

end ChangeEquiv

section DualBundle

variable [CompleteSpace 𝕜] {r : ℕ} (e : F ≃L[𝕜] (Fin r → 𝕜)) (V : B → Type*)
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- On the fibre over `x`, identify a dual coordinate vector `w : Fin r → 𝕜` of
`(ofBundle 𝕜 e V).dual` with the continuous linear functional on `V x` pairing a vector with
coordinates `u = e ((trivializationAt F V x) ⟨x, v⟩).2` to `∑ k, u k * w k`. -/
noncomputable def ofBundleDualFiberEquiv (x : B) :
    (ofBundle 𝕜 e V).dual.core.Fiber x ≃L[𝕜] (V x →L[𝕜] 𝕜) :=
  (dualFiberEquiv (ofBundle 𝕜 e V) x).trans
    ((ofBundleFiberEquiv e V x).arrowCongr (ContinuousLinearEquiv.refl 𝕜 𝕜))

/-- Explicit dual pairing convention: a dual coordinate vector `w` evaluates on `v : V x` by
pairing the `e`-coordinates of `v` in `trivializationAt F V x` with `w`. -/
@[simp]
theorem ofBundleDualFiberEquiv_apply_apply (x : B) (w : Fin r → 𝕜) (v : V x) :
    ofBundleDualFiberEquiv e V x w v =
      ∑ k, e ((trivializationAt F V x) ⟨x, v⟩).2 k * w k := by
  unfold ofBundleDualFiberEquiv
  refine (congrArg (fun f : V x →L[𝕜] 𝕜 ↦ f v)
    (ContinuousLinearEquiv.trans_apply _ _ w)).trans ?_
  refine (ContinuousLinearEquiv.arrowCongr_apply (ofBundleFiberEquiv e V x)
    (ContinuousLinearEquiv.refl 𝕜 𝕜) ((dualFiberEquiv (ofBundle 𝕜 e V) x) w) v).trans ?_
  refine (ContinuousLinearEquiv.refl_apply 𝕜 _ _).trans ?_
  refine (dualFiberEquiv_apply_apply (ofBundle 𝕜 e V) x w
    ((ofBundleFiberEquiv e V x).symm v)).trans ?_
  exact Finset.sum_congr rfl fun k _ ↦
    congrArg (· k * w k) (ofBundleFiberEquiv_symm_apply e V x v)

/-- Evaluated on a vector `(trivializationAt F V x).symm x u` of the preferred trivialization at
`x`, a dual coordinate vector `w` pairs `e u` with `w`. -/
theorem ofBundleDualFiberEquiv_apply_symm (x : B) (w : Fin r → 𝕜) (u : F) :
    ofBundleDualFiberEquiv e V x w ((trivializationAt F V x).symm x u) =
      ∑ k, e u k * w k := by
  rw [ofBundleDualFiberEquiv_apply_apply,
    (trivializationAt F V x).apply_mk_symm (mem_baseSet_trivializationAt F V x) u]

/-- The `i`th standard basis vector `Pi.single i 1` of the dual core corresponds to the `i`th
coordinate functional `u ↦ e u i` on the preferred trivialization at `x`. -/
theorem ofBundleDualFiberEquiv_single_apply_symm (x : B) (i : Fin r) (u : F) :
    ofBundleDualFiberEquiv e V x (Pi.single i 1) ((trivializationAt F V x).symm x u) =
      e u i :=
  (ofBundleDualFiberEquiv_apply_symm e V x (Pi.single i 1) u).trans
    (by simp [Pi.single_apply])

/-- The dual coordinates of a functional `α : V x →L[𝕜] 𝕜` are its values on the basis vectors
`(trivializationAt F V x).symm x (e.symm (Pi.single i 1))`. -/
@[simp]
theorem ofBundleDualFiberEquiv_symm_apply (x : B) (α : V x →L[𝕜] 𝕜) (i : Fin r) :
    (ofBundleDualFiberEquiv e V x).symm α i =
      α ((trivializationAt F V x).symm x (e.symm (Pi.single i 1))) := by
  unfold ofBundleDualFiberEquiv
  refine (congrArg (fun c : Fin r → 𝕜 ↦ c i)
    (ContinuousLinearEquiv.symm_trans_apply _ _ α)).trans ?_
  refine (dualFiberEquiv_symm_apply (ofBundle 𝕜 e V) x _ i).trans ?_
  refine (congrArg (fun E : (V x →L[𝕜] 𝕜) ≃L[𝕜] ((ofBundle 𝕜 e V).core.Fiber x →L[𝕜] 𝕜) ↦
      E α (Pi.single i 1))
    (ContinuousLinearEquiv.arrowCongr_symm (ofBundleFiberEquiv e V x)
      (ContinuousLinearEquiv.refl 𝕜 𝕜))).trans ?_
  refine (ContinuousLinearEquiv.arrowCongr_apply (ofBundleFiberEquiv e V x).symm
    (ContinuousLinearEquiv.refl 𝕜 𝕜).symm α (Pi.single i 1)).trans ?_
  have hrefl : ((ContinuousLinearEquiv.refl 𝕜 𝕜).symm
      (α ((ofBundleFiberEquiv e V x).symm.symm (Pi.single i 1)))) =
      α ((ofBundleFiberEquiv e V x).symm.symm (Pi.single i 1)) := by simp
  refine hrefl.trans ?_
  exact congrArg α
    ((congrFun (congrArg DFunLike.coe
        (ContinuousLinearEquiv.symm_symm (ofBundleFiberEquiv e V x))) (Pi.single i 1)).trans
      (ofBundleFiberEquiv_apply e V x (Pi.single i 1)))

/-- In the preferred Hom-bundle chart at `a`, `ofBundleDualFiberEquiv` reads a dual-core
coordinate vector through the constant continuous linear equivalence
`w ↦ (ContinuousLinearEquiv.piRing.symm w) ∘L e`. -/
theorem ofBundleDualFiberEquiv_inCoordinates (a : B) {x : B}
    (hx : x ∈ (trivializationAt F V a).baseSet) (w : Fin r → 𝕜) :
    ContinuousLinearMap.inCoordinates F V 𝕜 (Trivial B 𝕜) a x a x
        (ofBundleDualFiberEquiv e V x w) =
      ((ContinuousLinearEquiv.piRing (𝕜 := 𝕜) (E := 𝕜) (Fin r)).symm
        (((ofBundle 𝕜 e V).dual.core.localTriv a ⟨x, w⟩).2)).comp e.toContinuousLinearMap := by
  have hx' : x ∈ (ofBundle 𝕜 e V).core.baseSet a := (baseSet_ofBundle e V a).symm ▸ hx
  have hdual := congrArg (·.comp e.toContinuousLinearMap)
    (dualFiberEquiv_inCoordinates (ofBundle 𝕜 e V) a x hx' w)
  refine ContinuousLinearMap.ext fun u ↦ ?_
  have hin := congrArg (fun f : F →L[𝕜] 𝕜 ↦ f u) hdual
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inCoordinates,
    ContinuousLinearEquiv.coe_coe, (ofBundle 𝕜 e V).trivializationAt_core] at hin
  let v₀ : (ofBundle 𝕜 e V).core.Fiber x :=
    ((ofBundle 𝕜 e V).core.localTriv a).symmL 𝕜 x (e u)
  have htriv_snd : (trivializationAt F V a ⟨x, ofBundleFiberEquiv e V x v₀⟩).2 = u := by
    refine (trivializationAt_ofBundleFiberEquiv_snd e V a hx v₀).trans ?_
    have hv₀ : (((ofBundle 𝕜 e V).core.localTriv a) ⟨x, v₀⟩).2 = e u := by
      dsimp only [v₀]
      rw [((ofBundle 𝕜 e V).core.localTriv a).symmL_apply hx']
      exact congrArg Prod.snd (((ofBundle 𝕜 e V).core.localTriv a).apply_mk_symm hx' (e u))
    rw [hv₀, e.symm_apply_apply]
  have hfib : ofBundleFiberEquiv e V x v₀ = (trivializationAt F V a).symmL 𝕜 x u := by
    rw [(trivializationAt F V a).symmL_apply hx, ← htriv_snd]
    exact ((trivializationAt F V a).symm_apply_apply_mk hx (ofBundleFiberEquiv e V x v₀)).symm
  refine (congrArg (fun g : 𝕜 →L[𝕜] 𝕜 ↦ g _)
    (Trivial.continuousLinearMapAt_trivialization 𝕜 B 𝕜 x)).trans ?_
  rw [ContinuousLinearMap.id_apply]
  refine (congrArg (ofBundleDualFiberEquiv e V x w) hfib.symm).trans ?_
  have hpair : ofBundleDualFiberEquiv e V x w (ofBundleFiberEquiv e V x v₀) =
      dualFiberEquiv (ofBundle 𝕜 e V) x w v₀ := by
    unfold ofBundleDualFiberEquiv
    refine (congrArg (fun f : V x →L[𝕜] 𝕜 ↦ f (ofBundleFiberEquiv e V x v₀))
      (ContinuousLinearEquiv.trans_apply _ _ w)).trans ?_
    refine (ContinuousLinearEquiv.arrowCongr_apply (ofBundleFiberEquiv e V x)
      (ContinuousLinearEquiv.refl 𝕜 𝕜) ((dualFiberEquiv (ofBundle 𝕜 e V) x) w)
      (ofBundleFiberEquiv e V x v₀)).trans ?_
    refine (ContinuousLinearEquiv.refl_apply 𝕜 _ _).trans ?_
    exact congrArg (dualFiberEquiv (ofBundle 𝕜 e V) x w)
      ((ofBundleFiberEquiv e V x).symm_apply_apply v₀)
  refine hpair.trans ?_
  refine (congrArg (fun g : 𝕜 →L[𝕜] 𝕜 ↦ g _)
    (Trivial.continuousLinearMapAt_trivialization 𝕜 B 𝕜 x)).symm.trans ?_
  exact hin

/-- Near any `p₀`, reading `ofBundleDualFiberEquiv` in the Hom-bundle chart at `p₀.proj`
eventually agrees with a fixed continuous linear equivalence applied to the dual core chart at
`p₀.proj`. -/
theorem eventuallyEq_inCoordinates_ofBundleDualFiberEquiv
    (p₀ : (ofBundle 𝕜 e V).dual.core.TotalSpace) :
    (fun q : (ofBundle 𝕜 e V).dual.core.TotalSpace ↦
        ContinuousLinearMap.inCoordinates F V 𝕜 (Trivial B 𝕜) p₀.proj q.proj p₀.proj q.proj
          (ofBundleDualFiberEquiv e V q.proj q.snd)) =ᶠ[nhds p₀]
      fun q ↦
        ((ContinuousLinearEquiv.piRing (𝕜 := 𝕜) (E := 𝕜) (Fin r)).symm.trans
          (e.symm.arrowCongr (ContinuousLinearEquiv.refl 𝕜 𝕜))).toContinuousLinearMap
          (((ofBundle 𝕜 e V).dual.core.localTriv p₀.proj q).2) := by
  filter_upwards [(ofBundle 𝕜 e V).dual.localTriv_source_mem_nhds p₀] with q hq
  exact (ofBundleDualFiberEquiv_inCoordinates e V p₀.proj
    ((baseSet_ofBundle e V p₀.proj) ▸
      ((ofBundle 𝕜 e V).dual.core.mem_localTriv_source p₀.proj q).1 hq) q.snd).trans
    (ContinuousLinearEquiv.piRing_symm_trans_arrowCongr_apply e _).symm

/-- Reading dual-core coordinates as functionals on `V` is continuous on total spaces. -/
theorem continuous_ofBundleDualFiberEquiv :
    Continuous fun p : (ofBundle 𝕜 e V).dual.core.TotalSpace ↦
      TotalSpace.mk' (F →L[𝕜] 𝕜) (E := fun x ↦ V x →L[𝕜] 𝕜) p.proj
        (ofBundleDualFiberEquiv e V p.proj p.snd) := by
  refine continuous_iff_continuousAt.2 fun p ↦ ?_
  rw [continuousAt_hom_bundle]
  refine ⟨(ofBundle 𝕜 e V).dual.core.continuous_proj.continuousAt, ?_⟩
  let L : (Fin r → 𝕜) →L[𝕜] (F →L[𝕜] 𝕜) :=
    ((ContinuousLinearEquiv.piRing (𝕜 := 𝕜) (E := 𝕜) (Fin r)).symm.trans
      (e.symm.arrowCongr (ContinuousLinearEquiv.refl 𝕜 𝕜))).toContinuousLinearMap
  exact (L.continuous.continuousAt.comp
    ((ofBundle 𝕜 e V).dual.continuousAt_localTriv_self_snd p)).congr_of_eventuallyEq
    (eventuallyEq_inCoordinates_ofBundleDualFiberEquiv e V p)

/-- The reconstructed total space of `(ofBundle 𝕜 e V).dual` is homeomorphic to Mathlib's dual
bundle `fun x ↦ V x →L[𝕜] 𝕜`, over the identity of the base and by `ofBundleDualFiberEquiv` on
each fibre. -/
noncomputable def ofBundleDualTotalSpaceHomeomorph :
    (ofBundle 𝕜 e V).dual.core.TotalSpace ≃ₜ
      TotalSpace (F →L[𝕜] 𝕜) (fun x ↦ V x →L[𝕜] 𝕜) :=
  bundleHomeomorph (𝕜 := 𝕜) (ofBundleDualFiberEquiv e V)
    (continuous_ofBundleDualFiberEquiv e V)

@[simp]
theorem ofBundleDualTotalSpaceHomeomorph_apply
    (p : (ofBundle 𝕜 e V).dual.core.TotalSpace) :
    ofBundleDualTotalSpaceHomeomorph e V p =
      ⟨p.proj, ofBundleDualFiberEquiv e V p.proj p.snd⟩ :=
  bundleHomeomorph_apply _ _ p

@[simp]
theorem ofBundleDualTotalSpaceHomeomorph_symm_apply
    (p : TotalSpace (F →L[𝕜] 𝕜) (fun x ↦ V x →L[𝕜] 𝕜)) :
    (ofBundleDualTotalSpaceHomeomorph e V).symm p =
      ⟨p.proj, (ofBundleDualFiberEquiv e V p.proj).symm p.snd⟩ :=
  bundleHomeomorph_symm_apply _ _ p

end DualBundle

section DualChange

variable [CompleteSpace 𝕜] {r₁ r₂ : ℕ} (e₁ : F ≃L[𝕜] (Fin r₁ → 𝕜)) (e₂ : F ≃L[𝕜] (Fin r₂ → 𝕜))
  (V : B → Type*) [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- Composing the dual change-of-coordinates maps `e₁ ↦ e₂` and `e₂ ↦ e₁` yields the identity
morphism on `(ofBundle 𝕜 e₂ V).dual`. -/
theorem dualMap_changeIso_comp :
    (dualMap (ofBundleChangeIso e₁ e₂ V).hom) ≫
        (dualMap (ofBundleChangeIso e₂ e₁ V).hom) =
      𝟙 (ofBundle 𝕜 e₂ V).dual := by
  rw [← ofBundleChangeIso_inv e₂ e₁ V]
  exact ((dualFunctor 𝕜 B).mapIso (ofBundleChangeIso e₂ e₁ V).op).inv_hom_id

end DualChange

section DualChangeBundle

variable [CompleteSpace 𝕜] {r₁ r₂ : ℕ} (e₁ : F ≃L[𝕜] (Fin r₁ → 𝕜)) (e₂ : F ≃L[𝕜] (Fin r₂ → 𝕜))
  (V : B → Type*) [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- Changing the coordinate equivalence acts contravariantly on the dual core and commutes with the
identification `ofBundleDualFiberEquiv` to `V x →L[𝕜] 𝕜`. -/
theorem ofBundleDualFiberEquiv_dualMap_changeIso (x : B) (w : Fin r₁ → 𝕜) :
    ofBundleDualFiberEquiv e₂ V x
        ((dualMap (ofBundleChangeIso e₂ e₁ V).hom).fiberMap x w) =
      ofBundleDualFiberEquiv e₁ V x w := by
  ext v
  unfold ofBundleDualFiberEquiv
  refine (congrArg (fun f : V x →L[𝕜] 𝕜 ↦ f v)
    (ContinuousLinearEquiv.trans_apply _ _ _)).trans ?_
  refine (ContinuousLinearEquiv.arrowCongr_apply (ofBundleFiberEquiv e₂ V x)
    (ContinuousLinearEquiv.refl 𝕜 𝕜) _ v).trans ?_
  refine (ContinuousLinearEquiv.refl_apply 𝕜 _ _).trans ?_
  have hdual : dualFiberEquiv (ofBundle 𝕜 e₂ V) x
        ((dualMap (ofBundleChangeIso e₂ e₁ V).hom).fiberMap x w)
        ((ofBundleFiberEquiv e₂ V x).symm v) =
      dualFiberEquiv (ofBundle 𝕜 e₁ V) x w
        ((ofBundleChangeIso e₂ e₁ V).hom.fiberMap x
          ((ofBundleFiberEquiv e₂ V x).symm v)) :=
    congrArg (fun f : (ofBundle 𝕜 e₂ V).core.Fiber x →L[𝕜] 𝕜 ↦
        f ((ofBundleFiberEquiv e₂ V x).symm v))
      (dualFiberEquiv_fiberMap_dualMap (ofBundleChangeIso e₂ e₁ V).hom x w)
  have hfib : (ofBundleChangeIso e₂ e₁ V).hom.fiberMap x ((ofBundleFiberEquiv e₂ V x).symm v) =
      (ofBundleFiberEquiv e₁ V x).symm v :=
    (ofBundleFiberEquiv e₁ V x).eq_symm_apply.mpr <|
      (ofBundleFiberEquiv_changeIso e₂ e₁ V x _).trans
        ((ofBundleFiberEquiv e₂ V x).apply_symm_apply v)
  refine (hdual.trans (congrArg (dualFiberEquiv (ofBundle 𝕜 e₁ V) x w) hfib)).trans ?_
  refine (ContinuousLinearEquiv.refl_apply 𝕜 _ _).symm.trans ?_
  refine (ContinuousLinearEquiv.arrowCongr_apply (ofBundleFiberEquiv e₁ V x)
    (ContinuousLinearEquiv.refl 𝕜 𝕜) _ v).symm.trans ?_
  exact (congrArg (fun f : V x →L[𝕜] 𝕜 ↦ f v)
    (ContinuousLinearEquiv.trans_apply _ _ w)).symm

end DualChangeBundle

end TauCeti.FiniteRankBundleCore
