/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.ExteriorPower
public import TauCeti.Topology.VectorBundle.FiniteRank.Dual
public import TauCeti.Analysis.Normed.Module.Alternating.TopDegree
public import TauCeti.Topology.VectorBundle.ContinuousAlternatingMap
import TauCeti.Topology.Algebra.Module.Determinant

/-!
# Determinant line bundles of finite-rank cores and top-degree alternating forms

For any finite-rank bundle core `A`, its determinant line `A.det = ⋀^{rank A} A` has rank one, so
its coordinate fibre `Fin A.det.rank → 𝕜` is canonically identified with the scalar field `𝕜` by
`TauCeti.FiniteRankBundleCore.detScalarEquiv A` (defined in
`TauCeti.Topology.VectorBundle.FiniteRank.ExteriorPower`).

Over a complete scalar field, the determinant of the dual core `A.dual.det` and the dual of the
determinant line `A.det.dual` both have transitions given by multiplication by the determinant of
the reverse transition of `A` (`coordChange_det_dual`, `coordChange_dual_det`). The canonical
coordinate identification yields the isomorphism `dualDetIsoDetDual A : A.dual.det ≅ A.det.dual`,
recording the convention `det(A*) ≅ (det A)*` under which the unit scalar in `A.dual.det`
corresponds to the unit scalar in `A.det.dual`.

For a vector bundle `V` with model fibre `F` equipped with a coordinate equivalence
`e : F ≃L[𝕜] (Fin r → 𝕜)`, the transition functions of `(ofBundle 𝕜 e V).dual.det` are
multiplication by
`LinearMap.det ((trivializationAt F V j).coordChangeL 𝕜 (trivializationAt F V i) x)`, independent
of `e` (`coordChange_det_dual_ofBundle`). Changing the coordinate equivalence from `e₁` to `e₂`
acts by the functorial image of `ofBundleChangeIso` under `dualFunctor` and `exteriorPower`
(`ofBundleDualDetChangeIso e₁ e₂ V`), scaling scalar coordinates by
`LinearMap.det (e₂.symm.trans e₁).toLinearEquiv.toLinearMap`. When `e = b.equivFunL` comes from
a basis `b : Module.Basis (Fin r) 𝕜 F`, the fibre equivalence `ofBundleDualDetFiberEquiv b V x`
identifies `(ofBundle 𝕜 b.equivFunL V).dual.det` with Mathlib's top-degree alternating form
bundle `fun x ↦ V x [⋀^Fin r]→L[𝕜] 𝕜`, glueing to a homeomorphism of total spaces
`ofBundleDualDetTotalSpaceHomeomorph b V` that commutes strictly with `ofBundleDualDetChangeIso`
and scales by `b₁.det b₂` (`detScalarEquiv_ofBundleDualDetChangeIso_basis_hom`). Under this
top-exterior-power convention, the unit coordinate `fun _ ↦ 1` over `x` corresponds to
`b.continuousDet` pulled back along the preferred trivialization at `x`, and inversely a top-degree
form `ω` is sent to its value on the local frame `i ↦ (trivializationAt F V x).symm x (b i)`.

## References

* John W. Milnor and James D. Stasheff, *Characteristic Classes*, Princeton University Press, 1974,
  §3.
* Daniel Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, §2.2.
-/

public section

open Bundle CategoryTheory FiberBundle Set VectorBundleCore

namespace TauCeti.FiniteRankBundleCore

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]

section DualDet

variable [CompleteSpace 𝕜]

/-- The transitions of `A.dual.det` are multiplication by the determinants of the reverse
transitions of `A`. -/
theorem coordChange_det_dual (A : FiniteRankBundleCore 𝕜 B) (i j x : B) :
    A.dual.det.core.coordChange i j x =
      (A.core.coordChange j i x).det •
        ContinuousLinearMap.id 𝕜 (Fin A.dual.det.rank → 𝕜) := by
  rw [coordChange_det]
  exact congrArg (· • ContinuousLinearMap.id 𝕜 _)
    ((congrArg ContinuousLinearMap.det (coordChange_dual A i j x)).trans
      (ContinuousLinearMap.det_piTranspose _))

/-- The transitions of `A.det.dual` are multiplication by the determinants of the reverse
transitions of `A`. -/
theorem coordChange_dual_det (A : FiniteRankBundleCore 𝕜 B) (i j x : B) :
    A.det.dual.core.coordChange i j x =
      (A.core.coordChange j i x).det •
        ContinuousLinearMap.id 𝕜 (Fin A.det.dual.rank → 𝕜) := by
  rw [coordChange_dual, coordChange_det, ContinuousLinearMap.piTranspose_smul,
    ContinuousLinearMap.piTranspose_id]
  -- `A.det.dual.rank` and `A.det.rank` are definitionally equal, so the identity maps agree.
  rfl

/-- Canonical isomorphism `det(A*) ≅ (det A)*` between the determinant line of the dual core and
the dual of the determinant line, sending the unit scalar coordinate to the unit scalar
coordinate. -/
noncomputable def dualDetIsoDetDual (A : FiniteRankBundleCore 𝕜 B) :
    A.dual.det ≅ A.det.dual :=
  constIso
    (fun i ↦ ((localTriv_baseSet_det A.dual i).trans (localTriv_baseSet_det A i).symm).le)
    ((detScalarEquiv A.dual).trans (detScalarEquiv A).symm) fun i j x _ _ ↦ by
      rw [coordChange_det_dual, coordChange_dual_det]
      ext v : 1
      simp only [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply, map_smul]

@[simp]
theorem fiberMap_dualDetIsoDetDual_hom (A : FiniteRankBundleCore 𝕜 B) (x : B) :
    (dualDetIsoDetDual A).hom.fiberMap x =
      ((detScalarEquiv A.dual).trans (detScalarEquiv A).symm).toContinuousLinearMap :=
  fiberMap_constIso_hom _ _ _ x

@[simp]
theorem fiberMap_dualDetIsoDetDual_inv (A : FiniteRankBundleCore 𝕜 B) (x : B) :
    (dualDetIsoDetDual A).inv.fiberMap x =
      ((detScalarEquiv A).trans (detScalarEquiv A.dual).symm).toContinuousLinearMap :=
  fiberMap_constIso_inv _ _ _ x

theorem detScalarEquiv_dualDetIsoDetDual_hom (A : FiniteRankBundleCore 𝕜 B) (x : B)
    (v : Fin A.dual.det.rank → 𝕜) :
    detScalarEquiv A ((dualDetIsoDetDual A).hom.fiberMap x v) = detScalarEquiv A.dual v := by
  have h : (dualDetIsoDetDual A).hom.fiberMap x v =
      (detScalarEquiv A).symm (detScalarEquiv A.dual v) :=
    congrFun (congrArg DFunLike.coe (fiberMap_dualDetIsoDetDual_hom A x)) v
  exact (congrArg (detScalarEquiv A) h).trans ((detScalarEquiv A).apply_symm_apply _)

theorem detScalarEquiv_dualDetIsoDetDual_inv (A : FiniteRankBundleCore 𝕜 B) (x : B)
    (v : Fin A.det.dual.rank → 𝕜) :
    detScalarEquiv A.dual ((dualDetIsoDetDual A).inv.fiberMap x v) = detScalarEquiv A v := by
  have h : (dualDetIsoDetDual A).inv.fiberMap x v =
      (detScalarEquiv A.dual).symm (detScalarEquiv A v) :=
    congrFun (congrArg DFunLike.coe (fiberMap_dualDetIsoDetDual_inv A x)) v
  exact (congrArg (detScalarEquiv A.dual) h).trans ((detScalarEquiv A.dual).apply_symm_apply _)

end DualDet

section OfBundleDualDet

variable [CompleteSpace 𝕜] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The transition of `(ofBundle 𝕜 e V).dual.det` from chart `i` to chart `j` is scalar
multiplication by the determinant of the reverse transition of `V` from `j` to `i`, independent of
the coordinate equivalence `e`. -/
theorem coordChange_det_dual_ofBundle {r : ℕ} (e : F ≃L[𝕜] (Fin r → 𝕜)) (V : B → Type*)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
    [FiberBundle F V] [VectorBundle 𝕜 F V] (i j x : B) :
    (ofBundle 𝕜 e V).dual.det.core.coordChange i j x =
      LinearMap.det (((trivializationAt F V j).coordChangeL 𝕜
          (trivializationAt F V i) x : F →L[𝕜] F) : F →ₗ[𝕜] F) •
        ContinuousLinearMap.id 𝕜 (Fin (ofBundle 𝕜 e V).dual.det.rank → 𝕜) := by
  rw [coordChange_det_dual, coordChange_ofBundle]
  congr 1
  have hconj : ((e.toContinuousLinearMap.comp
      (((trivializationAt F V j).coordChangeL 𝕜 (trivializationAt F V i) x : F →L[𝕜] F).comp
        e.symm.toContinuousLinearMap) : (Fin r → 𝕜) →L[𝕜] (Fin r → 𝕜)) :
        (Fin r → 𝕜) →ₗ[𝕜] (Fin r → 𝕜)) =
      e.toLinearEquiv.conj
        (((trivializationAt F V j).coordChangeL 𝕜 (trivializationAt F V i) x : F →L[𝕜] F) :
          F →ₗ[𝕜] F) := by
    ext v k
    simp [LinearEquiv.conj_apply]
  rw [ContinuousLinearMap.det, hconj]
  exact LinearMap.det_conj _ e.toLinearEquiv

section TopFormBundle

variable {r : ℕ} (b : Module.Basis (Fin r) 𝕜 F) (V : B → Type*)
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- On the fibre over `x`, identify the determinant line of `(ofBundle 𝕜 b.equivFunL V).dual` with
the line of top-degree continuous alternating forms `V x [⋀^Fin r]→L[𝕜] 𝕜`: a scalar coordinate
`c` maps to `c` times `b.continuousDet` pulled back along `trivializationAt F V x`. -/
noncomputable def ofBundleDualDetFiberEquiv (x : B) :
    (ofBundle 𝕜 b.equivFunL V).dual.det.core.Fiber x ≃L[𝕜] (V x [⋀^Fin r]→L[𝕜] 𝕜) :=
  (detScalarEquiv (ofBundle 𝕜 b.equivFunL V).dual).trans
    (b.topFormEquiv.symm.trans
      (VectorBundle.continuousLinearEquivAt 𝕜 F V x).symm.continuousAlternatingMapCongrLeft)

/-- Explicit evaluation formula for `ofBundleDualDetFiberEquiv` on an `r`-tuple of vectors in
`V x`. -/
@[simp]
theorem ofBundleDualDetFiberEquiv_apply_apply (x : B)
    (v : Fin (ofBundle 𝕜 b.equivFunL V).dual.det.rank → 𝕜) (u : Fin r → V x) :
    ofBundleDualDetFiberEquiv b V x v u =
      detScalarEquiv (ofBundle 𝕜 b.equivFunL V).dual v *
        b.det (fun i ↦ (trivializationAt F V x ⟨x, u i⟩).2) := by
  refine (congrFun (congrArg DFunLike.coe
    (ContinuousLinearEquiv.trans_apply (detScalarEquiv (ofBundle 𝕜 b.equivFunL V).dual) _ v))
    u).trans ?_
  rw [ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.continuousAlternatingMapCongrLeft_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply]
  exact (b.topFormEquiv_symm_apply _ _).trans <|
    congrArg (detScalarEquiv (ofBundle 𝕜 b.equivFunL V).dual v * ·) <|
      congrArg b.det <| funext fun i ↦ by simp [VectorBundle.continuousLinearEquivAt]

/-- Explicit top-exterior-power formula on fibres: `ofBundleDualDetFiberEquiv b V x v` scales the
pullback of `b.continuousDet` along `(trivializationAt F V x).continuousLinearMapAt 𝕜 x` by
`detScalarEquiv _ v`. -/
theorem ofBundleDualDetFiberEquiv_apply (x : B)
    (v : Fin (ofBundle 𝕜 b.equivFunL V).dual.det.rank → 𝕜) :
    ofBundleDualDetFiberEquiv b V x v =
      detScalarEquiv (ofBundle 𝕜 b.equivFunL V).dual v •
        b.continuousDet.compContinuousLinearMap
          ((trivializationAt F V x).continuousLinearMapAt 𝕜 x) := by
  ext u
  simp only [ofBundleDualDetFiberEquiv_apply_apply, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, Module.Basis.continuousDet_apply,
    smul_eq_mul, Function.comp_def,
    (trivializationAt F V x).continuousLinearMapAt_apply_of_mem (R := 𝕜)
      (mem_baseSet_trivializationAt F V x)]

/-- Under `ofBundleDualDetFiberEquiv`, the unit coordinate `fun _ ↦ 1` corresponds to the
determinant form `b.continuousDet` pulled back along `trivializationAt F V x`. -/
theorem ofBundleDualDetFiberEquiv_const_one (x : B) :
    ofBundleDualDetFiberEquiv b V x (fun _ ↦ 1) =
      b.continuousDet.compContinuousLinearMap
        ((trivializationAt F V x).continuousLinearMapAt 𝕜 x) := by
  rw [ofBundleDualDetFiberEquiv_apply, detScalarEquiv_const, one_smul]

/-- Inversely, `ofBundleDualDetFiberEquiv` sends a top-degree alternating form `ω` on `V x` to
the constant coordinate given by evaluating `ω` on the preferred frame
`k ↦ (trivializationAt F V x).symm x (b k)`. -/
@[simp]
theorem ofBundleDualDetFiberEquiv_symm_apply (x : B) (ω : V x [⋀^Fin r]→L[𝕜] 𝕜)
    (i : Fin (ofBundle 𝕜 b.equivFunL V).dual.det.rank) :
    (ofBundleDualDetFiberEquiv b V x).symm ω i =
      ω (fun k ↦ (trivializationAt F V x).symm x (b k)) := by
  unfold ofBundleDualDetFiberEquiv
  refine (congrArg (fun v : Fin (ofBundle 𝕜 b.equivFunL V).dual.det.rank → 𝕜 ↦ v i)
    (ContinuousLinearEquiv.symm_trans_apply _ _ ω)).trans ?_
  refine (detScalarEquiv_symm_apply (ofBundle 𝕜 b.equivFunL V).dual _ i).trans ?_
  rw [ContinuousLinearEquiv.symm_trans_apply, ContinuousLinearEquiv.symm_symm,
    Module.Basis.topFormEquiv_apply]
  have hcongr :
      (VectorBundle.continuousLinearEquivAt 𝕜 F V x).symm.continuousAlternatingMapCongrLeft.symm ω =
        ω.compContinuousLinearMap
          ((VectorBundle.continuousLinearEquivAt 𝕜 F V x).symm : F →L[𝕜] V x) := by
    rw [ContinuousLinearEquiv.symm_apply_eq]
    ext u
    simp [ContinuousLinearEquiv.continuousAlternatingMapCongrLeft_apply, Function.comp_def,
      (trivializationAt F V x).symm_apply_apply_mk (mem_baseSet_trivializationAt F V x)]
  rw [hcongr, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  exact congrArg ω <| funext fun k ↦
    (congrFun ((trivializationAt F V x).symm_continuousLinearEquivAt_eq (R := 𝕜)
      (mem_baseSet_trivializationAt F V x)) (b k)).trans
      ((trivializationAt F V x).symmL_apply (mem_baseSet_trivializationAt F V x) (b k))

/-- On the base set of `trivializationAt F V a`, `ofBundleDualDetFiberEquiv` intertwines the core
chart at `a` with the preferred alternating-bundle chart at `a` via the constant equivalence
`b.topFormEquiv.symm ∘ detScalarEquiv`. -/
theorem trivializationAt_ofBundleDualDetFiberEquiv_snd (a : B) {x : B}
    (hx : x ∈ (trivializationAt F V a).baseSet)
    (v : Fin (ofBundle 𝕜 b.equivFunL V).dual.det.rank → 𝕜) :
    (trivializationAt (F [⋀^Fin r]→L[𝕜] 𝕜) (fun y ↦ V y [⋀^Fin r]→L[𝕜] 𝕜) a
        ⟨x, ofBundleDualDetFiberEquiv b V x v⟩).2 =
      b.topFormEquiv.symm (detScalarEquiv (ofBundle 𝕜 b.equivFunL V).dual
        (((ofBundle 𝕜 b.equivFunL V).dual.det.core.localTriv a ⟨x, v⟩).2)) := by
  let T : F →L[𝕜] F := (trivializationAt F V a).coordChangeL 𝕜 (trivializationAt F V x) x
  have htriv :
      detScalarEquiv (ofBundle 𝕜 b.equivFunL V).dual
        (((ofBundle 𝕜 b.equivFunL V).dual.det.core.localTriv a ⟨x, v⟩).2) =
      LinearMap.det (T : F →ₗ[𝕜] F) * detScalarEquiv (ofBundle 𝕜 b.equivFunL V).dual v := by
    have h1 : (((ofBundle 𝕜 b.equivFunL V).dual.det.core.localTriv a ⟨x, v⟩).2 :
        Fin (ofBundle 𝕜 b.equivFunL V).dual.det.rank → 𝕜) =
        LinearMap.det (T : F →ₗ[𝕜] F) • v := by
      rw [VectorBundleCore.localTriv_apply]; dsimp only
      rw [(ofBundle 𝕜 b.equivFunL V).dual.det.indexAt_eq, coordChange_det_dual_ofBundle]
      simp only [smul_apply, ContinuousLinearMap.id_apply, T]
    rw [h1, map_smul, smul_eq_mul]
  rw [FiberBundle.trivializationAt_continuousAlternatingMap_apply_snd, htriv]
  ext u
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ofBundleDualDetFiberEquiv_apply_apply, Module.Basis.topFormEquiv_symm_apply,
    Function.comp_apply]
  have hfun : (fun i ↦ (trivializationAt F V x ⟨x, (trivializationAt F V a).symmL 𝕜 x (u i)⟩).2) =
      (T : F →ₗ[𝕜] F) ∘ u := funext fun i ↦ by
    rw [(trivializationAt F V a).symmL_apply hx]
    exact congrArg Prod.snd ((trivializationAt F V a).mk_coordChangeL (R := 𝕜)
      (trivializationAt F V x) ⟨hx, mem_baseSet_trivializationAt F V x⟩ (u i)).symm
  rw [hfun, b.det_comp]; ring

/-- Near any `p₀`, reading `ofBundleDualDetFiberEquiv` in the preferred alternating-bundle chart
at `p₀.proj` eventually agrees with the constant equivalence `b.topFormEquiv.symm ∘ detScalarEquiv`
applied to the determinant core chart at `p₀.proj`. -/
theorem eventuallyEq_trivializationAt_ofBundleDualDetFiberEquiv_snd
    (p₀ : (ofBundle 𝕜 b.equivFunL V).dual.det.core.TotalSpace) :
    (fun q : (ofBundle 𝕜 b.equivFunL V).dual.det.core.TotalSpace ↦
        (trivializationAt (F [⋀^Fin r]→L[𝕜] 𝕜) (fun y ↦ V y [⋀^Fin r]→L[𝕜] 𝕜) p₀.proj
          ⟨q.proj, ofBundleDualDetFiberEquiv b V q.proj q.snd⟩).2) =ᶠ[nhds p₀]
      fun q ↦
        ((detScalarEquiv (ofBundle 𝕜 b.equivFunL V).dual).trans b.topFormEquiv.symm)
          (((ofBundle 𝕜 b.equivFunL V).dual.det.core.localTriv p₀.proj q).2) := by
  have hbase (i : B) : (ofBundle 𝕜 b.equivFunL V).dual.det.core.baseSet i =
      (trivializationAt F V i).baseSet :=
    (localTriv_baseSet_det (ofBundle 𝕜 b.equivFunL V).dual i).trans
      (baseSet_ofBundle b.equivFunL V i)
  have hnhds := (ofBundle 𝕜 b.equivFunL V).dual.det.core.localTrivAt_source_mem_nhds p₀
  rw [VectorBundleCore.localTrivAt, (ofBundle 𝕜 b.equivFunL V).dual.det.indexAt_eq] at hnhds
  filter_upwards [hnhds] with q hq
  exact trivializationAt_ofBundleDualDetFiberEquiv_snd b V p₀.proj
    ((hbase p₀.proj) ▸
      ((ofBundle 𝕜 b.equivFunL V).dual.det.core.mem_localTriv_source p₀.proj q).1 hq) q.snd

/-- Reading determinant-core coordinates as top-degree alternating forms on `V` is continuous on
total spaces. -/
theorem continuous_ofBundleDualDetFiberEquiv :
    Continuous fun p : (ofBundle 𝕜 b.equivFunL V).dual.det.core.TotalSpace ↦
      TotalSpace.mk' (F [⋀^Fin r]→L[𝕜] 𝕜) (E := fun x ↦ V x [⋀^Fin r]→L[𝕜] 𝕜)
        p.proj (ofBundleDualDetFiberEquiv b V p.proj p.snd) := by
  refine continuous_iff_continuousAt.2 fun p ↦ ?_
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨(ofBundle 𝕜 b.equivFunL V).dual.det.core.continuous_proj.continuousAt, ?_⟩
  let L := (detScalarEquiv (ofBundle 𝕜 b.equivFunL V).dual).trans b.topFormEquiv.symm
  have hc : ContinuousAt
      (fun q : (ofBundle 𝕜 b.equivFunL V).dual.det.core.TotalSpace ↦
        ((ofBundle 𝕜 b.equivFunL V).dual.det.core.localTriv p.proj q).2) p := by
    simpa only [VectorBundleCore.localTrivAt,
      (ofBundle 𝕜 b.equivFunL V).dual.det.indexAt_eq] using
      (ofBundle 𝕜 b.equivFunL V).dual.det.core.continuousAt_localTrivAt_snd p
  exact (L.continuous.continuousAt.comp hc).congr_of_eventuallyEq
    (eventuallyEq_trivializationAt_ofBundleDualDetFiberEquiv_snd b V p)

/-- The reconstructed total space of `(ofBundle 𝕜 b.equivFunL V).dual.det` is homeomorphic to
Mathlib's top-degree alternating form bundle `fun x ↦ V x [⋀^Fin r]→L[𝕜] 𝕜`, over the identity of
the base and by `ofBundleDualDetFiberEquiv b V x` on each fibre. -/
noncomputable def ofBundleDualDetTotalSpaceHomeomorph :
    (ofBundle 𝕜 b.equivFunL V).dual.det.core.TotalSpace ≃ₜ
      TotalSpace (F [⋀^Fin r]→L[𝕜] 𝕜) (fun x ↦ V x [⋀^Fin r]→L[𝕜] 𝕜) :=
  bundleHomeomorph (𝕜 := 𝕜) (ofBundleDualDetFiberEquiv b V)
    (continuous_ofBundleDualDetFiberEquiv b V)

@[simp]
theorem ofBundleDualDetTotalSpaceHomeomorph_apply
    (p : (ofBundle 𝕜 b.equivFunL V).dual.det.core.TotalSpace) :
    ofBundleDualDetTotalSpaceHomeomorph b V p =
      ⟨p.proj, ofBundleDualDetFiberEquiv b V p.proj p.snd⟩ :=
  bundleHomeomorph_apply _ _ p

@[simp]
theorem ofBundleDualDetTotalSpaceHomeomorph_symm_apply
    (p : TotalSpace (F [⋀^Fin r]→L[𝕜] 𝕜) (fun x ↦ V x [⋀^Fin r]→L[𝕜] 𝕜)) :
    (ofBundleDualDetTotalSpaceHomeomorph b V).symm p =
      ⟨p.proj, (ofBundleDualDetFiberEquiv b V p.proj).symm p.snd⟩ :=
  bundleHomeomorph_symm_apply _ _ p

end TopFormBundle

section EquivChange

variable {r : ℕ} (e₁ e₂ : F ≃L[𝕜] (Fin r → 𝕜)) (V : B → Type*)
  [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- Changing the coordinate equivalence from `e₁` to `e₂` induces a canonical isomorphism between
the determinant line bundles `(ofBundle 𝕜 e₁ V).dual.det` and `(ofBundle 𝕜 e₂ V).dual.det`,
defined functorially from `ofBundleChangeIso` via `dualFunctor` and `exteriorPower`. -/
noncomputable def ofBundleDualDetChangeIso :
    (ofBundle 𝕜 e₁ V).dual.det ≅ (ofBundle 𝕜 e₂ V).dual.det :=
  eqToIso (det_def (ofBundle 𝕜 e₁ V).dual) ≪≫
    (exteriorPower 𝕜 B r).mapIso
      ((dualFunctor 𝕜 B).mapIso (ofBundleChangeIso e₂ e₁ V).op) ≪≫
    (eqToIso (det_def (ofBundle 𝕜 e₂ V).dual)).symm

/-- The coordinate-change isomorphism `ofBundleDualDetChangeIso` has forward morphism given by the
functorial image of `ofBundleChangeIso e₂ e₁ V` under `dualMap` and `exteriorPower`. -/
theorem ofBundleDualDetChangeIso_hom_eq_exteriorPower_dualMap :
    (ofBundleDualDetChangeIso e₁ e₂ V).hom =
      (eqToIso (det_def (ofBundle 𝕜 e₁ V).dual)).hom ≫
        (exteriorPower 𝕜 B r).map
          (dualMap (ofBundleChangeIso e₂ e₁ V).hom) ≫
        (eqToIso (det_def (ofBundle 𝕜 e₂ V).dual)).inv :=
  congrArg ((eqToIso (det_def (ofBundle 𝕜 e₁ V).dual)).hom ≫ ·) <|
    Iso.trans_hom ((exteriorPower 𝕜 B r).mapIso
      ((dualFunctor 𝕜 B).mapIso (ofBundleChangeIso e₂ e₁ V).op))
      (eqToIso (det_def (ofBundle 𝕜 e₂ V).dual)).symm

/-- Reversing the coordinate equivalences `e₁` and `e₂` gives the inverse isomorphism of
`ofBundleDualDetChangeIso`. -/
theorem ofBundleDualDetChangeIso_symm :
    (ofBundleDualDetChangeIso e₁ e₂ V).symm = ofBundleDualDetChangeIso e₂ e₁ V := by
  have hop : (ofBundleChangeIso e₂ e₁ V).op.symm = (ofBundleChangeIso e₁ e₂ V).op :=
    Iso.ext <| Quiver.Hom.unop_inj (ofBundleChangeIso_inv e₂ e₁ V)
  have hmid :
      ((exteriorPower 𝕜 B r).mapIso
          ((dualFunctor 𝕜 B).mapIso (ofBundleChangeIso e₂ e₁ V).op)).symm =
        (exteriorPower 𝕜 B r).mapIso
          ((dualFunctor 𝕜 B).mapIso (ofBundleChangeIso e₁ e₂ V).op) :=
    (Functor.mapIso_symm _ _).symm.trans <|
      congrArg (exteriorPower 𝕜 B r).mapIso <|
        (Functor.mapIso_symm _ _).symm.trans (congrArg (dualFunctor 𝕜 B).mapIso hop)
  calc (ofBundleDualDetChangeIso e₁ e₂ V).symm
      = ((exteriorPower 𝕜 B r).mapIso
            ((dualFunctor 𝕜 B).mapIso (ofBundleChangeIso e₂ e₁ V).op) ≪≫
            (eqToIso (det_def (ofBundle 𝕜 e₂ V).dual)).symm).symm ≪≫
          (eqToIso (det_def (ofBundle 𝕜 e₁ V).dual)).symm :=
        Iso.trans_symm _ _
    _ = ((eqToIso (det_def (ofBundle 𝕜 e₂ V).dual)).symm.symm ≪≫
            ((exteriorPower 𝕜 B r).mapIso
              ((dualFunctor 𝕜 B).mapIso (ofBundleChangeIso e₂ e₁ V).op)).symm) ≪≫
          (eqToIso (det_def (ofBundle 𝕜 e₁ V).dual)).symm :=
        congrArg (· ≪≫ (eqToIso (det_def (ofBundle 𝕜 e₁ V).dual)).symm) (Iso.trans_symm _ _)
    _ = ofBundleDualDetChangeIso e₂ e₁ V := by
        rw [Iso.symm_symm_eq, hmid]
        exact Iso.trans_assoc _ _ _

theorem ofBundleDualDetChangeIso_inv :
    (ofBundleDualDetChangeIso e₁ e₂ V).inv = (ofBundleDualDetChangeIso e₂ e₁ V).hom :=
  congrArg Iso.hom (ofBundleDualDetChangeIso_symm e₁ e₂ V)

@[simp]
theorem detScalarEquiv_ofBundleDualDetChangeIso_hom (x : B)
    (v : Fin (ofBundle 𝕜 e₁ V).dual.det.rank → 𝕜) :
    detScalarEquiv (ofBundle 𝕜 e₂ V).dual
        ((ofBundleDualDetChangeIso e₁ e₂ V).hom.fiberMap x v) =
      LinearMap.det (e₂.symm.trans e₁).toLinearEquiv.toLinearMap *
        detScalarEquiv (ofBundle 𝕜 e₁ V).dual v := by
  rw [ofBundleDualDetChangeIso_hom_eq_exteriorPower_dualMap]
  let c : 𝕜 := LinearMap.det (e₂.symm.trans e₁).toLinearEquiv.toLinearMap
  have h1 : ((dualMap (ofBundleChangeIso e₂ e₁ V).hom).fiberMap x :
        (Fin r → 𝕜) →L[𝕜] (Fin r → 𝕜)) =
      (e₂.symm.trans e₁).toContinuousLinearMap.piTranspose :=
    (fiberMap_dualMap _ x).trans (congrArg ContinuousLinearMap.piTranspose
      (fiberMap_ofBundleChangeIso_hom e₂ e₁ V x))
  have hdet : (e₂.symm.trans e₁).toContinuousLinearMap.piTranspose.det = c := by
    rw [ContinuousLinearMap.det_piTranspose, ContinuousLinearMap.det]
    exact congrArg LinearMap.det (LinearMap.ext fun u ↦ by simp)
  have hmap :
      (((exteriorPower 𝕜 B r).map
          (dualMap (ofBundleChangeIso e₂ e₁ V).hom)).fiberMap x :
        (Fin (r.choose r) → 𝕜) →L[𝕜] (Fin (r.choose r) → 𝕜)) =
      c • ContinuousLinearMap.id 𝕜 (Fin (r.choose r) → 𝕜) :=
    (fiberMap_exteriorPower_map r _ x).trans <|
      (congrArg (ContinuousLinearMap.exteriorPowerCoords r) h1).trans <|
        (ContinuousLinearMap.exteriorPowerCoords_self _).trans <|
          congrArg (· • ContinuousLinearMap.id 𝕜 (Fin (r.choose r) → 𝕜)) hdet
  refine detScalarEquiv_eqToIso_hom_comp_inv (det_def (ofBundle 𝕜 e₁ V).dual)
    (det_def (ofBundle 𝕜 e₂ V).dual) _ x v c fun u j₁ j₂ hj ↦ ?_
  rw [Fin.ext hj]
  exact congrArg (fun S : (Fin (r.choose r) → 𝕜) →L[𝕜] (Fin (r.choose r) → 𝕜) ↦ S u j₂) hmap

@[simp]
theorem detScalarEquiv_ofBundleDualDetChangeIso_inv (x : B)
    (v : Fin (ofBundle 𝕜 e₂ V).dual.det.rank → 𝕜) :
    detScalarEquiv (ofBundle 𝕜 e₁ V).dual
        ((ofBundleDualDetChangeIso e₁ e₂ V).inv.fiberMap x v) =
      LinearMap.det (e₁.symm.trans e₂).toLinearEquiv.toLinearMap *
        detScalarEquiv (ofBundle 𝕜 e₂ V).dual v := by
  rw [ofBundleDualDetChangeIso_inv, detScalarEquiv_ofBundleDualDetChangeIso_hom]

end EquivChange

section BasisChange

variable {r : ℕ} (b₁ b₂ : Module.Basis (Fin r) 𝕜 F) (V : B → Type*)
  [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- Specialization of `detScalarEquiv_ofBundleDualDetChangeIso_hom` to basis equivalences, where
the scaling factor is `b₁.det b₂`. -/
theorem detScalarEquiv_ofBundleDualDetChangeIso_basis_hom (x : B)
    (v : Fin (ofBundle 𝕜 b₁.equivFunL V).dual.det.rank → 𝕜) :
    detScalarEquiv (ofBundle 𝕜 b₂.equivFunL V).dual
        ((ofBundleDualDetChangeIso b₁.equivFunL b₂.equivFunL V).hom.fiberMap x v) =
      b₁.det b₂ * detScalarEquiv (ofBundle 𝕜 b₁.equivFunL V).dual v := by
  rw [detScalarEquiv_ofBundleDualDetChangeIso_hom]
  exact congrArg (· * _) (b₁.det_equivFunL_symm_trans b₂)

/-- Specialization of `detScalarEquiv_ofBundleDualDetChangeIso_inv` to basis equivalences, where
the scaling factor is `b₂.det b₁`. -/
theorem detScalarEquiv_ofBundleDualDetChangeIso_basis_inv (x : B)
    (v : Fin (ofBundle 𝕜 b₂.equivFunL V).dual.det.rank → 𝕜) :
    detScalarEquiv (ofBundle 𝕜 b₁.equivFunL V).dual
        ((ofBundleDualDetChangeIso b₁.equivFunL b₂.equivFunL V).inv.fiberMap x v) =
      b₂.det b₁ * detScalarEquiv (ofBundle 𝕜 b₂.equivFunL V).dual v := by
  rw [ofBundleDualDetChangeIso_inv, detScalarEquiv_ofBundleDualDetChangeIso_basis_hom]

end BasisChange

section BasisChangeTopForm

variable {r : ℕ} (b₁ b₂ : Module.Basis (Fin r) 𝕜 F) (V : B → Type*)
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- Changing the model basis commutes strictly with the top-alternating-form identification
`ofBundleDualDetFiberEquiv`. -/
theorem ofBundleDualDetFiberEquiv_changeIso (x : B)
    (v : Fin (ofBundle 𝕜 b₁.equivFunL V).dual.det.rank → 𝕜) :
    ofBundleDualDetFiberEquiv b₂ V x
        ((ofBundleDualDetChangeIso b₁.equivFunL b₂.equivFunL V).hom.fiberMap x v) =
      ofBundleDualDetFiberEquiv b₁ V x v := by
  ext u
  rw [ofBundleDualDetFiberEquiv_apply_apply, ofBundleDualDetFiberEquiv_apply_apply,
    detScalarEquiv_ofBundleDualDetChangeIso_basis_hom, b₁.det.eq_smul_basis_det b₂]
  simp only [smul_apply, smul_eq_mul, b₂.det_self, mul_one]; ring

end BasisChangeTopForm

end OfBundleDualDet

end TauCeti.FiniteRankBundleCore
