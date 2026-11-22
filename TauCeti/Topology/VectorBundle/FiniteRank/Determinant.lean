/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.ExteriorPower
public import TauCeti.Topology.VectorBundle.FiniteRank.ModelEquiv
public import TauCeti.Analysis.Normed.Module.Alternating.TopDegree
public import TauCeti.Topology.VectorBundle.ContinuousAlternatingMap
import TauCeti.Topology.Algebra.Module.Determinant

/-!
# Determinant line bundles of finite-rank cores and top-degree alternating forms

For any finite-rank bundle core `A`, its determinant line `A.det = ⋀^{rank A} A` has rank one, so
its coordinate fibre `Fin A.det.rank → 𝕜` is canonically identified with the scalar field `𝕜` by
`TauCeti.FiniteRankBundleCore.detScalarEquiv A`.

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
of `e` (`coordChange_ofBundle_dual_det`). When `e = b.equivFunL` comes from a basis
`b : Module.Basis (Fin r) 𝕜 F`, the fibre equivalence `ofBundleDualDetFiberEquiv b V x` identifies
`(ofBundle 𝕜 b.equivFunL V).dual.det` with Mathlib's top-degree alternating form bundle
`fun x ↦ V x [⋀^Fin r]→L[𝕜] 𝕜`, glueing to a homeomorphism of total spaces
`ofBundleDualDetTotalSpaceHomeomorph b V`. Under this top-exterior-power convention, the unit
coordinate `fun _ ↦ 1` over `x` corresponds to `b.continuousDet` pulled back along the preferred
trivialization at `x`, and inversely a top-degree form `ω` is sent to its value on the local frame
`i ↦ (trivializationAt F V x).symm x (b i)`. Changing the basis from `b₁` to `b₂` acts by the
functorial image of `ofBundleChangeIso` under `dualFunctor` and `exteriorPower`
(`ofBundleDualDetChangeIso b₁ b₂ V`), scaling scalar coordinates by `b₁.det b₂` and commuting
strictly with `ofBundleDualDetFiberEquiv`.

## References

* John W. Milnor and James D. Stasheff, *Characteristic Classes*, Princeton University Press, 1974,
  §3.
* Daniel Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, §2.2.
-/

public section

open Bundle CategoryTheory FiberBundle Set VectorBundleCore

namespace TauCeti.FiniteRankBundleCore

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]

section DetScalar

/-- Canonical identification of the rank-one coordinate fibre `Fin A.det.rank → 𝕜` of the
determinant line bundle core with the scalar field `𝕜`. -/
noncomputable def detScalarEquiv (A : FiniteRankBundleCore 𝕜 B) :
    (Fin A.det.rank → 𝕜) ≃L[𝕜] 𝕜 :=
  (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ : Fin 1 ↦ 𝕜) (finCongr A.rank_det)).trans
    (ContinuousLinearEquiv.funUnique (Fin 1) 𝕜 𝕜)

theorem detScalarEquiv_apply (A : FiniteRankBundleCore 𝕜 B) (v : Fin A.det.rank → 𝕜) :
    detScalarEquiv A v = v ⟨0, A.rank_det ▸ Nat.zero_lt_one⟩ := (rfl)

@[simp]
theorem detScalarEquiv_symm_apply (A : FiniteRankBundleCore 𝕜 B) (c : 𝕜) (i : Fin A.det.rank) :
    (detScalarEquiv A).symm c i = c := (rfl)

@[simp]
theorem detScalarEquiv_const (A : FiniteRankBundleCore 𝕜 B) (c : 𝕜) :
    detScalarEquiv A (fun _ ↦ c) = c := (rfl)

/-- Every coordinate vector in the rank-one fibre `Fin A.det.rank → 𝕜` is constant with value
`detScalarEquiv A v`. -/
theorem det_fiber_eq_const (A : FiniteRankBundleCore 𝕜 B) (v : Fin A.det.rank → 𝕜)
    (i : Fin A.det.rank) :
    v i = detScalarEquiv A v :=
  congrArg v (Fin.ext (Nat.lt_one_iff.mp (A.rank_det ▸ i.isLt)))

end DetScalar

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
    (by intro i; exact (localTriv_baseSet_det A.dual i).trans (localTriv_baseSet_det A i).symm)
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
theorem coordChange_ofBundle_dual_det {r : ℕ} (e : F ≃L[𝕜] (Fin r → 𝕜)) (V : B → Type*)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
    [FiberBundle F V] [VectorBundle 𝕜 F V] (i j x : B) :
    (ofBundle 𝕜 e V).dual.det.core.coordChange i j x =
      LinearMap.det (((trivializationAt F V j).coordChangeL 𝕜
          (trivializationAt F V i) x : F →L[𝕜] F) : F →ₗ[𝕜] F) •
        ContinuousLinearMap.id 𝕜 (Fin (ofBundle 𝕜 e V).dual.det.rank → 𝕜) := by
  rw [coordChange_det_dual, coordChange_ofBundle]
  congr 1
  exact LinearMap.det_conj
    (((trivializationAt F V j).coordChangeL 𝕜 (trivializationAt F V i) x : F →L[𝕜] F) : F →ₗ[𝕜] F)
    e.toLinearEquiv

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
        b.det (fun i ↦ (trivializationAt F V x ⟨x, u i⟩).2) :=
  b.topFormEquiv_symm_apply
    (detScalarEquiv (ofBundle 𝕜 b.equivFunL V).dual v)
    (fun i ↦ (trivializationAt F V x ⟨x, u i⟩).2)

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
      rw [(ofBundle 𝕜 b.equivFunL V).dual.det.indexAt_eq, coordChange_ofBundle_dual_det]
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
  filter_upwards [(ofBundle 𝕜 b.equivFunL V).dual.det.localTriv_source_mem_nhds p₀] with q hq
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
  exact (L.continuous.continuousAt.comp
    ((ofBundle 𝕜 b.equivFunL V).dual.det.continuousAt_localTriv_self_snd p)).congr_of_eventuallyEq
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

section BasisChange

variable {r : ℕ} (b₁ b₂ : Module.Basis (Fin r) 𝕜 F) (V : B → Type*)
  [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- Changing the model basis from `b₁` to `b₂` induces a canonical isomorphism between the
determinant line bundles `(ofBundle 𝕜 b₁.equivFunL V).dual.det` and
`(ofBundle 𝕜 b₂.equivFunL V).dual.det`, defined functorially from `ofBundleChangeIso` via
`dualFunctor` and `exteriorPower`. -/
noncomputable def ofBundleDualDetChangeIso :
    (ofBundle 𝕜 b₁.equivFunL V).dual.det ≅ (ofBundle 𝕜 b₂.equivFunL V).dual.det :=
  eqToIso (det_def (ofBundle 𝕜 b₁.equivFunL V).dual) ≪≫
    (exteriorPower 𝕜 B r).mapIso
      ((dualFunctor 𝕜 B).mapIso (ofBundleChangeIso b₂.equivFunL b₁.equivFunL V).op) ≪≫
    (eqToIso (det_def (ofBundle 𝕜 b₂.equivFunL V).dual)).symm

/-- The basis-change isomorphism `ofBundleDualDetChangeIso` has forward morphism given by the
functorial image of `ofBundleChangeIso b₂.equivFunL b₁.equivFunL V` under `dualMap` and
`exteriorPower`. -/
theorem ofBundleDualDetChangeIso_hom_eq_exteriorPower_dualMap :
    (ofBundleDualDetChangeIso b₁ b₂ V).hom =
      (eqToIso (det_def (ofBundle 𝕜 b₁.equivFunL V).dual)).hom ≫
        (exteriorPower 𝕜 B r).map
          (dualMap (ofBundleChangeIso b₂.equivFunL b₁.equivFunL V).hom) ≫
        (eqToIso (det_def (ofBundle 𝕜 b₂.equivFunL V).dual)).inv := by
  simp [ofBundleDualDetChangeIso]
  rfl

theorem ofBundleDualDetChangeIso_inv :
    (ofBundleDualDetChangeIso b₁ b₂ V).inv = (ofBundleDualDetChangeIso b₂ b₁ V).hom := by
  rw [← Category.id_comp (ofBundleDualDetChangeIso b₂ b₁ V).hom,
    ← (ofBundleDualDetChangeIso b₁ b₂ V).inv_hom_id, Category.assoc]
  suffices h : (ofBundleDualDetChangeIso b₁ b₂ V).hom ≫
      (ofBundleDualDetChangeIso b₂ b₁ V).hom = 𝟙 _ by
    rw [h, Category.comp_id]
  have hcancel : ∀ {Y₁ Y₂ : FiniteRankBundleCore 𝕜 B}
      (h₁ : Y₁.det = (exteriorPower 𝕜 B r).obj Y₁)
      (h₂ : Y₂.det = (exteriorPower 𝕜 B r).obj Y₂)
      (f : Y₁ ⟶ Y₂) (g : Y₂ ⟶ Y₁), f ≫ g = 𝟙 Y₁ →
      ((eqToIso h₁).hom ≫ (exteriorPower 𝕜 B r).map f ≫ (eqToIso h₂).inv) ≫
        ((eqToIso h₂).hom ≫ (exteriorPower 𝕜 B r).map g ≫ (eqToIso h₁).inv) = 𝟙 Y₁.det := by
    intro Y₁ Y₂ h₁ h₂ f g hfg
    simp only [Category.assoc]
    rw [← Category.assoc (eqToIso h₂).inv, Iso.inv_hom_id, Category.id_comp,
      ← Category.assoc ((exteriorPower 𝕜 B r).map f), ← CategoryTheory.Functor.map_comp, hfg,
      CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id]
  rw [ofBundleDualDetChangeIso_hom_eq_exteriorPower_dualMap,
    ofBundleDualDetChangeIso_hom_eq_exteriorPower_dualMap]
  exact hcancel (det_def _) (det_def _) _ _ (dualMap_changeIso_comp b₂.equivFunL b₁.equivFunL V)

@[simp]
theorem detScalarEquiv_ofBundleDualDetChangeIso_hom (x : B)
    (v : Fin (ofBundle 𝕜 b₁.equivFunL V).dual.det.rank → 𝕜) :
    detScalarEquiv (ofBundle 𝕜 b₂.equivFunL V).dual
        ((ofBundleDualDetChangeIso b₁ b₂ V).hom.fiberMap x v) =
      b₁.det b₂ * detScalarEquiv (ofBundle 𝕜 b₁.equivFunL V).dual v := by
  have h1 : ((dualMap (ofBundleChangeIso b₂.equivFunL b₁.equivFunL V).hom).fiberMap x :
        (Fin r → 𝕜) →L[𝕜] (Fin r → 𝕜)) =
      (b₂.equivFunL.symm.trans b₁.equivFunL).toContinuousLinearMap.piTranspose :=
    (fiberMap_dualMap _ x).trans (congrArg ContinuousLinearMap.piTranspose
      (fiberMap_ofBundleChangeIso_hom b₂.equivFunL b₁.equivFunL V x))
  have hmap :
      (((exteriorPower 𝕜 B r).map
          (dualMap (ofBundleChangeIso b₂.equivFunL b₁.equivFunL V).hom)).fiberMap x :
        (Fin (r.choose r) → 𝕜) →L[𝕜] (Fin (r.choose r) → 𝕜)) =
      b₁.det b₂ • ContinuousLinearMap.id 𝕜 (Fin (r.choose r) → 𝕜) :=
    (fiberMap_exteriorPower_map r _ x).trans <|
      (congrArg (ContinuousLinearMap.exteriorPowerCoords r) h1).trans <|
        (ContinuousLinearMap.exteriorPowerCoords_self _).trans <|
          congrArg (· • ContinuousLinearMap.id 𝕜 (Fin (r.choose r) → 𝕜))
            ((ContinuousLinearMap.det_piTranspose _).trans (b₁.det_equivFunL_symm_trans b₂))
  have hconj : ∀ {Y₁ Y₂ Z₁ Z₂ : FiniteRankBundleCore 𝕜 B} (h₁ : Y₁ = Z₁) (h₂ : Y₂ = Z₂)
      (g : Z₁ ⟶ Z₂) (w : Fin Y₁.rank → 𝕜) (i₁ : Fin Y₁.rank) (i₂ : Fin Y₂.rank)
      (_ : i₁.val = i₂.val) (c : 𝕜)
      (_ : ∀ u (j : Fin Z₂.rank) (j' : Fin Z₁.rank), j'.val = j.val → g.fiberMap x u j = c * u j'),
      ((eqToIso h₁).hom ≫ g ≫ (eqToIso h₂).inv).fiberMap x w i₂ = c * w i₁ := by
    intro Y₁ Y₂ Z₁ Z₂ h₁ h₂ g w i₁ i₂ hidx c hg
    subst h₁ h₂
    simp only [eqToIso_refl, Iso.refl_hom, Iso.refl_inv, Category.id_comp, Category.comp_id]
    exact hg w i₂ i₁ hidx
  refine (detScalarEquiv_apply _ _).trans ?_
  rw [ofBundleDualDetChangeIso_hom_eq_exteriorPower_dualMap]
  refine (hconj (det_def (ofBundle 𝕜 b₁.equivFunL V).dual)
    (det_def (ofBundle 𝕜 b₂.equivFunL V).dual) _ v
    ⟨0, (ofBundle 𝕜 b₁.equivFunL V).dual.rank_det ▸ Nat.zero_lt_one⟩
    ⟨0, (ofBundle 𝕜 b₂.equivFunL V).dual.rank_det ▸ Nat.zero_lt_one⟩ rfl (b₁.det b₂)
    fun u j j' hjj ↦ ?_).trans ?_
  · rw [Fin.ext hjj]
    exact congrArg (fun S : (Fin (r.choose r) → 𝕜) →L[𝕜] (Fin (r.choose r) → 𝕜) ↦ S u j) hmap
  · exact congrArg (b₁.det b₂ * ·) (detScalarEquiv_apply (ofBundle 𝕜 b₁.equivFunL V).dual v).symm

@[simp]
theorem detScalarEquiv_ofBundleDualDetChangeIso_inv (x : B)
    (v : Fin (ofBundle 𝕜 b₂.equivFunL V).dual.det.rank → 𝕜) :
    detScalarEquiv (ofBundle 𝕜 b₁.equivFunL V).dual
        ((ofBundleDualDetChangeIso b₁ b₂ V).inv.fiberMap x v) =
      b₂.det b₁ * detScalarEquiv (ofBundle 𝕜 b₂.equivFunL V).dual v := by
  rw [ofBundleDualDetChangeIso_inv, detScalarEquiv_ofBundleDualDetChangeIso_hom]

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
        ((ofBundleDualDetChangeIso b₁ b₂ V).hom.fiberMap x v) =
      ofBundleDualDetFiberEquiv b₁ V x v := by
  ext u
  rw [ofBundleDualDetFiberEquiv_apply_apply, ofBundleDualDetFiberEquiv_apply_apply,
    detScalarEquiv_ofBundleDualDetChangeIso_hom, b₁.det.eq_smul_basis_det b₂]
  simp only [smul_apply, smul_eq_mul, b₂.det_self, mul_one]; ring

end BasisChangeTopForm

end OfBundleDualDet

end TauCeti.FiniteRankBundleCore
