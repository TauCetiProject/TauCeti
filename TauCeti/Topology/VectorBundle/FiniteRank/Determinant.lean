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
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.Topology.Algebra.Module.Equiv.Pi

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
`e : F ≃L[𝕜] (Fin r → 𝕜)`, the transition functions of `(ofBundleEquiv e V).dual.det` are
multiplication by
`LinearMap.det ((trivializationAt F V j).coordChangeL 𝕜 (trivializationAt F V i) x)`, independent
of `e` (`coordChange_ofBundleEquiv_dual_det`). When `e = b.equivFunL` comes from a basis
`b : Module.Basis (Fin r) 𝕜 F`, the fibre equivalence `ofBundleEquivDualDetFiberEquiv b V x`
identifies `(ofBundleEquiv b.equivFunL V).dual.det` with Mathlib's top-degree alternating form
bundle `fun x ↦ V x [⋀^Fin r]→L[𝕜] 𝕜`, glueing to a homeomorphism of total spaces
`ofBundleEquivDualDetTotalSpaceHomeomorph b V`. Under this top-exterior-power convention, the unit
coordinate `fun _ ↦ 1` over `x` corresponds to `b.continuousDet` pulled back along the preferred
trivialization at `x`, and inversely a top-degree form `ω` is sent to its value on the local frame
`i ↦ (trivializationAt F V x).symm x (b i)`. Changing the basis from `b₁` to `b₂` acts by scalar
multiplication by `b₁.det b₂` (`ofBundleEquivDualDetChangeIso b₁ b₂ V`), agrees with the functorial
image of `ofBundleEquivChangeIso` under `dualFunctor` and `exteriorPower`, and commutes strictly
with `ofBundleEquivDualDetFiberEquiv`.

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

section OfBundleEquivDualDet

variable [CompleteSpace 𝕜] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The transition of `(ofBundleEquiv e V).dual.det` from chart `i` to chart `j` is scalar
multiplication by the determinant of the reverse transition of `V` from `j` to `i`, independent of
the coordinate equivalence `e`. -/
theorem coordChange_ofBundleEquiv_dual_det {r : ℕ} (e : F ≃L[𝕜] (Fin r → 𝕜)) (V : B → Type*)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
    [FiberBundle F V] [VectorBundle 𝕜 F V] (i j x : B) :
    (ofBundleEquiv e V).dual.det.core.coordChange i j x =
      LinearMap.det (((trivializationAt F V j).coordChangeL 𝕜
          (trivializationAt F V i) x : F →L[𝕜] F) : F →ₗ[𝕜] F) •
        ContinuousLinearMap.id 𝕜 (Fin (ofBundleEquiv e V).dual.det.rank → 𝕜) := by
  rw [coordChange_det_dual, coordChange_ofBundleEquiv]
  congr 1
  exact LinearMap.det_conj
    (((trivializationAt F V j).coordChangeL 𝕜 (trivializationAt F V i) x : F →L[𝕜] F) : F →ₗ[𝕜] F)
    e.toLinearEquiv

section TopFormBundle

variable {r : ℕ} (b : Module.Basis (Fin r) 𝕜 F) (V : B → Type*)
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- On the fibre over `x`, identify the determinant line of `(ofBundleEquiv b.equivFunL V).dual`
with the line of top-degree continuous alternating forms `V x [⋀^Fin r]→L[𝕜] 𝕜`: a scalar
coordinate `c` maps to `c` times `b.continuousDet` pulled back along `trivializationAt F V x`. -/
noncomputable def ofBundleEquivDualDetFiberEquiv (x : B) :
    (ofBundleEquiv b.equivFunL V).dual.det.core.Fiber x ≃L[𝕜] (V x [⋀^Fin r]→L[𝕜] 𝕜) :=
  (detScalarEquiv (ofBundleEquiv b.equivFunL V).dual).trans
    (b.topFormEquiv.symm.trans
      (VectorBundle.continuousLinearEquivAt 𝕜 F V x).symm.continuousAlternatingMapCongrLeft)

/-- Explicit evaluation formula for `ofBundleEquivDualDetFiberEquiv` on an `r`-tuple of vectors in
`V x`. -/
@[simp]
theorem ofBundleEquivDualDetFiberEquiv_apply_apply (x : B)
    (v : Fin (ofBundleEquiv b.equivFunL V).dual.det.rank → 𝕜) (u : Fin r → V x) :
    ofBundleEquivDualDetFiberEquiv b V x v u =
      detScalarEquiv (ofBundleEquiv b.equivFunL V).dual v *
        b.det (fun i ↦ (trivializationAt F V x ⟨x, u i⟩).2) :=
  b.topFormEquiv_symm_apply
    (detScalarEquiv (ofBundleEquiv b.equivFunL V).dual v)
    (fun i ↦ (trivializationAt F V x ⟨x, u i⟩).2)

/-- Explicit top-exterior-power formula on fibres: `ofBundleEquivDualDetFiberEquiv b V x v` scales
the pullback of `b.continuousDet` along `(trivializationAt F V x).continuousLinearMapAt 𝕜 x` by
`detScalarEquiv _ v`. -/
theorem ofBundleEquivDualDetFiberEquiv_apply (x : B)
    (v : Fin (ofBundleEquiv b.equivFunL V).dual.det.rank → 𝕜) :
    ofBundleEquivDualDetFiberEquiv b V x v =
      detScalarEquiv (ofBundleEquiv b.equivFunL V).dual v •
        b.continuousDet.compContinuousLinearMap
          ((trivializationAt F V x).continuousLinearMapAt 𝕜 x) := by
  ext u
  simp only [ofBundleEquivDualDetFiberEquiv_apply_apply, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, Module.Basis.continuousDet_apply,
    smul_eq_mul, Function.comp_def,
    (trivializationAt F V x).continuousLinearMapAt_apply_of_mem (R := 𝕜)
      (mem_baseSet_trivializationAt F V x)]

/-- Under `ofBundleEquivDualDetFiberEquiv`, the unit coordinate `fun _ ↦ 1` corresponds to the
determinant form `b.continuousDet` pulled back along `trivializationAt F V x`. -/
theorem ofBundleEquivDualDetFiberEquiv_const_one (x : B) :
    ofBundleEquivDualDetFiberEquiv b V x (fun _ ↦ 1) =
      b.continuousDet.compContinuousLinearMap
        ((trivializationAt F V x).continuousLinearMapAt 𝕜 x) := by
  rw [ofBundleEquivDualDetFiberEquiv_apply, detScalarEquiv_const, one_smul]

/-- Inversely, `ofBundleEquivDualDetFiberEquiv` sends a top-degree alternating form `ω` on `V x`
to the constant coordinate given by evaluating `ω` on the preferred frame
`k ↦ (trivializationAt F V x).symm x (b k)`. -/
@[simp]
theorem ofBundleEquivDualDetFiberEquiv_symm_apply (x : B) (ω : V x [⋀^Fin r]→L[𝕜] 𝕜)
    (i : Fin (ofBundleEquiv b.equivFunL V).dual.det.rank) :
    (ofBundleEquivDualDetFiberEquiv b V x).symm ω i =
      ω (fun k ↦ (trivializationAt F V x).symm x (b k)) := by
  let v := (ofBundleEquivDualDetFiberEquiv b V x).symm ω
  have hω : ω (fun k ↦ (trivializationAt F V x).symm x (b k)) =
      detScalarEquiv (ofBundleEquiv b.equivFunL V).dual v := by
    have h1 := ofBundleEquivDualDetFiberEquiv_apply_apply b V x v
      (fun k ↦ (trivializationAt F V x).symm x (b k))
    rw [ContinuousLinearEquiv.apply_symm_apply] at h1
    have htriv : (fun k ↦ (trivializationAt F V x ⟨x, (trivializationAt F V x).symm x (b k)⟩).2) =
        b := funext fun k ↦
      congrArg Prod.snd
        ((trivializationAt F V x).apply_mk_symm (mem_baseSet_trivializationAt F V x) (b k))
    rw [htriv, b.det_self, mul_one] at h1
    exact h1
  exact (det_fiber_eq_const _ v i).trans hω.symm

/-- On the base set of `trivializationAt F V a`, `ofBundleEquivDualDetFiberEquiv` intertwines the
core chart at `a` with the preferred alternating-bundle chart at `a` via the constant equivalence
`b.topFormEquiv.symm ∘ detScalarEquiv`. -/
theorem trivializationAt_ofBundleEquivDualDetFiberEquiv_snd (a : B) {x : B}
    (hx : x ∈ (trivializationAt F V a).baseSet)
    (v : Fin (ofBundleEquiv b.equivFunL V).dual.det.rank → 𝕜) :
    (trivializationAt (F [⋀^Fin r]→L[𝕜] 𝕜) (fun y ↦ V y [⋀^Fin r]→L[𝕜] 𝕜) a
        ⟨x, ofBundleEquivDualDetFiberEquiv b V x v⟩).2 =
      b.topFormEquiv.symm (detScalarEquiv (ofBundleEquiv b.equivFunL V).dual
        (((ofBundleEquiv b.equivFunL V).dual.det.core.localTriv a ⟨x, v⟩).2)) := by
  let T : F →L[𝕜] F := (trivializationAt F V a).coordChangeL 𝕜 (trivializationAt F V x) x
  have htriv :
      detScalarEquiv (ofBundleEquiv b.equivFunL V).dual
        (((ofBundleEquiv b.equivFunL V).dual.det.core.localTriv a ⟨x, v⟩).2) =
      LinearMap.det (T : F →ₗ[𝕜] F) * detScalarEquiv (ofBundleEquiv b.equivFunL V).dual v := by
    have h1 : (((ofBundleEquiv b.equivFunL V).dual.det.core.localTriv a ⟨x, v⟩).2 :
        Fin (ofBundleEquiv b.equivFunL V).dual.det.rank → 𝕜) =
        LinearMap.det (T : F →ₗ[𝕜] F) • v := by
      rw [VectorBundleCore.localTriv_apply]; dsimp only
      rw [(ofBundleEquiv b.equivFunL V).dual.det.indexAt_eq, coordChange_ofBundleEquiv_dual_det]
      simp only [smul_apply, ContinuousLinearMap.id_apply, T]
    rw [h1, map_smul, smul_eq_mul]
  rw [FiberBundle.trivializationAt_continuousAlternatingMap_apply_snd, htriv]
  ext u
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ofBundleEquivDualDetFiberEquiv_apply_apply, Module.Basis.topFormEquiv_symm_apply,
    Function.comp_apply]
  have hfun : (fun i ↦ (trivializationAt F V x ⟨x, (trivializationAt F V a).symmL 𝕜 x (u i)⟩).2) =
      (T : F →ₗ[𝕜] F) ∘ u := funext fun i ↦ by
    rw [(trivializationAt F V a).symmL_apply hx]
    exact congrArg Prod.snd ((trivializationAt F V a).mk_coordChangeL (R := 𝕜)
      (trivializationAt F V x) ⟨hx, mem_baseSet_trivializationAt F V x⟩ (u i)).symm
  rw [hfun, b.det_comp]; ring

/-- Near any `p₀`, reading `ofBundleEquivDualDetFiberEquiv` in the preferred alternating-bundle
chart at `p₀.proj` eventually agrees with the constant equivalence
`b.topFormEquiv.symm ∘ detScalarEquiv` applied to the determinant core chart at `p₀.proj`. -/
theorem eventuallyEq_trivializationAt_ofBundleEquivDualDetFiberEquiv_snd
    (p₀ : (ofBundleEquiv b.equivFunL V).dual.det.core.TotalSpace) :
    (fun q : (ofBundleEquiv b.equivFunL V).dual.det.core.TotalSpace ↦
        (trivializationAt (F [⋀^Fin r]→L[𝕜] 𝕜) (fun y ↦ V y [⋀^Fin r]→L[𝕜] 𝕜) p₀.proj
          ⟨q.proj, ofBundleEquivDualDetFiberEquiv b V q.proj q.snd⟩).2) =ᶠ[nhds p₀]
      fun q ↦
        ((detScalarEquiv (ofBundleEquiv b.equivFunL V).dual).trans b.topFormEquiv.symm)
          (((ofBundleEquiv b.equivFunL V).dual.det.core.localTriv p₀.proj q).2) := by
  have hbase (i : B) : (ofBundleEquiv b.equivFunL V).dual.det.core.baseSet i =
      (trivializationAt F V i).baseSet :=
    (localTriv_baseSet_det (ofBundleEquiv b.equivFunL V).dual i).trans
      (baseSet_ofBundleEquiv b.equivFunL V i)
  have hU :=
    ((ofBundleEquiv b.equivFunL V).dual.det.core.localTriv p₀.proj).open_source.mem_nhds <|
      ((ofBundleEquiv b.equivFunL V).dual.det.core.mem_localTriv_source p₀.proj p₀).2
        ((hbase p₀.proj).symm ▸ mem_baseSet_trivializationAt F V p₀.proj)
  filter_upwards [hU] with q hq
  exact trivializationAt_ofBundleEquivDualDetFiberEquiv_snd b V p₀.proj
    ((hbase p₀.proj) ▸
      ((ofBundleEquiv b.equivFunL V).dual.det.core.mem_localTriv_source p₀.proj q).1 hq) q.snd

/-- Reading determinant-core coordinates as top-degree alternating forms on `V` is continuous on
total spaces. -/
theorem continuous_ofBundleEquivDualDetFiberEquiv :
    Continuous fun p : (ofBundleEquiv b.equivFunL V).dual.det.core.TotalSpace ↦
      TotalSpace.mk' (F [⋀^Fin r]→L[𝕜] 𝕜) (E := fun x ↦ V x [⋀^Fin r]→L[𝕜] 𝕜)
        p.proj (ofBundleEquivDualDetFiberEquiv b V p.proj p.snd) := by
  refine continuous_iff_continuousAt.2 fun p ↦ ?_
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨(ofBundleEquiv b.equivFunL V).dual.det.core.continuous_proj.continuousAt, ?_⟩
  have hbase (i : B) : (ofBundleEquiv b.equivFunL V).dual.det.core.baseSet i =
      (trivializationAt F V i).baseSet :=
    (localTriv_baseSet_det (ofBundleEquiv b.equivFunL V).dual i).trans
      (baseSet_ofBundleEquiv b.equivFunL V i)
  have hU := ((ofBundleEquiv b.equivFunL V).dual.det.core.localTriv p.proj).open_source.mem_nhds <|
    ((ofBundleEquiv b.equivFunL V).dual.det.core.mem_localTriv_source p.proj p).2
      ((hbase p.proj).symm ▸ mem_baseSet_trivializationAt F V p.proj)
  have hc :=
    (((ofBundleEquiv b.equivFunL V).dual.det.core.localTriv p.proj).continuousOn.continuousAt
      hU).snd
  let L := (detScalarEquiv (ofBundleEquiv b.equivFunL V).dual).trans b.topFormEquiv.symm
  exact (L.continuous.continuousAt.comp hc).congr_of_eventuallyEq
    (eventuallyEq_trivializationAt_ofBundleEquivDualDetFiberEquiv_snd b V p)

/-- The reconstructed total space of `(ofBundleEquiv b.equivFunL V).dual.det` is homeomorphic to
Mathlib's top-degree alternating form bundle `fun x ↦ V x [⋀^Fin r]→L[𝕜] 𝕜`, over the identity of
the base and by `ofBundleEquivDualDetFiberEquiv b V x` on each fibre. -/
noncomputable def ofBundleEquivDualDetTotalSpaceHomeomorph :
    (ofBundleEquiv b.equivFunL V).dual.det.core.TotalSpace ≃ₜ
      TotalSpace (F [⋀^Fin r]→L[𝕜] 𝕜) (fun x ↦ V x [⋀^Fin r]→L[𝕜] 𝕜) :=
  bundleHomeomorph (𝕜 := 𝕜) (ofBundleEquivDualDetFiberEquiv b V)
    (continuous_ofBundleEquivDualDetFiberEquiv b V)

@[simp]
theorem ofBundleEquivDualDetTotalSpaceHomeomorph_apply
    (p : (ofBundleEquiv b.equivFunL V).dual.det.core.TotalSpace) :
    ofBundleEquivDualDetTotalSpaceHomeomorph b V p =
      ⟨p.proj, ofBundleEquivDualDetFiberEquiv b V p.proj p.snd⟩ :=
  bundleHomeomorph_apply _ _ p

@[simp]
theorem ofBundleEquivDualDetTotalSpaceHomeomorph_symm_apply
    (p : TotalSpace (F [⋀^Fin r]→L[𝕜] 𝕜) (fun x ↦ V x [⋀^Fin r]→L[𝕜] 𝕜)) :
    (ofBundleEquivDualDetTotalSpaceHomeomorph b V).symm p =
      ⟨p.proj, (ofBundleEquivDualDetFiberEquiv b V p.proj).symm p.snd⟩ :=
  bundleHomeomorph_symm_apply _ _ p

end TopFormBundle

section BasisChange

variable {r : ℕ} (b₁ b₂ : Module.Basis (Fin r) 𝕜 F) (V : B → Type*)
  [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

private noncomputable def detScaleEquiv :
    (Fin (ofBundleEquiv b₁.equivFunL V).dual.det.rank → 𝕜) ≃L[𝕜]
      (Fin (ofBundleEquiv b₂.equivFunL V).dual.det.rank → 𝕜) :=
  (detScalarEquiv (ofBundleEquiv b₁.equivFunL V).dual).trans
    ((ContinuousLinearEquiv.unitsEquivAut 𝕜 (b₁.isUnit_det b₂).unit).trans
      (detScalarEquiv (ofBundleEquiv b₂.equivFunL V).dual).symm)

/-- Changing the model basis from `b₁` to `b₂` induces a canonical isomorphism between the
determinant line bundles `(ofBundleEquiv b₁.equivFunL V).dual.det` and
`(ofBundleEquiv b₂.equivFunL V).dual.det`, scaling scalar coordinates by `b₁.det b₂`. -/
noncomputable def ofBundleEquivDualDetChangeIso :
    (ofBundleEquiv b₁.equivFunL V).dual.det ≅ (ofBundleEquiv b₂.equivFunL V).dual.det :=
  constIso
    (by
      intro i
      exact ((localTriv_baseSet_det (ofBundleEquiv b₁.equivFunL V).dual i).trans
        ((baseSet_ofBundleEquiv b₁.equivFunL V i).trans
          (baseSet_ofBundleEquiv b₂.equivFunL V i).symm)).trans
        (localTriv_baseSet_det (ofBundleEquiv b₂.equivFunL V).dual i).symm)
    (detScaleEquiv b₁ b₂ V) fun i j x _ _ ↦ by
      rw [coordChange_ofBundleEquiv_dual_det, coordChange_ofBundleEquiv_dual_det]
      ext v : 1
      simp only [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply, map_smul]

@[simp]
theorem detScalarEquiv_ofBundleEquivDualDetChangeIso_hom (x : B)
    (v : Fin (ofBundleEquiv b₁.equivFunL V).dual.det.rank → 𝕜) :
    detScalarEquiv (ofBundleEquiv b₂.equivFunL V).dual
        ((ofBundleEquivDualDetChangeIso b₁ b₂ V).hom.fiberMap x v) =
      b₁.det b₂ * detScalarEquiv (ofBundleEquiv b₁.equivFunL V).dual v := by
  have h : (ofBundleEquivDualDetChangeIso b₁ b₂ V).hom.fiberMap x =
      (detScaleEquiv b₁ b₂ V).toContinuousLinearMap :=
    fiberMap_constIso_hom _ _ _ x
  rw [h]
  simp [detScaleEquiv, ContinuousLinearEquiv.unitsEquivAut_apply, IsUnit.unit_spec, mul_comm]

@[simp]
theorem detScalarEquiv_ofBundleEquivDualDetChangeIso_inv (x : B)
    (v : Fin (ofBundleEquiv b₂.equivFunL V).dual.det.rank → 𝕜) :
    detScalarEquiv (ofBundleEquiv b₁.equivFunL V).dual
        ((ofBundleEquivDualDetChangeIso b₁ b₂ V).inv.fiberMap x v) =
      b₂.det b₁ * detScalarEquiv (ofBundleEquiv b₂.equivFunL V).dual v := by
  have h : (ofBundleEquivDualDetChangeIso b₁ b₂ V).inv.fiberMap x =
      (detScaleEquiv b₁ b₂ V).symm.toContinuousLinearMap :=
    fiberMap_constIso_inv _ _ _ x
  rw [h]
  simp only [detScaleEquiv, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.symm_trans_apply, ContinuousLinearEquiv.symm_symm,
    ContinuousLinearEquiv.unitsEquivAut_apply_symm, Module.Basis.det_inv, mul_comm]

omit [CompleteSpace 𝕜] in
private theorem eq_eqToIso_conj_of_fiberMap_smul_id
    {X₁ X₂ Y₁ Y₂ : FiniteRankBundleCore 𝕜 B}
    (h₁ : X₁ = Y₁) (h₂ : X₂ = Y₂) (hX : X₁.rank = X₂.rank) (hY : Y₁.rank = Y₂.rank)
    (c : 𝕜) (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂)
    (hf : ∀ x v i, f.fiberMap x v i = c * v (Fin.cast hX.symm i))
    (hg : ∀ x v i, g.fiberMap x v i = c * v (Fin.cast hY.symm i)) :
    f = (eqToIso h₁).hom ≫ g ≫ (eqToIso h₂).inv := by
  subst h₁ h₂
  simp only [eqToIso_refl, Iso.refl_hom, Iso.refl_inv, Category.id_comp, Category.comp_id]
  exact hom_ext fun x ↦ ContinuousLinearMap.ext fun v ↦ funext fun i ↦
    (hf x v i).trans (hg x v i).symm

omit [TopologicalSpace B] in
/-- The determinant of the coordinate transition `b₁.equivFunL ∘ b₂.equivFunL.symm` equals
`b₁.det b₂`. -/
theorem det_equivFunL_symm_trans :
    LinearMap.det ((b₂.equivFunL.symm.trans b₁.equivFunL).toContinuousLinearMap :
      (Fin r → 𝕜) →ₗ[𝕜] (Fin r → 𝕜)) = b₁.det b₂ := by
  have hconj := LinearMap.det_conj (b₁.equiv b₂ (Equiv.refl (Fin r))).toLinearMap b₁.equivFun
  rw [Module.Basis.det_basis b₂ b₁] at hconj
  refine (congrArg LinearMap.det (LinearMap.ext fun v ↦ ?_)).trans hconj
  simp [Module.Basis.equiv_apply]

/-- The basis-change isomorphism `ofBundleEquivDualDetChangeIso` agrees with the functorial image
of `ofBundleEquivChangeIso b₂.equivFunL b₁.equivFunL V` under `dualMap` and `exteriorPower`. -/
theorem ofBundleEquivDualDetChangeIso_hom_eq_exteriorPower_dualMap :
    (ofBundleEquivDualDetChangeIso b₁ b₂ V).hom =
      (eqToIso (det_def (ofBundleEquiv b₁.equivFunL V).dual)).hom ≫
        (exteriorPower 𝕜 B r).map
          (dualMap (ofBundleEquivChangeIso b₂.equivFunL b₁.equivFunL V).hom) ≫
        (eqToIso (det_def (ofBundleEquiv b₂.equivFunL V).dual)).inv := by
  refine eq_eqToIso_conj_of_fiberMap_smul_id
    (det_def (ofBundleEquiv b₁.equivFunL V).dual) (det_def (ofBundleEquiv b₂.equivFunL V).dual)
    ((rank_det _).trans (rank_det _).symm) rfl (b₁.det b₂) _ _ ?_ ?_
  · intro x v i
    exact (det_fiber_eq_const (ofBundleEquiv b₂.equivFunL V).dual _ i).trans <|
      (detScalarEquiv_ofBundleEquivDualDetChangeIso_hom b₁ b₂ V x v).trans
        (congrArg (b₁.det b₂ * ·)
          (det_fiber_eq_const (ofBundleEquiv b₁.equivFunL V).dual v _).symm)
  · intro x v i
    have h1 : ((dualMap (ofBundleEquivChangeIso b₂.equivFunL b₁.equivFunL V).hom).fiberMap x :
          (Fin r → 𝕜) →L[𝕜] (Fin r → 𝕜)) =
        (b₂.equivFunL.symm.trans b₁.equivFunL).toContinuousLinearMap.piTranspose :=
      (fiberMap_dualMap _ x).trans (congrArg ContinuousLinearMap.piTranspose
        (fiberMap_ofBundleEquivChangeIso_hom b₂.equivFunL b₁.equivFunL V x))
    have hmap :
        (((exteriorPower 𝕜 B r).map
            (dualMap (ofBundleEquivChangeIso b₂.equivFunL b₁.equivFunL V).hom)).fiberMap x :
          (Fin (r.choose r) → 𝕜) →L[𝕜] (Fin (r.choose r) → 𝕜)) =
        b₁.det b₂ • ContinuousLinearMap.id 𝕜 (Fin (r.choose r) → 𝕜) :=
      (fiberMap_exteriorPower_map r _ x).trans <|
        (congrArg (ContinuousLinearMap.exteriorPowerCoords r) h1).trans <|
          (ContinuousLinearMap.exteriorPowerCoords_self _).trans <|
            congrArg (· • ContinuousLinearMap.id 𝕜 (Fin (r.choose r) → 𝕜))
              ((ContinuousLinearMap.det_piTranspose _).trans (det_equivFunL_symm_trans b₁ b₂))
    exact congrArg (fun S : (Fin (r.choose r) → 𝕜) →L[𝕜] (Fin (r.choose r) → 𝕜) ↦ S v i) hmap

end BasisChange

section BasisChangeTopForm

variable {r : ℕ} (b₁ b₂ : Module.Basis (Fin r) 𝕜 F) (V : B → Type*)
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- Changing the model basis commutes strictly with the top-alternating-form identification
`ofBundleEquivDualDetFiberEquiv`. -/
theorem ofBundleEquivDualDetFiberEquiv_changeIso (x : B)
    (v : Fin (ofBundleEquiv b₁.equivFunL V).dual.det.rank → 𝕜) :
    ofBundleEquivDualDetFiberEquiv b₂ V x
        ((ofBundleEquivDualDetChangeIso b₁ b₂ V).hom.fiberMap x v) =
      ofBundleEquivDualDetFiberEquiv b₁ V x v := by
  ext u
  rw [ofBundleEquivDualDetFiberEquiv_apply_apply, ofBundleEquivDualDetFiberEquiv_apply_apply,
    detScalarEquiv_ofBundleEquivDualDetChangeIso_hom, b₁.det.eq_smul_basis_det b₂]
  simp only [smul_apply, smul_eq_mul, b₂.det_self, mul_one]; ring

end BasisChangeTopForm

end OfBundleEquivDualDet

end TauCeti.FiniteRankBundleCore
