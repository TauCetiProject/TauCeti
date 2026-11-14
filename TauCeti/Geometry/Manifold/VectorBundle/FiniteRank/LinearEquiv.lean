/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.LinearEquiv
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.Basic

/-!
# Smooth and holomorphic finite-rank cores from model-fibre coordinates

Presenting a `C^n` vector bundle `V` with model fibre `F` through a continuous linear equivalence
`e : F ≃L[𝕜] (Fin r → 𝕜)` produces a `C^n` finite-rank core (`isContMDiff_ofLinearEquiv`), because
its transitions are the chart transitions of `V` conjugated by the continuous linear equivalence
`e.arrowCongr e`. Over a complex manifold (`I = 𝓘(ℂ, EB)`, `n = ∞`), this equips any holomorphic
vector bundle with model fibre `F` with a holomorphic finite-rank core.

All topological comparisons from `TauCeti.Topology.VectorBundle.FiniteRank.LinearEquiv` upgrade to
`C^n` diffeomorphisms over the identity of `B`, without any smoothness hypothesis on the base or on
`V`:

* `FiniteRankBundleCore.ofLinearEquivTotalSpaceDiffeomorph` identifies the reconstructed total space
  of `ofLinearEquiv e V` with `TotalSpace F V`;
* `FiniteRankBundleCore.ofLinearEquivChangeDiffeomorph` upgrades the change-of-coordinates
  isomorphism `ofLinearEquivChangeIso e₁ e₂ V` to a `C^n` diffeomorphism commuting with
  `ofLinearEquivTotalSpaceDiffeomorph`;
* over a complete scalar field, `FiniteRankBundleCore.ofLinearEquivDualDiffeomorph` upgrades
  `ofLinearEquivDualIso e V` to a `C^n` diffeomorphism between `(ofLinearEquiv e V).dual` and the
  core of Mathlib's dual bundle `fun x ↦ V x →L[𝕜] 𝕜` in `dualCoords e`.
-/

public section

open Bundle CategoryTheory Set VectorBundleCore
open scoped Manifold ContDiff

namespace TauCeti.FiniteRankBundleCore

universe u v w z

section General

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜]
  {B : Type u} [TopologicalSpace B]
  {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  [TopologicalSpace HB] [ChartedSpace HB B] {I : ModelWithCorners 𝕜 EB HB} {n : ℕ∞ω}
  {F : Type w} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- If `V` is a `C^n` vector bundle with model fibre `F`, then `ofLinearEquiv e V` is a `C^n`
finite-rank core. For complex scalars at regularity `∞`, this is the holomorphic core structure. -/
instance isContMDiff_ofLinearEquiv {r : ℕ} (e : F ≃L[𝕜] (Fin r → 𝕜)) (V : B → Type z)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
    [FiberBundle F V] [VectorBundle 𝕜 F V] [ContMDiffVectorBundle n F V I] :
    (ofLinearEquiv e V).core.IsContMDiff I n where
  contMDiffOn_coordChange b c := by
    dsimp +instances only [ofLinearEquiv]
    exact (e.arrowCongr e).contDiff.contMDiff.comp_contMDiffOn
      (contMDiffOn_coordChangeL (IB := I) (n := n)
        (trivializationAt F V b) (trivializationAt F V c))

section TotalSpace

variable {r : ℕ} (e : F ≃L[𝕜] (Fin r → 𝕜)) (V : B → Type z)
  [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- The forward map of `ofLinearEquivTotalSpaceHomeomorph` is `C^n` at every order, without any
smoothness hypothesis on `B` or `V`. -/
theorem contMDiff_ofLinearEquivTotalSpaceHomeomorph :
    ContMDiff (I.prod 𝓘(𝕜, Fin (ofLinearEquiv e V).rank → 𝕜)) (I.prod 𝓘(𝕜, F)) n
      (ofLinearEquivTotalSpaceHomeomorph e V) := by
  intro p₀
  rw [Bundle.contMDiffAt_totalSpace_iff, ofLinearEquivTotalSpaceHomeomorph_apply]
  refine ⟨((contMDiff_proj (ofLinearEquiv e V).core.Fiber).congr fun p ↦ by simp).contMDiffAt, ?_⟩
  have hp₀ : p₀ ∈ ((ofLinearEquiv e V).core.localTriv p₀.proj).source :=
    (ofLinearEquiv e V).core.mem_source_at p₀.proj p₀.2
  have hU := ((ofLinearEquiv e V).core.localTriv p₀.proj).open_source.mem_nhds hp₀
  refine (e.symm.contDiff.comp_contMDiffAt
    ((ofLinearEquiv e V).contMDiffAt_localTriv_snd p₀)).congr_of_eventuallyEq ?_
  filter_upwards [hU] with q hq
  exact congrArg Prod.snd (trivializationAt_ofLinearEquivTotalSpaceHomeomorph e V p₀.proj q
    (((ofLinearEquiv e V).core.localTriv p₀.proj).mem_source.1 hq))

/-- The inverse map of `ofLinearEquivTotalSpaceHomeomorph` is `C^n` at every order, without any
smoothness hypothesis on `B` or `V`. -/
theorem contMDiff_ofLinearEquivTotalSpaceHomeomorph_symm :
    ContMDiff (I.prod 𝓘(𝕜, F)) (I.prod 𝓘(𝕜, Fin (ofLinearEquiv e V).rank → 𝕜)) n
      (ofLinearEquivTotalSpaceHomeomorph e V).symm := by
  intro p₀
  rw [Bundle.contMDiffAt_totalSpace_iff]
  have hproj : ((ofLinearEquivTotalSpaceHomeomorph e V).symm p₀).proj = p₀.proj := by simp
  rw [hproj]
  refine ⟨((contMDiff_proj V).congr fun p ↦ by simp).contMDiffAt, ?_⟩
  have hp₀ := FiberBundle.mem_trivializationAt_proj_source (x := p₀)
  have hU := (trivializationAt F V p₀.proj).open_source.mem_nhds hp₀
  refine (e.contDiff.comp_contMDiffAt
    (p₀.contMDiffAt_trivializationAt_snd (IB := I) (n := n))).congr_of_eventuallyEq ?_
  filter_upwards [hU] with q hq
  rw [(ofLinearEquiv e V).trivializationAt_core]
  have htriv := congrArg (fun z ↦ e z.2) (trivializationAt_ofLinearEquivTotalSpaceHomeomorph e V
    p₀.proj ((ofLinearEquivTotalSpaceHomeomorph e V).symm q)
    (by simpa using (trivializationAt F V p₀.proj).mem_source.1 hq))
  rw [Homeomorph.apply_symm_apply] at htriv
  exact (e.apply_symm_apply _).symm.trans htriv.symm

/-- The reconstructed total space of `ofLinearEquiv e V` is `C^n` diffeomorphic to `TotalSpace F V`
over the identity of `B`, without completeness or smoothness hypotheses. -/
noncomputable def ofLinearEquivTotalSpaceDiffeomorph
    (I : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω) :
    (ofLinearEquiv e V).core.TotalSpace ≃ₘ^n⟮I.prod 𝓘(𝕜, Fin (ofLinearEquiv e V).rank → 𝕜),
      I.prod 𝓘(𝕜, F)⟯ TotalSpace F V where
  toEquiv := (ofLinearEquivTotalSpaceHomeomorph e V).toEquiv
  contMDiff_toFun := contMDiff_ofLinearEquivTotalSpaceHomeomorph e V
  contMDiff_invFun := contMDiff_ofLinearEquivTotalSpaceHomeomorph_symm e V

@[simp] theorem ofLinearEquivTotalSpaceDiffeomorph_toHomeomorph :
    (ofLinearEquivTotalSpaceDiffeomorph e V I n).toHomeomorph =
      ofLinearEquivTotalSpaceHomeomorph e V :=
  Homeomorph.ext fun _ ↦ rfl

@[simp] theorem ofLinearEquivTotalSpaceDiffeomorph_apply
    (p : (ofLinearEquiv e V).core.TotalSpace) :
    ofLinearEquivTotalSpaceDiffeomorph e V I n p =
      ⟨p.proj, ofLinearEquivFiberEquiv e V p.proj p.2⟩ :=
  ofLinearEquivTotalSpaceHomeomorph_apply e V p

@[simp] theorem ofLinearEquivTotalSpaceDiffeomorph_symm_apply (p : TotalSpace F V) :
    (ofLinearEquivTotalSpaceDiffeomorph e V I n).symm p =
      ⟨p.proj, (ofLinearEquivFiberEquiv e V p.proj).symm p.2⟩ :=
  ofLinearEquivTotalSpaceHomeomorph_symm_apply e V p

end TotalSpace

/-! ### Smooth change of model coordinates -/

/-- Changing the model-fibre coordinate equivalence from `e₁` to `e₂` induces a `C^n` diffeomorphism
of reconstructed total spaces, upgrading `ofLinearEquivChangeIso e₁ e₂ V`. -/
noncomputable def ofLinearEquivChangeDiffeomorph {r₁ r₂ : ℕ}
    (e₁ : F ≃L[𝕜] (Fin r₁ → 𝕜)) (e₂ : F ≃L[𝕜] (Fin r₂ → 𝕜)) (V : B → Type z)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
    [FiberBundle F V] [VectorBundle 𝕜 F V]
    (I : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω) :
    (ofLinearEquiv e₁ V).core.TotalSpace ≃ₘ^n⟮I.prod 𝓘(𝕜, Fin (ofLinearEquiv e₁ V).rank → 𝕜),
      I.prod 𝓘(𝕜, Fin (ofLinearEquiv e₂ V).rank → 𝕜)⟯ (ofLinearEquiv e₂ V).core.TotalSpace :=
  CoordinateHom.toDiffeomorphOfInv
    (ofLinearEquivChangeIso e₁ e₂ V).hom (ofLinearEquivChangeIso e₁ e₂ V).inv
    (ofLinearEquivChangeIso e₁ e₂ V).hom_inv_id (ofLinearEquivChangeIso e₁ e₂ V).inv_hom_id
    (contMDiff_totalSpaceMap_of_mem_baseSet _ (e₁.symm.trans e₂).toContinuousLinearMap
      fun x b _ v ↦ by
        rw [fiberMap_ofLinearEquivChangeIso_hom]
        exact (congrArg (fun w ↦ e₂ ((trivializationAt F V x).coordChangeL 𝕜
          (trivializationAt F V b) x w)) (e₂.symm_apply_apply (e₁.symm v))).trans
          (congrArg e₂ (e₁.symm_apply_apply _)).symm)
    (contMDiff_totalSpaceMap_of_mem_baseSet _ (e₂.symm.trans e₁).toContinuousLinearMap
      fun x b _ v ↦ by
        rw [fiberMap_ofLinearEquivChangeIso_inv]
        exact (congrArg (fun w ↦ e₁ ((trivializationAt F V x).coordChangeL 𝕜
          (trivializationAt F V b) x w)) (e₁.symm_apply_apply (e₂.symm v))).trans
          (congrArg e₁ (e₂.symm_apply_apply _)).symm)

@[simp] theorem coe_ofLinearEquivChangeDiffeomorph {r₁ r₂ : ℕ}
    (e₁ : F ≃L[𝕜] (Fin r₁ → 𝕜)) (e₂ : F ≃L[𝕜] (Fin r₂ → 𝕜)) (V : B → Type z)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
    [FiberBundle F V] [VectorBundle 𝕜 F V] :
    ⇑(ofLinearEquivChangeDiffeomorph e₁ e₂ V I n) =
      (ofLinearEquivChangeIso e₁ e₂ V).hom.totalSpaceMap :=
  CoordinateHom.coe_toDiffeomorphOfInv _ _ _ _ _ _

@[simp] theorem coe_ofLinearEquivChangeDiffeomorph_symm {r₁ r₂ : ℕ}
    (e₁ : F ≃L[𝕜] (Fin r₁ → 𝕜)) (e₂ : F ≃L[𝕜] (Fin r₂ → 𝕜)) (V : B → Type z)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
    [FiberBundle F V] [VectorBundle 𝕜 F V] :
    ⇑(ofLinearEquivChangeDiffeomorph e₁ e₂ V I n).symm =
      (ofLinearEquivChangeIso e₁ e₂ V).inv.totalSpaceMap :=
  CoordinateHom.coe_toDiffeomorphOfInv_symm _ _ _ _ _ _

theorem ofLinearEquivTotalSpaceDiffeomorph_changeDiffeomorph {r₁ r₂ : ℕ}
    (e₁ : F ≃L[𝕜] (Fin r₁ → 𝕜)) (e₂ : F ≃L[𝕜] (Fin r₂ → 𝕜)) (V : B → Type z)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
    [FiberBundle F V] [VectorBundle 𝕜 F V]
    (p : (ofLinearEquiv e₁ V).core.TotalSpace) :
    ofLinearEquivTotalSpaceDiffeomorph e₂ V I n
        (ofLinearEquivChangeDiffeomorph e₁ e₂ V I n p) =
      ofLinearEquivTotalSpaceDiffeomorph e₁ V I n p := by
  rw [ofLinearEquivTotalSpaceDiffeomorph_apply, ofLinearEquivTotalSpaceDiffeomorph_apply,
    ← ofLinearEquivTotalSpaceHomeomorph_apply, ← ofLinearEquivTotalSpaceHomeomorph_apply,
    coe_ofLinearEquivChangeDiffeomorph, ofLinearEquivTotalSpaceHomeomorph_changeIso_hom]

end General

/-! ### Smooth dual comparison -/

section Dual

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {B : Type u} [TopologicalSpace B]
  {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  [TopologicalSpace HB] [ChartedSpace HB B] {I : ModelWithCorners 𝕜 EB HB} {n : ℕ∞ω}
  {F : Type w} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {r : ℕ} (e : F ≃L[𝕜] (Fin r → 𝕜)) (V : B → Type z)
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- Over a complete scalar field, `(ofLinearEquiv e V).dual` is `C^n` diffeomorphic on total spaces
to `ofLinearEquiv (dualCoords e) (fun x ↦ V x →L[𝕜] 𝕜)` by the identity on every coordinate fibre,
upgrading `ofLinearEquivDualIso e V`. -/
noncomputable def ofLinearEquivDualDiffeomorph
    (I : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω) :
    (ofLinearEquiv e V).dual.core.TotalSpace ≃ₘ^n⟮
      I.prod 𝓘(𝕜, Fin (ofLinearEquiv e V).dual.rank → 𝕜),
      I.prod 𝓘(𝕜, Fin (ofLinearEquiv (dualCoords e) (fun y ↦ V y →L[𝕜] 𝕜)).rank → 𝕜)⟯
        (ofLinearEquiv (dualCoords e) (fun y ↦ V y →L[𝕜] 𝕜)).core.TotalSpace :=
  CoordinateHom.toDiffeomorphOfInv
    (ofLinearEquivDualIso e V).hom (ofLinearEquivDualIso e V).inv
    (ofLinearEquivDualIso e V).hom_inv_id (ofLinearEquivDualIso e V).inv_hom_id
    (contMDiff_totalSpaceMap_of_mem_baseSet _ (ContinuousLinearMap.id 𝕜 (Fin r → 𝕜))
      fun x b hb v ↦ by
        have hx : x ∈ (trivializationAt F V x).baseSet := mem_baseSet_trivializationAt F V x
        have hb' : x ∈ (trivializationAt F V b).baseSet := hb
        rw [fiberMap_ofLinearEquivDualIso_hom, coordChange_ofLinearEquiv_dualCoords e V hx hb']
        rfl)
    (contMDiff_totalSpaceMap_of_mem_baseSet _ (ContinuousLinearMap.id 𝕜 (Fin r → 𝕜))
      fun x b hb v ↦ by
        have hx : x ∈ (trivializationAt F V x).baseSet := mem_baseSet_trivializationAt F V x
        have hb' : x ∈ (trivializationAt F V b).baseSet := by simpa using hb
        rw [fiberMap_ofLinearEquivDualIso_inv, coordChange_ofLinearEquiv_dualCoords e V hx hb']
        rfl)

@[simp] theorem coe_ofLinearEquivDualDiffeomorph :
    ⇑(ofLinearEquivDualDiffeomorph e V I n) =
      (ofLinearEquivDualIso e V).hom.totalSpaceMap :=
  CoordinateHom.coe_toDiffeomorphOfInv _ _ _ _ _ _

@[simp] theorem coe_ofLinearEquivDualDiffeomorph_symm :
    ⇑(ofLinearEquivDualDiffeomorph e V I n).symm =
      (ofLinearEquivDualIso e V).inv.totalSpaceMap :=
  CoordinateHom.coe_toDiffeomorphOfInv_symm _ _ _ _ _ _

end Dual

end TauCeti.FiniteRankBundleCore
