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

Presenting a `C^n` vector bundle `V` with model fibre `F` through `e : F ≃L[𝕜] (Fin r → 𝕜)` yields
a `C^n` finite-rank core (`isContMDiff_ofLinearEquiv`; holomorphic when `I = 𝓘(ℂ, EB)` and
`n = ∞`), and upgrades the topological comparisons of
`TauCeti.Topology.VectorBundle.FiniteRank.LinearEquiv` to `C^n` diffeomorphisms over `B`:

* `ofLinearEquivTotalSpaceDiffeomorph` identifies `(ofLinearEquiv e V).core.TotalSpace` with
  `TotalSpace F V`;
* `ofLinearEquivChangeDiffeomorph` upgrades `ofLinearEquivChangeIso e₁ e₂ V`, commuting with
  `ofLinearEquivTotalSpaceDiffeomorph`;
* over a complete field, `ofLinearEquivDualDiffeomorph` upgrades `ofLinearEquivDualIso e V`.
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
finite-rank core (holomorphic when `𝕜 = ℂ` and `n = ∞`). -/
instance isContMDiff_ofLinearEquiv {r : ℕ} (e : F ≃L[𝕜] (Fin r → 𝕜)) (V : B → Type z)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
    [FiberBundle F V] [VectorBundle 𝕜 F V] [ContMDiffVectorBundle n F V I] :
    (ofLinearEquiv e V).core.IsContMDiff I n where
  contMDiffOn_coordChange b c := by
    rw [baseSet_ofLinearEquiv, baseSet_ofLinearEquiv]
    exact ((e.arrowCongr e).contDiff.contMDiff.comp_contMDiffOn
      (contMDiffOn_coordChangeL (IB := I) (n := n)
        (trivializationAt F V b) (trivializationAt F V c))).congr fun x _ ↦
      coordChange_ofLinearEquiv e V b c x

section TotalSpace

variable {r : ℕ} (e : F ≃L[𝕜] (Fin r → 𝕜)) (V : B → Type z)
  [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- The forward map of `ofLinearEquivTotalSpaceHomeomorph` is `C^n` at every order, without
smoothness hypotheses on `B` or `V`. -/
theorem contMDiff_ofLinearEquivTotalSpaceHomeomorph :
    ContMDiff (I.prod 𝓘(𝕜, Fin (ofLinearEquiv e V).rank → 𝕜)) (I.prod 𝓘(𝕜, F)) n
      (ofLinearEquivTotalSpaceHomeomorph e V) := by
  intro p₀
  rw [Bundle.contMDiffAt_totalSpace_iff, ofLinearEquivTotalSpaceHomeomorph_apply]
  refine ⟨((contMDiff_proj (ofLinearEquiv e V).core.Fiber).congr fun p ↦ by simp).contMDiffAt, ?_⟩
  have hU := ((ofLinearEquiv e V).core.localTriv p₀.proj).open_source.mem_nhds
    (((ofLinearEquiv e V).core.mem_localTriv_source p₀.proj p₀).2
      ((ofLinearEquiv e V).mem_baseSet_self p₀.proj))
  exact (e.symm.contDiff.comp_contMDiffAt
    ((ofLinearEquiv e V).contMDiffAt_localTriv_snd p₀)).congr_of_eventuallyEq
      (Filter.eventually_of_mem hU fun q hq ↦ congrArg Prod.snd
        (trivializationAt_ofLinearEquivTotalSpaceHomeomorph e V p₀.proj q
          ((localTriv_baseSet_ofLinearEquiv e V p₀.proj).symm ▸
            ((ofLinearEquiv e V).core.localTriv p₀.proj).mem_source.1 hq)))

/-- The inverse map of `ofLinearEquivTotalSpaceHomeomorph` is `C^n` at every order, without
smoothness hypotheses on `B` or `V`. -/
theorem contMDiff_ofLinearEquivTotalSpaceHomeomorph_symm :
    ContMDiff (I.prod 𝓘(𝕜, F)) (I.prod 𝓘(𝕜, Fin (ofLinearEquiv e V).rank → 𝕜)) n
      (ofLinearEquivTotalSpaceHomeomorph e V).symm := by
  intro p₀
  rw [Bundle.contMDiffAt_totalSpace_iff]
  have hproj : ((ofLinearEquivTotalSpaceHomeomorph e V).symm p₀).proj = p₀.proj := by simp
  rw [hproj]
  refine ⟨((contMDiff_proj V).congr fun p ↦ by simp).contMDiffAt, ?_⟩
  have hU := (trivializationAt F V p₀.proj).open_source.mem_nhds
    (FiberBundle.mem_trivializationAt_proj_source (x := p₀))
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
      ⟨p.proj, ofLinearEquivFiberEquiv e V p.proj p.snd⟩ :=
  ofLinearEquivTotalSpaceHomeomorph_apply e V p

@[simp] theorem ofLinearEquivTotalSpaceDiffeomorph_symm_apply (p : TotalSpace F V) :
    (ofLinearEquivTotalSpaceDiffeomorph e V I n).symm p =
      ⟨p.proj, (ofLinearEquivFiberEquiv e V p.proj).symm p.snd⟩ :=
  ofLinearEquivTotalSpaceHomeomorph_symm_apply e V p

end TotalSpace

/-! ### Smooth change of model coordinates -/

section Change

variable {r₁ r₂ : ℕ} (e₁ : F ≃L[𝕜] (Fin r₁ → 𝕜)) (e₂ : F ≃L[𝕜] (Fin r₂ → 𝕜)) (V : B → Type z)
  [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- Changing the model-fibre coordinate equivalence from `e₁` to `e₂` induces a `C^n` diffeomorphism
of reconstructed total spaces, upgrading `ofLinearEquivChangeIso e₁ e₂ V`. -/
noncomputable def ofLinearEquivChangeDiffeomorph (I : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω) :
    (ofLinearEquiv e₁ V).core.TotalSpace ≃ₘ^n⟮I.prod 𝓘(𝕜, Fin (ofLinearEquiv e₁ V).rank → 𝕜),
      I.prod 𝓘(𝕜, Fin (ofLinearEquiv e₂ V).rank → 𝕜)⟯ (ofLinearEquiv e₂ V).core.TotalSpace :=
  constIsoDiffeomorph (A := ofLinearEquiv e₁ V) (D := ofLinearEquiv e₂ V)
    (fun b ↦ (baseSet_ofLinearEquiv e₁ V b).trans (baseSet_ofLinearEquiv e₂ V b).symm)
    (e₁.symm.trans e₂) fun b c x _ _ ↦
      coordChange_comp_ofLinearEquiv_change e₁ e₂ V b c x

@[simp] theorem coe_ofLinearEquivChangeDiffeomorph :
    ⇑(ofLinearEquivChangeDiffeomorph e₁ e₂ V I n) =
      (ofLinearEquivChangeIso e₁ e₂ V).hom.totalSpaceMap := by
  rw [ofLinearEquivChangeDiffeomorph]
  refine (coe_constIsoDiffeomorph _ _ _).trans (congrArg CoordinateHom.totalSpaceMap
    (hom_ext fun x ↦ ?_))
  exact (fiberMap_constIso_hom (A := ofLinearEquiv e₁ V) (D := ofLinearEquiv e₂ V)
    _ (e₁.symm.trans e₂) _ x).trans (fiberMap_ofLinearEquivChangeIso_hom e₁ e₂ V x).symm

@[simp] theorem coe_ofLinearEquivChangeDiffeomorph_symm :
    ⇑(ofLinearEquivChangeDiffeomorph e₁ e₂ V I n).symm =
      (ofLinearEquivChangeIso e₁ e₂ V).inv.totalSpaceMap := by
  rw [ofLinearEquivChangeDiffeomorph]
  refine (coe_constIsoDiffeomorph_symm _ _ _).trans (congrArg CoordinateHom.totalSpaceMap
    (hom_ext fun x ↦ ?_))
  exact (fiberMap_constIso_inv (A := ofLinearEquiv e₁ V) (D := ofLinearEquiv e₂ V)
    _ (e₁.symm.trans e₂) _ x).trans (fiberMap_ofLinearEquivChangeIso_inv e₁ e₂ V x).symm

/-- The change-of-coordinates diffeomorphism `ofLinearEquivChangeDiffeomorph e₁ e₂ V I n` commutes
with the two reconstruction diffeomorphisms `ofLinearEquivTotalSpaceDiffeomorph e₁ V I n` and
`ofLinearEquivTotalSpaceDiffeomorph e₂ V I n` onto `TotalSpace F V`. -/
theorem ofLinearEquivTotalSpaceDiffeomorph_changeDiffeomorph
    (p : (ofLinearEquiv e₁ V).core.TotalSpace) :
    ofLinearEquivTotalSpaceDiffeomorph e₂ V I n
        (ofLinearEquivChangeDiffeomorph e₁ e₂ V I n p) =
      ofLinearEquivTotalSpaceDiffeomorph e₁ V I n p := by
  rw [ofLinearEquivTotalSpaceDiffeomorph_apply, ofLinearEquivTotalSpaceDiffeomorph_apply,
    ← ofLinearEquivTotalSpaceHomeomorph_apply, ← ofLinearEquivTotalSpaceHomeomorph_apply,
    coe_ofLinearEquivChangeDiffeomorph, ofLinearEquivTotalSpaceHomeomorph_changeIso_hom]

end Change

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
noncomputable def ofLinearEquivDualDiffeomorph (I : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω) :
    (ofLinearEquiv e V).dual.core.TotalSpace ≃ₘ^n⟮
      I.prod 𝓘(𝕜, Fin (ofLinearEquiv e V).dual.rank → 𝕜),
      I.prod 𝓘(𝕜, Fin (ofLinearEquiv (dualCoords e) (fun y ↦ V y →L[𝕜] 𝕜)).rank → 𝕜)⟯
        (ofLinearEquiv (dualCoords e) (fun y ↦ V y →L[𝕜] 𝕜)).core.TotalSpace :=
  constIsoDiffeomorph (A := (ofLinearEquiv e V).dual)
    (D := ofLinearEquiv (dualCoords e) (fun y ↦ V y →L[𝕜] 𝕜))
    (fun i ↦ (baseSet_ofLinearEquiv_dual e V i).trans (by rw [baseSet_ofLinearEquiv]; simp))
    (ContinuousLinearEquiv.refl 𝕜 (Fin r → 𝕜))
    fun _ _ _ hi hj ↦ coordChange_comp_ofLinearEquiv_dual e V hi hj

@[simp] theorem coe_ofLinearEquivDualDiffeomorph :
    ⇑(ofLinearEquivDualDiffeomorph e V I n) =
      (ofLinearEquivDualIso e V).hom.totalSpaceMap := by
  rw [ofLinearEquivDualDiffeomorph]
  refine (coe_constIsoDiffeomorph _ _ _).trans (congrArg CoordinateHom.totalSpaceMap
    (hom_ext fun x ↦ ?_))
  exact (fiberMap_constIso_hom (A := (ofLinearEquiv e V).dual)
    (D := ofLinearEquiv (dualCoords e) (fun y ↦ V y →L[𝕜] 𝕜))
    _ (ContinuousLinearEquiv.refl 𝕜 (Fin r → 𝕜)) _ x).trans
    (fiberMap_ofLinearEquivDualIso_hom e V x).symm

@[simp] theorem coe_ofLinearEquivDualDiffeomorph_symm :
    ⇑(ofLinearEquivDualDiffeomorph e V I n).symm =
      (ofLinearEquivDualIso e V).inv.totalSpaceMap := by
  rw [ofLinearEquivDualDiffeomorph]
  refine (coe_constIsoDiffeomorph_symm _ _ _).trans (congrArg CoordinateHom.totalSpaceMap
    (hom_ext fun x ↦ ?_))
  exact (fiberMap_constIso_inv (A := (ofLinearEquiv e V).dual)
    (D := ofLinearEquiv (dualCoords e) (fun y ↦ V y →L[𝕜] 𝕜))
    _ (ContinuousLinearEquiv.refl 𝕜 (Fin r → 𝕜)) _ x).trans
    (fiberMap_ofLinearEquivDualIso_inv e V x).symm

end Dual

end TauCeti.FiniteRankBundleCore
