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
      (ofLinearEquivTotalSpaceHomeomorph e V) :=
  contMDiff_of_localTriv_snd_of_mem_baseSet (ofLinearEquiv e V)
    (ofLinearEquivTotalSpaceHomeomorph e V)
    (fun p ↦ by rw [ofLinearEquivTotalSpaceHomeomorph_apply]) e.symm.toContinuousLinearMap
    fun b p hp ↦ congrArg Prod.snd
      (trivializationAt_ofLinearEquivTotalSpaceHomeomorph e V b p
        ((baseSet_ofLinearEquiv e V b) ▸ hp))

/-- The inverse map of `ofLinearEquivTotalSpaceHomeomorph` is `C^n` at every order, without
smoothness hypotheses on `B` or `V`. -/
theorem contMDiff_ofLinearEquivTotalSpaceHomeomorph_symm :
    ContMDiff (I.prod 𝓘(𝕜, F)) (I.prod 𝓘(𝕜, Fin (ofLinearEquiv e V).rank → 𝕜)) n
      (ofLinearEquivTotalSpaceHomeomorph e V).symm :=
  contMDiff_of_trivializationAt_snd_of_mem_baseSet (ofLinearEquiv e V)
    (ofLinearEquivTotalSpaceHomeomorph e V).symm
    (fun p ↦ by rw [ofLinearEquivTotalSpaceHomeomorph_symm_apply]) e.toContinuousLinearMap
    fun b q hq ↦ localTriv_ofLinearEquivTotalSpaceHomeomorph_symm e V b q hq

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

variable {r₁ r₂ r₃ : ℕ} (e₁ : F ≃L[𝕜] (Fin r₁ → 𝕜)) (e₂ : F ≃L[𝕜] (Fin r₂ → 𝕜))
  (e₃ : F ≃L[𝕜] (Fin r₃ → 𝕜)) (V : B → Type z)
  [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- The forward total-space map of `ofLinearEquivChangeIso e₁ e₂ V` is `C^n` at every
regularity. -/
theorem contMDiff_totalSpaceMap_ofLinearEquivChangeIso_hom :
    ContMDiff (I.prod 𝓘(𝕜, Fin (ofLinearEquiv e₁ V).rank → 𝕜))
      (I.prod 𝓘(𝕜, Fin (ofLinearEquiv e₂ V).rank → 𝕜)) n
      (ofLinearEquivChangeIso e₁ e₂ V).hom.totalSpaceMap :=
  contMDiff_totalSpaceMap_of_fiberMap_eq (ofLinearEquivChangeIso e₁ e₂ V).hom
    (e₁.symm.trans e₂).toContinuousLinearMap
    (fiberMap_ofLinearEquivChangeIso_hom e₁ e₂ V)
    fun b c x _ _ ↦ coordChange_comp_ofLinearEquiv_change e₁ e₂ V b c x

/-- The inverse total-space map of `ofLinearEquivChangeIso e₁ e₂ V` is `C^n` at every
regularity. -/
theorem contMDiff_totalSpaceMap_ofLinearEquivChangeIso_inv :
    ContMDiff (I.prod 𝓘(𝕜, Fin (ofLinearEquiv e₂ V).rank → 𝕜))
      (I.prod 𝓘(𝕜, Fin (ofLinearEquiv e₁ V).rank → 𝕜)) n
      (ofLinearEquivChangeIso e₁ e₂ V).inv.totalSpaceMap :=
  contMDiff_totalSpaceMap_of_fiberMap_eq (ofLinearEquivChangeIso e₁ e₂ V).inv
    (e₂.symm.trans e₁).toContinuousLinearMap
    (fiberMap_ofLinearEquivChangeIso_inv e₁ e₂ V)
    fun b c x _ _ ↦ coordChange_comp_ofLinearEquiv_change e₂ e₁ V b c x

/-- Changing the model-fibre coordinate equivalence from `e₁` to `e₂` induces a `C^n` diffeomorphism
of reconstructed total spaces, upgrading `ofLinearEquivChangeIso e₁ e₂ V`. -/
noncomputable def ofLinearEquivChangeDiffeomorph (I : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω) :
    (ofLinearEquiv e₁ V).core.TotalSpace ≃ₘ^n⟮I.prod 𝓘(𝕜, Fin (ofLinearEquiv e₁ V).rank → 𝕜),
      I.prod 𝓘(𝕜, Fin (ofLinearEquiv e₂ V).rank → 𝕜)⟯ (ofLinearEquiv e₂ V).core.TotalSpace :=
  isoToDiffeomorph (ofLinearEquivChangeIso e₁ e₂ V)
    (contMDiff_totalSpaceMap_ofLinearEquivChangeIso_hom e₁ e₂ V)
    (contMDiff_totalSpaceMap_ofLinearEquivChangeIso_inv e₁ e₂ V)

@[simp] theorem coe_ofLinearEquivChangeDiffeomorph :
    ⇑(ofLinearEquivChangeDiffeomorph e₁ e₂ V I n) =
      (ofLinearEquivChangeIso e₁ e₂ V).hom.totalSpaceMap :=
  coe_isoToDiffeomorph _ _ _

theorem coe_ofLinearEquivChangeDiffeomorph_symm :
    ⇑(ofLinearEquivChangeDiffeomorph e₁ e₂ V I n).symm =
      (ofLinearEquivChangeIso e₁ e₂ V).inv.totalSpaceMap :=
  coe_isoToDiffeomorph_symm _ _ _

/-- Changing from a coordinate equivalence to itself induces the identity diffeomorphism. -/
@[simp] theorem ofLinearEquivChangeDiffeomorph_self :
    ofLinearEquivChangeDiffeomorph e₁ e₁ V I n =
      Diffeomorph.refl (I.prod 𝓘(𝕜, Fin (ofLinearEquiv e₁ V).rank → 𝕜))
        (ofLinearEquiv e₁ V).core.TotalSpace n :=
  Diffeomorph.ext fun p ↦ by
    rw [coe_ofLinearEquivChangeDiffeomorph, ofLinearEquivChangeIso_self, Iso.refl_hom]
    exact congrFun (CoordinateHom.totalSpaceMap_id _) p

/-- Inverting a coordinate-change diffeomorphism reverses the two coordinate equivalences. -/
@[simp] theorem ofLinearEquivChangeDiffeomorph_symm :
    (ofLinearEquivChangeDiffeomorph e₁ e₂ V I n).symm =
      ofLinearEquivChangeDiffeomorph e₂ e₁ V I n :=
  Diffeomorph.ext fun p ↦ by
    rw [coe_ofLinearEquivChangeDiffeomorph_symm, coe_ofLinearEquivChangeDiffeomorph,
      ← Iso.symm_hom, ofLinearEquivChangeIso_symm]

/-- Composing two coordinate-change diffeomorphisms yields the direct coordinate-change
diffeomorphism. -/
@[simp] theorem ofLinearEquivChangeDiffeomorph_trans :
    (ofLinearEquivChangeDiffeomorph e₁ e₂ V I n).trans
        (ofLinearEquivChangeDiffeomorph e₂ e₃ V I n) =
      ofLinearEquivChangeDiffeomorph e₁ e₃ V I n :=
  Diffeomorph.ext fun p ↦ by
    rw [Diffeomorph.coe_trans, Function.comp_apply, coe_ofLinearEquivChangeDiffeomorph,
      coe_ofLinearEquivChangeDiffeomorph, coe_ofLinearEquivChangeDiffeomorph]
    exact (congrFun (CoordinateHom.totalSpaceMap_comp
      (ofLinearEquivChangeIso e₂ e₃ V).hom (ofLinearEquivChangeIso e₁ e₂ V).hom) p).symm.trans
      (congrArg (fun f : ofLinearEquiv e₁ V ⟶ ofLinearEquiv e₃ V ↦ f.totalSpaceMap p)
        (ofLinearEquivChangeIso_hom_comp e₁ e₂ e₃ V))

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

/-- Over a complete scalar field, the forward total-space map of `ofLinearEquivDualIso e V` is
`C^n` at every regularity. -/
theorem contMDiff_totalSpaceMap_ofLinearEquivDualIso_hom :
    ContMDiff (I.prod 𝓘(𝕜, Fin (ofLinearEquiv e V).dual.rank → 𝕜))
      (I.prod 𝓘(𝕜, Fin (ofLinearEquiv (dualCoords e) (fun y ↦ V y →L[𝕜] 𝕜)).rank → 𝕜)) n
      (ofLinearEquivDualIso e V).hom.totalSpaceMap :=
  contMDiff_totalSpaceMap_of_fiberMap_eq (ofLinearEquivDualIso e V).hom
    (ContinuousLinearMap.id 𝕜 (Fin r → 𝕜))
    (fiberMap_ofLinearEquivDualIso_hom e V)
    fun _ _ _ hi hj ↦ coordChange_comp_ofLinearEquiv_dual e V hi hj

/-- Over a complete scalar field, the inverse total-space map of `ofLinearEquivDualIso e V` is
`C^n` at every regularity. -/
theorem contMDiff_totalSpaceMap_ofLinearEquivDualIso_inv :
    ContMDiff
      (I.prod 𝓘(𝕜, Fin (ofLinearEquiv (dualCoords e) (fun y ↦ V y →L[𝕜] 𝕜)).rank → 𝕜))
      (I.prod 𝓘(𝕜, Fin (ofLinearEquiv e V).dual.rank → 𝕜)) n
      (ofLinearEquivDualIso e V).inv.totalSpaceMap :=
  contMDiff_totalSpaceMap_of_fiberMap_eq (ofLinearEquivDualIso e V).inv
    (ContinuousLinearMap.id 𝕜 (Fin r → 𝕜))
    (fiberMap_ofLinearEquivDualIso_inv e V)
    fun _ _ _ hi hj ↦ coordChange_comp_ofLinearEquiv_dual_symm e V hi hj

/-- Over a complete scalar field, `(ofLinearEquiv e V).dual` is `C^n` diffeomorphic on total spaces
to `ofLinearEquiv (dualCoords e) (fun x ↦ V x →L[𝕜] 𝕜)` by the identity on every coordinate fibre,
upgrading `ofLinearEquivDualIso e V`. -/
noncomputable def ofLinearEquivDualDiffeomorph (I : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω) :
    (ofLinearEquiv e V).dual.core.TotalSpace ≃ₘ^n⟮
      I.prod 𝓘(𝕜, Fin (ofLinearEquiv e V).dual.rank → 𝕜),
      I.prod 𝓘(𝕜, Fin (ofLinearEquiv (dualCoords e) (fun y ↦ V y →L[𝕜] 𝕜)).rank → 𝕜)⟯
        (ofLinearEquiv (dualCoords e) (fun y ↦ V y →L[𝕜] 𝕜)).core.TotalSpace :=
  isoToDiffeomorph (ofLinearEquivDualIso e V)
    (contMDiff_totalSpaceMap_ofLinearEquivDualIso_hom e V)
    (contMDiff_totalSpaceMap_ofLinearEquivDualIso_inv e V)

@[simp] theorem coe_ofLinearEquivDualDiffeomorph :
    ⇑(ofLinearEquivDualDiffeomorph e V I n) =
      (ofLinearEquivDualIso e V).hom.totalSpaceMap :=
  coe_isoToDiffeomorph _ _ _

@[simp] theorem coe_ofLinearEquivDualDiffeomorph_symm :
    ⇑(ofLinearEquivDualDiffeomorph e V I n).symm =
      (ofLinearEquivDualIso e V).inv.totalSpaceMap :=
  coe_isoToDiffeomorph_symm _ _ _

end Dual

end TauCeti.FiniteRankBundleCore
