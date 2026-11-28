/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.OrderOfElement
public import TauCeti.Geometry.Manifold.Quotient.AssociatedBundle
public import TauCeti.Topology.Covering.CharacterBundle
import TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.Basic
import TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.Dual
import TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.Monoidal

/-!
# Duals and tensor-power trivializations of character line bundles

Let `p : E → X` be a quotient covering map for a group `G` (`IsQuotientCoveringMap p G`) over a
charted space `X`. Building on `IsQuotientCoveringMap.characterFiniteRankCore χ` from
`TauCeti.Geometry.Manifold.Quotient.AssociatedBundle` and
`IsQuotientCoveringMap.characterFiniteRankCoreInvIso` from
`TauCeti.Topology.Covering.CharacterBundle`, this file provides:

* `IsQuotientCoveringMap.characterFiniteRankCoreInvDiffeomorph`: over a complete scalar field, a
  glued `C^n` total-space equivalence over `X` identifying
  `(hp.characterFiniteRankCore χ).dual` with `hp.characterFiniteRankCore χ⁻¹`;
* `IsQuotientCoveringMap.characterFiniteRankCoreOneDiffeomorph`,
  `IsQuotientCoveringMap.characterFiniteRankCoreMulDiffeomorph`, and
  `IsQuotientCoveringMap.characterFiniteRankCoreTensorPowerDiffeomorph` (together with the
  underlying `_hom` and `_inv` `ContMDiff` total-space map lemmas): glued `C^n` total-space
  equivalences identifying the unit, tensor product, and `m`-th tensor power of
  `hp.characterFiniteRankCore χ` with the corresponding character bundle cores;
* `exists_trivialization_baseSet_eq_univ_tensorPow_characterFiniteRankCore_iff`,
  `exists_trivialization_baseSet_eq_univ_tensorPow_characterFiniteRankCore_of_orderOf_dvd`,
  `exists_trivialization_baseSet_eq_univ_tensorPow_characterFiniteRankCore_orderOf`, and
  `exists_trivialization_baseSet_eq_univ_tensorPow_characterFiniteRankCore_natCard`: global `C^n`
  trivialization criteria for `tensorPow (hp.characterFiniteRankCore χ) m` via
  `hp.characterFiniteRankCoreTensorPowerIso χ m`, without Picard theory;
* `exists_trivialization_baseSet_eq_univ_tensorPow_characterFiniteRankCore_iff_orderOf_dvd` and
  `isLeast_pos_trivialization_tensorPow_characterFiniteRankCore`: exact divisibility and
  least-exponent global-trivialization criteria over compact connected complex coverings.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, Section 2.2.
-/

public section

open Bundle CategoryTheory MonoidalCategory Set TauCeti TauCeti.FiniteRankBundleCore
open VectorBundleCore
open scoped Manifold ContDiff

namespace IsQuotientCoveringMap

section Dual

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB}
  {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X] [ChartedSpace HB X]
  [Group G] [MulAction G E] {p : E → X} (hp : IsQuotientCoveringMap p G) {n : ℕ∞ω}

/-- Over a complete scalar field, the `C^n` bundle equivalence identifying
`(hp.characterFiniteRankCore χ).dual` with `hp.characterFiniteRankCore χ⁻¹` over the identity of
`X`. -/
noncomputable def characterFiniteRankCoreInvDiffeomorph [CompleteSpace 𝕜] (χ : G →* 𝕜ˣ) :
    (hp.characterFiniteRankCore χ).dual.core.TotalSpace ≃ₘ^n⟮
      IB.prod 𝓘(𝕜, Fin (hp.characterFiniteRankCore χ).dual.rank → 𝕜),
      IB.prod 𝓘(𝕜, Fin (hp.characterFiniteRankCore χ⁻¹).rank → 𝕜)⟯
    (hp.characterFiniteRankCore χ⁻¹).core.TotalSpace :=
  constIsoDiffeomorph (A := (hp.characterFiniteRankCore χ).dual)
    (D := hp.characterFiniteRankCore χ⁻¹)
    (hp.baseSet_dual_characterFiniteRankCore χ) (ContinuousLinearEquiv.refl 𝕜 (Fin 1 → 𝕜))
    (hp.coordChange_characterFiniteRankCore_inv_intertwines χ)

@[simp] theorem coe_characterFiniteRankCoreInvDiffeomorph [CompleteSpace 𝕜] (χ : G →* 𝕜ˣ) :
    ⇑(hp.characterFiniteRankCoreInvDiffeomorph (IB := IB) (n := n) χ) =
      (hp.characterFiniteRankCoreInvIso χ).hom.totalSpaceMap := by
  rw [hp.characterFiniteRankCoreInvIso_def χ]
  exact coe_constIsoDiffeomorph (I := IB) (n := n) _ _ _

@[simp] theorem coe_characterFiniteRankCoreInvDiffeomorph_symm [CompleteSpace 𝕜] (χ : G →* 𝕜ˣ) :
    ⇑(hp.characterFiniteRankCoreInvDiffeomorph (IB := IB) (n := n) χ).symm =
      (hp.characterFiniteRankCoreInvIso χ).inv.totalSpaceMap := by
  rw [hp.characterFiniteRankCoreInvIso_def χ]
  exact coe_constIsoDiffeomorph_symm (I := IB) (n := n) _ _ _

/-- Over a complete scalar field, the forward total-space map of
`hp.characterFiniteRankCoreInvIso χ` is `C^n`. -/
theorem contMDiff_totalSpaceMap_characterFiniteRankCoreInvIso_hom [CompleteSpace 𝕜]
    (χ : G →* 𝕜ˣ) :
    ContMDiff (IB.prod 𝓘(𝕜, Fin (hp.characterFiniteRankCore χ).dual.rank → 𝕜))
      (IB.prod 𝓘(𝕜, Fin (hp.characterFiniteRankCore χ⁻¹).rank → 𝕜)) n
      (hp.characterFiniteRankCoreInvIso χ).hom.totalSpaceMap :=
  coe_characterFiniteRankCoreInvDiffeomorph (hp := hp) (IB := IB) (n := n) χ ▸
    (hp.characterFiniteRankCoreInvDiffeomorph (IB := IB) (n := n) χ).contMDiff

/-- Over a complete scalar field, the inverse total-space map of
`hp.characterFiniteRankCoreInvIso χ` is `C^n`. -/
theorem contMDiff_totalSpaceMap_characterFiniteRankCoreInvIso_inv [CompleteSpace 𝕜]
    (χ : G →* 𝕜ˣ) :
    ContMDiff (IB.prod 𝓘(𝕜, Fin (hp.characterFiniteRankCore χ⁻¹).rank → 𝕜))
      (IB.prod 𝓘(𝕜, Fin (hp.characterFiniteRankCore χ).dual.rank → 𝕜)) n
      (hp.characterFiniteRankCoreInvIso χ).inv.totalSpaceMap :=
  coe_characterFiniteRankCoreInvDiffeomorph_symm (hp := hp) (IB := IB) (n := n) χ ▸
    (hp.characterFiniteRankCoreInvDiffeomorph (IB := IB) (n := n) χ).symm.contMDiff

end Dual

section TensorPower

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} {n : ℕ∞ω}
  {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X] [ChartedSpace HB X]
  [Group G] [MulAction G E] {p : E → X} (hp : IsQuotientCoveringMap p G)

/-- The forward total-space map of `hp.characterFiniteRankCoreCongr h` is `C^n`. -/
theorem contMDiff_totalSpaceMap_characterFiniteRankCoreCongr_hom {χ ψ : G →* 𝕜ˣ}
    (h : χ = ψ) :
    ContMDiff (IB.prod 𝓘(𝕜, Fin (hp.characterFiniteRankCore χ).rank → 𝕜))
      (IB.prod 𝓘(𝕜, Fin (hp.characterFiniteRankCore ψ).rank → 𝕜)) n
      (hp.characterFiniteRankCoreCongr h).hom.totalSpaceMap := by
  subst h
  rw [characterFiniteRankCoreCongr_refl, Iso.refl_hom]
  have hid : (𝟙 (hp.characterFiniteRankCore χ) :
      hp.characterFiniteRankCore χ ⟶ hp.characterFiniteRankCore χ) =
      CoordinateHom.id (hp.characterFiniteRankCore χ).core :=
    FiniteRankBundleCore.hom_ext fun x ↦ by simp
  rw [hid]
  exact CoordinateHom.contMDiff_totalSpaceMap_id _

/-- The inverse total-space map of `hp.characterFiniteRankCoreCongr h` is `C^n`. -/
theorem contMDiff_totalSpaceMap_characterFiniteRankCoreCongr_inv {χ ψ : G →* 𝕜ˣ}
    (h : χ = ψ) :
    ContMDiff (IB.prod 𝓘(𝕜, Fin (hp.characterFiniteRankCore ψ).rank → 𝕜))
      (IB.prod 𝓘(𝕜, Fin (hp.characterFiniteRankCore χ).rank → 𝕜)) n
      (hp.characterFiniteRankCoreCongr h).inv.totalSpaceMap := by
  subst h
  rw [characterFiniteRankCoreCongr_refl, Iso.refl_inv]
  have hid : (𝟙 (hp.characterFiniteRankCore χ) :
      hp.characterFiniteRankCore χ ⟶ hp.characterFiniteRankCore χ) =
      CoordinateHom.id (hp.characterFiniteRankCore χ).core :=
    FiniteRankBundleCore.hom_ext fun x ↦ by simp
  rw [hid]
  exact CoordinateHom.contMDiff_totalSpaceMap_id _

/-- The forward total-space map of `hp.characterFiniteRankCoreOneIso` is `C^n`. -/
theorem contMDiff_totalSpaceMap_characterFiniteRankCoreOneIso_hom :
    ContMDiff (IB.prod 𝓘(𝕜, Fin (hp.characterFiniteRankCore (1 : G →* 𝕜ˣ)).rank → 𝕜))
      (IB.prod 𝓘(𝕜, Fin (𝟙_ (FiniteRankBundleCore 𝕜 X)).rank → 𝕜)) n
      (hp.characterFiniteRankCoreOneIso (𝕜 := 𝕜)).hom.totalSpaceMap := by
  let e : hp.characterFiniteRankCore (1 : G →* 𝕜ˣ) ≅ 𝟙_ (FiniteRankBundleCore 𝕜 X) :=
    isoTrivialOfCoordChangeEqId (hp.characterFiniteRankCore 1)
      (ContinuousLinearEquiv.refl 𝕜 (Fin 1 → 𝕜)) fun i j x _ _ ↦ by
        rw [characterFiniteRankCore_coordChange, MonoidHom.one_apply, Units.val_one, one_smul]
  have hhom : (hp.characterFiniteRankCoreOneIso (𝕜 := 𝕜)).hom = e.hom := by
    dsimp only [e]
    refine (FiniteRankBundleCore.hom_ext fun x ↦ ?_).symm
    exact (FiniteRankBundleCore.fiberMap_isoTrivialOfCoordChangeEqId_hom _ _ _ x).trans
      (hp.fiberMap_characterFiniteRankCoreOneIso_hom x).symm
  rw [hhom]
  exact contMDiff_totalSpaceMap_isoTrivialOfCoordChangeEqId_hom _ _ _

/-- The inverse total-space map of `hp.characterFiniteRankCoreOneIso` is `C^n`. -/
theorem contMDiff_totalSpaceMap_characterFiniteRankCoreOneIso_inv :
    ContMDiff (IB.prod 𝓘(𝕜, Fin (𝟙_ (FiniteRankBundleCore 𝕜 X)).rank → 𝕜))
      (IB.prod 𝓘(𝕜, Fin (hp.characterFiniteRankCore (1 : G →* 𝕜ˣ)).rank → 𝕜)) n
      (hp.characterFiniteRankCoreOneIso (𝕜 := 𝕜)).inv.totalSpaceMap := by
  let e : hp.characterFiniteRankCore (1 : G →* 𝕜ˣ) ≅ 𝟙_ (FiniteRankBundleCore 𝕜 X) :=
    isoTrivialOfCoordChangeEqId (hp.characterFiniteRankCore 1)
      (ContinuousLinearEquiv.refl 𝕜 (Fin 1 → 𝕜)) fun i j x _ _ ↦ by
        rw [characterFiniteRankCore_coordChange, MonoidHom.one_apply, Units.val_one, one_smul]
  have hinv : (hp.characterFiniteRankCoreOneIso (𝕜 := 𝕜)).inv = e.inv := by
    dsimp only [e]
    refine (FiniteRankBundleCore.hom_ext fun x ↦ ?_).symm
    exact (FiniteRankBundleCore.fiberMap_isoTrivialOfCoordChangeEqId_inv _ _ _ x).trans
      (hp.fiberMap_characterFiniteRankCoreOneIso_inv x).symm
  rw [hinv]
  exact contMDiff_totalSpaceMap_isoTrivialOfCoordChangeEqId_inv _ _ _

/-- The `C^n` bundle equivalence identifying `hp.characterFiniteRankCore 1` with the monoidal
unit `𝟙_ (FiniteRankBundleCore 𝕜 X)` over the identity of `X`. -/
noncomputable def characterFiniteRankCoreOneDiffeomorph :
    (hp.characterFiniteRankCore (1 : G →* 𝕜ˣ)).core.TotalSpace ≃ₘ^n⟮
      IB.prod 𝓘(𝕜, Fin (hp.characterFiniteRankCore (1 : G →* 𝕜ˣ)).rank → 𝕜),
      IB.prod 𝓘(𝕜, Fin (𝟙_ (FiniteRankBundleCore 𝕜 X)).rank → 𝕜)⟯
    (𝟙_ (FiniteRankBundleCore 𝕜 X)).core.TotalSpace :=
  isoToDiffeomorph (hp.characterFiniteRankCoreOneIso (𝕜 := 𝕜))
    (hp.contMDiff_totalSpaceMap_characterFiniteRankCoreOneIso_hom (IB := IB) (n := n))
    (hp.contMDiff_totalSpaceMap_characterFiniteRankCoreOneIso_inv (IB := IB) (n := n))

@[simp] theorem coe_characterFiniteRankCoreOneDiffeomorph :
    ⇑(hp.characterFiniteRankCoreOneDiffeomorph (𝕜 := 𝕜) (IB := IB) (n := n)) =
      (hp.characterFiniteRankCoreOneIso (𝕜 := 𝕜)).hom.totalSpaceMap :=
  coe_isoToDiffeomorph _ _ _

@[simp] theorem coe_characterFiniteRankCoreOneDiffeomorph_symm :
    ⇑(hp.characterFiniteRankCoreOneDiffeomorph (𝕜 := 𝕜) (IB := IB) (n := n)).symm =
      (hp.characterFiniteRankCoreOneIso (𝕜 := 𝕜)).inv.totalSpaceMap :=
  coe_isoToDiffeomorph_symm _ _ _

/-- The forward total-space map of `hp.characterFiniteRankCoreMulIso χ ψ` is `C^n`. -/
theorem contMDiff_totalSpaceMap_characterFiniteRankCoreMulIso_hom (χ ψ : G →* 𝕜ˣ) :
    ContMDiff
      (IB.prod 𝓘(𝕜, Fin (hp.characterFiniteRankCore χ ⊗
        hp.characterFiniteRankCore ψ).rank → 𝕜))
      (IB.prod 𝓘(𝕜, Fin (hp.characterFiniteRankCore (χ * ψ)).rank → 𝕜)) n
      (hp.characterFiniteRankCoreMulIso χ ψ).hom.totalSpaceMap := by
  let Φ := constIsoDiffeomorph (I := IB) (n := n)
    (A := hp.characterFiniteRankCore χ ⊗ hp.characterFiniteRankCore ψ)
    (D := hp.characterFiniteRankCore (χ * ψ))
    (fun _ ↦ Set.inter_self _) (hp.characterMulFiberEquiv χ ψ)
    fun i j x _ _ ↦ hp.characterFiniteRankCore_mul_intertwine χ ψ i j x
  let e := constIso (A := hp.characterFiniteRankCore χ ⊗ hp.characterFiniteRankCore ψ)
    (D := hp.characterFiniteRankCore (χ * ψ))
    (fun _ ↦ Set.inter_self _) (hp.characterMulFiberEquiv χ ψ)
    fun i j x _ _ ↦ hp.characterFiniteRankCore_mul_intertwine χ ψ i j x
  have hhom : (hp.characterFiniteRankCoreMulIso χ ψ).hom = e.hom := by
    dsimp only [e]
    exact (FiniteRankBundleCore.hom_ext fun x ↦
      (FiniteRankBundleCore.fiberMap_constIso_hom _ _ _ x).trans
        (hp.fiberMap_characterFiniteRankCoreMulIso_hom χ ψ x).symm).symm
  rw [hhom]
  exact (coe_constIsoDiffeomorph (I := IB) (n := n) (A := hp.characterFiniteRankCore χ ⊗
      hp.characterFiniteRankCore ψ) (D := hp.characterFiniteRankCore (χ * ψ))
    (fun _ ↦ Set.inter_self _) (hp.characterMulFiberEquiv χ ψ) _).symm ▸ Φ.contMDiff

/-- The inverse total-space map of `hp.characterFiniteRankCoreMulIso χ ψ` is `C^n`. -/
theorem contMDiff_totalSpaceMap_characterFiniteRankCoreMulIso_inv (χ ψ : G →* 𝕜ˣ) :
    ContMDiff (IB.prod 𝓘(𝕜, Fin (hp.characterFiniteRankCore (χ * ψ)).rank → 𝕜))
      (IB.prod 𝓘(𝕜, Fin (hp.characterFiniteRankCore χ ⊗
        hp.characterFiniteRankCore ψ).rank → 𝕜)) n
      (hp.characterFiniteRankCoreMulIso χ ψ).inv.totalSpaceMap := by
  let Φ := constIsoDiffeomorph (I := IB) (n := n)
    (A := hp.characterFiniteRankCore χ ⊗ hp.characterFiniteRankCore ψ)
    (D := hp.characterFiniteRankCore (χ * ψ))
    (fun _ ↦ Set.inter_self _) (hp.characterMulFiberEquiv χ ψ)
    fun i j x _ _ ↦ hp.characterFiniteRankCore_mul_intertwine χ ψ i j x
  let e := constIso (A := hp.characterFiniteRankCore χ ⊗ hp.characterFiniteRankCore ψ)
    (D := hp.characterFiniteRankCore (χ * ψ))
    (fun _ ↦ Set.inter_self _) (hp.characterMulFiberEquiv χ ψ)
    fun i j x _ _ ↦ hp.characterFiniteRankCore_mul_intertwine χ ψ i j x
  have hinv : (hp.characterFiniteRankCoreMulIso χ ψ).inv = e.inv := by
    dsimp only [e]
    exact (FiniteRankBundleCore.hom_ext fun x ↦
      (FiniteRankBundleCore.fiberMap_constIso_inv _ _ _ x).trans
        (hp.fiberMap_characterFiniteRankCoreMulIso_inv χ ψ x).symm).symm
  rw [hinv]
  exact (coe_constIsoDiffeomorph_symm (I := IB) (n := n) (A := hp.characterFiniteRankCore χ ⊗
      hp.characterFiniteRankCore ψ) (D := hp.characterFiniteRankCore (χ * ψ))
    (fun _ ↦ Set.inter_self _) (hp.characterMulFiberEquiv χ ψ) _).symm ▸ Φ.symm.contMDiff

/-- The `C^n` bundle equivalence identifying
`(hp.characterFiniteRankCore χ ⊗ hp.characterFiniteRankCore ψ).core.TotalSpace` with
`(hp.characterFiniteRankCore (χ * ψ)).core.TotalSpace` over the identity of `X`. -/
noncomputable def characterFiniteRankCoreMulDiffeomorph (χ ψ : G →* 𝕜ˣ) :
    (hp.characterFiniteRankCore χ ⊗ hp.characterFiniteRankCore ψ).core.TotalSpace ≃ₘ^n⟮
      IB.prod 𝓘(𝕜, Fin (hp.characterFiniteRankCore χ ⊗
        hp.characterFiniteRankCore ψ).rank → 𝕜),
      IB.prod 𝓘(𝕜, Fin (hp.characterFiniteRankCore (χ * ψ)).rank → 𝕜)⟯
    (hp.characterFiniteRankCore (χ * ψ)).core.TotalSpace :=
  isoToDiffeomorph (hp.characterFiniteRankCoreMulIso χ ψ)
    (hp.contMDiff_totalSpaceMap_characterFiniteRankCoreMulIso_hom (IB := IB) (n := n) χ ψ)
    (hp.contMDiff_totalSpaceMap_characterFiniteRankCoreMulIso_inv (IB := IB) (n := n) χ ψ)

@[simp] theorem coe_characterFiniteRankCoreMulDiffeomorph (χ ψ : G →* 𝕜ˣ) :
    ⇑(hp.characterFiniteRankCoreMulDiffeomorph (IB := IB) (n := n) χ ψ) =
      (hp.characterFiniteRankCoreMulIso χ ψ).hom.totalSpaceMap :=
  coe_isoToDiffeomorph _ _ _

@[simp] theorem coe_characterFiniteRankCoreMulDiffeomorph_symm (χ ψ : G →* 𝕜ˣ) :
    ⇑(hp.characterFiniteRankCoreMulDiffeomorph (IB := IB) (n := n) χ ψ).symm =
      (hp.characterFiniteRankCoreMulIso χ ψ).inv.totalSpaceMap :=
  coe_isoToDiffeomorph_symm _ _ _

/-- The forward total-space map of `hp.characterFiniteRankCoreTensorPowerIso χ m` is `C^n`. -/
theorem contMDiff_totalSpaceMap_characterFiniteRankCoreTensorPowerIso_hom (χ : G →* 𝕜ˣ) :
    ∀ m : ℕ,
      ContMDiff (IB.prod 𝓘(𝕜, Fin (tensorPow (hp.characterFiniteRankCore χ) m).rank → 𝕜))
        (IB.prod 𝓘(𝕜, Fin (hp.characterFiniteRankCore (χ ^ m)).rank → 𝕜)) n
        (hp.characterFiniteRankCoreTensorPowerIso χ m).hom.totalSpaceMap
  | 0 => by
    have hcomp {A D C : FiniteRankBundleCore 𝕜 X} (f : A ⟶ D) (g : D ⟶ C) :
        f ≫ g = g.comp f :=
      FiniteRankBundleCore.hom_ext fun x ↦ by simp
    have h1 := hp.contMDiff_totalSpaceMap_characterFiniteRankCoreOneIso_inv (IB := IB) (n := n)
    have h2 := hp.contMDiff_totalSpaceMap_characterFiniteRankCoreCongr_hom (IB := IB) (n := n)
      (pow_zero χ).symm
    rw [characterFiniteRankCoreTensorPowerIso_zero, Iso.trans_hom, Iso.symm_hom, hcomp]
    exact CoordinateHom.contMDiff_totalSpaceMap_comp h2 h1
  | m + 1 => by
    have hcomp {A D C : FiniteRankBundleCore 𝕜 X} (f : A ⟶ D) (g : D ⟶ C) :
        f ≫ g = g.comp f :=
      FiniteRankBundleCore.hom_ext fun x ↦ by simp
    have ih := contMDiff_totalSpaceMap_characterFiniteRankCoreTensorPowerIso_hom χ m
    have hmul := hp.contMDiff_totalSpaceMap_characterFiniteRankCoreMulIso_hom (IB := IB) (n := n)
      χ (χ ^ m)
    have hcongr := hp.contMDiff_totalSpaceMap_characterFiniteRankCoreCongr_hom (IB := IB) (n := n)
      (pow_succ' χ m).symm
    have htensor_hom : ContMDiff
        (IB.prod 𝓘(𝕜, Fin (hp.characterFiniteRankCore χ ⊗
          tensorPow (hp.characterFiniteRankCore χ) m).rank → 𝕜))
        (IB.prod 𝓘(𝕜, Fin (hp.characterFiniteRankCore χ ⊗
          hp.characterFiniteRankCore (χ ^ m)).rank → 𝕜)) n
        ((𝟙 (hp.characterFiniteRankCore χ)) ⊗ₘ
          (hp.characterFiniteRankCoreTensorPowerIso χ m).hom).totalSpaceMap :=
      contMDiff_totalSpaceMap_monoidalTensorHom _ _
        (CoordinateHom.contMDiff_totalSpaceMap_id _) ih
    rw [characterFiniteRankCoreTensorPowerIso_succ, Iso.trans_hom, Iso.trans_hom, tensorIso_hom,
      Iso.refl_hom, hcomp, hcomp]
    exact CoordinateHom.contMDiff_totalSpaceMap_comp
      (CoordinateHom.contMDiff_totalSpaceMap_comp hcongr hmul) htensor_hom

/-- The inverse total-space map of `hp.characterFiniteRankCoreTensorPowerIso χ m` is `C^n`. -/
theorem contMDiff_totalSpaceMap_characterFiniteRankCoreTensorPowerIso_inv (χ : G →* 𝕜ˣ) :
    ∀ m : ℕ,
      ContMDiff (IB.prod 𝓘(𝕜, Fin (hp.characterFiniteRankCore (χ ^ m)).rank → 𝕜))
        (IB.prod 𝓘(𝕜, Fin (tensorPow (hp.characterFiniteRankCore χ) m).rank → 𝕜)) n
        (hp.characterFiniteRankCoreTensorPowerIso χ m).inv.totalSpaceMap
  | 0 => by
    have hcomp {A D C : FiniteRankBundleCore 𝕜 X} (f : A ⟶ D) (g : D ⟶ C) :
        f ≫ g = g.comp f :=
      FiniteRankBundleCore.hom_ext fun x ↦ by simp
    have h1 := hp.contMDiff_totalSpaceMap_characterFiniteRankCoreOneIso_hom (IB := IB) (n := n)
    have h2 := hp.contMDiff_totalSpaceMap_characterFiniteRankCoreCongr_inv (IB := IB) (n := n)
      (pow_zero χ).symm
    rw [characterFiniteRankCoreTensorPowerIso_zero, Iso.trans_inv, Iso.symm_inv, hcomp]
    exact CoordinateHom.contMDiff_totalSpaceMap_comp h1 h2
  | m + 1 => by
    have hcomp {A D C : FiniteRankBundleCore 𝕜 X} (f : A ⟶ D) (g : D ⟶ C) :
        f ≫ g = g.comp f :=
      FiniteRankBundleCore.hom_ext fun x ↦ by simp
    have ih := contMDiff_totalSpaceMap_characterFiniteRankCoreTensorPowerIso_inv χ m
    have hmul := hp.contMDiff_totalSpaceMap_characterFiniteRankCoreMulIso_inv (IB := IB) (n := n)
      χ (χ ^ m)
    have hcongr := hp.contMDiff_totalSpaceMap_characterFiniteRankCoreCongr_inv (IB := IB) (n := n)
      (pow_succ' χ m).symm
    have htensor_inv : ContMDiff
        (IB.prod 𝓘(𝕜, Fin (hp.characterFiniteRankCore χ ⊗
          hp.characterFiniteRankCore (χ ^ m)).rank → 𝕜))
        (IB.prod 𝓘(𝕜, Fin (hp.characterFiniteRankCore χ ⊗
          tensorPow (hp.characterFiniteRankCore χ) m).rank → 𝕜)) n
        ((𝟙 (hp.characterFiniteRankCore χ)) ⊗ₘ
          (hp.characterFiniteRankCoreTensorPowerIso χ m).inv).totalSpaceMap :=
      contMDiff_totalSpaceMap_monoidalTensorHom _ _
        (CoordinateHom.contMDiff_totalSpaceMap_id _) ih
    rw [characterFiniteRankCoreTensorPowerIso_succ, Iso.trans_inv, Iso.trans_inv, tensorIso_inv,
      Iso.refl_inv, hcomp, hcomp]
    exact CoordinateHom.contMDiff_totalSpaceMap_comp
      htensor_inv (CoordinateHom.contMDiff_totalSpaceMap_comp hmul hcongr)

/-- The `C^n` bundle equivalence identifying
`(tensorPow (hp.characterFiniteRankCore χ) m).core.TotalSpace` with
`(hp.characterFiniteRankCore (χ ^ m)).core.TotalSpace` over the identity of `X`. -/
noncomputable def characterFiniteRankCoreTensorPowerDiffeomorph (χ : G →* 𝕜ˣ) (m : ℕ) :
    (tensorPow (hp.characterFiniteRankCore χ) m).core.TotalSpace ≃ₘ^n⟮
      IB.prod 𝓘(𝕜, Fin (tensorPow (hp.characterFiniteRankCore χ) m).rank → 𝕜),
      IB.prod 𝓘(𝕜, Fin (hp.characterFiniteRankCore (χ ^ m)).rank → 𝕜)⟯
    (hp.characterFiniteRankCore (χ ^ m)).core.TotalSpace :=
  isoToDiffeomorph (hp.characterFiniteRankCoreTensorPowerIso χ m)
    (hp.contMDiff_totalSpaceMap_characterFiniteRankCoreTensorPowerIso_hom (IB := IB) (n := n) χ m)
    (hp.contMDiff_totalSpaceMap_characterFiniteRankCoreTensorPowerIso_inv (IB := IB) (n := n) χ m)

@[simp] theorem coe_characterFiniteRankCoreTensorPowerDiffeomorph (χ : G →* 𝕜ˣ) (m : ℕ) :
    ⇑(hp.characterFiniteRankCoreTensorPowerDiffeomorph (IB := IB) (n := n) χ m) =
      (hp.characterFiniteRankCoreTensorPowerIso χ m).hom.totalSpaceMap :=
  coe_isoToDiffeomorph _ _ _

@[simp] theorem coe_characterFiniteRankCoreTensorPowerDiffeomorph_symm (χ : G →* 𝕜ˣ) (m : ℕ) :
    ⇑(hp.characterFiniteRankCoreTensorPowerDiffeomorph (IB := IB) (n := n) χ m).symm =
      (hp.characterFiniteRankCoreTensorPowerIso χ m).inv.totalSpaceMap :=
  coe_isoToDiffeomorph_symm _ _ _

variable [CompleteSpace 𝕜]

/-- The `m`-th tensor power `tensorPow (hp.characterFiniteRankCore χ) m` admits a global compatible
`C^n` trivialization if and only if `hp.characterCore (χ ^ m)` does. -/
theorem exists_trivialization_baseSet_eq_univ_tensorPow_characterFiniteRankCore_iff
    (χ : G →* 𝕜ˣ) (m : ℕ) :
    (∃ (e : Trivialization (Fin (tensorPow (hp.characterFiniteRankCore χ) m).rank → 𝕜)
        (π _ (tensorPow (hp.characterFiniteRankCore χ) m).core.Fiber)) (_ : e.IsLinear 𝕜),
        e.toOpenPartialHomeomorph ∈
          (contMDiffFiberwiseLinear X (Fin (tensorPow (hp.characterFiniteRankCore χ) m).rank → 𝕜)
            IB n).maximalAtlas
            (TotalSpace _ (tensorPow (hp.characterFiniteRankCore χ) m).core.Fiber) ∧
          e.baseSet = univ) ↔
      ∃ (e : Trivialization 𝕜 (π 𝕜 (hp.characterCore (χ ^ m)).Fiber)) (_ : e.IsLinear 𝕜),
        e.toOpenPartialHomeomorph ∈
          (contMDiffFiberwiseLinear X 𝕜 IB n).maximalAtlas
            (TotalSpace 𝕜 (hp.characterCore (χ ^ m)).Fiber) ∧
          e.baseSet = univ := by
  have htriv := CoordinateHom.exists_trivialization_baseSet_eq_univ_iff_of_inv
    (by simp) (by simp)
    (hp.characterFiniteRankCoreTensorPowerIso χ m).hom
    (hp.characterFiniteRankCoreTensorPowerIso χ m).inv
    (hp.characterFiniteRankCoreTensorPowerIso χ m).hom_inv_id
    (hp.characterFiniteRankCoreTensorPowerIso χ m).inv_hom_id
    (hp.contMDiff_totalSpaceMap_characterFiniteRankCoreTensorPowerIso_hom (IB := IB) (n := n) χ m)
    (hp.contMDiff_totalSpaceMap_characterFiniteRankCoreTensorPowerIso_inv (IB := IB) (n := n) χ m)
  exact htriv.trans
    (hp.exists_trivialization_baseSet_eq_univ_characterFiniteRankCore_iff IB n (χ ^ m))

/-- Whenever `orderOf χ ∣ m`, the `m`-th tensor power `tensorPow (hp.characterFiniteRankCore χ) m`
admits a global compatible `C^n` trivialization over `X`. -/
theorem exists_trivialization_baseSet_eq_univ_tensorPow_characterFiniteRankCore_of_orderOf_dvd
    {χ : G →* 𝕜ˣ} {m : ℕ} (hdvd : orderOf χ ∣ m) :
    ∃ (e : Trivialization (Fin (tensorPow (hp.characterFiniteRankCore χ) m).rank → 𝕜)
      (π _ (tensorPow (hp.characterFiniteRankCore χ) m).core.Fiber)) (_ : e.IsLinear 𝕜),
      e.toOpenPartialHomeomorph ∈
        (contMDiffFiberwiseLinear X (Fin (tensorPow (hp.characterFiniteRankCore χ) m).rank → 𝕜)
          IB n).maximalAtlas
          (TotalSpace _ (tensorPow (hp.characterFiniteRankCore χ) m).core.Fiber) ∧
        e.baseSet = univ := by
  rw [hp.exists_trivialization_baseSet_eq_univ_tensorPow_characterFiniteRankCore_iff,
    orderOf_dvd_iff_pow_eq_one.1 hdvd]
  exact hp.exists_trivialization_baseSet_eq_univ_characterCore_one

/-- For every character `χ`, the `orderOf χ`-th tensor power
`tensorPow (hp.characterFiniteRankCore χ) (orderOf χ)` admits a global compatible `C^n`
trivialization. -/
theorem exists_trivialization_baseSet_eq_univ_tensorPow_characterFiniteRankCore_orderOf
    (χ : G →* 𝕜ˣ) :
    ∃ (e : Trivialization (Fin (tensorPow (hp.characterFiniteRankCore χ) (orderOf χ)).rank → 𝕜)
      (π _ (tensorPow (hp.characterFiniteRankCore χ) (orderOf χ)).core.Fiber)) (_ : e.IsLinear 𝕜),
      e.toOpenPartialHomeomorph ∈
        (contMDiffFiberwiseLinear X
          (Fin (tensorPow (hp.characterFiniteRankCore χ) (orderOf χ)).rank → 𝕜)
          IB n).maximalAtlas
          (TotalSpace _ (tensorPow (hp.characterFiniteRankCore χ) (orderOf χ)).core.Fiber) ∧
        e.baseSet = univ :=
  hp.exists_trivialization_baseSet_eq_univ_tensorPow_characterFiniteRankCore_of_orderOf_dvd dvd_rfl

/-- For every character `χ : G →* 𝕜ˣ`, the `Nat.card G`-th tensor power
`tensorPow (hp.characterFiniteRankCore χ) (Nat.card G)` admits a global compatible `C^n`
trivialization; for a finite deck group `G` of order `N = Nat.card G`, every character line bundle
has `N`-torsion tensor power. -/
theorem exists_trivialization_baseSet_eq_univ_tensorPow_characterFiniteRankCore_natCard
    (χ : G →* 𝕜ˣ) :
    ∃ (e : Trivialization (Fin (tensorPow (hp.characterFiniteRankCore χ) (Nat.card G)).rank → 𝕜)
      (π _ (tensorPow (hp.characterFiniteRankCore χ) (Nat.card G)).core.Fiber)) (_ : e.IsLinear 𝕜),
      e.toOpenPartialHomeomorph ∈
        (contMDiffFiberwiseLinear X
          (Fin (tensorPow (hp.characterFiniteRankCore χ) (Nat.card G)).rank → 𝕜)
          IB n).maximalAtlas
          (TotalSpace _ (tensorPow (hp.characterFiniteRankCore χ) (Nat.card G)).core.Fiber) ∧
        e.baseSet = univ := by
  refine hp.exists_trivialization_baseSet_eq_univ_tensorPow_characterFiniteRankCore_of_orderOf_dvd
    (orderOf_dvd_iff_pow_eq_one.2 ?_)
  ext g
  simp [← map_pow, pow_card_eq_one']

end TensorPower

section ComplexCompact

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℂ EM] {HM : Type*} [TopologicalSpace HM]
  {I : ModelWithCorners ℂ EM HM} [I.Boundaryless]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℂ EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners ℂ EB HB} {n : ℕ∞ω}
  {E X G : Type*} [TopologicalSpace E] [ChartedSpace HM E] [IsManifold I 1 E] [CompactSpace E]
  [TopologicalSpace X] [ChartedSpace HB X]
  [Group G] [MulAction G E] {p : E → X} (hp : IsQuotientCoveringMap p G)
  (hpd : MDifferentiable I IB p) (hn : n ≠ 0)
include hpd hn

/-- When `E` is a compact connected complex manifold and `p : E → X` is differentiable (`n ≠ 0`),
the `m`-th tensor power `tensorPow (hp.characterFiniteRankCore χ) m` admits a global compatible
`C^n` trivialization if and only if `orderOf χ ∣ m`. -/
theorem exists_trivialization_baseSet_eq_univ_tensorPow_characterFiniteRankCore_iff_orderOf_dvd
    [ConnectedSpace E] (χ : G →* ℂˣ) (m : ℕ) :
    (∃ (e : Trivialization (Fin (tensorPow (hp.characterFiniteRankCore χ) m).rank → ℂ)
        (π _ (tensorPow (hp.characterFiniteRankCore χ) m).core.Fiber)) (_ : e.IsLinear ℂ),
        e.toOpenPartialHomeomorph ∈
          (contMDiffFiberwiseLinear X (Fin (tensorPow (hp.characterFiniteRankCore χ) m).rank → ℂ)
            IB n).maximalAtlas
            (TotalSpace _ (tensorPow (hp.characterFiniteRankCore χ) m).core.Fiber) ∧
          e.baseSet = univ) ↔
      orderOf χ ∣ m :=
  (hp.exists_trivialization_baseSet_eq_univ_tensorPow_characterFiniteRankCore_iff χ m).trans
    ((hp.exists_trivialization_baseSet_eq_univ_characterCore_iff_eq_one hpd hn (χ ^ m)).trans
      (orderOf_dvd_iff_pow_eq_one (x := χ)).symm)

/-- When `E` is a compact connected complex manifold, `p : E → X` is differentiable (`n ≠ 0`), and
`χ : G →* ℂˣ` has finite order, the exact order of `hp.characterFiniteRankCore χ` under `tensorPow`
is `orderOf χ`. -/
theorem isLeast_pos_trivialization_tensorPow_characterFiniteRankCore
    [ConnectedSpace E] {χ : G →* ℂˣ} (hχ : IsOfFinOrder χ) :
    IsLeast {m : ℕ | 0 < m ∧
      ∃ (e : Trivialization (Fin (tensorPow (hp.characterFiniteRankCore χ) m).rank → ℂ)
        (π _ (tensorPow (hp.characterFiniteRankCore χ) m).core.Fiber)) (_ : e.IsLinear ℂ),
        e.toOpenPartialHomeomorph ∈
          (contMDiffFiberwiseLinear X (Fin (tensorPow (hp.characterFiniteRankCore χ) m).rank → ℂ)
            IB n).maximalAtlas
            (TotalSpace _ (tensorPow (hp.characterFiniteRankCore χ) m).core.Fiber) ∧
          e.baseSet = univ} (orderOf χ) :=
  ⟨⟨hχ.orderOf_pos,
    hp.exists_trivialization_baseSet_eq_univ_tensorPow_characterFiniteRankCore_orderOf χ⟩,
    fun _ hm ↦ Nat.le_of_dvd hm.1 <|
      (hp.exists_trivialization_baseSet_eq_univ_tensorPow_characterFiniteRankCore_iff_orderOf_dvd
        hpd hn χ _).1 hm.2⟩

end ComplexCompact

end IsQuotientCoveringMap
