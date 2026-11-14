/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Quotient.AssociatedBundle
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.Monoidal
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.Dual
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.Scalar
public import TauCeti.Topology.Covering.CharacterBundle
public import TauCeti.Geometry.Manifold.Complex.Compact
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Smooth and holomorphic monoidal algebra and tensor order of character line bundles

Let `p : E → X` be a quotient covering map for a group `G` (`IsQuotientCoveringMap p G`) over a
charted space `X`. For every character `χ : G →* 𝕜ˣ`, both the `E`-indexed scalar line-bundle core
`IsQuotientCoveringMap.characterCore χ` and its point-indexed rank-one presentation
`IsQuotientCoveringMap.characterFiniteRankCore χ` in `FiniteRankBundleCore 𝕜 X` are `C^n` vector
bundles for every model and every regularity `n`, and the topological monoidal identifications from
`TauCeti.Topology.Covering.CharacterBundle` refine to `C^n` bundle equivalences over `X`:

* `IsQuotientCoveringMap.characterFiniteRankCoreDiffeomorph`: `C^n` bundle equivalence between
  `(hp.characterFiniteRankCore χ).core` and `hp.characterCore χ`;
* `IsQuotientCoveringMap.characterFiniteRankCoreOneDiffeomorph`,
  `IsQuotientCoveringMap.characterFiniteRankCoreMulDiffeomorph`,
  `IsQuotientCoveringMap.characterFiniteRankCoreInvDiffeomorph`, and
  `IsQuotientCoveringMap.characterFiniteRankCorePowDiffeomorph`: `C^n` bundle equivalences
  realizing `L_1 ≃ 𝟙`, `L_{χ₁} ⊗ L_{χ₂} ≃ L_{χ₁ * χ₂}`, `L_χ∨ ≃ L_{χ⁻¹}`, and
  `L_χ^{⊗ m} ≃ L_{χ ^ m}` (holomorphic over `𝓘(ℂ, EB)` at regularity `∞`).

Over a complete scalar field, twisting cocycle morphisms by `χ₁⁻¹` shows that `hp.characterCore χ₁`
and `hp.characterCore χ₂` are `C^n` bundle-equivalent if and only if
`hp.characterCore (χ₁⁻¹ * χ₂)` admits a global compatible `C^n` trivialization
(`IsQuotientCoveringMap.exists_bundleDiffeomorph_characterCore_iff_exists_trivialization`), and
when `p` is a `C^n` local diffeomorphism this is equivalent to the existence of a
nowhere-vanishing `(χ₁⁻¹ * χ₂)`-equivariant `C^n` function on `E`
(`IsQuotientCoveringMap.exists_bundleDiffeomorph_characterCore_iff`). Likewise, the `m`-th tensor
power `tensorPow (hp.characterFiniteRankCore χ) m` is globally `C^n`-trivial whenever
`orderOf χ ∣ m` (via `IsQuotientCoveringMap`'s
`exists_trivialization_baseSet_eq_univ_tensorPow_characterFiniteRankCore_of_orderOf_dvd`),
in particular at `m = orderOf χ` and `m = Nat.card G`.

When `E` is a nonempty compact connected complex manifold (for instance, in a finite unramified
covering of a compact complex manifold such as a Hopf manifold or Enriques surface), every
holomorphic function on `E` is constant, so a nontrivial character admits no nonzero equivariant
holomorphic function (`MDifferentiable.eq_zero_of_smul_eq_mul_of_ne_one`). Consequently,
`hp.characterCore χ` is holomorphically trivial if and only if `χ = 1`
(`IsQuotientCoveringMap.exists_trivialization_baseSet_eq_univ_characterCore_iff_eq_one`), two
character line bundles are holomorphically isomorphic if and only if their characters are equal
(`IsQuotientCoveringMap.exists_bundleDiffeomorph_characterCore_iff_eq`), and for a
finite-order character `χ` the exact order of `hp.characterFiniteRankCore χ` under `tensorPow` is
`orderOf χ`
(`IsQuotientCoveringMap.isLeast_pos_trivialization_tensorPow_characterFiniteRankCore`).

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, Section 2.2.
* Phillip Griffiths and Joseph Harris, *Principles of Algebraic Geometry*, Wiley, 1978,
  Chapter 1, §2.
* Wolf P. Barth, Klaus Hulek, Chris A. M. Peters, and Antonius Van de Ven, *Compact Complex
  Surfaces*, 2nd ed., Springer, 2004, Chapter I, §15 (torsion line bundles from unramified
  coverings).
-/

public section

open Bundle CategoryTheory ContinuousLinearEquiv MonoidalCategory Module Set TauCeti
  TauCeti.FiniteRankBundleCore Topology VectorBundleCore
open scoped Manifold ContDiff

namespace MDifferentiable

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℂ EM] {HM : Type*} [TopologicalSpace HM]
  {I : ModelWithCorners ℂ EM HM} [I.Boundaryless]
  {E G : Type*} [TopologicalSpace E] [ChartedSpace HM E] [IsManifold I 1 E]
  [CompactSpace E] [PreconnectedSpace E] [Group G] [MulAction G E]

/-- On a compact connected complex manifold, a holomorphic function `f : E → ℂ` that transforms by
a nontrivial character `χ : G →* ℂˣ` under a group action vanishes identically. -/
theorem eq_zero_of_smul_eq_mul_of_ne_one {f : E → ℂ} (hf : MDifferentiable I 𝓘(ℂ) f)
    {χ : G →* ℂˣ} (hfG : ∀ (g : G) (y : E), f (g • y) = χ g * f y) (hχ : χ ≠ 1) :
    f = 0 := by
  funext y
  obtain ⟨g, hg⟩ : ∃ g, χ g ≠ 1 := by
    by_contra! h
    exact hχ (MonoidHom.ext h)
  have hconst : f y = (χ g : ℂ) * f y :=
    (hf.apply_eq_of_compactSpace y (g • y)).trans (hfG g y)
  have hsub : ((χ g : ℂ) - 1) * f y = 0 := by
    rw [sub_mul, one_mul, sub_eq_zero]
    exact hconst.symm
  exact (mul_eq_zero.1 hsub).resolve_left (sub_ne_zero.2 <| Units.val_eq_one.not.2 hg)

end MDifferentiable

namespace IsQuotientCoveringMap

section RegularityAndMonoidal

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB}
  {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X] [ChartedSpace HB X]
  [Group G] [MulAction G E] {p : E → X} (hp : IsQuotientCoveringMap p G) {n : ℕ∞ω}

/-- The scalar line-bundle core of a deck-group character has locally constant transitions, so it
is `C^n` for every model of the base and every regularity. -/
instance isContMDiff_characterCore (χ : G →* 𝕜ˣ) : (hp.characterCore χ).IsContMDiff IB n := by
  rw [characterCore_def]
  infer_instance

/-- The point-indexed rank-one presentation `hp.characterFiniteRankCore χ` is `C^n` for every model
of the base and every regularity. -/
instance isContMDiff_characterFiniteRankCore (χ : G →* 𝕜ˣ) :
    (hp.characterFiniteRankCore χ).core.IsContMDiff IB n :=
  inferInstanceAs ((ofScalarCore (hp.characterCore χ)).core.IsContMDiff IB n)

/-- The `C^n` bundle equivalence identifying `(hp.characterFiniteRankCore χ).core` with
`hp.characterCore χ` over the identity of `X`, without completeness assumptions on `𝕜`. -/
noncomputable def characterFiniteRankCoreDiffeomorph (χ : G →* 𝕜ˣ) :
    (hp.characterFiniteRankCore χ).core.TotalSpace ≃ₘ^n⟮
      IB.prod 𝓘(𝕜, Fin (hp.characterFiniteRankCore χ).rank → 𝕜), IB.prod 𝓘(𝕜)⟯
    (hp.characterCore χ).TotalSpace :=
  ofScalarCoreDiffeomorph (hp.characterCore χ)

@[simp]
theorem coe_characterFiniteRankCoreDiffeomorph (χ : G →* 𝕜ˣ) :
    ⇑(hp.characterFiniteRankCoreDiffeomorph (IB := IB) (n := n) χ) =
      (toScalarCore (hp.characterCore χ)).totalSpaceMap :=
  coe_ofScalarCoreDiffeomorph (hp.characterCore χ)

@[simp]
theorem coe_characterFiniteRankCoreDiffeomorph_symm (χ : G →* 𝕜ˣ) :
    ⇑(hp.characterFiniteRankCoreDiffeomorph (IB := IB) (n := n) χ).symm =
      (fromScalarCore (hp.characterCore χ)).totalSpaceMap :=
  coe_ofScalarCoreDiffeomorph_symm (hp.characterCore χ)

@[simp]
theorem characterFiniteRankCoreDiffeomorph_toHomeomorph (χ : G →* 𝕜ˣ) :
    (hp.characterFiniteRankCoreDiffeomorph (IB := IB) (n := n) χ).toHomeomorph =
      hp.characterFiniteRankCoreHomeomorph χ := by
  apply Homeomorph.ext
  intro p
  change ⇑(hp.characterFiniteRankCoreDiffeomorph (IB := IB) (n := n) χ) p =
    ⇑(hp.characterFiniteRankCoreHomeomorph χ) p
  rw [hp.coe_characterFiniteRankCoreDiffeomorph, hp.coe_characterFiniteRankCoreHomeomorph]

variable (𝕜) in
/-- The `C^n` bundle equivalence identifying `hp.characterFiniteRankCore 1` with the monoidal unit
`𝟙_ (FiniteRankBundleCore 𝕜 X)`, without completeness assumptions on `𝕜`. -/
noncomputable def characterFiniteRankCoreOneDiffeomorph :
    (hp.characterFiniteRankCore (1 : G →* 𝕜ˣ)).core.TotalSpace ≃ₘ^n⟮
      IB.prod 𝓘(𝕜, Fin (hp.characterFiniteRankCore (1 : G →* 𝕜ˣ)).rank → 𝕜),
      IB.prod 𝓘(𝕜, Fin (𝟙_ (FiniteRankBundleCore 𝕜 X)).rank → 𝕜)⟯
    (𝟙_ (FiniteRankBundleCore 𝕜 X)).core.TotalSpace :=
  diffeomorphTrivialOfCoordChangeEqId (hp.characterFiniteRankCore (1 : G →* 𝕜ˣ))
    fun i j x _ _ ↦ hp.coordChange_characterFiniteRankCore_one i j x

@[simp]
theorem coe_characterFiniteRankCoreOneDiffeomorph :
    ⇑(hp.characterFiniteRankCoreOneDiffeomorph (IB := IB) (n := n) 𝕜) =
      (hp.characterFiniteRankCoreOneIso 𝕜).hom.totalSpaceMap :=
  (coe_diffeomorphTrivialOfCoordChangeEqId _ _).trans <|
    congrArg CoordinateHom.totalSpaceMap <| CoordinateHom.fiberMap_injective <| funext fun x ↦
      (fiberMap_isoTrivialOfCoordChangeEqId_hom _ _ x).trans
        (hp.fiberMap_characterFiniteRankCoreOneIso_hom x).symm

@[simp]
theorem coe_characterFiniteRankCoreOneDiffeomorph_symm :
    ⇑(hp.characterFiniteRankCoreOneDiffeomorph (IB := IB) (n := n) 𝕜).symm =
      (hp.characterFiniteRankCoreOneIso 𝕜).inv.totalSpaceMap :=
  (coe_diffeomorphTrivialOfCoordChangeEqId_symm _ _).trans <|
    congrArg CoordinateHom.totalSpaceMap <| CoordinateHom.fiberMap_injective <| funext fun x ↦
      (fiberMap_isoTrivialOfCoordChangeEqId_inv _ _ x).trans
        (hp.fiberMap_characterFiniteRankCoreOneIso_inv x).symm

/-- The `C^n` bundle equivalence identifying
`hp.characterFiniteRankCore χ₁ ⊗ hp.characterFiniteRankCore χ₂` with
`hp.characterFiniteRankCore (χ₁ * χ₂)` over the identity of `X`. -/
noncomputable def characterFiniteRankCoreMulDiffeomorph (χ₁ χ₂ : G →* 𝕜ˣ) :
    (hp.characterFiniteRankCore χ₁ ⊗ hp.characterFiniteRankCore χ₂).core.TotalSpace ≃ₘ^n⟮
      IB.prod 𝓘(𝕜, Fin (hp.characterFiniteRankCore χ₁ ⊗ hp.characterFiniteRankCore χ₂).rank → 𝕜),
      IB.prod 𝓘(𝕜, Fin (hp.characterFiniteRankCore (χ₁ * χ₂)).rank → 𝕜)⟯
    (hp.characterFiniteRankCore (χ₁ * χ₂)).core.TotalSpace :=
  constIsoDiffeomorph (A := tensor (hp.characterFiniteRankCore χ₁) (hp.characterFiniteRankCore χ₂))
    (D := hp.characterFiniteRankCore (χ₁ * χ₂))
    (hp.baseSet_tensor_characterFiniteRankCore χ₁ χ₂) (kroneckerLid 𝕜 1)
    fun i j x _ _ ↦ hp.coordChange_characterFiniteRankCore_mul_intertwines χ₁ χ₂ i j x

@[simp]
theorem coe_characterFiniteRankCoreMulDiffeomorph (χ₁ χ₂ : G →* 𝕜ˣ) :
    ⇑(hp.characterFiniteRankCoreMulDiffeomorph (IB := IB) (n := n) χ₁ χ₂) =
      (hp.characterFiniteRankCoreMulIso χ₁ χ₂).hom.totalSpaceMap :=
  (coe_constIsoDiffeomorph _ _ _).trans <|
    congrArg CoordinateHom.totalSpaceMap <| CoordinateHom.fiberMap_injective <| funext fun x ↦
      (fiberMap_constIso_hom _ _ _ x).trans
        (hp.fiberMap_characterFiniteRankCoreMulIso_hom χ₁ χ₂ x).symm

@[simp]
theorem coe_characterFiniteRankCoreMulDiffeomorph_symm (χ₁ χ₂ : G →* 𝕜ˣ) :
    ⇑(hp.characterFiniteRankCoreMulDiffeomorph (IB := IB) (n := n) χ₁ χ₂).symm =
      (hp.characterFiniteRankCoreMulIso χ₁ χ₂).inv.totalSpaceMap :=
  (coe_constIsoDiffeomorph_symm _ _ _).trans <|
    congrArg CoordinateHom.totalSpaceMap <| CoordinateHom.fiberMap_injective <| funext fun x ↦
      (fiberMap_constIso_inv _ _ _ x).trans
        (hp.fiberMap_characterFiniteRankCoreMulIso_inv χ₁ χ₂ x).symm

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

@[simp]
theorem coe_characterFiniteRankCoreInvDiffeomorph [CompleteSpace 𝕜] (χ : G →* 𝕜ˣ) :
    ⇑(hp.characterFiniteRankCoreInvDiffeomorph (IB := IB) (n := n) χ) =
      (hp.characterFiniteRankCoreInvIso χ).hom.totalSpaceMap :=
  (coe_constIsoDiffeomorph _ _ _).trans <|
    congrArg CoordinateHom.totalSpaceMap <| CoordinateHom.fiberMap_injective <| funext fun x ↦
      (fiberMap_constIso_hom _ _ _ x).trans
        (hp.fiberMap_characterFiniteRankCoreInvIso_hom χ x).symm

@[simp]
theorem coe_characterFiniteRankCoreInvDiffeomorph_symm [CompleteSpace 𝕜] (χ : G →* 𝕜ˣ) :
    ⇑(hp.characterFiniteRankCoreInvDiffeomorph (IB := IB) (n := n) χ).symm =
      (hp.characterFiniteRankCoreInvIso χ).inv.totalSpaceMap :=
  (coe_constIsoDiffeomorph_symm _ _ _).trans <|
    congrArg CoordinateHom.totalSpaceMap <| CoordinateHom.fiberMap_injective <| funext fun x ↦
      (fiberMap_constIso_inv _ _ _ x).trans
        (hp.fiberMap_characterFiniteRankCoreInvIso_inv χ x).symm

/-- The forward unit comparison `(hp.characterFiniteRankCoreOneIso 𝕜).hom` has `C^n` chart
operators. -/
theorem contMDiffOn_inChartCoordinates_characterFiniteRankCoreOneIso_hom (i j : X) :
    ContMDiffOn IB
      𝓘(𝕜, (Fin (hp.characterFiniteRankCore (1 : G →* 𝕜ˣ)).rank → 𝕜) →L[𝕜]
        (Fin (𝟙_ (FiniteRankBundleCore 𝕜 X)).rank → 𝕜)) n
      (fun x ↦ (hp.characterFiniteRankCore (1 : G →* 𝕜ˣ)).core.inChartCoordinates
        (𝟙_ (FiniteRankBundleCore 𝕜 X)).core i j x
        ((hp.characterFiniteRankCoreOneIso 𝕜).hom.fiberMap x))
      ((hp.characterFiniteRankCore (1 : G →* 𝕜ˣ)).core.baseSet i ∩
        (𝟙_ (FiniteRankBundleCore 𝕜 X)).core.baseSet j) :=
  contMDiffOn_inChartCoordinates_of_coordChange_comp
    (hp.characterFiniteRankCoreOneIso 𝕜).hom (subset_univ _)
    (ContinuousLinearMap.id 𝕜 (Fin 1 → 𝕜)) fun x _ v ↦ by
      rw [hp.fiberMap_characterFiniteRankCoreOneIso_hom, hp.coordChange_characterFiniteRankCore_one]
      simp only [MonoidalCategoryStruct.tensorUnit, coordChange_trivial]
      rfl

/-- The inverse unit comparison `(hp.characterFiniteRankCoreOneIso 𝕜).inv` has `C^n` chart
operators. -/
theorem contMDiffOn_inChartCoordinates_characterFiniteRankCoreOneIso_inv (i j : X) :
    ContMDiffOn IB
      𝓘(𝕜, (Fin (𝟙_ (FiniteRankBundleCore 𝕜 X)).rank → 𝕜) →L[𝕜]
        (Fin (hp.characterFiniteRankCore (1 : G →* 𝕜ˣ)).rank → 𝕜)) n
      (fun x ↦ (𝟙_ (FiniteRankBundleCore 𝕜 X)).core.inChartCoordinates
        (hp.characterFiniteRankCore (1 : G →* 𝕜ˣ)).core i j x
        ((hp.characterFiniteRankCoreOneIso 𝕜).inv.fiberMap x))
      ((𝟙_ (FiniteRankBundleCore 𝕜 X)).core.baseSet i ∩
        (hp.characterFiniteRankCore (1 : G →* 𝕜ˣ)).core.baseSet j) :=
  contMDiffOn_inChartCoordinates_of_comp_coordChange
    (hp.characterFiniteRankCoreOneIso 𝕜).inv (subset_univ _)
    (ContinuousLinearMap.id 𝕜 (Fin 1 → 𝕜)) fun x _ v ↦ by
      rw [hp.fiberMap_characterFiniteRankCoreOneIso_inv, hp.coordChange_characterFiniteRankCore_one]
      simp only [MonoidalCategoryStruct.tensorUnit, coordChange_trivial]
      rfl

/-- The forward multiplicativity comparison `(hp.characterFiniteRankCoreMulIso χ₁ χ₂).hom` has `C^n`
chart operators. -/
theorem contMDiffOn_inChartCoordinates_characterFiniteRankCoreMulIso_hom (χ₁ χ₂ : G →* 𝕜ˣ)
    (i j : X) :
    ContMDiffOn IB
      𝓘(𝕜, (Fin (hp.characterFiniteRankCore χ₁ ⊗ hp.characterFiniteRankCore χ₂).rank → 𝕜) →L[𝕜]
        (Fin (hp.characterFiniteRankCore (χ₁ * χ₂)).rank → 𝕜)) n
      (fun x ↦ (hp.characterFiniteRankCore χ₁ ⊗
          hp.characterFiniteRankCore χ₂).core.inChartCoordinates
        (hp.characterFiniteRankCore (χ₁ * χ₂)).core i j x
        ((hp.characterFiniteRankCoreMulIso χ₁ χ₂).hom.fiberMap x))
      ((hp.characterFiniteRankCore χ₁ ⊗ hp.characterFiniteRankCore χ₂).core.baseSet i ∩
        (hp.characterFiniteRankCore (χ₁ * χ₂)).core.baseSet j) :=
  contMDiffOn_inChartCoordinates_of_coordChange_comp
    (hp.characterFiniteRankCoreMulIso χ₁ χ₂).hom
    (hp.baseSet_tensor_characterFiniteRankCore χ₁ χ₂ i).le
    (kroneckerLid 𝕜 1).toContinuousLinearMap fun x _ v ↦ by
      rw [hp.fiberMap_characterFiniteRankCoreMulIso_hom]
      exact DFunLike.congr_fun
        (hp.coordChange_characterFiniteRankCore_mul_intertwines χ₁ χ₂ i x x) v

/-- The inverse multiplicativity comparison `(hp.characterFiniteRankCoreMulIso χ₁ χ₂).inv` has `C^n`
chart operators. -/
theorem contMDiffOn_inChartCoordinates_characterFiniteRankCoreMulIso_inv (χ₁ χ₂ : G →* 𝕜ˣ)
    (i j : X) :
    ContMDiffOn IB
      𝓘(𝕜, (Fin (hp.characterFiniteRankCore (χ₁ * χ₂)).rank → 𝕜) →L[𝕜]
        (Fin (hp.characterFiniteRankCore χ₁ ⊗ hp.characterFiniteRankCore χ₂).rank → 𝕜)) n
      (fun x ↦ (hp.characterFiniteRankCore (χ₁ * χ₂)).core.inChartCoordinates
        (hp.characterFiniteRankCore χ₁ ⊗ hp.characterFiniteRankCore χ₂).core i j x
        ((hp.characterFiniteRankCoreMulIso χ₁ χ₂).inv.fiberMap x))
      ((hp.characterFiniteRankCore (χ₁ * χ₂)).core.baseSet i ∩
        (hp.characterFiniteRankCore χ₁ ⊗ hp.characterFiniteRankCore χ₂).core.baseSet j) :=
  contMDiffOn_inChartCoordinates_of_comp_coordChange
    (hp.characterFiniteRankCoreMulIso χ₁ χ₂).inv
    (hp.baseSet_tensor_characterFiniteRankCore χ₁ χ₂ j).le
    (kroneckerLid 𝕜 1).symm.toContinuousLinearMap fun x _ v ↦ by
      rw [hp.fiberMap_characterFiniteRankCoreMulIso_inv]
      refine (kroneckerLid 𝕜 1).eq_symm_apply.2 ?_
      exact (DFunLike.congr_fun
        (hp.coordChange_characterFiniteRankCore_mul_intertwines χ₁ χ₂ x j x)
        ((kroneckerLid 𝕜 1).symm v)).trans
        (congrArg ((hp.characterFiniteRankCore (χ₁ * χ₂)).core.coordChange x j x)
          ((kroneckerLid 𝕜 1).apply_symm_apply v))

/-- The forward isomorphism `hp.characterFiniteRankCorePowIso χ m` has `C^n` chart operators,
without completeness assumptions on `𝕜`. -/
theorem contMDiffOn_inChartCoordinates_characterFiniteRankCorePowIso_hom (χ : G →* 𝕜ˣ) (m : ℕ) :
    ∀ i j : X,
      ContMDiffOn IB
        𝓘(𝕜, (Fin (tensorPow (hp.characterFiniteRankCore χ) m).rank → 𝕜) →L[𝕜]
          (Fin (hp.characterFiniteRankCore (χ ^ m)).rank → 𝕜)) n
        (fun x ↦ (tensorPow (hp.characterFiniteRankCore χ) m).core.inChartCoordinates
          (hp.characterFiniteRankCore (χ ^ m)).core i j x
          ((hp.characterFiniteRankCorePowIso χ m).hom.fiberMap x))
        ((tensorPow (hp.characterFiniteRankCore χ) m).core.baseSet i ∩
          (hp.characterFiniteRankCore (χ ^ m)).core.baseSet j) := by
  induction m with
  | zero =>
    intro i j
    rw [hp.characterFiniteRankCorePowIso_zero χ, Iso.trans_hom, Iso.symm_hom, eqToIso.hom]
    exact CoordinateHom.contMDiffOn_inChartCoordinates_comp
      (contMDiffOn_inChartCoordinates_eqToHom (I := IB) (n := n)
        (congrArg hp.characterFiniteRankCore (pow_zero χ).symm))
      hp.contMDiffOn_inChartCoordinates_characterFiniteRankCoreOneIso_inv i j
  | succ m ih =>
    intro i j
    rw [hp.characterFiniteRankCorePowIso_succ χ m, Iso.trans_hom, Iso.trans_hom, ← Category.assoc,
      whiskerLeftIso_hom, eqToIso.hom]
    exact CoordinateHom.contMDiffOn_inChartCoordinates_comp
      (contMDiffOn_inChartCoordinates_eqToHom (I := IB) (n := n)
        (congrArg hp.characterFiniteRankCore (pow_succ' χ m).symm))
      (CoordinateHom.contMDiffOn_inChartCoordinates_comp
        (hp.contMDiffOn_inChartCoordinates_characterFiniteRankCoreMulIso_hom χ (χ ^ m))
        (contMDiffOn_inChartCoordinates_whiskerLeft (A := hp.characterFiniteRankCore χ)
          (hp.characterFiniteRankCorePowIso χ m).hom ih)) i j

/-- The inverse isomorphism `hp.characterFiniteRankCorePowIso χ m` has `C^n` chart operators,
without completeness assumptions on `𝕜`. -/
theorem contMDiffOn_inChartCoordinates_characterFiniteRankCorePowIso_inv (χ : G →* 𝕜ˣ) (m : ℕ) :
    ∀ i j : X,
      ContMDiffOn IB
        𝓘(𝕜, (Fin (hp.characterFiniteRankCore (χ ^ m)).rank → 𝕜) →L[𝕜]
          (Fin (tensorPow (hp.characterFiniteRankCore χ) m).rank → 𝕜)) n
        (fun x ↦ (hp.characterFiniteRankCore (χ ^ m)).core.inChartCoordinates
          (tensorPow (hp.characterFiniteRankCore χ) m).core i j x
          ((hp.characterFiniteRankCorePowIso χ m).inv.fiberMap x))
        ((hp.characterFiniteRankCore (χ ^ m)).core.baseSet i ∩
          (tensorPow (hp.characterFiniteRankCore χ) m).core.baseSet j) := by
  induction m with
  | zero =>
    intro i j
    rw [hp.characterFiniteRankCorePowIso_zero χ, Iso.trans_inv, Iso.symm_inv, eqToIso.inv]
    exact CoordinateHom.contMDiffOn_inChartCoordinates_comp
      hp.contMDiffOn_inChartCoordinates_characterFiniteRankCoreOneIso_hom
      (contMDiffOn_inChartCoordinates_eqToHom (I := IB) (n := n)
        (congrArg hp.characterFiniteRankCore (pow_zero χ))) i j
  | succ m ih =>
    intro i j
    rw [hp.characterFiniteRankCorePowIso_succ χ m, Iso.trans_inv, Iso.trans_inv,
      whiskerLeftIso_inv, eqToIso.inv]
    exact CoordinateHom.contMDiffOn_inChartCoordinates_comp
      (contMDiffOn_inChartCoordinates_whiskerLeft (A := hp.characterFiniteRankCore χ)
        (hp.characterFiniteRankCorePowIso χ m).inv ih)
      (CoordinateHom.contMDiffOn_inChartCoordinates_comp
        (hp.contMDiffOn_inChartCoordinates_characterFiniteRankCoreMulIso_inv χ (χ ^ m))
        (contMDiffOn_inChartCoordinates_eqToHom (I := IB) (n := n)
          (congrArg hp.characterFiniteRankCore (pow_succ' χ m)))) i j

/-- The forward isomorphism `hp.characterFiniteRankCorePowIso χ m` glues to a `C^n` map on total
spaces. -/
theorem contMDiff_totalSpaceMap_characterFiniteRankCorePowIso_hom (χ : G →* 𝕜ˣ) (m : ℕ) :
    ContMDiff (IB.prod 𝓘(𝕜, Fin (tensorPow (hp.characterFiniteRankCore χ) m).rank → 𝕜))
      (IB.prod 𝓘(𝕜, Fin (hp.characterFiniteRankCore (χ ^ m)).rank → 𝕜)) n
      (hp.characterFiniteRankCorePowIso χ m).hom.totalSpaceMap :=
  (hp.characterFiniteRankCorePowIso χ m).hom.contMDiff_totalSpaceMap
    (hp.contMDiffOn_inChartCoordinates_characterFiniteRankCorePowIso_hom χ m)

/-- The inverse isomorphism `hp.characterFiniteRankCorePowIso χ m` glues to a `C^n` map on total
spaces. -/
theorem contMDiff_totalSpaceMap_characterFiniteRankCorePowIso_inv (χ : G →* 𝕜ˣ) (m : ℕ) :
    ContMDiff (IB.prod 𝓘(𝕜, Fin (hp.characterFiniteRankCore (χ ^ m)).rank → 𝕜))
      (IB.prod 𝓘(𝕜, Fin (tensorPow (hp.characterFiniteRankCore χ) m).rank → 𝕜)) n
      (hp.characterFiniteRankCorePowIso χ m).inv.totalSpaceMap :=
  (hp.characterFiniteRankCorePowIso χ m).inv.contMDiff_totalSpaceMap
    (hp.contMDiffOn_inChartCoordinates_characterFiniteRankCorePowIso_inv χ m)

/-- The `C^n` bundle equivalence identifying `tensorPow (hp.characterFiniteRankCore χ) m` with
`hp.characterFiniteRankCore (χ ^ m)` over the identity of `X`, without completeness assumptions on
`𝕜`. -/
noncomputable def characterFiniteRankCorePowDiffeomorph (χ : G →* 𝕜ˣ) (m : ℕ) :
    (tensorPow (hp.characterFiniteRankCore χ) m).core.TotalSpace ≃ₘ^n⟮
      IB.prod 𝓘(𝕜, Fin (tensorPow (hp.characterFiniteRankCore χ) m).rank → 𝕜),
      IB.prod 𝓘(𝕜, Fin (hp.characterFiniteRankCore (χ ^ m)).rank → 𝕜)⟯
    (hp.characterFiniteRankCore (χ ^ m)).core.TotalSpace :=
  (hp.characterFiniteRankCorePowIso χ m).hom.toDiffeomorphOfInv
    (hp.characterFiniteRankCorePowIso χ m).inv
    (hp.characterFiniteRankCorePowIso χ m).hom_inv_id
    (hp.characterFiniteRankCorePowIso χ m).inv_hom_id
    (hp.contMDiff_totalSpaceMap_characterFiniteRankCorePowIso_hom χ m)
    (hp.contMDiff_totalSpaceMap_characterFiniteRankCorePowIso_inv χ m)

@[simp]
theorem coe_characterFiniteRankCorePowDiffeomorph (χ : G →* 𝕜ˣ) (m : ℕ) :
    ⇑(hp.characterFiniteRankCorePowDiffeomorph (IB := IB) (n := n) χ m) =
      (hp.characterFiniteRankCorePowIso χ m).hom.totalSpaceMap :=
  CoordinateHom.coe_toDiffeomorphOfInv _ _ _ _ _ _

@[simp]
theorem coe_characterFiniteRankCorePowDiffeomorph_symm (χ : G →* 𝕜ˣ) (m : ℕ) :
    ⇑(hp.characterFiniteRankCorePowDiffeomorph (IB := IB) (n := n) χ m).symm =
      (hp.characterFiniteRankCorePowIso χ m).inv.totalSpaceMap :=
  CoordinateHom.coe_toDiffeomorphOfInv_symm _ _ _ _ _ _

/-! ### Twisting `C^n` chart operators and sections of scalar character cores -/

/-- Multiplying a `C^n` operator-valued function on a chart overlap by the locally constant scalar
`ψ (hp.deckChange e e' x)` preserves `ContMDiffOn`. -/
private theorem contMDiffOn_deckChange_smul (ψ : G →* 𝕜ˣ) {e e' : E}
    {g : X → 𝕜 →L[𝕜] 𝕜}
    (hg : ContMDiffOn IB 𝓘(𝕜, 𝕜 →L[𝕜] 𝕜) n g
      ((hp.isLocalHomeomorph.localInverseAt e).source ∩
        (hp.isLocalHomeomorph.localInverseAt e').source)) :
    ContMDiffOn IB 𝓘(𝕜, 𝕜 →L[𝕜] 𝕜) n (fun x ↦ (ψ (hp.deckChange e e' x) : 𝕜) • g x)
      ((hp.isLocalHomeomorph.localInverseAt e).source ∩
        (hp.isLocalHomeomorph.localInverseAt e').source) := by
  set U := (hp.isLocalHomeomorph.localInverseAt e).source ∩
    (hp.isLocalHomeomorph.localInverseAt e').source
  have hU : IsOpen U :=
    (hp.isLocalHomeomorph.localInverseAt e).open_source.inter
      (hp.isLocalHomeomorph.localInverseAt e').open_source
  intro x₀ hx₀
  have hAt : ContMDiffAt IB 𝓘(𝕜, 𝕜 →L[𝕜] 𝕜) n
      (fun x ↦ (ψ (hp.deckChange e e' x₀) : 𝕜) • g x) x₀ :=
    (((ψ (hp.deckChange e e' x₀) : 𝕜) •
      ContinuousLinearMap.id 𝕜 (𝕜 →L[𝕜] 𝕜)).contDiff.comp_contMDiffAt
      (hg.contMDiffAt (hU.mem_nhds hx₀)))
  exact (hAt.congr_of_eventuallyEq <|
    Filter.Eventually.mono (hp.eventually_deckChange_eq hx₀) fun x hx ↦ by
      rw [hx]).contMDiffWithinAt

/-- Twisting a cocycle morphism via `hp.characterCoreHomEquiv χ₁ χ₂` preserves `C^n` regularity of
every chart operator. -/
theorem contMDiffOn_inChartCoordinates_characterCoreHomEquiv_iff (χ₁ χ₂ : G →* 𝕜ˣ)
    (a : CoordinateHom (hp.characterCore χ₁) (hp.characterCore χ₂)) (e e' : E) :
    ContMDiffOn IB 𝓘(𝕜, 𝕜 →L[𝕜] 𝕜) n
        (fun x ↦ (hp.characterCore (1 : G →* 𝕜ˣ)).inChartCoordinates
          (hp.characterCore (χ₁⁻¹ * χ₂)) e e' x
          ((hp.characterCoreHomEquiv χ₁ χ₂ a).fiberMap x))
        ((hp.characterCore (1 : G →* 𝕜ˣ)).baseSet e ∩
          (hp.characterCore (χ₁⁻¹ * χ₂)).baseSet e') ↔
      ContMDiffOn IB 𝓘(𝕜, 𝕜 →L[𝕜] 𝕜) n
        (fun x ↦ (hp.characterCore χ₁).inChartCoordinates (hp.characterCore χ₂) e e' x
          (a.fiberMap x))
        ((hp.characterCore χ₁).baseSet e ∩ (hp.characterCore χ₂).baseSet e') := by
  simp only [hp.fiberMap_characterCoreHomEquiv, hp.characterCore_baseSet]
  constructor
  · intro hb
    refine (hp.contMDiffOn_deckChange_smul χ₁ hb).congr fun x hx ↦ ?_
    exact hp.inChartCoordinates_characterCore_eq_smul χ₁ χ₂ a.fiberMap e e' hx
  · intro ha
    refine (hp.contMDiffOn_deckChange_smul χ₁⁻¹ ha).congr fun x hx ↦ ?_
    rw [hp.inChartCoordinates_characterCore_eq_smul χ₁ χ₂ a.fiberMap e e' hx, MonoidHom.inv_apply,
      smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]

/-- The canonical unit section `x ↦ 1` of `hp.characterCore 1` is `C^n` at every regularity. -/
theorem contMDiff_one_section_characterCore_one :
    ContMDiff IB (IB.prod 𝓘(𝕜)) n
      (fun x : X ↦ TotalSpace.mk' 𝕜 (E := (hp.characterCore (1 : G →* 𝕜ˣ)).Fiber) x (1 : 𝕜)) := by
  let s : ∀ x, (hp.characterCore (1 : G →* 𝕜ˣ)).Fiber x := fun _ ↦ (1 : 𝕜)
  change ContMDiff IB (IB.prod 𝓘(𝕜)) n (fun x ↦ TotalSpace.mk' 𝕜 x (s x))
  intro x
  set y := (hp.characterCore (1 : G →* 𝕜ˣ)).indexAt x
  have : MemTrivializationAtlas ((hp.characterCore (1 : G →* 𝕜ˣ)).localTriv y) := ⟨⟨y, rfl⟩⟩
  rw [Trivialization.contMDiffAt_section_iff ((hp.characterCore (1 : G →* 𝕜ˣ)).localTriv y)
    ((hp.characterCore (1 : G →* 𝕜ˣ)).mem_baseSet_at x)]
  refine (contMDiffAt_const (c := (1 : 𝕜))).congr_of_eventuallyEq ?_
  filter_upwards [((hp.characterCore (1 : G →* 𝕜ˣ)).isOpen_baseSet y).mem_nhds
    ((hp.characterCore (1 : G →* 𝕜ˣ)).mem_baseSet_at x)] with x' _
  simp [s, localTriv_apply, hp.characterCore_one_coordChange]

/-- A `C^n` section `σ` of `hp.characterCore χ` defines a `C^n` family of fibrewise scalar
multiplications `v ↦ v • σ x` from `hp.characterCore 1` to `hp.characterCore χ`. -/
private theorem contMDiffOn_inChartCoordinates_smulRight_of_section (χ : G →* 𝕜ˣ)
    {σ : ∀ x, (hp.characterCore χ).Fiber x}
    (hσ : ContMDiff IB (IB.prod 𝓘(𝕜)) n (fun x ↦ TotalSpace.mk' 𝕜 x (σ x))) (e e' : E) :
    ContMDiffOn IB 𝓘(𝕜, 𝕜 →L[𝕜] 𝕜) n
      (fun x ↦ (hp.characterCore (1 : G →* 𝕜ˣ)).inChartCoordinates (hp.characterCore χ) e e' x
        ((ContinuousLinearMap.id 𝕜 𝕜).smulRight (σ x : 𝕜)))
      ((hp.characterCore (1 : G →* 𝕜ˣ)).baseSet e ∩ (hp.characterCore χ).baseSet e') := by
  let s : X → 𝕜 := fun x ↦ σ x
  have : MemTrivializationAtlas ((hp.characterCore χ).localTriv e') := ⟨⟨e', rfl⟩⟩
  have hopen : IsOpen ((hp.characterCore (1 : G →* 𝕜ˣ)).baseSet e ∩
      (hp.characterCore χ).baseSet e') :=
    ((hp.characterCore (1 : G →* 𝕜ˣ)).isOpen_baseSet e).inter
      ((hp.characterCore χ).isOpen_baseSet e')
  have hsub : (hp.characterCore (1 : G →* 𝕜ˣ)).baseSet e ∩ (hp.characterCore χ).baseSet e' ⊆
      ((hp.characterCore χ).localTriv e').baseSet :=
    inter_subset_right.trans (by simp)
  have hloc : ContMDiffOn IB 𝓘(𝕜) n (fun x ↦ ((hp.characterCore χ).localTriv e' ⟨x, σ x⟩).2)
      ((hp.characterCore (1 : G →* 𝕜ˣ)).baseSet e ∩ (hp.characterCore χ).baseSet e') :=
    (((hp.characterCore χ).localTriv e').contMDiffOn_section_iff hopen hsub).1 hσ.contMDiffOn
  refine ((ContinuousLinearMap.lsmul 𝕜 𝕜).contMDiff.comp_contMDiffOn hloc).congr fun x _ ↦ ?_
  change (hp.characterCore (1 : G →* 𝕜ˣ)).inChartCoordinates (hp.characterCore χ) e e' x
      ((ContinuousLinearMap.id 𝕜 𝕜).smulRight (s x)) =
    ContinuousLinearMap.lsmul 𝕜 𝕜 (((hp.characterCore χ).localTriv e' ⟨x, s x⟩).2)
  rw [hp.inChartCoordinates_characterCore_one_smulRight χ s e e' x]
  refine ContinuousLinearMap.ext fun v ↦ ?_
  change (v : 𝕜) * ((hp.characterCore χ).localTriv e' ⟨x, s x⟩).2 =
    ((hp.characterCore χ).localTriv e' ⟨x, s x⟩).2 * v
  exact mul_comm _ _

end RegularityAndMonoidal

/-! ### `C^n` bundle equivalences, tensor powers, and tensor order -/

section CompleteField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB}
  {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X] [ChartedSpace HB X]
  [Group G] [MulAction G E] {p : E → X} (hp : IsQuotientCoveringMap p G) {n : ℕ∞ω}

/-- Over a complete scalar field, any nowhere-vanishing `C^n` section of
`hp.characterCore (χ₁⁻¹ * χ₂)` induces a `C^n` bundle equivalence between `hp.characterCore χ₁` and
`hp.characterCore χ₂`. -/
theorem exists_bundleDiffeomorph_characterCore_of_section_ne_zero (χ₁ χ₂ : G →* 𝕜ˣ)
    {σ : ∀ x, (hp.characterCore (χ₁⁻¹ * χ₂)).Fiber x}
    (hσ : ContMDiff IB (IB.prod 𝓘(𝕜)) n fun x ↦ TotalSpace.mk' 𝕜 x (σ x))
    (hσ₀ : ∀ x, σ x ≠ 0) :
    ∃ e : ∀ x, (hp.characterCore χ₁).Fiber x ≃L[𝕜] (hp.characterCore χ₂).Fiber x,
      ContMDiff (IB.prod 𝓘(𝕜)) (IB.prod 𝓘(𝕜)) n
        (fun p : (hp.characterCore χ₁).TotalSpace ↦ TotalSpace.mk' 𝕜 p.proj (e p.proj p.2)) := by
  let s : X → 𝕜 := fun x ↦ σ x
  have hs₀ : ∀ x, s x ≠ 0 := hσ₀
  let ϕ : X → 𝕜 →L[𝕜] 𝕜 := fun x ↦ (ContinuousLinearMap.id 𝕜 𝕜).smulRight (s x)
  have hϕon := hp.contMDiffOn_inChartCoordinates_smulRight_of_section (χ₁⁻¹ * χ₂) hσ
  have hϕ : ContMDiff IB (IB.prod 𝓘(𝕜, 𝕜 →L[𝕜] 𝕜)) n (fun x ↦
      TotalSpace.mk' (𝕜 →L[𝕜] 𝕜)
        (E := fun y ↦ (hp.characterCore (1 : G →* 𝕜ˣ)).Fiber y →L[𝕜]
          (hp.characterCore (χ₁⁻¹ * χ₂)).Fiber y) x (ϕ x)) :=
    contMDiff_hom_bundle_iff_forall_contMDiffOn.2 hϕon
  let b : CoordinateHom (hp.characterCore (1 : G →* 𝕜ˣ)) (hp.characterCore (χ₁⁻¹ * χ₂)) :=
    CoordinateHom.ofContinuous ϕ hϕ.continuous
  let a : CoordinateHom (hp.characterCore χ₁) (hp.characterCore χ₂) :=
    (hp.characterCoreHomEquiv χ₁ χ₂).symm b
  have hab : hp.characterCoreHomEquiv χ₁ χ₂ a = b :=
    (hp.characterCoreHomEquiv χ₁ χ₂).apply_symm_apply b
  have ha : ∀ i j, ContMDiffOn IB 𝓘(𝕜, 𝕜 →L[𝕜] 𝕜) n
      (fun x ↦ (hp.characterCore χ₁).inChartCoordinates (hp.characterCore χ₂) i j x
        (a.fiberMap x))
      ((hp.characterCore χ₁).baseSet i ∩ (hp.characterCore χ₂).baseSet j) := fun i j ↦ by
    rw [← hp.contMDiffOn_inChartCoordinates_characterCoreHomEquiv_iff χ₁ χ₂ a i j, hab,
      CoordinateHom.fiberMap_ofContinuous]
    exact hϕon i j
  have hbij : ∀ x, Function.Bijective (a.fiberMap x) := fun x ↦ by
    rw [hp.fiberMap_characterCoreHomEquiv_symm, CoordinateHom.fiberMap_ofContinuous]
    refine ⟨fun u v huv ↦ mul_right_cancel₀ (hs₀ x) huv,
      fun w ↦ ⟨w * (s x)⁻¹, inv_mul_cancel_right₀ (hs₀ x) w⟩⟩
  refine ⟨a.fiberEquiv hbij, (a.contMDiff_totalSpaceMap ha).congr fun ⟨x, v⟩ ↦ ?_⟩
  simp [CoordinateHom.totalSpaceMap_mk]

/-- Over a complete scalar field, the character line bundles `hp.characterCore χ₁` and
`hp.characterCore χ₂` are `C^n` bundle-equivalent over `X` if and only if
`hp.characterCore (χ₁⁻¹ * χ₂)` admits a global compatible `C^n` trivialization. -/
theorem exists_bundleDiffeomorph_characterCore_iff_exists_trivialization (χ₁ χ₂ : G →* 𝕜ˣ) :
    (∃ e : ∀ x, (hp.characterCore χ₁).Fiber x ≃L[𝕜] (hp.characterCore χ₂).Fiber x,
        ContMDiff (IB.prod 𝓘(𝕜)) (IB.prod 𝓘(𝕜)) n
          (fun p : (hp.characterCore χ₁).TotalSpace ↦ TotalSpace.mk' 𝕜 p.proj (e p.proj p.2))) ↔
      ∃ (e : Trivialization 𝕜 (π 𝕜 (hp.characterCore (χ₁⁻¹ * χ₂)).Fiber)) (_ : e.IsLinear 𝕜),
        e.toOpenPartialHomeomorph ∈
          (contMDiffFiberwiseLinear X 𝕜 IB n).maximalAtlas
            (TotalSpace 𝕜 (hp.characterCore (χ₁⁻¹ * χ₂)).Fiber) ∧
          e.baseSet = univ := by
  rw [ContMDiffVectorBundle.exists_trivialization_baseSet_eq_univ_iff_exists_ne_zero
    (finrank_self 𝕜)]
  refine ⟨?_, fun ⟨σ, hσ, hσ₀⟩ ↦ hp.exists_bundleDiffeomorph_characterCore_of_section_ne_zero
    χ₁ χ₂ hσ hσ₀⟩
  rintro ⟨e, he⟩
  obtain ⟨a, ha, hbij, -⟩ := CoordinateHom.exists_toDiffeomorph_eq e he
  let b := hp.characterCoreHomEquiv χ₁ χ₂ a
  have hb : ∀ i j, ContMDiffOn IB 𝓘(𝕜, 𝕜 →L[𝕜] 𝕜) n
      (fun x ↦ (hp.characterCore (1 : G →* 𝕜ˣ)).inChartCoordinates
        (hp.characterCore (χ₁⁻¹ * χ₂)) i j x (b.fiberMap x))
      ((hp.characterCore (1 : G →* 𝕜ˣ)).baseSet i ∩
        (hp.characterCore (χ₁⁻¹ * χ₂)).baseSet j) :=
    fun i j ↦ (hp.contMDiffOn_inChartCoordinates_characterCoreHomEquiv_iff χ₁ χ₂ a i j).2 (ha i j)
  have hbtot := b.contMDiff_totalSpaceMap hb
  have hcomp : (fun x ↦ TotalSpace.mk' 𝕜 (E := (hp.characterCore (χ₁⁻¹ * χ₂)).Fiber) x
      (b.fiberMap x (1 : 𝕜))) =
      b.totalSpaceMap ∘ fun x ↦
        TotalSpace.mk' 𝕜 (E := (hp.characterCore (1 : G →* 𝕜ˣ)).Fiber) x (1 : 𝕜) := by
    funext x
    rw [Function.comp_apply, CoordinateHom.totalSpaceMap_def]
  refine ⟨fun x ↦ b.fiberMap x (1 : 𝕜),
    hcomp ▸ hbtot.comp hp.contMDiff_one_section_characterCore_one, fun x h0 ↦ ?_⟩
  have h0' : (hp.characterCoreHomEquiv χ₁ χ₂ a).fiberMap x (1 : 𝕜) = 0 := h0
  rw [hp.fiberMap_characterCoreHomEquiv] at h0'
  exact one_ne_zero ((hbij x).1 (h0'.trans (map_zero (a.fiberMap x)).symm))

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
          e.baseSet = univ :=
  (CoordinateHom.exists_trivialization_baseSet_eq_univ_iff_of_inv
    (by simp) (by simp)
    (hp.characterFiniteRankCorePowIso χ m).hom
    (hp.characterFiniteRankCorePowIso χ m).inv
    (hp.characterFiniteRankCorePowIso χ m).hom_inv_id
    (hp.characterFiniteRankCorePowIso χ m).inv_hom_id
    (hp.contMDiff_totalSpaceMap_characterFiniteRankCorePowIso_hom χ m)
    (hp.contMDiff_totalSpaceMap_characterFiniteRankCorePowIso_inv χ m)).trans
    (exists_trivialization_baseSet_eq_univ_ofScalarCore_iff (hp.characterCore (χ ^ m)))

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

/-- When only the trivial character has a globally `C^n`-trivial character bundle, two character
line bundles `hp.characterCore χ₁` and `hp.characterCore χ₂` are `C^n` bundle-equivalent if and
only if `χ₁ = χ₂`. -/
theorem exists_bundleDiffeomorph_characterCore_iff_eq_of_eq_one
    (hinj : ∀ ψ : G →* 𝕜ˣ,
      (∃ (e : Trivialization 𝕜 (π 𝕜 (hp.characterCore ψ).Fiber)) (_ : e.IsLinear 𝕜),
        e.toOpenPartialHomeomorph ∈
          (contMDiffFiberwiseLinear X 𝕜 IB n).maximalAtlas
            (TotalSpace 𝕜 (hp.characterCore ψ).Fiber) ∧
          e.baseSet = univ) → ψ = 1)
    (χ₁ χ₂ : G →* 𝕜ˣ) :
    (∃ e : ∀ x, (hp.characterCore χ₁).Fiber x ≃L[𝕜] (hp.characterCore χ₂).Fiber x,
        ContMDiff (IB.prod 𝓘(𝕜)) (IB.prod 𝓘(𝕜)) n
          (fun p : (hp.characterCore χ₁).TotalSpace ↦ TotalSpace.mk' 𝕜 p.proj (e p.proj p.2))) ↔
      χ₁ = χ₂ := by
  refine ⟨fun h ↦ inv_mul_eq_one.1 (hinj (χ₁⁻¹ * χ₂)
    ((hp.exists_bundleDiffeomorph_characterCore_iff_exists_trivialization χ₁ χ₂).1 h)), ?_⟩
  rintro rfl
  exact ⟨fun x ↦ ContinuousLinearEquiv.refl 𝕜 ((hp.characterCore χ₁).Fiber x), contMDiff_id⟩

/-- When only the trivial character has a globally `C^n`-trivial character bundle, the `m`-th
tensor power `tensorPow (hp.characterFiniteRankCore χ) m` is globally `C^n`-trivial if and only if
`orderOf χ ∣ m`. -/
theorem exists_trivialization_tensorPow_characterFiniteRankCore_iff_orderOf_dvd_of_eq_one
    (hinj : ∀ ψ : G →* 𝕜ˣ,
      (∃ (e : Trivialization 𝕜 (π 𝕜 (hp.characterCore ψ).Fiber)) (_ : e.IsLinear 𝕜),
        e.toOpenPartialHomeomorph ∈
          (contMDiffFiberwiseLinear X 𝕜 IB n).maximalAtlas
            (TotalSpace 𝕜 (hp.characterCore ψ).Fiber) ∧
          e.baseSet = univ) → ψ = 1)
    (χ : G →* 𝕜ˣ) (m : ℕ) :
    (∃ (e : Trivialization (Fin (tensorPow (hp.characterFiniteRankCore χ) m).rank → 𝕜)
        (π _ (tensorPow (hp.characterFiniteRankCore χ) m).core.Fiber)) (_ : e.IsLinear 𝕜),
        e.toOpenPartialHomeomorph ∈
          (contMDiffFiberwiseLinear X (Fin (tensorPow (hp.characterFiniteRankCore χ) m).rank → 𝕜)
            IB n).maximalAtlas
            (TotalSpace _ (tensorPow (hp.characterFiniteRankCore χ) m).core.Fiber) ∧
          e.baseSet = univ) ↔
      orderOf χ ∣ m :=
  ⟨fun h ↦ orderOf_dvd_iff_pow_eq_one.2 <| hinj (χ ^ m) <|
    (hp.exists_trivialization_baseSet_eq_univ_tensorPow_characterFiniteRankCore_iff χ m).1 h,
    hp.exists_trivialization_baseSet_eq_univ_tensorPow_characterFiniteRankCore_of_orderOf_dvd⟩

/-- When only the trivial character has a globally `C^n`-trivial character bundle, the least
positive exponent `m` for which `tensorPow (hp.characterFiniteRankCore χ) m` is globally
`C^n`-trivial is `orderOf χ` whenever `χ` has finite order. -/
theorem isLeast_pos_trivialization_tensorPow_characterFiniteRankCore_of_eq_one
    (hinj : ∀ ψ : G →* 𝕜ˣ,
      (∃ (e : Trivialization 𝕜 (π 𝕜 (hp.characterCore ψ).Fiber)) (_ : e.IsLinear 𝕜),
        e.toOpenPartialHomeomorph ∈
          (contMDiffFiberwiseLinear X 𝕜 IB n).maximalAtlas
            (TotalSpace 𝕜 (hp.characterCore ψ).Fiber) ∧
          e.baseSet = univ) → ψ = 1)
    {χ : G →* 𝕜ˣ} (hχ : IsOfFinOrder χ) :
    IsLeast {m : ℕ | 0 < m ∧
      ∃ (e : Trivialization (Fin (tensorPow (hp.characterFiniteRankCore χ) m).rank → 𝕜)
        (π _ (tensorPow (hp.characterFiniteRankCore χ) m).core.Fiber)) (_ : e.IsLinear 𝕜),
        e.toOpenPartialHomeomorph ∈
          (contMDiffFiberwiseLinear X (Fin (tensorPow (hp.characterFiniteRankCore χ) m).rank → 𝕜)
            IB n).maximalAtlas
            (TotalSpace _ (tensorPow (hp.characterFiniteRankCore χ) m).core.Fiber) ∧
          e.baseSet = univ} (orderOf χ) :=
  ⟨⟨hχ.orderOf_pos,
    hp.exists_trivialization_baseSet_eq_univ_tensorPow_characterFiniteRankCore_orderOf χ⟩,
    fun _ hm ↦ Nat.le_of_dvd hm.1 <|
      (hp.exists_trivialization_tensorPow_characterFiniteRankCore_iff_orderOf_dvd_of_eq_one
        hinj χ _).1 hm.2⟩

/-- If `p` is a `C^n` local diffeomorphism, `hp.characterCore χ₁` and `hp.characterCore χ₂` are
`C^n` bundle-equivalent over `X` if and only if there is a nowhere-vanishing `C^n` function
`f : E → 𝕜` satisfying `f (g • y) = (χ₁⁻¹ * χ₂) g * f y`. -/
theorem exists_bundleDiffeomorph_characterCore_iff
    {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
    {I : ModelWithCorners 𝕜 EM HM} [ChartedSpace HM E]
    (hpd : IsLocalDiffeomorph I IB n p) (χ₁ χ₂ : G →* 𝕜ˣ) :
    (∃ e : ∀ x, (hp.characterCore χ₁).Fiber x ≃L[𝕜] (hp.characterCore χ₂).Fiber x,
        ContMDiff (IB.prod 𝓘(𝕜)) (IB.prod 𝓘(𝕜)) n
          (fun p : (hp.characterCore χ₁).TotalSpace ↦ TotalSpace.mk' 𝕜 p.proj (e p.proj p.2))) ↔
      ∃ f : E → 𝕜, ContMDiff I 𝓘(𝕜) n f ∧ (∀ y, f y ≠ 0) ∧
        ∀ (g : G) (y : E), f (g • y) = (χ₁⁻¹ * χ₂) g * f y :=
  (hp.exists_bundleDiffeomorph_characterCore_iff_exists_trivialization χ₁ χ₂).trans
    (hp.exists_trivialization_baseSet_eq_univ_characterCore_iff hpd (χ₁⁻¹ * χ₂))

end CompleteField

/-! ### Compact connected complex coverings -/

section CompactComplex

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℂ EM] {HM : Type*} [TopologicalSpace HM]
  {I : ModelWithCorners ℂ EM HM} [I.Boundaryless]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℂ EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners ℂ EB HB}
  {E X G : Type*} [TopologicalSpace E] [ChartedSpace HM E] [IsManifold I 1 E]
  [CompactSpace E] [PreconnectedSpace E]
  [TopologicalSpace X] [ChartedSpace HB X]
  [Group G] [MulAction G E] {p : E → X} (hp : IsQuotientCoveringMap p G) {n : ℕ∞ω}

/-- Auxiliary lemma eliminating `Z = hp.associatedCore ...` by `subst` on a free core variable. -/
private theorem eq_zero_section_of_eq_associatedCore
    (hpd : IsLocalDiffeomorph I IB n p) (hn : n ≠ 0) {χ : G →* ℂˣ} (hχ : χ ≠ 1)
    (Z : VectorBundleCore ℂ X ℂ E)
    (hZ : Z = hp.associatedCore ((Units.map (algebraMap ℂ (ℂ →L[ℂ] ℂ)).toMonoidHom).comp χ))
    {σ : ∀ x, Z.Fiber x}
    (hσ : ContMDiff IB (IB.prod 𝓘(ℂ)) n (fun x ↦ TotalSpace.mk' ℂ x (σ x))) :
    σ = 0 := by
  subst hZ
  let ρ := (Units.map (algebraMap ℂ (ℂ →L[ℂ] ℂ)).toMonoidHom).comp χ
  have hf : ContMDiff I 𝓘(ℂ) n (hp.associatedSectionEquiv ρ σ : E → ℂ) :=
    (hp.contMDiff_section_associatedCore_iff ρ hpd le_rfl).1 hσ
  have hfG : ∀ (g : G) (y : E),
      (hp.associatedSectionEquiv ρ σ : E → ℂ) (g • y) =
        χ g * (hp.associatedSectionEquiv ρ σ : E → ℂ) y := fun g y ↦ by
    simpa [ρ, ContinuousLinearMap.algebraMap_apply, smul_eq_mul] using
      (hp.associatedSectionEquiv ρ σ).2 g y
  have hf0 := (hf.mdifferentiable hn).eq_zero_of_smul_eq_mul_of_ne_one hfG hχ
  funext x
  obtain ⟨y, rfl⟩ := hp.surjective x
  exact (hp.associatedSectionEquiv_apply_eq_zero_iff ρ σ y).1 (congrFun hf0 y)

/-- Over a quotient covering `p : E → X` by complex local diffeomorphisms whose total space `E` is
a compact connected complex manifold, every `C^n` section (`n ≠ 0`, in particular holomorphic at
`n = ∞`) of `hp.characterCore χ` for a nontrivial character `χ ≠ 1` vanishes identically. -/
theorem eq_zero_section_characterCore_of_ne_one
    (hpd : IsLocalDiffeomorph I IB n p) (hn : n ≠ 0) {χ : G →* ℂˣ} (hχ : χ ≠ 1)
    {σ : ∀ x, (hp.characterCore χ).Fiber x}
    (hσ : ContMDiff IB (IB.prod 𝓘(ℂ)) n (fun x ↦ TotalSpace.mk' ℂ x (σ x))) :
    σ = 0 :=
  hp.eq_zero_section_of_eq_associatedCore hpd hn hχ (hp.characterCore χ) (hp.characterCore_def χ)
    hσ

variable [Nonempty E]

/-- When `E` is a nonempty compact connected complex manifold and `p : E → X` is a `C^n` local
diffeomorphism (`n ≠ 0`), `hp.characterCore χ` admits a global compatible `C^n` trivialization if
and only if `χ = 1`. -/
theorem exists_trivialization_baseSet_eq_univ_characterCore_iff_eq_one
    (hpd : IsLocalDiffeomorph I IB n p) (hn : n ≠ 0) (χ : G →* ℂˣ) :
    (∃ (e : Trivialization ℂ (π ℂ (hp.characterCore χ).Fiber)) (_ : e.IsLinear ℂ),
        e.toOpenPartialHomeomorph ∈
          (contMDiffFiberwiseLinear X ℂ IB n).maximalAtlas
            (TotalSpace ℂ (hp.characterCore χ).Fiber) ∧
          e.baseSet = univ) ↔
      χ = 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ hp.exists_trivialization_baseSet_eq_univ_characterCore_one⟩
  obtain ⟨f, hf, hf₀, hfG⟩ := (hp.exists_trivialization_baseSet_eq_univ_characterCore_iff hpd χ).1 h
  by_contra hχ
  obtain ⟨y₀⟩ := ‹Nonempty E›
  exact hf₀ y₀ (congrFun ((hf.mdifferentiable hn).eq_zero_of_smul_eq_mul_of_ne_one hfG hχ) y₀)

/-- When `E` is a nonempty compact connected complex manifold and `p : E → X` is a `C^n` local
diffeomorphism (`n ≠ 0`), two character line bundles `hp.characterCore χ₁` and
`hp.characterCore χ₂` are `C^n` bundle-equivalent (in particular holomorphically isomorphic at
`n = ∞`) if and only if `χ₁ = χ₂`. -/
theorem exists_bundleDiffeomorph_characterCore_iff_eq
    (hpd : IsLocalDiffeomorph I IB n p) (hn : n ≠ 0) (χ₁ χ₂ : G →* ℂˣ) :
    (∃ e : ∀ x, (hp.characterCore χ₁).Fiber x ≃L[ℂ] (hp.characterCore χ₂).Fiber x,
        ContMDiff (IB.prod 𝓘(ℂ)) (IB.prod 𝓘(ℂ)) n
          (fun p : (hp.characterCore χ₁).TotalSpace ↦ TotalSpace.mk' ℂ p.proj (e p.proj p.2))) ↔
      χ₁ = χ₂ :=
  hp.exists_bundleDiffeomorph_characterCore_iff_eq_of_eq_one
    (fun ψ ↦ (hp.exists_trivialization_baseSet_eq_univ_characterCore_iff_eq_one hpd hn ψ).1)
    χ₁ χ₂

/-- When `E` is a nonempty compact connected complex manifold and `p : E → X` is a `C^n` local
diffeomorphism (`n ≠ 0`), the `m`-th tensor power `tensorPow (hp.characterFiniteRankCore χ) m`
admits a global compatible `C^n` trivialization if and only if `orderOf χ ∣ m`. -/
theorem exists_trivialization_baseSet_eq_univ_tensorPow_characterFiniteRankCore_iff_orderOf_dvd
    (hpd : IsLocalDiffeomorph I IB n p) (hn : n ≠ 0) (χ : G →* ℂˣ) (m : ℕ) :
    (∃ (e : Trivialization (Fin (tensorPow (hp.characterFiniteRankCore χ) m).rank → ℂ)
        (π _ (tensorPow (hp.characterFiniteRankCore χ) m).core.Fiber)) (_ : e.IsLinear ℂ),
        e.toOpenPartialHomeomorph ∈
          (contMDiffFiberwiseLinear X (Fin (tensorPow (hp.characterFiniteRankCore χ) m).rank → ℂ)
            IB n).maximalAtlas
            (TotalSpace _ (tensorPow (hp.characterFiniteRankCore χ) m).core.Fiber) ∧
          e.baseSet = univ) ↔
      orderOf χ ∣ m :=
  hp.exists_trivialization_tensorPow_characterFiniteRankCore_iff_orderOf_dvd_of_eq_one
    (fun ψ ↦ (hp.exists_trivialization_baseSet_eq_univ_characterCore_iff_eq_one hpd hn ψ).1)
    χ m

/-- When `E` is a nonempty compact connected complex manifold, `p : E → X` is a `C^n` local
diffeomorphism (`n ≠ 0`), and `χ : G →* ℂˣ` has finite order, the exact order of
`hp.characterFiniteRankCore χ` under `tensorPow` is `orderOf χ`. -/
theorem isLeast_pos_trivialization_tensorPow_characterFiniteRankCore
    (hpd : IsLocalDiffeomorph I IB n p) (hn : n ≠ 0) {χ : G →* ℂˣ} (hχ : IsOfFinOrder χ) :
    IsLeast {m : ℕ | 0 < m ∧
      ∃ (e : Trivialization (Fin (tensorPow (hp.characterFiniteRankCore χ) m).rank → ℂ)
        (π _ (tensorPow (hp.characterFiniteRankCore χ) m).core.Fiber)) (_ : e.IsLinear ℂ),
        e.toOpenPartialHomeomorph ∈
          (contMDiffFiberwiseLinear X (Fin (tensorPow (hp.characterFiniteRankCore χ) m).rank → ℂ)
            IB n).maximalAtlas
            (TotalSpace _ (tensorPow (hp.characterFiniteRankCore χ) m).core.Fiber) ∧
          e.baseSet = univ} (orderOf χ) :=
  hp.isLeast_pos_trivialization_tensorPow_characterFiniteRankCore_of_eq_one
    (fun ψ ↦ (hp.exists_trivialization_baseSet_eq_univ_characterCore_iff_eq_one hpd hn ψ).1)
    hχ

end CompactComplex

end IsQuotientCoveringMap
