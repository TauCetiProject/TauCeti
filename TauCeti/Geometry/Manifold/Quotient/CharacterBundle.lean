/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Quotient.Picard
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.Dual
public import TauCeti.Topology.Covering.CharacterBundle

/-!
# Duals, cocycle twisting, and bundle equivalences of character line bundles

Let `p : E → X` be a quotient covering map for a group `G` (`IsQuotientCoveringMap p G`) over a
charted space `X`. Building on the `C^n` character cores `IsQuotientCoveringMap.characterCore χ`
and `IsQuotientCoveringMap.characterContMDiffCore IB n χ` from
`TauCeti.Geometry.Manifold.Quotient.AssociatedBundle` and
`TauCeti.Geometry.Manifold.Quotient.Picard`, this file provides:

* `IsQuotientCoveringMap.characterContMDiffCoreDualIso` and
  `IsQuotientCoveringMap.characterFiniteRankCoreInvDiffeomorph`: over a complete scalar field, the
  dual `(hp.characterContMDiffCore IB n χ).dual` is canonically isomorphic in
  `ContMDiffFiniteRankBundleCore IB n X` to `hp.characterContMDiffCore IB n χ⁻¹`, with glued
  `C^n` total-space equivalence over `X`;
* `IsQuotientCoveringMap.contMDiffOn_inChartCoordinates_characterCoreHomEquiv_iff`,
  `IsQuotientCoveringMap.exists_bundleDiffeomorph_characterCore_iff_exists_trivialization`, and
  `IsQuotientCoveringMap.exists_bundleDiffeomorph_characterCore_iff`: twisting cocycle morphisms by
  `χ₁⁻¹` shows that `hp.characterCore χ₁` and `hp.characterCore χ₂` are `C^n` bundle-equivalent
  over `X` if and only if `hp.characterCore (χ₁⁻¹ * χ₂)` admits a global compatible `C^n`
  trivialization (and, when `p` is a `C^n` local diffeomorphism, if and only if `E` admits a
  nowhere-vanishing `(χ₁⁻¹ * χ₂)`-equivariant `C^n` function);
* `IsQuotientCoveringMap.exists_bundleDiffeomorph_characterCore_iff_eq`,
  `IsQuotientCoveringMap`'s
  `exists_trivialization_baseSet_eq_univ_tensorPow_characterFiniteRankCore_iff_orderOf_dvd`,
  and `IsQuotientCoveringMap.isLeast_pos_trivialization_tensorPow_characterFiniteRankCore`:
  global-trivialization and bundle-equivalence characterizations for compact connected complex
  coverings at `n ≠ 0` (in particular holomorphic at `n = ∞`).

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

namespace IsQuotientCoveringMap

section DualAndTwisting

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB}
  {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X] [ChartedSpace HB X]
  [Group G] [MulAction G E] {p : E → X} (hp : IsQuotientCoveringMap p G) {n : ℕ∞ω}

section Dual

variable (IB n) [CompleteSpace 𝕜]

/-- Over a complete scalar field, the dual of `hp.characterContMDiffCore IB n χ` is canonically
isomorphic in `ContMDiffFiniteRankBundleCore IB n X` to `hp.characterContMDiffCore IB n χ⁻¹`. -/
noncomputable def characterContMDiffCoreDualIso (χ : G →* 𝕜ˣ) :
    (hp.characterContMDiffCore IB n χ).dual ≅ hp.characterContMDiffCore IB n χ⁻¹ :=
  ContMDiffFiniteRankBundleCore.constIso
    (A := (hp.characterContMDiffCore IB n χ).dual)
    (D := hp.characterContMDiffCore IB n χ⁻¹)
    (hp.baseSet_dual_characterFiniteRankCore χ) (ContinuousLinearEquiv.refl 𝕜 (Fin 1 → 𝕜))
    (hp.coordChange_characterFiniteRankCore_inv_intertwines χ)

@[simp] theorem characterContMDiffCoreDualIso_hom_toHom (χ : G →* 𝕜ˣ) :
    (hp.characterContMDiffCoreDualIso IB n χ).hom.toHom =
      (hp.characterFiniteRankCoreInvIso χ).hom :=
  (ContMDiffFiniteRankBundleCore.constIso_hom_toHom _ _ _).trans
    (hp.characterFiniteRankCoreInvIso_def χ ▸ rfl)

@[simp] theorem characterContMDiffCoreDualIso_inv_toHom (χ : G →* 𝕜ˣ) :
    (hp.characterContMDiffCoreDualIso IB n χ).inv.toHom =
      (hp.characterFiniteRankCoreInvIso χ).inv :=
  (ContMDiffFiniteRankBundleCore.constIso_inv_toHom _ _ _).trans
    (hp.characterFiniteRankCoreInvIso_def χ ▸ rfl)

end Dual

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
  have hU : IsOpen ((hp.isLocalHomeomorph.localInverseAt e).source ∩
      (hp.isLocalHomeomorph.localInverseAt e').source) :=
    (hp.isLocalHomeomorph.localInverseAt e).open_source.inter
      (hp.isLocalHomeomorph.localInverseAt e').open_source
  intro x₀ hx₀
  have hAt : ContMDiffAt IB 𝓘(𝕜, 𝕜 →L[𝕜] 𝕜) n
      (fun x ↦ (ψ (hp.deckChange e e' x₀) : 𝕜) • g x) x₀ :=
    (((ψ (hp.deckChange e e' x₀) : 𝕜) •
      ContinuousLinearMap.id 𝕜 (𝕜 →L[𝕜] 𝕜)).contDiff.comp_contMDiffAt
      (hg.contMDiffAt (hU.mem_nhds hx₀)))
  exact (hAt.congr_of_eventuallyEq <|
    Filter.Eventually.mono (hp.eventually_deckChange_eq hx₀) fun _ hx ↦ by
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
  refine ⟨fun hb ↦ (hp.contMDiffOn_deckChange_smul χ₁ hb).congr fun x hx ↦
      hp.inChartCoordinates_characterCore_eq_smul χ₁ χ₂ a.fiberMap e e' hx,
    fun ha ↦ (hp.contMDiffOn_deckChange_smul χ₁⁻¹ ha).congr fun x hx ↦ ?_⟩
  rw [hp.inChartCoordinates_characterCore_eq_smul χ₁ χ₂ a.fiberMap e e' hx, MonoidHom.inv_apply,
    smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]

/-- The canonical unit section `x ↦ 1` of `hp.characterCore 1` is `C^n` at every regularity. -/
theorem contMDiff_one_section_characterCore_one :
    ContMDiff IB (IB.prod 𝓘(𝕜)) n
      (fun x : X ↦ TotalSpace.mk' 𝕜 (E := (hp.characterCore (1 : G →* 𝕜ˣ)).Fiber) x (1 : 𝕜)) := by
  let s : ∀ x, (hp.characterCore (1 : G →* 𝕜ˣ)).Fiber x := fun _ ↦ (1 : 𝕜)
  intro x
  set y := (hp.characterCore (1 : G →* 𝕜ˣ)).indexAt x
  have : MemTrivializationAtlas ((hp.characterCore (1 : G →* 𝕜ˣ)).localTriv y) := ⟨⟨y, rfl⟩⟩
  refine (Trivialization.contMDiffAt_section_iff (s := s)
    ((hp.characterCore (1 : G →* 𝕜ˣ)).localTriv y)
    ((hp.characterCore (1 : G →* 𝕜ˣ)).mem_baseSet_at x)).2 ?_
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
  have : MemTrivializationAtlas ((hp.characterCore χ).localTriv e') := ⟨⟨e', rfl⟩⟩
  have hopen : IsOpen ((hp.characterCore (1 : G →* 𝕜ˣ)).baseSet e ∩
      (hp.characterCore χ).baseSet e') :=
    ((hp.characterCore (1 : G →* 𝕜ˣ)).isOpen_baseSet e).inter
      ((hp.characterCore χ).isOpen_baseSet e')
  have hloc : ContMDiffOn IB 𝓘(𝕜) n (fun x ↦ ((hp.characterCore χ).localTriv e' ⟨x, σ x⟩).snd)
      ((hp.characterCore (1 : G →* 𝕜ˣ)).baseSet e ∩ (hp.characterCore χ).baseSet e') :=
    (((hp.characterCore χ).localTriv e').contMDiffOn_section_iff hopen
      (inter_subset_right.trans (by simp))).1 hσ.contMDiffOn
  refine ((ContinuousLinearMap.lsmul 𝕜 𝕜).contMDiff.comp_contMDiffOn hloc).congr fun x _ ↦ ?_
  rw [hp.inChartCoordinates_characterCore_one_smulRight χ (fun y ↦ (σ y : 𝕜)) e e' x]
  exact ContinuousLinearMap.ext fun v ↦ mul_comm _ _

end DualAndTwisting

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
        (fun p : (hp.characterCore χ₁).TotalSpace ↦ TotalSpace.mk' 𝕜 p.proj (e p.proj p.snd)) := by
  let ϕ : X → 𝕜 →L[𝕜] 𝕜 := fun x ↦ (ContinuousLinearMap.id 𝕜 𝕜).smulRight (σ x : 𝕜)
  have hϕon := hp.contMDiffOn_inChartCoordinates_smulRight_of_section (χ₁⁻¹ * χ₂) hσ
  have hϕ : ContMDiff IB (IB.prod 𝓘(𝕜, 𝕜 →L[𝕜] 𝕜)) n (fun x ↦
      TotalSpace.mk' (𝕜 →L[𝕜] 𝕜)
        (E := fun y ↦ (hp.characterCore (1 : G →* 𝕜ˣ)).Fiber y →L[𝕜]
          (hp.characterCore (χ₁⁻¹ * χ₂)).Fiber y) x (ϕ x)) :=
    contMDiff_hom_bundle_iff_forall_contMDiffOn.2 hϕon
  let b := CoordinateHom.ofContinuous ϕ hϕ.continuous
  let a := (hp.characterCoreHomEquiv χ₁ χ₂).symm b
  have ha : ∀ i j, ContMDiffOn IB 𝓘(𝕜, 𝕜 →L[𝕜] 𝕜) n
      (fun x ↦ (hp.characterCore χ₁).inChartCoordinates (hp.characterCore χ₂) i j x
        (a.fiberMap x))
      ((hp.characterCore χ₁).baseSet i ∩ (hp.characterCore χ₂).baseSet j) := fun i j ↦ by
    rw [← hp.contMDiffOn_inChartCoordinates_characterCoreHomEquiv_iff χ₁ χ₂ a i j,
      (hp.characterCoreHomEquiv χ₁ χ₂).apply_symm_apply b, CoordinateHom.fiberMap_ofContinuous]
    exact hϕon i j
  have hbij : ∀ x, Function.Bijective (a.fiberMap x) := fun x ↦ by
    let c : 𝕜 := σ x
    have hc : c ≠ 0 := hσ₀ x
    rw [hp.fiberMap_characterCoreHomEquiv_symm, CoordinateHom.fiberMap_ofContinuous]
    exact ⟨fun _ _ huv ↦ mul_right_cancel₀ hc huv, fun w ↦ ⟨w * c⁻¹, inv_mul_cancel_right₀ hc w⟩⟩
  refine ⟨a.fiberEquiv hbij, (a.contMDiff_totalSpaceMap ha).congr fun ⟨x, v⟩ ↦ ?_⟩
  simp [CoordinateHom.totalSpaceMap_mk]

/-- Over a complete scalar field, the character line bundles `hp.characterCore χ₁` and
`hp.characterCore χ₂` are `C^n` bundle-equivalent over `X` if and only if
`hp.characterCore (χ₁⁻¹ * χ₂)` admits a global compatible `C^n` trivialization. -/
theorem exists_bundleDiffeomorph_characterCore_iff_exists_trivialization (χ₁ χ₂ : G →* 𝕜ˣ) :
    (∃ e : ∀ x, (hp.characterCore χ₁).Fiber x ≃L[𝕜] (hp.characterCore χ₂).Fiber x,
        ContMDiff (IB.prod 𝓘(𝕜)) (IB.prod 𝓘(𝕜)) n
          (fun p : (hp.characterCore χ₁).TotalSpace ↦ TotalSpace.mk' 𝕜 p.proj (e p.proj p.snd))) ↔
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
  have hbtot := b.contMDiff_totalSpaceMap fun i j ↦
    (hp.contMDiffOn_inChartCoordinates_characterCoreHomEquiv_iff χ₁ χ₂ a i j).2 (ha i j)
  refine ⟨fun x ↦ b.fiberMap x (1 : 𝕜),
    (hbtot.comp hp.contMDiff_one_section_characterCore_one).congr fun x ↦
      (CoordinateHom.totalSpaceMap_mk b x (1 : 𝕜)).symm, fun x h0 ↦ ?_⟩
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
          e.baseSet = univ := by
  have h1 : (tensorPow (hp.characterContMDiffCore IB n χ) m).toCore =
      tensorPow (hp.characterFiniteRankCore χ) m :=
    ContMDiffFiniteRankBundleCore.toCore_tensorPow _ m
  have hleft := ContMDiffPicardGroup.ofRankOne_eq_one_iff_exists_trivialization_baseSet_eq_univ
    (tensorPow (hp.characterContMDiffCore IB n χ) m) (by simp)
  rw [ContMDiffPicardGroup.ofRankOne_tensorPow _ (hp.rank_characterContMDiffCore IB n χ),
    hp.ofRankOne_characterContMDiffCore, ← map_pow,
    hp.characterPicardHom_eq_one_iff_exists_trivialization_baseSet_eq_univ] at hleft
  exact h1 ▸ hleft.symm

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
          (fun p : (hp.characterCore χ₁).TotalSpace ↦ TotalSpace.mk' 𝕜 p.proj (e p.proj p.snd))) ↔
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
          (fun p : (hp.characterCore χ₁).TotalSpace ↦ TotalSpace.mk' 𝕜 p.proj (e p.proj p.snd))) ↔
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
  [CompactSpace E] [ConnectedSpace E]
  [TopologicalSpace X] [ChartedSpace HB X]
  [Group G] [MulAction G E] {p : E → X} (hp : IsQuotientCoveringMap p G) {n : ℕ∞ω}

/-- When `E` is a compact connected complex manifold and `p : E → X` is differentiable (`n ≠ 0`),
two character line bundles `hp.characterCore χ₁` and `hp.characterCore χ₂` are `C^n`
bundle-equivalent (in particular holomorphically isomorphic at `n = ∞`) if and only if
`χ₁ = χ₂`. -/
theorem exists_bundleDiffeomorph_characterCore_iff_eq
    (hpd : MDifferentiable I IB p) (hn : n ≠ 0) (χ₁ χ₂ : G →* ℂˣ) :
    (∃ e : ∀ x, (hp.characterCore χ₁).Fiber x ≃L[ℂ] (hp.characterCore χ₂).Fiber x,
        ContMDiff (IB.prod 𝓘(ℂ)) (IB.prod 𝓘(ℂ)) n
          (fun p : (hp.characterCore χ₁).TotalSpace ↦ TotalSpace.mk' ℂ p.proj (e p.proj p.snd))) ↔
      χ₁ = χ₂ :=
  hp.exists_bundleDiffeomorph_characterCore_iff_eq_of_eq_one
    (fun ψ ↦ (hp.exists_trivialization_baseSet_eq_univ_characterCore_iff_eq_one hpd hn ψ).1)
    χ₁ χ₂

/-- When `E` is a compact connected complex manifold and `p : E → X` is differentiable (`n ≠ 0`),
the `m`-th tensor power `tensorPow (hp.characterFiniteRankCore χ) m` admits a global compatible
`C^n` trivialization if and only if `orderOf χ ∣ m`. -/
theorem exists_trivialization_baseSet_eq_univ_tensorPow_characterFiniteRankCore_iff_orderOf_dvd
    (hpd : MDifferentiable I IB p) (hn : n ≠ 0) (χ : G →* ℂˣ) (m : ℕ) :
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

/-- When `E` is a compact connected complex manifold, `p : E → X` is differentiable (`n ≠ 0`), and
`χ : G →* ℂˣ` has finite order, the exact order of `hp.characterFiniteRankCore χ` under `tensorPow`
is `orderOf χ`. -/
theorem isLeast_pos_trivialization_tensorPow_characterFiniteRankCore
    (hpd : MDifferentiable I IB p) (hn : n ≠ 0) {χ : G →* ℂˣ} (hχ : IsOfFinOrder χ) :
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
