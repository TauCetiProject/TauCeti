/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Complex
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
public import TauCeti.Geometry.Manifold.VectorBundle.Core.Trivial
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.Scalar
public import TauCeti.Geometry.Manifold.VectorBundle.FrameTrivialization
public import TauCeti.Topology.Covering.AssociatedBundle
import TauCeti.Algebra.Group.Hom.Defs
import TauCeti.Geometry.Manifold.ContMDiff.Defs
import TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.Basic

/-!
# Smooth and holomorphic bundles associated with representations of a deck group

Let `p : E → X` be a quotient covering map for a group `G` (`IsQuotientCoveringMap p G`), and let
`ρ : G →* (F →L[𝕜] F)ˣ` be a representation of `G`. The transitions of the associated vector
bundle `IsQuotientCoveringMap.associatedCore ρ` over `X` are locally constant, so for every model
and every regularity they are `C^n`: the associated bundle is a `C^n` vector bundle over any
charted space `X` (`IsQuotientCoveringMap.isContMDiff_associatedCore`), including analytic
regularity. Over a complex manifold, modelled on `𝓘(ℂ, EB)` with `n = ∞`, it is a holomorphic
vector bundle, and for a character `χ : G →* ℂˣ` the core `IsQuotientCoveringMap.characterCore χ`
is a holomorphic line bundle. Likewise, the point-indexed finite-rank core
`IsQuotientCoveringMap.associatedFiniteRankCore ρ` and its character specialization
`IsQuotientCoveringMap.characterFiniteRankCore χ` have locally constant transitions and hence are
`C^n` (`isContMDiff_associatedFiniteRankCore`, `isContMDiff_characterFiniteRankCore`); for a
character `χ`, `ofScalarCoreCharacterCoreDiffeomorph` identifies `FiniteRankBundleCore.ofScalarCore
(hp.characterCore χ)` with `characterFiniteRankCore χ`, `characterFiniteRankCoreDiffeomorph`
identifies the total space of `characterFiniteRankCore χ` with that of `characterCore χ` via a
`C^n` diffeomorphism over `X`, yielding the equivalence of nowhere-vanishing `C^n` sections
(`exists_section_ne_zero_characterFiniteRankCore_iff`) and global trivializations over complete
fields (`exists_trivialization_baseSet_eq_univ_characterFiniteRankCore_iff`).

When `p` is moreover a `C^n` local diffeomorphism, as the orbit projection of a free properly
discontinuous action by `C^n` maps is (`TauCeti.isLocalDiffeomorph_quotientMk`), the regularity
of a section can be read upstairs. A section of the associated bundle is `C^m`, for `m ≤ n`,
exactly when the corresponding `ρ`-equivariant function on `E`
(`IsQuotientCoveringMap.associatedSectionEquiv`) is `C^m`
(`IsQuotientCoveringMap.contMDiff_section_associatedCore_iff`). Holomorphic sections of the
holomorphic bundle associated with `ρ` are thus the holomorphic functions `f : E → F` with
`f (g • y) = ρ g (f y)`.

For a line bundle this decides triviality. The bundle associated with a representation on a line
has a global trivialization in its maximal `C^n` atlas exactly when there is a nowhere-vanishing
`C^n` equivariant function upstairs
(`IsQuotientCoveringMap.exists_trivialization_baseSet_eq_univ_associatedCore_iff`). For a
character `χ`, the holomorphic line bundle `characterCore χ` is holomorphically trivial exactly
when there is a nowhere-vanishing holomorphic `f : E → ℂ` with `f (g • y) = χ g * f y`
(`IsQuotientCoveringMap.exists_trivialization_baseSet_eq_univ_characterCore_iff`). The line bundle
of the trivial character is trivial for every quotient covering
(`IsQuotientCoveringMap.exists_trivialization_baseSet_eq_univ_characterCore_one`).

When `p` is differentiable and its covering space `E` is a compact connected complex manifold,
every holomorphic function on `E` is constant (`MDifferentiable.exists_eq_const_of_compactSpace`,
the maximum principle). Hence the holomorphic sections of the bundle associated with `ρ`
correspond to the `ρ`-invariant vectors of `F`
(`IsQuotientCoveringMap.mdifferentiable_section_associatedCore_iff_exists_eq_const`),
the line bundle of a nontrivial character has no nonzero holomorphic section
(`IsQuotientCoveringMap.eq_zero_of_contMDiff_section_characterCore`), the line bundle of `χ` is
holomorphically trivial exactly when `χ = 1`
(`IsQuotientCoveringMap.exists_trivialization_baseSet_eq_univ_characterCore_iff_eq_one`), and
two character line bundles are holomorphically isomorphic over `X` exactly when their characters
coincide (`IsQuotientCoveringMap.exists_bundleDiffeomorph_characterCore_iff_eq`).

## Main results

* `IsQuotientCoveringMap.isContMDiff_associatedCore`,
  `IsQuotientCoveringMap.isContMDiff_associatedFiniteRankCore`: the associated bundle (and its
  point-indexed finite-rank core) is `C^n`.
* `IsQuotientCoveringMap.ofScalarCoreCharacterCoreDiffeomorph`,
  `IsQuotientCoveringMap.characterFiniteRankCoreDiffeomorph`,
  `IsQuotientCoveringMap.exists_section_ne_zero_characterFiniteRankCore_iff`, and
  `IsQuotientCoveringMap.exists_trivialization_baseSet_eq_univ_characterFiniteRankCore_iff`:
  total-space `C^n` diffeomorphisms, nowhere-vanishing section equivalence, and global
  trivialization equivalence relating `FiniteRankBundleCore.ofScalarCore (hp.characterCore χ)`,
  `characterFiniteRankCore χ`, and `characterCore χ`.
* `IsQuotientCoveringMap.contMDiffAt_section_associatedCore_iff`,
  `IsQuotientCoveringMap.contMDiff_section_associatedCore_iff`: a section is `C^m` at `p y`, or
  globally, exactly when the corresponding equivariant function is `C^m` at `y`, or globally.
* `IsQuotientCoveringMap.exists_trivialization_baseSet_eq_univ_associatedCore_iff`,
  `IsQuotientCoveringMap.exists_trivialization_baseSet_eq_univ_characterCore_iff`: an associated
  line bundle is trivial exactly when there is a nowhere-vanishing equivariant function upstairs.
* `IsQuotientCoveringMap.mdifferentiable_section_associatedCore_iff_exists_eq_const`,
  `IsQuotientCoveringMap.contMDiff_section_associatedCore_iff_exists_eq_const`: if `p` is
  differentiable with compact preconnected complex covering manifold `E`, holomorphic sections
  over `X` have constant equivariant functions upstairs with `ρ`-invariant values.
* `IsQuotientCoveringMap.eq_zero_of_mdifferentiable_section_characterCore`,
  `IsQuotientCoveringMap.eq_zero_of_contMDiff_section_characterCore`,
  `IsQuotientCoveringMap.exists_trivialization_baseSet_eq_univ_characterCore_iff_eq_one`,
  `IsQuotientCoveringMap.exists_bundleDiffeomorph_characterCore_iff_eq`: if `p` is differentiable
  with compact connected complex covering manifold `E`, the line bundle of a nontrivial character
  over `X` has no nonzero holomorphic section, is not holomorphically trivial, and distinct
  characters yield non-isomorphic line bundles. The analogous vanishing results for rank-one
  representations and the triviality criterion for arbitrary representations are
  `IsQuotientCoveringMap.eq_zero_of_mdifferentiable_section_associatedCore`,
  `IsQuotientCoveringMap.eq_zero_of_contMDiff_section_associatedCore`, and
  `IsQuotientCoveringMap.exists_trivialization_baseSet_eq_univ_associatedCore_iff_eq_one`.
* `IsQuotientCoveringMap.contMDiffOn_inChartCoordinates_characterCoreHomEquiv_iff`,
  `IsQuotientCoveringMap.contMDiff_totalSpaceMap_characterCoreHomEquiv_iff`,
  `IsQuotientCoveringMap.characterCoreDiffeomorphOfSectionNeZero`,
  `IsQuotientCoveringMap.exists_bundleDiffeomorph_characterCore_iff_exists_trivialization`, and
  `IsQuotientCoveringMap.exists_bundleDiffeomorph_characterCore_iff`: twisting cocycle morphisms by
  `χ₁⁻¹` shows that `hp.characterCore χ₁` and `hp.characterCore χ₂` are `C^n` bundle-equivalent
  over `X` if and only if `hp.characterCore (χ₁⁻¹ * χ₂)` admits a global compatible `C^n`
  trivialization (and, when `p` is a `C^n` local diffeomorphism, if and only if `E` admits a
  nowhere-vanishing `(χ₁⁻¹ * χ₂)`-equivariant `C^n` function).

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, Section 2.2.
* Otto Forster, *Lectures on Riemann Surfaces*, Springer, 1981, §§4–5 (holomorphic descent along
  coverings).
-/

public section

open Bundle Filter Module Set Topology
open scoped Manifold ContDiff

namespace IsQuotientCoveringMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
  {I : ModelWithCorners 𝕜 EM HM}
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB}
  {E X G : Type*} [TopologicalSpace E] [ChartedSpace HM E] [TopologicalSpace X]
  [ChartedSpace HB X] [Group G] [MulAction G E] {p : E → X} (hp : IsQuotientCoveringMap p G)
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] (ρ : G →* (F →L[𝕜] F)ˣ) {n m : ℕ∞ω}

/-- The bundle associated with a representation of the deck group has locally constant
transitions, so it is a `C^n` vector bundle for every model of the base and every regularity. -/
instance isContMDiff_associatedCore : (hp.associatedCore ρ).IsContMDiff IB n where
  contMDiffOn_coordChange _ _ _ hx :=
    (contMDiffAt_const.congr_of_eventuallyEq
      (hp.eventually_associatedCore_coordChange_eq ρ hx)).contMDiffWithinAt

/-- The line bundle of a deck character is `C^n` for every model and regularity. -/
instance isContMDiff_characterCore (χ : G →* 𝕜ˣ) :
    (hp.characterCore χ).IsContMDiff IB n := by
  rw [characterCore_def]
  infer_instance

/-- The point-indexed finite-rank core associated with a representation of the deck group has
locally constant transitions, so it is a `C^n` vector bundle for every model of the base and every
regularity. -/
instance isContMDiff_associatedFiniteRankCore {r : ℕ}
    (ρ : G →* ((Fin r → 𝕜) →L[𝕜] (Fin r → 𝕜))ˣ) :
    (hp.associatedFiniteRankCore ρ).core.IsContMDiff IB n where
  contMDiffOn_coordChange _ _ _ hx :=
    (contMDiffAt_const.congr_of_eventuallyEq
      (hp.eventually_associatedFiniteRankCore_coordChange_eq ρ hx)).contMDiffWithinAt

/-- The point-indexed finite-rank core of a character is `C^n` for every model and regularity. -/
instance isContMDiff_characterFiniteRankCore (χ : G →* 𝕜ˣ) :
    (hp.characterFiniteRankCore χ).core.IsContMDiff IB n := by
  rw [characterFiniteRankCore_def]
  infer_instance

section FiniteRankComparison

variable (IB n)

/-- Total-space `C^n` diffeomorphism identifying `(hp.characterFiniteRankCore χ).core.TotalSpace`
with `(hp.characterCore χ).TotalSpace` over `X`. -/
noncomputable def characterFiniteRankCoreDiffeomorph (χ : G →* 𝕜ˣ) :
    (hp.characterFiniteRankCore χ).core.TotalSpace ≃ₘ^n⟮IB.prod
      𝓘(𝕜, Fin (hp.characterFiniteRankCore χ).rank → 𝕜), IB.prod 𝓘(𝕜)⟯
      (hp.characterCore χ).TotalSpace where
  toEquiv := (hp.characterFiniteRankCoreHomeomorph χ).toEquiv
  contMDiff_toFun :=
    (hp.characterFiniteRankCore χ).contMDiff_of_localTriv_snd
      (hp.characterFiniteRankCoreHomeomorph χ)
      (fun p₀ ↦ by simp [characterFiniteRankCoreHomeomorph_apply])
      (ContinuousLinearMap.proj (⟨0, by simp⟩ : Fin (hp.characterFiniteRankCore χ).rank))
      fun b p₀ ↦ by
        rw [← (hp.characterFiniteRankCore χ).trivializationAt_core,
          characterFiniteRankCoreHomeomorph_apply]
        exact hp.trivializationAt_characterCore_snd χ b p₀
  contMDiff_invFun :=
    (hp.characterFiniteRankCore χ).contMDiff_of_trivializationAt_snd
      (hp.characterFiniteRankCoreHomeomorph χ).symm
      (fun q ↦ by simp [characterFiniteRankCoreHomeomorph_symm_apply])
      (ContinuousLinearMap.pi fun _ ↦ ContinuousLinearMap.id 𝕜 𝕜) fun b q ↦ by
        ext k
        rw [← (hp.characterFiniteRankCore χ).trivializationAt_core,
          characterFiniteRankCoreHomeomorph_symm_apply]
        exact hp.trivializationAt_characterFiniteRankCore_snd χ b q k

@[simp] theorem characterFiniteRankCoreDiffeomorph_apply (χ : G →* 𝕜ˣ)
    (p₀ : (hp.characterFiniteRankCore χ).core.TotalSpace) :
    hp.characterFiniteRankCoreDiffeomorph IB n χ p₀ =
      ⟨p₀.proj, (p₀.snd : Fin (hp.characterFiniteRankCore χ).rank → 𝕜) ⟨0, by simp⟩⟩ :=
  hp.characterFiniteRankCoreHomeomorph_apply χ p₀

@[simp] theorem characterFiniteRankCoreDiffeomorph_symm_apply (χ : G →* 𝕜ˣ)
    (q : (hp.characterCore χ).TotalSpace) :
    (hp.characterFiniteRankCoreDiffeomorph IB n χ).symm q =
      ⟨q.proj, (fun _ ↦ (q.snd : 𝕜) : Fin (hp.characterFiniteRankCore χ).rank → 𝕜)⟩ :=
  hp.characterFiniteRankCoreHomeomorph_symm_apply χ q

/-- `hp.characterFiniteRankCore χ` admits a nowhere-vanishing `C^n` section if and only if
`hp.characterCore χ` does. -/
theorem exists_section_ne_zero_characterFiniteRankCore_iff (χ : G →* 𝕜ˣ) :
    (∃ σ : ∀ x, (hp.characterFiniteRankCore χ).core.Fiber x,
      ContMDiff IB (IB.prod 𝓘(𝕜, Fin (hp.characterFiniteRankCore χ).rank → 𝕜)) n
        (fun x ↦ TotalSpace.mk' (Fin (hp.characterFiniteRankCore χ).rank → 𝕜) x (σ x)) ∧
      ∀ x, σ x ≠ 0) ↔
    ∃ τ : ∀ x, (hp.characterCore χ).Fiber x,
      ContMDiff IB (IB.prod 𝓘(𝕜)) n (fun x ↦ TotalSpace.mk' 𝕜 x (τ x)) ∧
      ∀ x, τ x ≠ 0 := by
  let k₀ : Fin (hp.characterFiniteRankCore χ).rank := ⟨0, by simp⟩
  constructor
  · rintro ⟨σ, hσ, hσ₀⟩
    refine ⟨fun x ↦ (σ x : Fin (hp.characterFiniteRankCore χ).rank → 𝕜) k₀,
      ((hp.characterFiniteRankCoreDiffeomorph IB n χ).contMDiff.comp hσ).congr fun x ↦
        (hp.characterFiniteRankCoreDiffeomorph_apply IB n χ ⟨x, σ x⟩).symm,
      fun x h0 ↦ hσ₀ x ?_⟩
    exact funext fun k ↦ by
      obtain rfl : k = k₀ := Fin.ext (Nat.lt_one_iff.mp k.isLt)
      exact h0
  · rintro ⟨τ, hτ, hτ₀⟩
    exact ⟨fun x _ ↦ (τ x : 𝕜),
      ((hp.characterFiniteRankCoreDiffeomorph IB n χ).symm.contMDiff.comp hτ).congr fun x ↦
        (hp.characterFiniteRankCoreDiffeomorph_symm_apply IB n χ ⟨x, τ x⟩).symm,
      fun x h0 ↦ hτ₀ x (congrFun h0 k₀)⟩

/-- Total-space `C^n` diffeomorphism identifying
`(FiniteRankBundleCore.ofScalarCore (hp.characterCore χ)).core.TotalSpace` with
`(hp.characterFiniteRankCore χ).core.TotalSpace` over `X`. -/
noncomputable def ofScalarCoreCharacterCoreDiffeomorph (χ : G →* 𝕜ˣ) :
    (TauCeti.FiniteRankBundleCore.ofScalarCore (hp.characterCore χ)).core.TotalSpace ≃ₘ^n⟮
      IB.prod 𝓘(𝕜, Fin (TauCeti.FiniteRankBundleCore.ofScalarCore (hp.characterCore χ)).rank → 𝕜),
      IB.prod 𝓘(𝕜, Fin (hp.characterFiniteRankCore χ).rank → 𝕜)⟯
      (hp.characterFiniteRankCore χ).core.TotalSpace :=
  TauCeti.FiniteRankBundleCore.constIsoDiffeomorph
    (A := TauCeti.FiniteRankBundleCore.ofScalarCore (hp.characterCore χ))
    (D := hp.characterFiniteRankCore χ)
    (hp.baseSet_ofScalarCore_characterCore χ)
    (ContinuousLinearEquiv.refl 𝕜 (Fin 1 → 𝕜))
    fun i j x _ _ ↦ hp.coordChange_ofScalarCore_characterCore_intertwines χ i j x

@[simp] theorem coe_ofScalarCoreCharacterCoreDiffeomorph (χ : G →* 𝕜ˣ) :
    ⇑(hp.ofScalarCoreCharacterCoreDiffeomorph IB n χ) =
      (hp.ofScalarCoreCharacterCoreIso χ).hom.totalSpaceMap := by
  rw [hp.ofScalarCoreCharacterCoreIso_def χ]
  exact TauCeti.FiniteRankBundleCore.coe_constIsoDiffeomorph (I := IB) (n := n) _ _ _

@[simp] theorem coe_ofScalarCoreCharacterCoreDiffeomorph_symm (χ : G →* 𝕜ˣ) :
    ⇑(hp.ofScalarCoreCharacterCoreDiffeomorph IB n χ).symm =
      (hp.ofScalarCoreCharacterCoreIso χ).inv.totalSpaceMap := by
  rw [hp.ofScalarCoreCharacterCoreIso_def χ]
  exact TauCeti.FiniteRankBundleCore.coe_constIsoDiffeomorph_symm (I := IB) (n := n) _ _ _

/-- Over a complete scalar field, `hp.characterFiniteRankCore χ` admits a global compatible `C^n`
trivialization if and only if `hp.characterCore χ` does. -/
theorem exists_trivialization_baseSet_eq_univ_characterFiniteRankCore_iff [CompleteSpace 𝕜]
    (χ : G →* 𝕜ˣ) :
    (∃ (e : Trivialization (Fin (hp.characterFiniteRankCore χ).rank → 𝕜)
          (π _ (hp.characterFiniteRankCore χ).core.Fiber)) (_ : e.IsLinear 𝕜),
        e.toOpenPartialHomeomorph ∈
          (contMDiffFiberwiseLinear X
            (Fin (hp.characterFiniteRankCore χ).rank → 𝕜) IB n).maximalAtlas
            (TotalSpace _ (hp.characterFiniteRankCore χ).core.Fiber) ∧
          e.baseSet = univ) ↔
      ∃ (e : Trivialization 𝕜 (π 𝕜 (hp.characterCore χ).Fiber)) (_ : e.IsLinear 𝕜),
        e.toOpenPartialHomeomorph ∈
          (contMDiffFiberwiseLinear X 𝕜 IB n).maximalAtlas
            (TotalSpace 𝕜 (hp.characterCore χ).Fiber) ∧
          e.baseSet = univ := by
  have hhom : ContMDiff
      (IB.prod 𝓘(𝕜,
        Fin (TauCeti.FiniteRankBundleCore.ofScalarCore (hp.characterCore χ)).rank → 𝕜))
      (IB.prod 𝓘(𝕜, Fin (hp.characterFiniteRankCore χ).rank → 𝕜)) n
      (hp.ofScalarCoreCharacterCoreIso χ).hom.totalSpaceMap :=
    (hp.coe_ofScalarCoreCharacterCoreDiffeomorph IB n χ) ▸
      (hp.ofScalarCoreCharacterCoreDiffeomorph IB n χ).contMDiff
  have hinv : ContMDiff
      (IB.prod 𝓘(𝕜, Fin (hp.characterFiniteRankCore χ).rank → 𝕜))
      (IB.prod 𝓘(𝕜,
        Fin (TauCeti.FiniteRankBundleCore.ofScalarCore (hp.characterCore χ)).rank → 𝕜)) n
      (hp.ofScalarCoreCharacterCoreIso χ).inv.totalSpaceMap :=
    (hp.coe_ofScalarCoreCharacterCoreDiffeomorph_symm IB n χ) ▸
      (hp.ofScalarCoreCharacterCoreDiffeomorph IB n χ).symm.contMDiff
  have hiff := VectorBundleCore.CoordinateHom.exists_trivialization_baseSet_eq_univ_iff_of_inv
    (by simp) (by simp)
    (hp.ofScalarCoreCharacterCoreIso χ).hom (hp.ofScalarCoreCharacterCoreIso χ).inv
    (hp.ofScalarCoreCharacterCoreIso χ).hom_inv_id
    (hp.ofScalarCoreCharacterCoreIso χ).inv_hom_id hhom hinv
  exact hiff.symm.trans
    (TauCeti.FiniteRankBundleCore.exists_trivialization_baseSet_eq_univ_ofScalarCore_iff
      (hp.characterCore χ))

end FiniteRankComparison

/-- A section whose equivariant function upstairs is constant is `C^m`, for every model of the
base and every regularity `m`, without any regularity hypothesis on `p`. -/
theorem contMDiff_section_associatedCore_of_eq_const
    {σ : ∀ x, (hp.associatedCore ρ).Fiber x} {v : F}
    (hv : (hp.associatedSectionEquiv ρ σ : E → F) = Function.const E v) :
    ContMDiff IB (IB.prod 𝓘(𝕜, F)) m (fun x ↦ TotalSpace.mk' F x (σ x)) := by
  intro x
  set y := (hp.associatedCore ρ).indexAt x
  have : MemTrivializationAtlas ((hp.associatedCore ρ).localTriv y) := ⟨⟨y, rfl⟩⟩
  rw [Trivialization.contMDiffAt_section_iff ((hp.associatedCore ρ).localTriv y)
    ((hp.associatedCore ρ).mem_baseSet_at x)]
  refine (contMDiffAt_const (c := v)).congr_of_eventuallyEq ?_
  filter_upwards [((hp.associatedCore ρ).isOpen_baseSet y).mem_nhds
    ((hp.associatedCore ρ).mem_baseSet_at x)] with x' hx'
  rw [associatedCore_baseSet] at hx'
  rw [localTriv_associatedCore_apply_snd _ _ _ hx', hv, Function.const_apply]

/-- The vector bundle associated with the trivial representation has a global trivialization
in its maximal `C^n` atlas, for every quotient covering and normed fibre. -/
theorem exists_trivialization_baseSet_eq_univ_associatedCore_one :
    ∃ (e : Trivialization F (π F (hp.associatedCore (1 : G →* (F →L[𝕜] F)ˣ)).Fiber))
      (_ : e.IsLinear 𝕜),
      e.toOpenPartialHomeomorph ∈ (contMDiffFiberwiseLinear X F IB n).maximalAtlas
        (TotalSpace F (hp.associatedCore (1 : G →* (F →L[𝕜] F)ˣ)).Fiber) ∧
        e.baseSet = univ := by
  let Z := hp.associatedCore (1 : G →* (F →L[𝕜] F)ˣ)
  have hcoord (i j : E) (x : X) (_ : x ∈ Z.baseSet i ∩ Z.baseSet j) (v : F) :
      Z.coordChange i j x v = v := by
    simp [Z]
  exact ⟨Z.globalTrivializationOfCoordChangeEqId hcoord, inferInstance,
    Z.globalTrivializationOfCoordChangeEqId_mem_maximalAtlas hcoord,
    Z.globalTrivializationOfCoordChangeEqId_baseSet hcoord⟩

/-- The line bundle of the trivial character has a global trivialization in its maximal `C^n`
atlas, for every quotient covering. -/
theorem exists_trivialization_baseSet_eq_univ_characterCore_one :
    ∃ (e : Trivialization 𝕜 (π 𝕜 (hp.characterCore (1 : G →* 𝕜ˣ)).Fiber)) (_ : e.IsLinear 𝕜),
      e.toOpenPartialHomeomorph ∈ (contMDiffFiberwiseLinear X 𝕜 IB n).maximalAtlas
        (TotalSpace 𝕜 (hp.characterCore (1 : G →* 𝕜ˣ)).Fiber) ∧ e.baseSet = univ := by
  rw [characterCore_def, MonoidHom.comp_one]
  exact hp.exists_trivialization_baseSet_eq_univ_associatedCore_one

/-- If `p` is a `C^n` local diffeomorphism at `y` and `m ≤ n`, a section of the associated bundle
is `C^m` at `p y` exactly when the corresponding equivariant function is `C^m` at `y`. -/
theorem contMDiffAt_section_associatedCore_iff {y : E}
    (hpd : IsLocalDiffeomorphAt I IB n p y) (hm : m ≤ n)
    {σ : ∀ x, (hp.associatedCore ρ).Fiber x} :
    ContMDiffAt IB (IB.prod 𝓘(𝕜, F)) m (fun x ↦ TotalSpace.mk' F x (σ x)) (p y) ↔
      ContMDiffAt I 𝓘(𝕜, F) m (hp.associatedSectionEquiv ρ σ : E → F) y := by
  have : MemTrivializationAtlas ((hp.associatedCore ρ).localTriv y) := ⟨⟨y, rfl⟩⟩
  rw [Trivialization.contMDiffAt_section_iff ((hp.associatedCore ρ).localTriv y)
      (hp.mem_associatedCore_baseSet_self ρ y),
    ← hpd.contMDiffAt_comp_iff hm]
  exact (hp.eventuallyEq_localTriv_associatedSectionEquiv ρ σ y).contMDiffAt_iff

/-- If `p` is a `C^n` local diffeomorphism and `m ≤ n`, a section of the associated bundle is
`C^m` exactly when the corresponding equivariant function is `C^m`. -/
theorem contMDiff_section_associatedCore_iff (hpd : IsLocalDiffeomorph I IB n p)
    (hm : m ≤ n)
    {σ : ∀ x, (hp.associatedCore ρ).Fiber x} :
    ContMDiff IB (IB.prod 𝓘(𝕜, F)) m (fun x ↦ TotalSpace.mk' F x (σ x)) ↔
      ContMDiff I 𝓘(𝕜, F) m (hp.associatedSectionEquiv ρ σ : E → F) := by
  refine ⟨fun h y ↦ (hp.contMDiffAt_section_associatedCore_iff ρ (hpd y) hm).1 (h (p y)),
    fun h x ↦ ?_⟩
  obtain ⟨y, rfl⟩ := hp.surjective x
  exact (hp.contMDiffAt_section_associatedCore_iff ρ (hpd y) hm).2 (h y)

/-- If `p` is a `C^n` local diffeomorphism at `y` with `n ≠ 0`, a section of the associated bundle
is differentiable at `p y` exactly when its equivariant function is differentiable at `y`. -/
theorem mdifferentiableAt_section_associatedCore_iff {y : E}
    (hpd : IsLocalDiffeomorphAt I IB n p y) (hn : n ≠ 0)
    {σ : ∀ x, (hp.associatedCore ρ).Fiber x} :
    MDifferentiableAt IB (IB.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (σ x)) (p y) ↔
      MDifferentiableAt I 𝓘(𝕜, F) (hp.associatedSectionEquiv ρ σ : E → F) y := by
  have : MemTrivializationAtlas ((hp.associatedCore ρ).localTriv y) := ⟨⟨y, rfl⟩⟩
  rw [Trivialization.mdifferentiableAt_section_iff IB
      ((hp.associatedCore ρ).localTriv y) σ (hp.mem_associatedCore_baseSet_self ρ y),
    ← hpd.mdifferentiableAt_comp_iff hn]
  exact (hp.eventuallyEq_localTriv_associatedSectionEquiv ρ σ y).mdifferentiableAt_iff

/-- If `p` is differentiable at `y`, differentiability of a section at `p y` implies
differentiability of its equivariant function upstairs at `y`. -/
theorem mdifferentiableAt_associatedSectionEquiv {y : E}
    (hpd : MDifferentiableAt I IB p y) {σ : ∀ x, (hp.associatedCore ρ).Fiber x}
    (hσ : MDifferentiableAt IB (IB.prod 𝓘(𝕜, F))
      (fun x ↦ TotalSpace.mk' F x (σ x)) (p y)) :
    MDifferentiableAt I 𝓘(𝕜, F) (hp.associatedSectionEquiv ρ σ : E → F) y := by
  have : MemTrivializationAtlas ((hp.associatedCore ρ).localTriv y) := ⟨⟨y, rfl⟩⟩
  have hc := ((Trivialization.mdifferentiableAt_section_iff IB
    ((hp.associatedCore ρ).localTriv y) σ
    (hp.mem_associatedCore_baseSet_self ρ y)).1 hσ).comp y hpd
  exact hc.congr_of_eventuallyEq
    (hp.eventuallyEq_localTriv_associatedSectionEquiv ρ σ y).symm

/-- If `p` is a `C^n` local diffeomorphism with `n ≠ 0`, a section of the associated bundle is
differentiable exactly when its equivariant function is differentiable. -/
theorem mdifferentiable_section_associatedCore_iff (hpd : IsLocalDiffeomorph I IB n p)
    (hn : n ≠ 0)
    {σ : ∀ x, (hp.associatedCore ρ).Fiber x} :
    MDifferentiable IB (IB.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (σ x)) ↔
      MDifferentiable I 𝓘(𝕜, F) (hp.associatedSectionEquiv ρ σ : E → F) := by
  refine ⟨fun h y ↦ (hp.mdifferentiableAt_section_associatedCore_iff ρ (hpd y) hn).1 (h (p y)),
    fun h x ↦ ?_⟩
  obtain ⟨y, rfl⟩ := hp.surjective x
  exact (hp.mdifferentiableAt_section_associatedCore_iff ρ (hpd y) hn).2 (h y)

variable [CompleteSpace 𝕜] (hpd : IsLocalDiffeomorph I IB n p)
include hpd

/-- If `p` is a `C^n` local diffeomorphism, the bundle associated with a representation on a line
has a global trivialization in its maximal `C^n` atlas exactly when there is a nowhere-vanishing
`C^n` equivariant function on `E`. -/
theorem exists_trivialization_baseSet_eq_univ_associatedCore_iff (hF : finrank 𝕜 F = 1) :
    (∃ (e : Trivialization F (π F (hp.associatedCore ρ).Fiber)) (_ : e.IsLinear 𝕜),
        e.toOpenPartialHomeomorph ∈ (contMDiffFiberwiseLinear X F IB n).maximalAtlas
          (TotalSpace F (hp.associatedCore ρ).Fiber) ∧ e.baseSet = univ) ↔
      ∃ f : E → F, ContMDiff I 𝓘(𝕜, F) n f ∧ (∀ y, f y ≠ 0) ∧
        ∀ (g : G) (y : E), f (g • y) = (ρ g : F →L[𝕜] F) (f y) := by
  rw [ContMDiffVectorBundle.exists_trivialization_baseSet_eq_univ_iff_exists_ne_zero hF]
  constructor
  · rintro ⟨σ, hσ, hσ₀⟩
    refine ⟨hp.associatedSectionEquiv ρ σ,
      (hp.contMDiff_section_associatedCore_iff ρ hpd le_rfl).1 hσ, fun y ↦ ?_,
      (hp.associatedSectionEquiv ρ σ).property⟩
    rw [Ne, associatedSectionEquiv_apply_eq_zero_iff]
    exact hσ₀ _
  · rintro ⟨f, hf, hf₀, hfG⟩
    set σ := (hp.associatedSectionEquiv ρ).symm ⟨f, hfG⟩
    have hσ : (hp.associatedSectionEquiv ρ σ : E → F) = f := by
      simp only [σ, Equiv.apply_symm_apply]
    refine ⟨σ, (hp.contMDiff_section_associatedCore_iff ρ hpd le_rfl).2 (hσ ▸ hf), fun x ↦ ?_⟩
    obtain ⟨y, rfl⟩ := hp.surjective x
    rw [Ne, ← associatedSectionEquiv_apply_eq_zero_iff, hσ]
    exact hf₀ y

/-- If `p` is a `C^n` local diffeomorphism, the line bundle of a character `χ` of the deck group
has a global trivialization in its maximal `C^n` atlas exactly when there is a nowhere-vanishing
`C^n` function `f` on `E` with `f (g • y) = χ g * f y`. Over a complex manifold with `n = ∞`, the
holomorphic line bundle of `χ` is holomorphically trivial exactly when such a holomorphic `f`
exists. -/
theorem exists_trivialization_baseSet_eq_univ_characterCore_iff (χ : G →* 𝕜ˣ) :
    (∃ (e : Trivialization 𝕜 (π 𝕜 (hp.characterCore χ).Fiber)) (_ : e.IsLinear 𝕜),
        e.toOpenPartialHomeomorph ∈ (contMDiffFiberwiseLinear X 𝕜 IB n).maximalAtlas
          (TotalSpace 𝕜 (hp.characterCore χ).Fiber) ∧ e.baseSet = univ) ↔
      ∃ f : E → 𝕜, ContMDiff I 𝓘(𝕜) n f ∧ (∀ y, f y ≠ 0) ∧
        ∀ (g : G) (y : E), f (g • y) = χ g * f y := by
  rw [characterCore_def,
    hp.exists_trivialization_baseSet_eq_univ_associatedCore_iff _ hpd (finrank_self 𝕜)]
  simp

end IsQuotientCoveringMap

/-! ### Twisting `C^n` chart operators and bundle equivalences of scalar character cores -/

namespace IsQuotientCoveringMap

section CharacterTwisting

open VectorBundleCore

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB}
  {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X] [ChartedSpace HB X]
  [Group G] [MulAction G E] {p : E → X} (hp : IsQuotientCoveringMap p G) {n : ℕ∞ω}

/-- Multiplying a `C^n` operator-valued function on a chart overlap by the locally constant scalar
`ψ (hp.deckChange e e' x)` preserves `ContMDiffOn`. -/
private theorem contMDiffOn_deckChange_smul (ψ : G →* 𝕜ˣ) {e e' : E}
    {g : X → 𝕜 →L[𝕜] 𝕜}
    (hg : ContMDiffOn IB 𝓘(𝕜, 𝕜 →L[𝕜] 𝕜) n g
      ((hp.isLocalHomeomorph.localInverseAt e).source ∩
        (hp.isLocalHomeomorph.localInverseAt e').source)) :
    ContMDiffOn IB 𝓘(𝕜, 𝕜 →L[𝕜] 𝕜) n (fun x ↦ (ψ (hp.deckChange e e' x) : 𝕜) • g x)
      ((hp.isLocalHomeomorph.localInverseAt e).source ∩
        (hp.isLocalHomeomorph.localInverseAt e').source) :=
  have hψ : ContMDiffOn IB 𝓘(𝕜) n (fun x ↦ (ψ (hp.deckChange e e' x) : 𝕜))
      ((hp.isLocalHomeomorph.localInverseAt e).source ∩
        (hp.isLocalHomeomorph.localInverseAt e').source) :=
    TauCeti.contMDiffOn_of_eventuallyEq_const fun _ hx ↦
      ((hp.eventually_deckChange_eq hx).mono fun _ h ↦ congrArg (fun g ↦ (ψ g : 𝕜)) h).filter_mono
        nhdsWithin_le_nhds
  hψ.smul hg

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

/-- Twisting a cocycle morphism via `hp.characterCoreHomEquiv χ₁ χ₂` preserves `C^n` regularity of
its glued total-space map. -/
theorem contMDiff_totalSpaceMap_characterCoreHomEquiv_iff [CompleteSpace 𝕜] (χ₁ χ₂ : G →* 𝕜ˣ)
    (a : CoordinateHom (hp.characterCore χ₁) (hp.characterCore χ₂)) :
    ContMDiff (IB.prod 𝓘(𝕜)) (IB.prod 𝓘(𝕜)) n
        (hp.characterCoreHomEquiv χ₁ χ₂ a).totalSpaceMap ↔
      ContMDiff (IB.prod 𝓘(𝕜)) (IB.prod 𝓘(𝕜)) n a.totalSpaceMap := by
  rw [CoordinateHom.contMDiff_totalSpaceMap_iff, CoordinateHom.contMDiff_totalSpaceMap_iff]
  exact forall₂_congr fun e e' ↦
    hp.contMDiffOn_inChartCoordinates_characterCoreHomEquiv_iff χ₁ χ₂ a e e'

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

private noncomputable def characterCoreSectionHom (χ₁ χ₂ : G →* 𝕜ˣ) {σ : X → 𝕜}
    (hσ : ContMDiff IB (IB.prod 𝓘(𝕜)) n fun x ↦
      TotalSpace.mk' 𝕜 (E := (hp.characterCore (χ₁⁻¹ * χ₂)).Fiber) x (σ x)) :
    CoordinateHom (hp.characterCore χ₁) (hp.characterCore χ₂) :=
  let ϕ : X → 𝕜 →L[𝕜] 𝕜 := fun x ↦ (ContinuousLinearMap.id 𝕜 𝕜).smulRight (σ x)
  have hϕon := hp.contMDiffOn_inChartCoordinates_smulRight_of_section (χ₁⁻¹ * χ₂) hσ
  have hϕ : ContMDiff IB (IB.prod 𝓘(𝕜, 𝕜 →L[𝕜] 𝕜)) n (fun x ↦
      TotalSpace.mk' (𝕜 →L[𝕜] 𝕜)
        (E := fun y ↦ (hp.characterCore (1 : G →* 𝕜ˣ)).Fiber y →L[𝕜]
          (hp.characterCore (χ₁⁻¹ * χ₂)).Fiber y) x (ϕ x)) :=
    contMDiff_hom_bundle_iff_forall_contMDiffOn.2 hϕon
  (hp.characterCoreHomEquiv χ₁ χ₂).symm (CoordinateHom.ofContinuous ϕ hϕ.continuous)

private theorem fiberMap_characterCoreSectionHom (χ₁ χ₂ : G →* 𝕜ˣ) {σ : X → 𝕜}
    (hσ : ContMDiff IB (IB.prod 𝓘(𝕜)) n fun x ↦
      TotalSpace.mk' 𝕜 (E := (hp.characterCore (χ₁⁻¹ * χ₂)).Fiber) x (σ x))
    (x : X) (v : 𝕜) :
    (hp.characterCoreSectionHom χ₁ χ₂ hσ).fiberMap x v = σ x * v := by
  simp only [characterCoreSectionHom, hp.fiberMap_characterCoreHomEquiv_symm,
    CoordinateHom.fiberMap_ofContinuous, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul]
  exact mul_comm v (σ x)

private theorem bijective_characterCoreSectionHom (χ₁ χ₂ : G →* 𝕜ˣ) {σ : X → 𝕜}
    (hσ : ContMDiff IB (IB.prod 𝓘(𝕜)) n fun x ↦
      TotalSpace.mk' 𝕜 (E := (hp.characterCore (χ₁⁻¹ * χ₂)).Fiber) x (σ x))
    (hσ₀ : ∀ x, σ x ≠ 0) (x : X) :
    Function.Bijective ((hp.characterCoreSectionHom χ₁ χ₂ hσ).fiberMap x) := by
  have hc : σ x ≠ 0 := hσ₀ x
  refine ⟨fun _ _ huv ↦ ?_, fun w ↦ ⟨(σ x)⁻¹ * w, ?_⟩⟩
  · rw [hp.fiberMap_characterCoreSectionHom, hp.fiberMap_characterCoreSectionHom] at huv
    exact mul_left_cancel₀ hc huv
  · rw [hp.fiberMap_characterCoreSectionHom, mul_inv_cancel_left₀ hc w]

variable [CompleteSpace 𝕜] (IB n)

/-- Over a complete scalar field, a nowhere-vanishing `C^n` section `σ` of
`hp.characterCore (χ₁⁻¹ * χ₂)` induces a `C^n` bundle diffeomorphism from
`hp.characterCore χ₁` to `hp.characterCore χ₂` over `X`, multiplying each fibre by `σ x`. -/
noncomputable def characterCoreDiffeomorphOfSectionNeZero (χ₁ χ₂ : G →* 𝕜ˣ) {σ : X → 𝕜}
    (hσ : ContMDiff IB (IB.prod 𝓘(𝕜)) n fun x ↦
      TotalSpace.mk' 𝕜 (E := (hp.characterCore (χ₁⁻¹ * χ₂)).Fiber) x (σ x))
    (hσ₀ : ∀ x, σ x ≠ 0) :
    (hp.characterCore χ₁).TotalSpace ≃ₘ^n⟮IB.prod 𝓘(𝕜), IB.prod 𝓘(𝕜)⟯
      (hp.characterCore χ₂).TotalSpace :=
  (hp.characterCoreSectionHom χ₁ χ₂ hσ).toDiffeomorph
    (fun i j ↦ by
      rw [← hp.contMDiffOn_inChartCoordinates_characterCoreHomEquiv_iff χ₁ χ₂ _ i j]
      simp only [characterCoreSectionHom, (hp.characterCoreHomEquiv χ₁ χ₂).apply_symm_apply,
        CoordinateHom.fiberMap_ofContinuous]
      exact hp.contMDiffOn_inChartCoordinates_smulRight_of_section (χ₁⁻¹ * χ₂) hσ i j)
    (hp.bijective_characterCoreSectionHom χ₁ χ₂ hσ hσ₀)

@[simp]
theorem characterCoreDiffeomorphOfSectionNeZero_apply (χ₁ χ₂ : G →* 𝕜ˣ) {σ : X → 𝕜}
    (hσ : ContMDiff IB (IB.prod 𝓘(𝕜)) n fun x ↦
      TotalSpace.mk' 𝕜 (E := (hp.characterCore (χ₁⁻¹ * χ₂)).Fiber) x (σ x))
    (hσ₀ : ∀ x, σ x ≠ 0) (q : (hp.characterCore χ₁).TotalSpace) :
    hp.characterCoreDiffeomorphOfSectionNeZero IB n χ₁ χ₂ hσ hσ₀ q =
      ⟨q.proj, σ q.proj • q.snd⟩ := by
  rcases q with ⟨x, v⟩
  rw [characterCoreDiffeomorphOfSectionNeZero, CoordinateHom.coe_toDiffeomorph,
    CoordinateHom.totalSpaceMap_mk]
  exact TotalSpace.ext rfl (heq_of_eq (hp.fiberMap_characterCoreSectionHom χ₁ χ₂ hσ x v))

@[simp]
theorem characterCoreDiffeomorphOfSectionNeZero_symm_apply (χ₁ χ₂ : G →* 𝕜ˣ) {σ : X → 𝕜}
    (hσ : ContMDiff IB (IB.prod 𝓘(𝕜)) n fun x ↦
      TotalSpace.mk' 𝕜 (E := (hp.characterCore (χ₁⁻¹ * χ₂)).Fiber) x (σ x))
    (hσ₀ : ∀ x, σ x ≠ 0) (q : (hp.characterCore χ₂).TotalSpace) :
    (hp.characterCoreDiffeomorphOfSectionNeZero IB n χ₁ χ₂ hσ hσ₀).symm q =
      ⟨q.proj, (σ q.proj)⁻¹ • q.snd⟩ := by
  refine (hp.characterCoreDiffeomorphOfSectionNeZero IB n χ₁ χ₂ hσ hσ₀).injective ?_
  have h1 := (hp.characterCoreDiffeomorphOfSectionNeZero IB n χ₁ χ₂ hσ hσ₀).apply_symm_apply q
  have h2 := hp.characterCoreDiffeomorphOfSectionNeZero_apply IB n χ₁ χ₂ hσ hσ₀
    ⟨q.proj, (σ q.proj)⁻¹ • q.snd⟩
  have h3 : q = ⟨q.proj, σ q.proj • ((σ q.proj)⁻¹ • q.snd)⟩ :=
    TotalSpace.ext rfl (heq_of_eq (smul_inv_smul₀ (hσ₀ q.proj) (q.snd : 𝕜)).symm)
  exact h1.trans (h3.trans h2.symm)

variable {IB n}

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
  let s : X → 𝕜 := fun x ↦ σ x
  refine ⟨(hp.characterCoreSectionHom χ₁ χ₂ (σ := s) hσ).fiberEquiv
      (hp.bijective_characterCoreSectionHom χ₁ χ₂ (σ := s) hσ hσ₀),
    (hp.characterCoreDiffeomorphOfSectionNeZero IB n χ₁ χ₂ (σ := s) hσ hσ₀).contMDiff.congr
      fun q ↦ ?_⟩
  have h := hp.characterCoreDiffeomorphOfSectionNeZero_apply IB n χ₁ χ₂ (σ := s) hσ hσ₀ q
  have h1 : TotalSpace.mk' 𝕜 q.proj (((hp.characterCoreSectionHom χ₁ χ₂ (σ := s) hσ).fiberEquiv
        (hp.bijective_characterCoreSectionHom χ₁ χ₂ (σ := s) hσ hσ₀) q.proj) q.snd) =
      ⟨q.proj, s q.proj • q.snd⟩ :=
    TotalSpace.ext rfl (heq_of_eq ((CoordinateHom.fiberEquiv_apply _ _ q.proj q.snd).trans
      (hp.fiberMap_characterCoreSectionHom χ₁ χ₂ (σ := s) hσ q.proj q.snd)))
  exact h1.trans h.symm

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
  have hbtot : ContMDiff (IB.prod 𝓘(𝕜)) (IB.prod 𝓘(𝕜)) n b.totalSpaceMap :=
    (hp.contMDiff_totalSpaceMap_characterCoreHomEquiv_iff χ₁ χ₂ a).2
      (a.contMDiff_totalSpaceMap ha)
  refine ⟨fun x ↦ b.fiberMap x (1 : 𝕜),
    (hbtot.comp hp.contMDiff_one_section_characterCore_one).congr fun x ↦
      (CoordinateHom.totalSpaceMap_mk b x (1 : 𝕜)).symm, fun x h0 ↦ ?_⟩
  have h0' : (hp.characterCoreHomEquiv χ₁ χ₂ a).fiberMap x (1 : 𝕜) = 0 := h0
  rw [hp.fiberMap_characterCoreHomEquiv] at h0'
  exact one_ne_zero ((hbij x).1 (h0'.trans (map_zero (a.fiberMap x)).symm))

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

end CharacterTwisting

end IsQuotientCoveringMap

/-! ### Holomorphic sections over a compact connected covering space -/

namespace IsQuotientCoveringMap

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℂ EM] {HM : Type*}
  [TopologicalSpace HM] {I : ModelWithCorners ℂ EM HM} [I.Boundaryless]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℂ EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners ℂ EB HB}
  {E X G : Type*} [TopologicalSpace E] [ChartedSpace HM E] [IsManifold I 1 E] [CompactSpace E]
  [TopologicalSpace X] [ChartedSpace HB X] [Group G] [MulAction G E]
  {p : E → X} (hp : IsQuotientCoveringMap p G)
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] (ρ : G →* (F →L[ℂ] F)ˣ) {n m : ℕ∞ω}
  (hpd : MDifferentiable I IB p)
include hpd

/-- If `p` is differentiable with compact preconnected complex covering manifold `E`, a section
of the bundle associated with `ρ` over `X` is differentiable exactly when its equivariant function
upstairs is constant with a `ρ`-invariant value. -/
theorem mdifferentiable_section_associatedCore_iff_exists_eq_const [PreconnectedSpace E]
    {σ : ∀ x, (hp.associatedCore ρ).Fiber x} :
    MDifferentiable IB (IB.prod 𝓘(ℂ, F)) (fun x ↦ TotalSpace.mk' F x (σ x)) ↔
      ∃ v : F, (∀ g : G, (ρ g : F →L[ℂ] F) v = v) ∧
        (hp.associatedSectionEquiv ρ σ : E → F) = Function.const E v := by
  refine ⟨fun hσ ↦ ?_, fun ⟨v, _, hv⟩ ↦
    (hp.contMDiff_section_associatedCore_of_eq_const (m := 1) ρ hv).mdifferentiable one_ne_zero⟩
  have hf : MDifferentiable I 𝓘(ℂ, F) (hp.associatedSectionEquiv ρ σ : E → F) :=
    fun y ↦ hp.mdifferentiableAt_associatedSectionEquiv ρ (hpd y) (hσ (p y))
  cases isEmpty_or_nonempty E with
  | inl hE => exact ⟨0, fun g ↦ map_zero _, funext fun y ↦ isEmptyElim y⟩
  | inr hE =>
    -- A holomorphic function on a compact connected complex manifold is constant.
    obtain ⟨v, hv⟩ := hf.exists_eq_const_of_compactSpace
    refine ⟨v, fun g ↦ ?_, hv⟩
    obtain ⟨y⟩ : Nonempty E := inferInstance
    have h := (hp.associatedSectionEquiv ρ σ).property g y
    rw [hv, Function.const_apply, Function.const_apply] at h
    exact h.symm

/-- If `p` is differentiable with compact preconnected complex covering manifold `E`, a section
of the bundle associated with `ρ` over `X` is `C^m`, for `m ≠ 0`, exactly when its equivariant
function upstairs is constant with a `ρ`-invariant value. -/
theorem contMDiff_section_associatedCore_iff_exists_eq_const [PreconnectedSpace E]
    (hm₀ : m ≠ 0) {σ : ∀ x, (hp.associatedCore ρ).Fiber x} :
    ContMDiff IB (IB.prod 𝓘(ℂ, F)) m (fun x ↦ TotalSpace.mk' F x (σ x)) ↔
      ∃ v : F, (∀ g : G, (ρ g : F →L[ℂ] F) v = v) ∧
        (hp.associatedSectionEquiv ρ σ : E → F) = Function.const E v := by
  refine ⟨fun hσ ↦
    (hp.mdifferentiable_section_associatedCore_iff_exists_eq_const ρ hpd).1
      (hσ.mdifferentiable hm₀), fun ⟨_, _, hv⟩ ↦ ?_⟩
  exact hp.contMDiff_section_associatedCore_of_eq_const ρ hv

/-- If `p` is differentiable with compact preconnected complex covering manifold `E`, the
line bundle over `X` associated with a nontrivial representation has no nonzero differentiable
section. -/
theorem eq_zero_of_mdifferentiable_section_associatedCore [PreconnectedSpace E]
    (hF : finrank ℂ F = 1) (hρ : ρ ≠ 1) {σ : ∀ x, (hp.associatedCore ρ).Fiber x}
    (hσ : MDifferentiable IB (IB.prod 𝓘(ℂ, F)) (fun x ↦ TotalSpace.mk' F x (σ x))) :
    σ = 0 := by
  obtain ⟨v, hvG, hv⟩ :=
    (hp.mdifferentiable_section_associatedCore_iff_exists_eq_const ρ hpd).1 hσ
  have hv₀ : v = 0 := by
    by_contra hv₀
    apply hρ
    ext g w
    obtain ⟨c, rfl⟩ := exists_smul_eq_of_finrank_eq_one hF hv₀ w
    simp [hvG g]
  funext x
  obtain ⟨y, rfl⟩ := hp.surjective x
  refine (hp.associatedSectionEquiv_apply_eq_zero_iff ρ σ y).1 ?_
  rw [hv, Function.const_apply, hv₀]

/-- If `p` is differentiable with compact preconnected complex covering manifold `E`, the
line bundle over `X` associated with a nontrivial representation has no nonzero `C^m` section
when `m ≠ 0`. -/
theorem eq_zero_of_contMDiff_section_associatedCore [PreconnectedSpace E]
    (hF : finrank ℂ F = 1) (hρ : ρ ≠ 1) (hm₀ : m ≠ 0)
    {σ : ∀ x, (hp.associatedCore ρ).Fiber x}
    (hσ : ContMDiff IB (IB.prod 𝓘(ℂ, F)) m (fun x ↦ TotalSpace.mk' F x (σ x))) : σ = 0 :=
  hp.eq_zero_of_mdifferentiable_section_associatedCore ρ hpd hF hρ (hσ.mdifferentiable hm₀)

/-- If `p` is differentiable with compact preconnected complex covering manifold `E`, the
line bundle of a nontrivial character `χ` over `X` has no nonzero differentiable section. -/
theorem eq_zero_of_mdifferentiable_section_characterCore [PreconnectedSpace E] {χ : G →* ℂˣ}
    (hχ : χ ≠ 1) {σ : ∀ x, (hp.characterCore χ).Fiber x}
    (hσ : MDifferentiable IB (IB.prod 𝓘(ℂ)) (fun x ↦ TotalSpace.mk' ℂ x (σ x))) : σ = 0 := by
  revert σ
  rw [characterCore_def]
  intro σ hσ
  refine hp.eq_zero_of_mdifferentiable_section_associatedCore _ hpd (finrank_self ℂ) ?_ hσ
  exact fun hρ ↦ hχ ((MonoidHom.comp_eq_one_iff (Units.map_injective
    (FaithfulSMul.algebraMap_injective ℂ (ℂ →L[ℂ] ℂ)))).1 hρ)

/-- If `p` is differentiable with compact preconnected complex covering manifold `E`, the
line bundle of a nontrivial character over `X` has no nonzero `C^m` section when `m ≠ 0`. -/
theorem eq_zero_of_contMDiff_section_characterCore [PreconnectedSpace E] {χ : G →* ℂˣ}
    (hχ : χ ≠ 1) (hm₀ : m ≠ 0) {σ : ∀ x, (hp.characterCore χ).Fiber x}
    (hσ : ContMDiff IB (IB.prod 𝓘(ℂ)) m (fun x ↦ TotalSpace.mk' ℂ x (σ x))) : σ = 0 :=
  hp.eq_zero_of_mdifferentiable_section_characterCore hpd hχ (hσ.mdifferentiable hm₀)

/-- If `p` is differentiable with compact connected complex covering manifold `E`, the vector
bundle over `X` associated with `ρ` has a global trivialization in its maximal `C^n` atlas,
for `n ≠ 0`, exactly when `ρ` is trivial. -/
theorem exists_trivialization_baseSet_eq_univ_associatedCore_iff_eq_one [ConnectedSpace E]
    (hn : n ≠ 0) :
    (∃ (e : Trivialization F (π F (hp.associatedCore ρ).Fiber)) (_ : e.IsLinear ℂ),
        e.toOpenPartialHomeomorph ∈ (contMDiffFiberwiseLinear X F IB n).maximalAtlas
          (TotalSpace F (hp.associatedCore ρ).Fiber) ∧ e.baseSet = univ) ↔ ρ = 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸
    hp.exists_trivialization_baseSet_eq_univ_associatedCore_one⟩
  obtain ⟨e, -, he, hbase⟩ := h
  obtain ⟨y₀⟩ : Nonempty E := inferInstance
  ext g v
  let e₀ := (hp.associatedCore ρ).localTriv y₀
  have hy₀ := hp.mem_associatedCore_baseSet_self ρ y₀
  let w := (e ⟨p y₀, e₀.symm (p y₀) v⟩).2
  let σ : ∀ x, (hp.associatedCore ρ).Fiber x := fun x ↦ e.symm x w
  have hx (x : X) : x ∈ e.baseSet := hbase ▸ mem_univ x
  have hσ : ContMDiff IB (IB.prod 𝓘(ℂ, F)) n (fun x ↦ TotalSpace.mk' F x (σ x)) := by
    rw [← contMDiffOn_univ]
    apply (e.contMDiffOn_section_iff_of_mem_maximalAtlas he (by simp [hbase])).2
    simpa only [σ, e.apply_mk_symm (hx _)] using
      (contMDiffOn_const : ContMDiffOn IB 𝓘(ℂ, F) n (fun _ : X ↦ w) univ)
  obtain ⟨v', hv'G, hv'⟩ :=
    (hp.contMDiff_section_associatedCore_iff_exists_eq_const ρ hpd hn).1 hσ
  have hv : v' = v := by
    simpa only [associatedSectionEquiv_apply_coe, Function.const_apply, σ, w,
      e.symm_apply_apply_mk (hx _), e₀,
      ((hp.associatedCore ρ).localTriv y₀).apply_mk_symm hy₀] using
      (congrFun hv' y₀).symm
  simpa only [hv, MonoidHom.one_apply, Units.val_one, one_apply_eq_self] using hv'G g

/-- If `p` is differentiable with compact connected complex covering manifold `E`, the line
bundle of a character `χ` over `X` has a global trivialization in its maximal `C^n` atlas,
for `n ≠ 0`, exactly when `χ` is trivial. In particular, the holomorphic line bundle of a
nontrivial character is not holomorphically trivial. -/
theorem exists_trivialization_baseSet_eq_univ_characterCore_iff_eq_one [ConnectedSpace E]
    (hn : n ≠ 0) (χ : G →* ℂˣ) :
    (∃ (e : Trivialization ℂ (π ℂ (hp.characterCore χ).Fiber)) (_ : e.IsLinear ℂ),
        e.toOpenPartialHomeomorph ∈ (contMDiffFiberwiseLinear X ℂ IB n).maximalAtlas
          (TotalSpace ℂ (hp.characterCore χ).Fiber) ∧ e.baseSet = univ) ↔ χ = 1 := by
  rw [characterCore_def,
    hp.exists_trivialization_baseSet_eq_univ_associatedCore_iff_eq_one _ hpd hn]
  exact MonoidHom.comp_eq_one_iff (Units.map_injective
    (FaithfulSMul.algebraMap_injective ℂ (ℂ →L[ℂ] ℂ)))

/-- When `E` is a compact connected complex manifold and `p : E → X` is differentiable (`n ≠ 0`),
two character line bundles `hp.characterCore χ₁` and `hp.characterCore χ₂` are `C^n`
bundle-equivalent (in particular holomorphically isomorphic at `n = ∞`) if and only if
`χ₁ = χ₂`. -/
theorem exists_bundleDiffeomorph_characterCore_iff_eq [ConnectedSpace E]
    (hn : n ≠ 0) (χ₁ χ₂ : G →* ℂˣ) :
    (∃ e : ∀ x, (hp.characterCore χ₁).Fiber x ≃L[ℂ] (hp.characterCore χ₂).Fiber x,
        ContMDiff (IB.prod 𝓘(ℂ)) (IB.prod 𝓘(ℂ)) n
          (fun p : (hp.characterCore χ₁).TotalSpace ↦ TotalSpace.mk' ℂ p.proj (e p.proj p.snd))) ↔
      χ₁ = χ₂ :=
  ((hp.exists_bundleDiffeomorph_characterCore_iff_exists_trivialization χ₁ χ₂).trans
    (hp.exists_trivialization_baseSet_eq_univ_characterCore_iff_eq_one hpd hn
      (χ₁⁻¹ * χ₂))).trans
    ⟨fun h ↦ DFunLike.ext _ _ fun g ↦ inv_mul_eq_one.1 (DFunLike.congr_fun h g),
      fun h ↦ h ▸ DFunLike.ext _ _ fun g ↦ inv_mul_cancel (χ₁ g)⟩

end IsQuotientCoveringMap
