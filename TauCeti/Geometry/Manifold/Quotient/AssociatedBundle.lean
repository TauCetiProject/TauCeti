/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Complex
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
public import TauCeti.Geometry.Manifold.VectorBundle.FrameTrivialization
public import TauCeti.Topology.Covering.AssociatedBundle

/-!
# Smooth and holomorphic bundles associated with representations of a deck group

Let `p : E → X` be a quotient covering map for a group `G` (`IsQuotientCoveringMap p G`), and let
`ρ : G →* (F →L[𝕜] F)ˣ` be a representation of `G`. The transitions of the associated vector
bundle `IsQuotientCoveringMap.associatedCore ρ` over `X` are locally constant, so for every model
and every regularity they are `C^n`: the associated bundle is a `C^n` vector bundle over any
charted space `X` (`IsQuotientCoveringMap.isContMDiff_associatedCore`), including analytic
regularity. Over a complex manifold, modelled on `𝓘(ℂ, EB)` with `n = ∞`, it is a holomorphic
vector bundle, and for a character `χ : G →* ℂˣ` the core `IsQuotientCoveringMap.characterCore χ`
is a holomorphic line bundle.

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

When `E` is moreover a compact connected complex manifold, every holomorphic function on `E` is
constant (`MDifferentiable.exists_eq_const_of_compactSpace`, the maximum principle). Hence the
holomorphic sections of the bundle associated with `ρ` correspond to the `ρ`-invariant vectors of
`F` (`IsQuotientCoveringMap.contMDiff_section_associatedCore_iff_exists_eq_const`), the line bundle
of a nontrivial character has no nonzero holomorphic section
(`IsQuotientCoveringMap.eq_zero_of_contMDiff_section_characterCore`), and the line bundle of `χ` is
holomorphically trivial exactly when `χ = 1`
(`IsQuotientCoveringMap.exists_trivialization_baseSet_eq_univ_characterCore_iff_eq_one`).

## Main results

* `IsQuotientCoveringMap.isContMDiff_associatedCore`: the associated bundle is `C^n`.
* `IsQuotientCoveringMap.contMDiffAt_section_associatedCore_iff`,
  `IsQuotientCoveringMap.contMDiff_section_associatedCore_iff`: a section is `C^m` at `p y`, or
  globally, exactly when the corresponding equivariant function is `C^m` at `y`, or globally.
* `IsQuotientCoveringMap.exists_trivialization_baseSet_eq_univ_associatedCore_iff`,
  `IsQuotientCoveringMap.exists_trivialization_baseSet_eq_univ_characterCore_iff`: an associated
  line bundle is trivial exactly when there is a nowhere-vanishing equivariant function upstairs.
* `IsQuotientCoveringMap.contMDiff_section_associatedCore_iff_exists_eq_const`: over a compact
  preconnected complex manifold `E`, holomorphic sections are constant `ρ`-invariant functions
  upstairs.
* `IsQuotientCoveringMap.eq_zero_of_contMDiff_section_characterCore`,
  `IsQuotientCoveringMap.exists_trivialization_baseSet_eq_univ_characterCore_iff_eq_one`: over a
  compact connected complex manifold `E`, the line bundle of a nontrivial character has no nonzero
  holomorphic section and is not holomorphically trivial.

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

/-- The line bundle of the trivial character has a global trivialization in its maximal `C^n`
atlas: the section attached to the constant function `1` reads as `1` in every chart. -/
theorem exists_trivialization_baseSet_eq_univ_characterCore_one [CompleteSpace 𝕜] :
    ∃ (e : Trivialization 𝕜 (π 𝕜 (hp.characterCore (1 : G →* 𝕜ˣ)).Fiber)) (_ : e.IsLinear 𝕜),
      e.toOpenPartialHomeomorph ∈ (contMDiffFiberwiseLinear X 𝕜 IB n).maximalAtlas
        (TotalSpace 𝕜 (hp.characterCore (1 : G →* 𝕜ˣ)).Fiber) ∧ e.baseSet = univ := by
  rw [characterCore_def]
  set ρ₁ := (Units.map (algebraMap 𝕜 (𝕜 →L[𝕜] 𝕜)).toMonoidHom).comp (1 : G →* 𝕜ˣ)
  rw [ContMDiffVectorBundle.exists_trivialization_baseSet_eq_univ_iff_exists_ne_zero
    (finrank_self 𝕜)]
  refine ⟨(hp.associatedSectionEquiv ρ₁).symm ⟨fun _ ↦ 1, fun g y ↦ by simp [ρ₁]⟩, fun x ↦ ?_,
    fun x ↦ ?_⟩
  · set y := (hp.associatedCore ρ₁).indexAt x
    have : MemTrivializationAtlas ((hp.associatedCore ρ₁).localTriv y) := ⟨⟨y, rfl⟩⟩
    rw [Trivialization.contMDiffAt_section_iff ((hp.associatedCore ρ₁).localTriv y)
      ((hp.associatedCore ρ₁).mem_baseSet_at x)]
    refine (contMDiffAt_const (c := (1 : 𝕜))).congr_of_eventuallyEq ?_
    filter_upwards [((hp.associatedCore ρ₁).isOpen_baseSet y).mem_nhds
      ((hp.associatedCore ρ₁).mem_baseSet_at x)] with x' hx'
    rw [associatedCore_baseSet] at hx'
    rw [localTriv_associatedSectionEquiv_symm_apply_snd _ _ _ hx']
  · rw [associatedSectionEquiv_symm_apply]
    exact one_ne_zero (α := 𝕜)

variable (hpd : IsLocalDiffeomorph I IB n p)
include hpd

/-- If `p` is a `C^n` local diffeomorphism and `m ≤ n`, a section of the associated bundle is
`C^m` at `p y` exactly when the corresponding equivariant function is `C^m` at `y`. -/
theorem contMDiffAt_section_associatedCore_iff (hm : m ≤ n)
    {σ : ∀ x, (hp.associatedCore ρ).Fiber x} {y : E} :
    ContMDiffAt IB (IB.prod 𝓘(𝕜, F)) m (fun x ↦ TotalSpace.mk' F x (σ x)) (p y) ↔
      ContMDiffAt I 𝓘(𝕜, F) m (hp.associatedSectionEquiv ρ σ : E → F) y := by
  have : MemTrivializationAtlas ((hp.associatedCore ρ).localTriv y) := ⟨⟨y, rfl⟩⟩
  set s := hp.isLocalHomeomorph.localInverseAt y
  rw [Trivialization.contMDiffAt_section_iff ((hp.associatedCore ρ).localTriv y)
      (hp.mem_associatedCore_baseSet_self ρ y),
    ← (hpd y).contMDiffAt_comp_iff hm]
  refine Filter.EventuallyEq.contMDiffAt_iff ?_
  -- Near `y`, the section read in the chart through `y` and pulled back along `p` is the
  -- equivariant function, since the local section through `y` inverts `p` there.
  filter_upwards [s.open_target.mem_nhds (hp.isLocalHomeomorph.self_mem_localInverseAt_target)]
    with z hz
  have hsource := s.map_target hz
  have hinv := s.right_inv hz
  rw [hp.isLocalHomeomorph.localInverseAt_symm] at hsource hinv
  rw [Function.comp_apply, localTriv_associatedCore_apply_snd _ _ _ hsource, hinv]

/-- If `p` is a `C^n` local diffeomorphism and `m ≤ n`, a section of the associated bundle is
`C^m` exactly when the corresponding equivariant function is `C^m`. -/
theorem contMDiff_section_associatedCore_iff (hm : m ≤ n)
    {σ : ∀ x, (hp.associatedCore ρ).Fiber x} :
    ContMDiff IB (IB.prod 𝓘(𝕜, F)) m (fun x ↦ TotalSpace.mk' F x (σ x)) ↔
      ContMDiff I 𝓘(𝕜, F) m (hp.associatedSectionEquiv ρ σ : E → F) := by
  refine ⟨fun h y ↦ (hp.contMDiffAt_section_associatedCore_iff ρ hpd hm).1 (h (p y)),
    fun h x ↦ ?_⟩
  obtain ⟨y, rfl⟩ := hp.surjective x
  exact (hp.contMDiffAt_section_associatedCore_iff ρ hpd hm).2 (h y)

variable [CompleteSpace 𝕜]

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
      (hp.associatedSectionEquiv ρ σ).2⟩
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
  (hpd : IsLocalDiffeomorph I IB n p)
include hpd

/-- Over a compact preconnected complex manifold `E`, a section of the bundle associated with `ρ` is
`C^m`, for `0 < m ≤ n`, exactly when its equivariant function upstairs is constant, with a
`ρ`-invariant value. Thus every holomorphic section is represented by a constant `G`-invariant
function upstairs. -/
theorem contMDiff_section_associatedCore_iff_exists_eq_const [PreconnectedSpace E] (hm : m ≤ n)
    (hm₀ : m ≠ 0) {σ : ∀ x, (hp.associatedCore ρ).Fiber x} :
    ContMDiff IB (IB.prod 𝓘(ℂ, F)) m (fun x ↦ TotalSpace.mk' F x (σ x)) ↔
      ∃ v : F, (∀ g : G, (ρ g : F →L[ℂ] F) v = v) ∧
        (hp.associatedSectionEquiv ρ σ : E → F) = Function.const E v := by
  rw [hp.contMDiff_section_associatedCore_iff ρ hpd hm]
  refine ⟨fun hf ↦ ?_, fun ⟨v, _, hv⟩ ↦ hv ▸ contMDiff_const⟩
  cases isEmpty_or_nonempty E with
  | inl hE => exact ⟨0, fun g ↦ map_zero _, funext fun y ↦ isEmptyElim y⟩
  | inr hE =>
    -- A holomorphic function on a compact connected complex manifold is constant.
    obtain ⟨v, hv⟩ := (hf.mdifferentiable hm₀).exists_eq_const_of_compactSpace
    refine ⟨v, fun g ↦ ?_, hv⟩
    obtain ⟨y⟩ : Nonempty E := inferInstance
    have h := (hp.associatedSectionEquiv ρ σ).2 g y
    rw [hv, Function.const_apply, Function.const_apply] at h
    exact h.symm

/-- Over a compact preconnected complex manifold `E`, the line bundle of a nontrivial character
`χ` of the deck group has no nonzero `C^m` section, for `0 < m ≤ n`. In particular it has no
nonzero holomorphic section. -/
theorem eq_zero_of_contMDiff_section_characterCore [PreconnectedSpace E] {χ : G →* ℂˣ}
    (hχ : χ ≠ 1) (hm : m ≤ n) (hm₀ : m ≠ 0) {σ : ∀ x, (hp.characterCore χ).Fiber x}
    (hσ : ContMDiff IB (IB.prod 𝓘(ℂ)) m (fun x ↦ TotalSpace.mk' ℂ x (σ x))) : σ = 0 := by
  obtain ⟨g, hg⟩ := DFunLike.ne_iff.1 hχ
  funext x
  obtain ⟨y, rfl⟩ := hp.surjective x
  revert σ
  rw [characterCore_def]
  intro σ hσ
  obtain ⟨v, hvG, hv⟩ :=
    (hp.contMDiff_section_associatedCore_iff_exists_eq_const _ hpd hm hm₀).1 hσ
  -- The invariant value satisfies `χ g * v = v` with `χ g ≠ 1`, so it vanishes.
  have hv₀ : v = 0 := by
    by_contra hv₀
    exact hg (Units.ext ((mul_eq_right₀ hv₀).1 (by simpa using hvG g)))
  refine (hp.associatedSectionEquiv_apply_eq_zero_iff _ σ y).1 ?_
  rw [hv, Function.const_apply, hv₀]

/-- Over a compact connected complex manifold `E`, the line bundle of a character `χ` of the deck
group has a global trivialization in its maximal `C^n` atlas, for `n ≠ 0`, exactly when `χ` is
trivial. In particular, the holomorphic line bundle of a nontrivial character is not
holomorphically trivial. -/
theorem exists_trivialization_baseSet_eq_univ_characterCore_iff_eq_one [ConnectedSpace E]
    (hn : n ≠ 0) (χ : G →* ℂˣ) :
    (∃ (e : Trivialization ℂ (π ℂ (hp.characterCore χ).Fiber)) (_ : e.IsLinear ℂ),
        e.toOpenPartialHomeomorph ∈ (contMDiffFiberwiseLinear X ℂ IB n).maximalAtlas
          (TotalSpace ℂ (hp.characterCore χ).Fiber) ∧ e.baseSet = univ) ↔ χ = 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ hp.exists_trivialization_baseSet_eq_univ_characterCore_one⟩
  obtain ⟨f, hf, hf₀, hfG⟩ :=
    (hp.exists_trivialization_baseSet_eq_univ_characterCore_iff hpd χ).1 h
  -- The nowhere-vanishing equivariant function is a nonzero constant `c` with `c = χ g * c`.
  obtain ⟨c, rfl⟩ := (hf.mdifferentiable hn).exists_eq_const_of_compactSpace
  obtain ⟨y⟩ : Nonempty E := inferInstance
  refine MonoidHom.ext fun g ↦ Units.ext ?_
  have h := hfG g y
  simp only [Function.const_apply] at h
  exact (mul_eq_right₀ (hf₀ y)).1 h.symm

end IsQuotientCoveringMap
