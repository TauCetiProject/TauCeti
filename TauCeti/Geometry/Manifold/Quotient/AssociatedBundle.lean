/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Complex
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
public import TauCeti.Geometry.Manifold.VectorBundle.Core.Trivial
public import TauCeti.Geometry.Manifold.VectorBundle.FrameTrivialization
public import TauCeti.Topology.Covering.AssociatedBundle
import TauCeti.Algebra.Group.Hom.Defs

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

When `p` is differentiable and its covering space `E` is a compact connected complex manifold,
every holomorphic function on `E` is constant (`MDifferentiable.exists_eq_const_of_compactSpace`,
the maximum principle). Hence the holomorphic sections of the bundle associated with `ρ`
correspond to the `ρ`-invariant vectors of `F`
(`IsQuotientCoveringMap.mdifferentiable_section_associatedCore_iff_exists_eq_const`),
the line bundle of a nontrivial character has no nonzero holomorphic section
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
* `IsQuotientCoveringMap.mdifferentiable_section_associatedCore_iff_exists_eq_const`,
  `IsQuotientCoveringMap.contMDiff_section_associatedCore_iff_exists_eq_const`: if `p` is
  differentiable with compact preconnected complex covering manifold `E`, holomorphic sections
  over `X` have constant equivariant functions upstairs with `ρ`-invariant values.
* `IsQuotientCoveringMap.eq_zero_of_mdifferentiable_section_characterCore`,
  `IsQuotientCoveringMap.eq_zero_of_contMDiff_section_characterCore`,
  `IsQuotientCoveringMap.exists_trivialization_baseSet_eq_univ_characterCore_iff_eq_one`: if `p`
  is differentiable with compact connected complex covering manifold `E`, the line bundle of a
  nontrivial character over `X` has no nonzero holomorphic section and is not holomorphically
  trivial. The analogous vanishing results for rank-one representations and the triviality
  criterion for arbitrary representations are
  `IsQuotientCoveringMap.eq_zero_of_mdifferentiable_section_associatedCore`,
  `IsQuotientCoveringMap.eq_zero_of_contMDiff_section_associatedCore`, and
  `IsQuotientCoveringMap.exists_trivialization_baseSet_eq_univ_associatedCore_iff_eq_one`.

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
    have h := (hp.associatedSectionEquiv ρ σ).2 g y
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

end IsQuotientCoveringMap
