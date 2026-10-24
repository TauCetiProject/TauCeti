/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Separation.Regular

/-!
# Local integrability

Local integrability on an open set is equivalent to local integrability on every open subdomain
whose closure is compact and contained in the original set. This form is useful when a proof can be
localized to relatively compact subdomains.

For a right-translation-invariant measure on an additive group with continuous addition,
local integrability is preserved by translating a function onto any set whose translate stays
inside the original domain.

A function locally integrable on a null-measurable set `s`, vanishing almost everywhere on `s` off
a null-measurable compact `K ⊆ s`, is integrable on the whole space after extension by zero. This
is the step that turns a local hypothesis plus compact support into a global one. Both sets are
asked to be null-measurable explicitly because nothing here ties the topology on `X` to its
measurable space -- there is no `OpensMeasurableSpace` or `BorelSpace` assumption, so neither
compactness nor closedness of `K` carries any measurability with it. (Absent a separation axiom
`K` need not even be closed, but that is the lesser obstacle.)

Pairing a locally integrable function with a fixed vector in an inner product space gives a
locally integrable scalar function, as Mathlib records for `Integrable` and `MemLp`.

An `Lᵖ` function for a locally finite restriction of a measure to a set, with `1 ≤ p`, is locally
integrable on that set.

A function continuous on a compact set is bounded there, so for a measure finite on compact sets
it lies in every `Lᵖ` on each measurable subset of that compact set.

A real function with values in `[0, 1]` almost everywhere on a measurable set agrees almost
everywhere there with a function that is locally integrable on the whole space and everywhere
`[0, 1]`-valued: clamp it to `[0, 1]` and extend it by zero.

## Main declarations

* `MeasureTheory.LocallyIntegrableOn.comp_add_right_of_mapsTo`: translation onto a smaller set
  preserves local integrability.
* `TauCeti.locallyIntegrableOn_iff_forall_isCompact_closure`: characterization by relatively
  compact open subdomains.
* `MeasureTheory.LocallyIntegrableOn.indicator_of_isClosed`: local integrability of relative
  zero extension when the support avoids the added boundary.
* `MeasureTheory.LocallyIntegrableOn.integrable_indicator_of_isCompact`: integrability of the
  extension by zero of a locally integrable function supported in a null-measurable compact subset.
* `MeasureTheory.LocallyIntegrable.inner_const`: pairing with a fixed vector preserves local
  integrability.
* `MeasureTheory.Lp.locallyIntegrableOn`: an `Lᵖ` function on a set, with `1 ≤ p`, is locally
  integrable on it.
* `ContinuousOn.memLp_restrict_of_subset_isCompact`: a function continuous on a compact set is in
  every `Lᵖ` on its measurable subsets.

## Attribution

The characterization uses Mathlib's `exists_open_between_and_isCompact_closure`
to find relatively compact open neighborhoods of individual points. Extension by zero rests on
Mathlib's `LocallyIntegrableOn.integrableOn_compact_subset`, which gives integrability on the
compact support.
-/

public section

open MeasureTheory Set TopologicalSpace

namespace MeasureTheory

variable {E F : Type*} [MeasurableSpace E] [AddGroup E] [TopologicalSpace E]
  [ContinuousAdd E] [BorelSpace E]
  [TopologicalSpace F] [ContinuousENorm F] {mu : Measure E} [mu.IsAddRightInvariant]
  {Omega V : Set E} {u : E → F} {h : E}

/-- Local integrability is preserved by a translation whose image stays in the original
domain. -/
theorem LocallyIntegrableOn.comp_add_right_of_mapsTo
    (hu : LocallyIntegrableOn u Omega mu) (hVO : MapsTo (· + h) V Omega) :
    LocallyIntegrableOn (fun x => u (x + h)) V mu := by
  intro x hx
  obtain ⟨s, hs, hus⟩ := hu (x + h) (hVO hx)
  refine ⟨(· + h) ⁻¹' s, ?_, ?_⟩
  · exact ((continuous_id.add continuous_const).continuousWithinAt.tendsto_nhdsWithin hVO) hs
  · simpa only [Function.comp_def] using
      ((measurePreserving_add_right mu h).integrableOn_comp_preimage
        (Homeomorph.addRight h).measurableEmbedding).2 hus

end MeasureTheory

namespace TauCeti

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {μ : Measure X}

section RelativelyCompactSubdomains

variable {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε]
  [LocallyCompactSpace X] [RegularSpace X] {f : X → ε} {Ω : Opens X}

/-- A function is locally integrable on an open set exactly when it is locally integrable on every
open subdomain with compact closure contained in that set. -/
theorem locallyIntegrableOn_iff_forall_isCompact_closure :
    LocallyIntegrableOn f Ω μ ↔
      ∀ V : Opens X, IsCompact (closure (V : Set X)) → closure (V : Set X) ⊆ Ω →
        LocallyIntegrableOn f V μ := by
  constructor
  · intro hf V _ hV
    exact hf.mono_set (subset_closure.trans hV)
  · intro h x hx
    obtain ⟨V, hVo, hxV, hVΩ, hVc⟩ :=
      exists_open_between_and_isCompact_closure isCompact_singleton Ω.isOpen
        (singleton_subset_iff.mpr hx)
    have hf := h ⟨V, hVo⟩ hVc hVΩ x (hxV (mem_singleton x))
    simp only [Opens.coe_mk, hVo.nhdsWithin_eq (hxV (mem_singleton x))] at hf
    exact hf.filter_mono nhdsWithin_le_nhds

end RelativelyCompactSubdomains

/-- A real function with values in `[0, 1]` almost everywhere on a measurable set `s` agrees almost
everywhere on `s` with a function that is locally integrable on the whole space and everywhere
`[0, 1]`-valued. -/
theorem exists_locallyIntegrable_mem_Icc_ae_eq [IsLocallyFiniteMeasure μ] {u : X → ℝ}
    {s : Set X} (hs : MeasurableSet s) (hu : AEStronglyMeasurable u (μ.restrict s))
    (hu01 : ∀ᵐ x ∂μ.restrict s, u x ∈ Icc (0 : ℝ) 1) :
    ∃ w : X → ℝ, LocallyIntegrable w μ ∧ (∀ x, w x ∈ Icc (0 : ℝ) 1) ∧ w =ᵐ[μ.restrict s] u := by
  -- Clamp `u` to `[0, 1]` and extend by zero outside `s`.
  let g : X → ℝ := fun x => max 0 (min (u x) 1)
  have hg : g =ᵐ[μ.restrict s] u := hu01.mono fun x hx => by simp [g, hx.1, hx.2]
  have hmem (x : X) : s.indicator g x ∈ Icc (0 : ℝ) 1 := by
    by_cases hx : x ∈ s
    · rw [indicator_of_mem hx]
      exact ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
    · rw [indicator_of_notMem hx]
      exact ⟨le_rfl, zero_le_one⟩
  refine ⟨s.indicator g, (locallyIntegrable_const (1 : ℝ)).mono
    ((aestronglyMeasurable_indicator_iff hs).2 (hu.congr hg.symm)) (ae_of_all _ fun x => ?_),
    hmem, (indicator_ae_eq_restrict hs.nullMeasurableSet).trans hg⟩
  rw [Real.norm_eq_abs, norm_one, abs_le]
  exact ⟨by linarith [(hmem x).1], (hmem x).2⟩

end TauCeti

namespace MeasureTheory.LocallyIntegrableOn

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {μ : Measure X}

section ExtendByZero

variable {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε] [PseudoMetrizableSpace ε]
  {f : X → ε} {s K : Set X}

/-- A function locally integrable on a null-measurable set `s` and vanishing almost everywhere on
`s` off a null-measurable compact `K ⊆ s` is, after extension by zero, integrable on the whole
space.

`K` carries its own null-measurability hypothesis rather than inheriting one from compactness:
no assumption here relates the topology on `X` to its measurable space, so a compact -- or even
closed -- set need not be measurable at all. -/
theorem integrable_indicator_of_isCompact (hloc : LocallyIntegrableOn f s μ)
    (hs : NullMeasurableSet s μ) (hK : IsCompact K)
    (hKmeas : NullMeasurableSet K μ) (hKs : K ⊆ s)
    (hf : ∀ᵐ x ∂μ.restrict s, x ∉ K → f x = 0) :
    Integrable (s.indicator f) μ := by
  have hae : s.indicator f =ᵐ[μ] K.indicator f := by
    filter_upwards [(ae_restrict_iff'₀ hs).1 hf] with x hx
    by_cases hxs : x ∈ s
    · by_cases hxK : x ∈ K
      · rw [Set.indicator_of_mem hxs, Set.indicator_of_mem hxK]
      · rw [Set.indicator_of_mem hxs, Set.indicator_of_notMem hxK, hx hxs hxK]
    · rw [Set.indicator_of_notMem hxs, Set.indicator_of_notMem fun hxK => hxs (hKs hxK)]
  exact ((hloc.integrableOn_compact_subset hKs hK).integrable_indicator₀ hKmeas).congr hae.symm

end ExtendByZero

section RelativeExtension

variable [OpensMeasurableSpace X] [LocallyCompactSpace X] [T2Space X]
  {F : Type*} [TopologicalSpace F] [ESeminormedAddMonoid F] [PseudoMetrizableSpace F]
  {f : X → F} {s t K : Set X}

/-- Extension by zero preserves local integrability on `t` when the function vanishes off a
closed set `K` and `t ∩ K` lies in its original measurable domain `s`. The support may meet the
boundary of `t`; it need not be compact. -/
theorem indicator_of_isClosed (hf : LocallyIntegrableOn f s μ) (hs : MeasurableSet s)
    (ht : IsLocallyClosed t) (hK : IsClosed K) (hKs : t ∩ K ⊆ s)
    (hzero : ∀ᵐ x ∂μ.restrict s, x ∉ K → f x = 0) :
    LocallyIntegrableOn (s.indicator f) t μ := by
  apply (locallyIntegrableOn_iff ht).2
  intro C hCt hC
  have hCK : C ∩ K ⊆ s := fun x hx => hKs ⟨hCt hx.1, hx.2⟩
  have hi := (hf.integrableOn_compact_subset hCK (hC.inter_right hK)).integrable_indicator
    (hC.isClosed.measurableSet.inter hK.measurableSet)
  refine (hi.mono_measure Measure.restrict_le_self).congr ?_
  filter_upwards [ae_restrict_mem hC.isClosed.measurableSet,
    ((ae_restrict_iff' hs).1 hzero).filter_mono
      (ae_mono Measure.restrict_le_self)] with x hxC hx
  by_cases hxK : x ∈ K
  · simp [hxC, hxK, hCK ⟨hxC, hxK⟩]
  · by_cases hxs : x ∈ s
    · simp [hxC, hxK, hxs, hx hxs hxK]
    · simp [hxC, hxK, hxs]

end RelativeExtension

end MeasureTheory.LocallyIntegrableOn

namespace MeasureTheory.LocallyIntegrable

variable {X 𝕜 E : Type*} [MeasurableSpace X] [TopologicalSpace X] {μ : Measure X} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {f : X → E}

/-- Pairing a locally integrable function with a fixed vector preserves local integrability, the
analogue of Mathlib's `MeasureTheory.Integrable.inner_const`. -/
theorem inner_const (hf : LocallyIntegrable f μ) (c : E) :
    LocallyIntegrable (fun x => inner 𝕜 (f x) c) μ := by
  simpa only [Function.comp_def, innerSLFlip_apply_apply] using
    locallyIntegrableOn_univ.1
      ((innerSLFlip 𝕜 c).locallyIntegrableOn_comp (hf.locallyIntegrableOn univ))

end MeasureTheory.LocallyIntegrable

namespace MeasureTheory.Lp

variable {X E : Type*} [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
  {μ : Measure X} {s : Set X} [IsLocallyFiniteMeasure (μ.restrict s)] [NormedAddCommGroup E]
  {p : ENNReal}

/-- An `Lᵖ` function on `s`, for `1 ≤ p` and a measure whose restriction to `s` is locally finite,
is locally integrable on `s`. -/
theorem locallyIntegrableOn (g : Lp E p (μ.restrict s)) (hp : 1 ≤ p) :
    LocallyIntegrableOn g s μ :=
  locallyIntegrableOn_of_locallyIntegrable_restrict ((Lp.memLp g).locallyIntegrable hp)

end MeasureTheory.Lp

section ContinuousOn

variable {X E : Type*} [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] [NormedAddCommGroup E]

/-- A function continuous on a compact set `K` lies in every `Lᵖ` on each measurable subset of
`K`, for a measure that is finite on compact sets: it is bounded there, and the subset has finite
measure. -/
theorem ContinuousOn.memLp_restrict_of_subset_isCompact {f : X → E} {K s : Set X}
    (hf : ContinuousOn f K) (hK : IsCompact K) (hs : MeasurableSet s) (hsK : s ⊆ K)
    (p : ENNReal) : MemLp f p (μ.restrict s) := by
  have : IsFiniteMeasure (μ.restrict s) :=
    isFiniteMeasure_restrict.2 (measure_lt_top_of_subset hsK hK.measure_lt_top.ne).ne
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf
  exact MemLp.of_bound (hf.aestronglyMeasurable_of_subset_isCompact hK hs hsK) C
    ((ae_restrict_iff' hs).2 (ae_of_all _ fun x hx => hC x (hsK hx)))

end ContinuousOn
