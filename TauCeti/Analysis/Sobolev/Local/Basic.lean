/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Prod
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
public import TauCeti.MeasureTheory.Function.PreciseRepresentative
public import TauCeti.MeasureTheory.Function.LocallyIntegrable
public import TauCeti.Topology.Sets.Opens
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas
import Mathlib.Topology.Separation.Regular
import TauCeti.MeasureTheory.Function.LpSeminorm.ContinuousOn

/-!
# Local vector-valued Lebesgue and Sobolev classes

`TauCeti.MemLpLoc p U f μ` requires `Lᵖ(μ)` membership on every compact subset of `U`, on an
arbitrary topological measurable space `α` and for any topological codomain `ε` carrying an extended
norm (`ENorm`). `TauCeti.MemWkpLoc p U k f μ` requires iterated weak derivatives through order `k`
on `interior U` relative to `μ`, with `Lᵖ(μ)` bounds on every compact subset of `U` itself, on an
arbitrary real normed space `E` and for any real normed codomain `F`. Both predicates default `μ`
to `volume` when a `MeasureSpace` instance is available.

For non-open domains such as half-discs reaching a boundary hyperplane, the `Lᵖ` bounds hold on
compact subsets touching the boundary, while weak-derivative test functions stay inside
`interior U`. On open sets this is the usual local Sobolev class `W^{k,p}_loc(Ω; F)`. Derivatives
take values in iterated continuous linear maps rather than scalar jets, and no basis or separability
of the codomain `F` is assumed. Membership in `Lᵖ` on each compact subset includes almost-everywhere
strong measurability (`MemLpLoc.aestronglyMeasurable_restrict`, `MemLpLoc.aestronglyMeasurable`).
The predicates concern actual functions, are invariant under almost-everywhere modifications on `U`,
and impose no global integrability condition on possibly unbounded domains; global `Lᵖ` membership
implies local membership (`MeasureTheory.MemLp.memLpLoc`, `MeasureTheory.MemLp.memLpLoc_of_ae_le`),
and a locally `Lᵖ` function vanishing outside a compact subset is globally `Lᵖ`
(`MemLpLoc.memLp_of_forall_notMem_eq_zero`).

This file supplies:
* restriction to smaller sets (`MemLpLoc.mono_set`, `MemWkpLoc.mono`), monotonicity and positive
  finite scaling of the reference measure (`MemLpLoc.mono_measure`, `MemLpLoc.smul_measure`,
  `memLpLoc_smul_measure_iff`), and almost-everywhere invariance (`MemLpLoc.congr_ae`,
  `MemWkpLoc.congr_ae`, `MemLpLoc.congr_mono`, `MemWkpLoc.congr_mono`);
* strong measurability on compact subsets and on open domains (`memLpLoc_zero_exponent_iff`,
  `MemLpLoc.aestronglyMeasurable_restrict`, `MemLpLoc.aestronglyMeasurable`);
* linearity, scalar multiplication, multiplication of a fixed vector by a scalar map
  (`MemLpLoc.smul_const`, `MemWkpLoc.smul_const`), continuous-linear postcomposition, pairing of
  maps and operator fields, continuous-linear change of codomain, multiplication of local `Lᵖ`
  functions by continuous factors (with extension by zero for factors supported in `U`, and global
  `Lᵖ` membership for compactly supported factors via `MemLpLoc.memLp_smul_of_hasCompactSupport`),
  and Hölder's inequality for pairing locally `Lᵖ` operator fields with locally `L^q` maps
  (`MemLpLoc.clm_apply`, `MemLpLoc.memLpLoc_one_clm_apply`,
  `MemLpLoc.locallyIntegrableOn_clm_apply`);
* decreasing the integrability exponent (`MemLpLoc.mono_exponent`, `MemWkpLoc.mono_exponent`) and
  decreasing the derivative order (`MemWkpLoc.of_succ`, `MemWkpLoc.of_le`);
* detection of local `Lᵖ` membership on open subsets with compact closure inside an open domain
  (`memLpLoc_of_forall_opens`), on balls via smaller concentric balls (`memLpLoc_ball_iff`), via
  local boundedness (`memLpLoc_of_forall_eventually_norm_le`), identification of local `L¹` with
  local integrability on locally closed sets (`memLpLoc_one_iff_locallyIntegrableOn`), and
  agreement with the precise representative on open sets when `1 ≤ p`
  (`MemLpLoc.ae_eq_preciseRepresentative`);
* uniqueness-of-weak-derivative consequences (`MemWkpLoc.memWkpLoc_of_hasWeakFDerivOn`,
  `MemWkpLoc.memLpLoc_of_hasWeakFDerivOn`), first-order characterization for continuous functions
  (`ContinuousOn.memWkpLoc_one_iff`, `ContinuousOn.memWkpLoc_one_iff_of_isOpen`), classical
  differentiability criteria (`memWkpLoc_one_of_differentiableOn`,
  `memWkpLoc_one_of_continuousOn_fderiv`), `Cᵏ` membership (`ContDiffOn.memWkpLoc`,
  `ContDiff.memWkpLoc`), and identification of derivatives of `Cᵏ` representatives on sets agreeing
  almost everywhere with their interior (`MemWkpLoc.hasWeakFDerivOn_fderiv_of_contDiffOn`,
  `MemWkpLoc.iteratedFDeriv_of_contDiffOn`);
* `TauCeti.WeakDerivChainLe`, comparing the `Lᵖ` norms of two maps and recursively every pair of
  their weak derivatives through a given order.

In positive order, completeness of the codomain is inherited from `TauCeti.HasWeakFDerivOn`; the
definitions admit every real normed codomain without an additional typeclass assumption.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (local Sobolev spaces and their elementary operations).
* W. Arendt and M. Kreuter, *Mapping theorems for Sobolev spaces of vector-valued functions*,
  Studia Math. 240 (2018), §2, pp. 2–3 (first-order Bochner Sobolev spaces).
-/

public noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal

namespace TauCeti

section MemLpLocENorm

variable {α ε : Type*} [TopologicalSpace α] [MeasurableSpace α] [TopologicalSpace ε] [ENorm ε]
  {μ ν : Measure α} {p q : ℝ≥0∞} {U V : Set α} {f g : α → ε}

/-- A function is locally `Lᵖ` on `U` with respect to `μ` when it belongs to `Lᵖ(μ)` on every
compact subset of `U`. When `U` meets its boundary, those compact subsets include the boundary. -/
def MemLpLoc (p : ℝ≥0∞) (U : Set α) (f : α → ε) (μ : Measure α := by volume_tac) : Prop :=
  ∀ K : Set α, K ⊆ U → IsCompact K → MemLp f p (μ.restrict K)

/-- Local `Lᵖ` membership is characterized by `Lᵖ` membership on every compact subset. -/
theorem memLpLoc_iff : MemLpLoc p U f μ ↔
    ∀ K : Set α, K ⊆ U → IsCompact K → MemLp f p (μ.restrict K) := Iff.rfl

/-- Local integrability restricts to any smaller set. -/
theorem MemLpLoc.mono_set (hf : MemLpLoc p U f μ) (hVU : V ⊆ U) : MemLpLoc p V f μ :=
  fun K hK hc => hf K (hK.trans hVU) hc

/-- Local `Lᵖ` membership is monotone under passing to a smaller measure. -/
theorem MemLpLoc.mono_measure (hf : MemLpLoc p U f μ) (hνμ : ν ≤ μ) : MemLpLoc p U f ν :=
  fun K hK hc => (hf K hK hc).mono_measure (Measure.restrict_mono subset_rfl hνμ)

/-- Scaling the reference measure by a finite constant preserves local `Lᵖ` membership. -/
theorem MemLpLoc.smul_measure (hf : MemLpLoc p U f μ) {c : ℝ≥0∞} (hc : c ≠ ∞) :
    MemLpLoc p U f (c • μ) := fun K hK hcK => by
  rw [Measure.restrict_smul]
  exact (hf K hK hcK).smul_measure hc

/-- Scaling the reference measure by a positive finite constant leaves local `Lᵖ` membership
unchanged. -/
theorem memLpLoc_smul_measure_iff {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ∞) :
    MemLpLoc p U f (c • μ) ↔ MemLpLoc p U f μ := by
  refine ⟨fun h => ?_, fun h => h.smul_measure hc⟩
  have h' := h.smul_measure (c := c⁻¹) (ENNReal.inv_ne_top.2 hc0)
  rwa [smul_smul, ENNReal.inv_mul_cancel hc0 hc, one_smul] at h'

/-- At exponent `0`, local `Lᵖ` membership is exactly almost-everywhere strong measurability on
every compact subset. -/
theorem memLpLoc_zero_exponent_iff : MemLpLoc 0 U f μ ↔
    ∀ K : Set α, K ⊆ U → IsCompact K → AEStronglyMeasurable f (μ.restrict K) := by
  simp only [memLpLoc_iff, memLp_zero_iff_aestronglyMeasurable]

/-- Local `Lᵖ` membership includes almost-everywhere strong measurability on every compact subset
of `U`, for every exponent `p` including `0` and `∞`. -/
theorem MemLpLoc.aestronglyMeasurable_restrict (hf : MemLpLoc p U f μ) {K : Set α}
    (hK : K ⊆ U) (hc : IsCompact K) : AEStronglyMeasurable f (μ.restrict K) :=
  (hf K hK hc).aestronglyMeasurable

/-- Local `Lᵖ` membership on `U` gives `Lᵖ` membership on every set whose closure is compact and
contained in `U`. -/
theorem MemLpLoc.memLp_of_closure_subset (hf : MemLpLoc p U f μ) (hV : IsCompact (closure V))
    (hVU : closure V ⊆ U) : MemLp f p (μ.restrict V) :=
  (hf _ hVU hV).mono_measure (Measure.restrict_mono subset_closure le_rfl)

/-- On an open set of a locally compact, regular, second-countable space, every locally `Lᵖ`
function with values in a pseudometrizable space is almost everywhere strongly measurable on the
whole open set. No separability of the codomain is assumed. -/
theorem MemLpLoc.aestronglyMeasurable [LocallyCompactSpace α] [RegularSpace α]
    [SecondCountableTopology α] [PseudoMetrizableSpace ε] {Ω : Opens α}
    (hf : MemLpLoc p Ω f μ) : AEStronglyMeasurable f (μ.restrict Ω) := by
  have hV : ∀ x : Ω, ∃ V : Opens α, (x : α) ∈ V ∧ IsCompact (closure (V : Set α)) ∧
      closure (V : Set α) ⊆ Ω := fun x => by
    obtain ⟨V, hVo, hxV, hVΩ, hVc⟩ := exists_open_between_and_isCompact_closure
      isCompact_singleton Ω.isOpen (Set.singleton_subset_iff.2 x.property)
    exact ⟨⟨V, hVo⟩, hxV rfl, hVc, hVΩ⟩
  choose V hxV hVc hVΩ using hV
  obtain ⟨T, hTc, hT⟩ := isOpen_iUnion_countable (fun x : Ω => (V x : Set α))
    (fun x => (V x).isOpen)
  have hΩ : (Ω : Set α) = ⋃ x ∈ T, (V x : Set α) := by
    refine Set.Subset.antisymm ?_ (Set.iUnion₂_subset fun x _ => subset_closure.trans (hVΩ x))
    rw [hT]
    intro x hx
    exact Set.mem_iUnion.2 ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
  rw [hΩ]
  have : Countable T := hTc.to_subtype
  rw [Set.biUnion_eq_iUnion]
  exact AEStronglyMeasurable.iUnion fun x =>
    (hf.memLp_of_closure_subset (hVc x) (hVΩ x)).aestronglyMeasurable

/-- A function that is `Lᵖ` on `U` is locally `Lᵖ` there. -/
theorem _root_.MeasureTheory.MemLp.memLpLoc (hf : MemLp f p (μ.restrict U)) :
    MemLpLoc p U f μ :=
  fun _ hK _ => hf.mono_measure (Measure.restrict_mono hK le_rfl)

/-- A function that is `Lᵖ` on a set `W` is locally `Lᵖ` on every set `U` contained in `W` up to a
null set, including on compact subsets of `U` that leave `W`. -/
theorem _root_.MeasureTheory.MemLp.memLpLoc_of_ae_le {W : Set α}
    (hf : MemLp f p (μ.restrict W)) (hUW : U ≤ᵐ[μ] W) : MemLpLoc p U f μ :=
  memLpLoc_iff.2 fun _ hK _ => hf.mono_measure
    (Measure.restrict_mono_ae ((Filter.EventuallySubset.of_subset hK).trans hUW))

/-- Local `Lᵖ` membership on a ball `ball c r` in a proper space is `Lᵖ` membership on every
smaller concentric ball `ball c R`, `R < r`. -/
theorem memLpLoc_ball_iff {α ε : Type*} [PseudoMetricSpace α] [ProperSpace α] [T2Space α]
    [MeasurableSpace α] [TopologicalSpace ε] [ENorm ε] {μ : Measure α} {p : ℝ≥0∞} {c : α}
    {r : ℝ} {f : α → ε} :
    MemLpLoc p (Metric.ball c r) f μ ↔ ∀ R < r, MemLp f p (μ.restrict (Metric.ball c R)) := by
  refine ⟨fun hf R hR => hf.memLp_of_closure_subset Metric.isCompact_closure_ball
    (Metric.closure_ball_subset_closedBall.trans (Metric.closedBall_subset_ball hR)),
    fun hf K hK hKc => ?_⟩
  obtain ⟨R, hR, hKR⟩ := exists_lt_subset_ball hKc.isClosed hK
  exact (hf R hR).mono_measure (Measure.restrict_mono hKR le_rfl)

/-- Almost-everywhere equality on `U` preserves local `Lᵖ` membership. -/
theorem MemLpLoc.congr_ae (hf : MemLpLoc p U f μ)
    (hfg : f =ᵐ[μ.restrict U] g) : MemLpLoc p U g μ := by
  intro K hK hc
  exact (hf K hK hc).ae_eq (ae_mono (Measure.restrict_mono_set μ hK) hfg)

/-- Restricting to a subset preserves local `Lᵖ` membership of any function agreeing with the
original one on that subset. -/
theorem MemLpLoc.congr_mono [T2Space α] [OpensMeasurableSpace α] (hf : MemLpLoc p U f μ)
    (hgf : Set.EqOn g f V) (hVU : V ⊆ U) :
    MemLpLoc p V g μ := fun K hK hc => (hf K (hK.trans hVU) hc).ae_eq <| by
  filter_upwards [ae_restrict_mem hc.measurableSet] with z hz using (hgf (hK hz)).symm

/-- Local `Lᵖ` membership only depends on the values of the function on the set. -/
theorem MemLpLoc.congr [T2Space α] [OpensMeasurableSpace α] (hf : MemLpLoc p U f μ)
    (hgf : Set.EqOn g f U) : MemLpLoc p U g μ :=
  hf.congr_mono hgf Set.Subset.rfl

/-- On an open set `Ω` of a locally compact regular space, a function that agrees almost everywhere
with an `Lᵖ` function on every open `W` whose closure is compact and contained in `Ω` is locally
`Lᵖ` on `Ω`. -/
theorem memLpLoc_of_forall_opens [LocallyCompactSpace α] [RegularSpace α] {Ω : Opens α}
    (h : ∀ W : Opens α, IsCompact (closure (W : Set α)) → closure (W : Set α) ⊆ Ω →
      ∃ g : α → ε, MemLp g p (μ.restrict (W : Set α)) ∧ g =ᵐ[μ.restrict W] f) :
    MemLpLoc p Ω f μ := by
  refine fun K hKΩ hK => ?_
  obtain ⟨W, hWo, hKW, hWΩ, hWc⟩ := exists_open_between_and_isCompact_closure hK Ω.isOpen hKΩ
  obtain ⟨g, hg, hgf⟩ := h ⟨W, hWo⟩ hWc hWΩ
  exact (hg.ae_eq hgf).mono_measure (Measure.restrict_mono hKW le_rfl)

end MemLpLocENorm

section MemLpLocContinuousENorm

variable {α ε : Type*} [TopologicalSpace α] [MeasurableSpace α] [TopologicalSpace ε]
  [ContinuousENorm ε] {μ : Measure α} {p q : ℝ≥0∞} {U : Set α} {f : α → ε}

/-- Compact subsets have finite measure when `μ` is finite on compacts, so decreasing the exponent
preserves local membership. In particular this passes from `∞` to every finite exponent. -/
theorem MemLpLoc.mono_exponent [IsFiniteMeasureOnCompacts μ] (hf : MemLpLoc p U f μ)
    (hqp : q ≤ p) : MemLpLoc q U f μ := by
  intro K hK hc
  have : IsFiniteMeasure (μ.restrict K) := ⟨by simpa using hc.measure_lt_top⟩
  exact (hf K hK hc).mono_exponent hqp

end MemLpLocContinuousENorm

section MemLpLocGroup

variable {α F G : Type*} [TopologicalSpace α] [MeasurableSpace α]
  [NormedAddCommGroup F] [NormedAddCommGroup G]
  {μ : Measure α} {p q : ℝ≥0∞} {U V : Set α} {f g : α → F}

/-- The zero function belongs to every local `Lᵖ` class. -/
@[simp]
theorem memLpLoc_zero : MemLpLoc p U (0 : α → F) μ := fun _ _ _ => MemLp.zero

/-- Local `Lᵖ` membership is closed under addition. -/
theorem MemLpLoc.add (hf : MemLpLoc p U f μ) (hg : MemLpLoc p U g μ) :
    MemLpLoc p U (f + g) μ := fun K hK hc => (hf K hK hc).add (hg K hK hc)

/-- Local `Lᵖ` membership is closed under negation. -/
theorem MemLpLoc.neg (hf : MemLpLoc p U f μ) : MemLpLoc p U (-f) μ :=
  fun K hK hc => (hf K hK hc).neg

/-- Local `Lᵖ` membership is closed under subtraction. -/
theorem MemLpLoc.sub (hf : MemLpLoc p U f μ) (hg : MemLpLoc p U g μ) :
    MemLpLoc p U (f - g) μ := fun K hK hc => (hf K hK hc).sub (hg K hK hc)

/-- A locally `Lᵖ` function on `U` that vanishes off a compact set `T ⊆ U` is `Lᵖ` on the whole
space. -/
theorem MemLpLoc.memLp_of_forall_notMem_eq_zero [T2Space α] [OpensMeasurableSpace α]
    (hf : MemLpLoc p U f μ) {T : Set α} (hT : IsCompact T) (hTU : T ⊆ U)
    (h0 : ∀ z ∉ T, f z = 0) : MemLp f p μ := by
  have : T.indicator f = f :=
    Set.indicator_eq_self.2 fun z hz => by_contra fun h' => hz (h0 z h')
  rw [← this, memLp_indicator_iff_restrict hT.measurableSet.nullMeasurableSet]
  exact hf T hTU hT

/-- A function continuous on `U` is locally `Lᵖ` there, with no global bound required. -/
theorem _root_.ContinuousOn.memLpLoc [T2Space α] [OpensMeasurableSpace α]
    [IsFiniteMeasureOnCompacts μ] (hf : ContinuousOn f U) : MemLpLoc p U f μ :=
  fun _K hK hc => (hf.mono hK).memLp_restrict_of_subset_isCompact
    hc hc.measurableSet subset_rfl p

open scoped Topology in
/-- An a.e.-strongly measurable function on `U` that is bounded near every point of `U` is locally
`Lᵖ` on `U` for every exponent, including infinity: it is bounded on each compact subset. -/
theorem memLpLoc_of_forall_eventually_norm_le [T2Space α] [OpensMeasurableSpace α]
    [IsFiniteMeasureOnCompacts μ] (hf : AEStronglyMeasurable f (μ.restrict U))
    (hb : ∀ z ∈ U, ∃ M, ∀ᶠ w in 𝓝 z, ‖f w‖ ≤ M) : MemLpLoc p U f μ := by
  intro K hKU hK
  have : IsFiniteMeasure (μ.restrict K) := isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
  -- a bound on `K`, glued from the local bounds by compactness
  obtain ⟨M, hM⟩ : ∃ M, ∀ w ∈ K, ‖f w‖ ≤ M := by
    refine hK.induction_on (p := fun t ↦ ∃ M, ∀ w ∈ t, ‖f w‖ ≤ M) ⟨0, by simp⟩
      (fun _ _ hst ⟨M, hM⟩ ↦ ⟨M, fun w hw ↦ hM w (hst hw)⟩)
      (fun _ _ ⟨M, hM⟩ ⟨N, hN⟩ ↦ ⟨max M N, fun w hw ↦ hw.elim
        (fun h ↦ (hM w h).trans (le_max_left M N)) fun h ↦ (hN w h).trans (le_max_right M N)⟩)
      fun z hz ↦ ?_
    obtain ⟨M, hM⟩ := hb z (hKU hz)
    exact ⟨_, mem_nhdsWithin_of_mem_nhds hM, M, fun _ hw ↦ hw⟩
  exact MemLp.of_bound (hf.mono_measure (Measure.restrict_mono hKU le_rfl)) M
    (ae_restrict_of_forall_mem hK.measurableSet hM)

/-- Every constant function is locally `Lᵖ` for all exponents, including infinity. -/
@[simp]
theorem memLpLoc_const [T2Space α] [OpensMeasurableSpace α] [IsFiniteMeasureOnCompacts μ]
    (c : F) : MemLpLoc p U (fun _ => c) μ :=
  continuousOn_const.memLpLoc

/-- A locally `Lᵖ` function on a locally closed set is locally integrable when `1 ≤ p`.
This supplies the local integrability hypothesis used by the weak-derivative API. -/
theorem MemLpLoc.locallyIntegrableOn [LocallyCompactSpace α] [IsFiniteMeasureOnCompacts μ]
    (hf : MemLpLoc p U f μ) (hp : 1 ≤ p) (hU : IsLocallyClosed U) :
    LocallyIntegrableOn f U μ :=
  (locallyIntegrableOn_iff hU).2 fun K hK hc =>
    memLp_one_iff_integrable.1 ((hf.mono_exponent hp) K hK hc)

/-- On a locally closed set, local `L¹` membership is exactly local integrability. -/
theorem memLpLoc_one_iff_locallyIntegrableOn [LocallyCompactSpace α] [IsFiniteMeasureOnCompacts μ]
    (hU : IsLocallyClosed U) :
    MemLpLoc 1 U f μ ↔ LocallyIntegrableOn f U μ :=
  ⟨fun hf => hf.locallyIntegrableOn le_rfl hU,
    fun hf _K hK hc => memLp_one_iff_integrable.2 (hf.integrableOn_compact_subset hK hc)⟩

/-- A finite sum of locally `Lᵖ` functions is locally `Lᵖ`, without a completeness assumption. -/
theorem MemLpLoc.sum {ι : Type*} (s : Finset ι) {f : ι → α → F}
    (hf : ∀ i ∈ s, MemLpLoc p U (f i) μ) : MemLpLoc p U (fun z => ∑ i ∈ s, f i z) μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty, Pi.zero_def] using (memLpLoc_zero (p := p) (U := U))
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi, Pi.add_def] using
      (hf i (Finset.mem_insert_self i s)).add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

end MemLpLocGroup

section MemLpLocNormedSpace

variable {α F G : Type*} [TopologicalSpace α] [MeasurableSpace α]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {μ : Measure α} {p q : ℝ≥0∞} {U V : Set α} {f g : α → F}

/-- Real scalar multiplication preserves local `Lᵖ` membership. -/
theorem MemLpLoc.const_smul (hf : MemLpLoc p U f μ) (c : ℝ) : MemLpLoc p U (c • f) μ :=
  fun K hK hc => (hf K hK hc).const_smul c

/-- A continuous linear map on the codomain preserves local `Lᵖ` membership. -/
theorem MemLpLoc.clm_comp (hf : MemLpLoc p U f μ) (A : F →L[ℝ] G) :
    MemLpLoc p U (fun z => A (f z)) μ :=
  fun K hK hc => A.comp_memLp' (hf K hK hc)

/-- Multiplying a fixed target vector by a scalar locally `Lᵖ` function is locally `Lᵖ`, with no
basis of the codomain required. -/
theorem MemLpLoc.smul_const {a : α → ℝ} (ha : MemLpLoc p U a μ) (v : F) :
    MemLpLoc p U (fun z => a z • v) μ :=
  ha.clm_comp ((ContinuousLinearMap.id ℝ ℝ).smulRight v)

/-- Pairing two locally `Lᵖ` fields of continuous linear maps into their product map preserves
local `Lᵖ` membership. -/
theorem MemLpLoc.clm_prod {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : α → E →L[ℝ] F} {B : α → E →L[ℝ] G} (hA : MemLpLoc p U A μ) (hB : MemLpLoc p U B μ) :
    MemLpLoc p U (fun z => (A z).prod (B z)) μ := by
  convert (hA.clm_comp (ContinuousLinearMap.compL ℝ E F (F × G)
    (ContinuousLinearMap.inl ℝ F G))).add
      (hB.clm_comp (ContinuousLinearMap.compL ℝ E G (F × G) (ContinuousLinearMap.inr ℝ F G)))
    using 1
  funext z
  ext v <;> simp

/-- Composing a locally `Lᵖ` operator family on the left with one continuous on `U` preserves
local `Lᵖ` membership, since the continuous factor is bounded on every compact subset of `U`. -/
theorem MemLpLoc.continuousOn_clm_comp [T2Space α] [OpensMeasurableSpace α]
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : α → G →L[ℝ] H} {B : α → F →L[ℝ] G} (hB : MemLpLoc p U B μ) (hA : ContinuousOn A U) :
    MemLpLoc p U (fun z => A z ∘L B z) μ :=
  memLpLoc_iff.2 fun K hKU hK => (memLpLoc_iff.1 hB K hKU hK).clm_comp_of_continuousOn
    (hA.mono hKU) hK hK.measurableSet subset_rfl

/-- Composing a locally `Lᵖ` operator family on the right with one continuous on `U` preserves
local `Lᵖ` membership, since the continuous factor is bounded on every compact subset of `U`. -/
theorem MemLpLoc.clm_comp_continuousOn [T2Space α] [OpensMeasurableSpace α]
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {B : α → G →L[ℝ] H} {E : α → F →L[ℝ] G} (hB : MemLpLoc p U B μ) (hE : ContinuousOn E U) :
    MemLpLoc p U (fun z => B z ∘L E z) μ :=
  memLpLoc_iff.2 fun K hKU hK => (ContinuousLinearMap.compL ℝ F G H).memLp_of_bilin p
    (memLpLoc_iff.1 hB K hKU hK)
    ((hE.mono hKU).memLp_top_restrict_of_subset_isCompact hK hK.measurableSet subset_rfl)

/-- **Hölder's inequality on compact subsets**, for a Hölder triple `1/r = 1/p + 1/q`: a locally
`Lᵖ` field of continuous linear maps applied to a locally `L^q` field is locally `Lʳ`. With `p = ∞`
this covers locally bounded coefficient fields. -/
theorem MemLpLoc.clm_apply {A : α → F →L[ℝ] G} {w : α → F} {r : ℝ≥0∞}
    [ENNReal.HolderTriple p q r] (hA : MemLpLoc p U A μ) (hw : MemLpLoc q U w μ) :
    MemLpLoc r U (fun z => A z (w z)) μ :=
  fun K hK hc => (ContinuousLinearMap.id ℝ (F →L[ℝ] G)).memLp_of_bilin r (hA K hK hc) (hw K hK hc)

/-- **Hölder's inequality on compact subsets** with exponent one: a locally `Lᵖ` field of
continuous linear maps applied to a locally `L^q` field is locally `L¹` when `1/p + 1/q ≤ 1`. -/
theorem MemLpLoc.memLpLoc_one_clm_apply [IsFiniteMeasureOnCompacts μ] {A : α → F →L[ℝ] G}
    {w : α → F} (hA : MemLpLoc p U A μ) (hw : MemLpLoc q U w μ) (hpq : p⁻¹ + q⁻¹ ≤ 1) :
    MemLpLoc 1 U (fun z => A z (w z)) μ := by
  have : ENNReal.HolderTriple p q (p⁻¹ + q⁻¹)⁻¹ := ⟨(inv_inv _).symm⟩
  exact (hA.clm_apply hw).mono_exponent (ENNReal.one_le_inv.2 hpq)

/-- **Hölder's inequality on compact subsets**: a locally `Lᵖ` field of continuous linear maps
applied to a locally `L^q` field is locally integrable on a locally closed set when
`1/p + 1/q ≤ 1`. -/
theorem MemLpLoc.locallyIntegrableOn_clm_apply [LocallyCompactSpace α]
    [IsFiniteMeasureOnCompacts μ] {A : α → F →L[ℝ] G} {w : α → F}
    (hA : MemLpLoc p U A μ) (hw : MemLpLoc q U w μ) (hpq : p⁻¹ + q⁻¹ ≤ 1)
    (hU : IsLocallyClosed U) : LocallyIntegrableOn (fun z => A z (w z)) U μ :=
  (hA.memLpLoc_one_clm_apply hw hpq).locallyIntegrableOn le_rfl hU

/-- A continuous linear change of codomain preserves and reflects local `Lᵖ` membership. -/
@[simp]
theorem _root_.ContinuousLinearEquiv.comp_memLpLoc_iff (e : F ≃L[ℝ] G) :
    MemLpLoc p U (fun z => e (f z)) μ ↔ MemLpLoc p U f μ := by
  constructor
  · intro h
    simpa only [ContinuousLinearEquiv.coe_coe, e.symm_apply_apply] using
      h.clm_comp e.symm.toContinuousLinearMap
  · exact fun h => h.clm_comp e.toContinuousLinearMap

/-- A factor continuous on `U` preserves local `Lᵖ` membership on `U`, since it is bounded on
every compact subset of `U`. -/
theorem MemLpLoc.continuousOn_smul [T2Space α] [OpensMeasurableSpace α]
    [IsFiniteMeasureOnCompacts μ] {χ : α → ℝ} (hf : MemLpLoc p U f μ) (hχ : ContinuousOn χ U) :
    MemLpLoc p U (fun z => χ z • f z) μ :=
  memLpLoc_iff.2 fun K hK hc =>
    (memLpLoc_iff.1 (hχ.memLpLoc (p := ⊤)) K hK hc).smul (memLpLoc_iff.1 hf K hK hc)

/-- A locally `Lᵖ` field of continuous linear maps applied to a map continuous on `U` is locally
`Lᵖ` on `U`, since the map is bounded on every compact subset of `U`. -/
theorem MemLpLoc.clm_apply_continuousOn [T2Space α] [OpensMeasurableSpace α]
    [IsFiniteMeasureOnCompacts μ] {A : α → F →L[ℝ] G} (hA : MemLpLoc p U A μ)
    (hf : ContinuousOn f U) : MemLpLoc p U (fun z => A z (f z)) μ :=
  memLpLoc_iff.2 fun K hK hc =>
    (memLpLoc_iff.1 hA K hK hc).of_bilin (fun B x => B x) 1
      (memLpLoc_iff.1 (hf.memLpLoc (p := ⊤)) K hK hc) isBoundedBilinearMap_apply.continuous
      (.of_forall fun z => by simpa using (A z).le_opNNNorm (f z))

/-- A continuous factor supported in `U` extends a local `Lᵖ` function on `U` by zero to a local
`Lᵖ` function on the whole space: on a compact set `K` the product only sees
`K ∩ tsupport χ`, a compact subset of `U`. -/
theorem MemLpLoc.continuous_smul_of_tsupport_subset [T2Space α] [OpensMeasurableSpace α]
    [IsFiniteMeasureOnCompacts μ] {χ : α → ℝ} (hf : MemLpLoc p U f μ)
    (hχ : Continuous χ) (hsupp : tsupport χ ⊆ U) :
    MemLpLoc p Set.univ (fun z => χ z • f z) μ := by
  have hT := hf.continuousOn_smul hχ.continuousOn
  have hcl : IsClosed (tsupport χ) := isClosed_tsupport χ
  refine memLpLoc_iff.2 fun K _ hK => ?_
  have heq : (fun z => χ z • f z) = (tsupport χ).indicator (fun z => χ z • f z) := by
    refine (Set.indicator_eq_self.2 ?_).symm
    exact (Function.support_smul_subset_left χ f).trans (subset_tsupport χ)
  rw [heq, memLp_indicator_iff_restrict hcl.measurableSet.nullMeasurableSet,
    Measure.restrict_restrict hcl.measurableSet]
  exact memLpLoc_iff.1 hT _ (Set.inter_subset_left.trans hsupp) (hK.inter_left hcl)

/-- A continuous compactly supported factor supported in `U` turns a locally `Lᵖ` function on `U`
into a function in `Lᵖ` of the whole space. -/
theorem MemLpLoc.memLp_smul_of_hasCompactSupport [T2Space α] [OpensMeasurableSpace α]
    [IsFiniteMeasureOnCompacts μ] {χ : α → ℝ} (hf : MemLpLoc p U f μ)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hsupp : tsupport χ ⊆ U) :
    MemLp (fun z => χ z • f z) p μ := by
  have hcl : IsClosed (tsupport χ) := isClosed_tsupport χ
  have heq : (fun z => χ z • f z) = (tsupport χ).indicator (fun z => χ z • f z) := by
    refine (Set.indicator_eq_self.2 ?_).symm
    exact (Function.support_smul_subset_left χ f).trans (subset_tsupport χ)
  rw [heq, memLp_indicator_iff_restrict hcl.measurableSet.nullMeasurableSet]
  exact memLpLoc_iff.1 (hf.continuousOn_smul hχ.continuousOn) _ hsupp hχc
/-- A continuous compactly supported factor whose support meets the closed set `T` inside `S`
makes a function in `MemLpLoc 1 S` integrable on `T`, even though `T` may be unbounded or leave
`S`. -/
theorem MemLpLoc.integrableOn_smul [T2Space α] [OpensMeasurableSpace α]
    {S T : Set α} {h : α → F} (hh : MemLpLoc 1 S h μ)
    {f : α → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) (hT : IsClosed T)
    (hfS : tsupport f ∩ T ⊆ S) : IntegrableOn (fun z => f z • h z) T μ := by
  have hK : IsCompact (tsupport f ∩ T) := hfc.isCompact.inter_right hT
  have hhK : IntegrableOn h (tsupport f ∩ T) μ :=
    memLp_one_iff_integrable.1 (hh _ hfS hK)
  refine (hhK.continuousOn_smul hf.continuousOn hK).of_forall_sdiff_eq_zero hT.measurableSet
    fun z hz => ?_
  simp [image_eq_zero_of_notMem_tsupport fun h => hz.2 ⟨h, hz.1⟩]

end MemLpLocNormedSpace

section PreciseRepresentative

open TauCeti.MeasureTheory in
/-- A locally `Lᵖ` function on an open set `Ω`, with `1 ≤ p`, agrees almost everywhere on `Ω` with
its precise representative, for any locally finite uniformly locally doubling measure. -/
theorem MemLpLoc.ae_eq_preciseRepresentative {α F : Type*} [PseudoMetricSpace α]
    [LocallyCompactSpace α] [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α]
    {μ : Measure α} [IsUnifLocDoublingMeasure μ] [IsLocallyFiniteMeasure μ]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {p : ℝ≥0∞} {Ω : Opens α} {f : α → F} (hp : 1 ≤ p) (hu : MemLpLoc p Ω f μ) :
    f =ᵐ[μ.restrict Ω] preciseRepresentative μ f :=
  ae_eq_restrict_preciseRepresentative Ω.isOpen
    (hu.locallyIntegrableOn hp Ω.isOpen.isLocallyClosed)

end PreciseRepresentative

/-! ### Local Sobolev classes `MemWkpLoc` -/

section MemWkpLoc

universe u v w

/-- Auxiliary recursion for `TauCeti.MemWkpLoc` whose codomain lies in `Type max u v`, so iterated
operator spaces `E →L[ℝ] F` stay in the same universe. -/
private def memWkpLocAux {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] (μ : Measure E) (p : ℝ≥0∞) (U : Set E) :
    (k : ℕ) → {F : Type max u v} → [NormedAddCommGroup F] → [NormedSpace ℝ F] → (E → F) → Prop
  | 0, _, _, _, f => MemLpLoc p U f μ
  | k + 1, F, _, _, f => MemLpLoc p U f μ ∧
      ∃ D : E → E →L[ℝ] F, HasWeakFDerivOn μ (Opens.interior U) f D ∧ memWkpLocAux μ p U k D

private theorem memWkpLocAux_univ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] {μ : Measure E} {p : ℝ≥0∞} {U : Set E} {k : ℕ}
    {F : Type max u v} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} :
    memWkpLocAux.{u, v} μ p U k f ↔ memWkpLocAux.{u, max u v} μ p U k f := by
  induction k generalizing F with
  | zero => exact Iff.rfl
  | succ k ih =>
    exact and_congr_right fun _ => exists_congr fun D =>
      and_congr_right fun _ => ih (F := E →L[ℝ] F) (f := D)

variable {E : Type u} {F : Type v} {G : Type w}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {μ : Measure E} {p q : ℝ≥0∞} {U V : Set E} {Ω : Opens E} {k l : ℕ} {f g : E → F}

/-- The iterated weak derivatives through order `k` exist on `interior U` relative to `μ` and are
`Lᵖ(μ)` on every compact subset of `U`, including compact sets reaching its boundary.
The first derivative takes values in `E →L[ℝ] F`; higher derivatives iterate this construction.
No integrability at infinity or boundary trace is required. -/
def MemWkpLoc (p : ℝ≥0∞) (U : Set E) (k : ℕ) (f : E → F)
    (μ : Measure E := by volume_tac) : Prop :=
  match k with
  | 0 => MemLpLoc p U f μ
  | k + 1 => MemLpLoc p U f μ ∧
      ∃ D : E → E →L[ℝ] F, HasWeakFDerivOn μ (Opens.interior U) f D ∧
        memWkpLocAux.{u, v} μ p U k D

private theorem memWkpLoc_iff_aux {F : Type max u v} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} :
    MemWkpLoc.{u, max u v} p U k f μ ↔ memWkpLocAux.{u, v} μ p U k f := by
  cases k with
  | zero => exact Iff.rfl
  | succ k =>
    exact and_congr_right fun _ => exists_congr fun _ => and_congr_right fun _ =>
      (memWkpLocAux_univ.{u, v}).symm

/-- At order zero the local Sobolev class is exactly the local `Lᵖ` class. -/
@[simp]
theorem memWkpLoc_zero_iff : MemWkpLoc p U 0 f μ ↔ MemLpLoc p U f μ := Iff.rfl

/-- The successor-order characterization supplies a weak derivative in the preceding class. -/
theorem memWkpLoc_succ_iff : MemWkpLoc p U (k + 1) f μ ↔ MemLpLoc p U f μ ∧
    ∃ D : E → E →L[ℝ] F, HasWeakFDerivOn μ (Opens.interior U) f D ∧
      MemWkpLoc p U k D μ :=
  and_congr_right fun _ => exists_congr fun _ => and_congr_right fun _ =>
    (memWkpLoc_iff_aux.{u, v}).symm

/-- On an open domain, the successor-order weak derivative is tested on the domain itself. -/
theorem memWkpLoc_succ_iff_of_isOpen : MemWkpLoc p Ω (k + 1) f μ ↔ MemLpLoc p Ω f μ ∧
    ∃ D : E → E →L[ℝ] F, HasWeakFDerivOn μ Ω f D ∧ MemWkpLoc p Ω k D μ := by
  simp only [memWkpLoc_succ_iff, Opens.interior_coe]

/-- For a continuous function, the `MemLpLoc` condition on the function itself is automatic, so
membership in `W^{1,p}_loc(U; F)` is equivalent to having a weak derivative on `interior U` in
`MemLpLoc p U`. -/
theorem _root_.ContinuousOn.memWkpLoc_one_iff [OpensMeasurableSpace E]
    [IsFiniteMeasureOnCompacts μ] (hf : ContinuousOn f U) :
    MemWkpLoc p U 1 f μ ↔
      ∃ D : E → E →L[ℝ] F, HasWeakFDerivOn μ (Opens.interior U) f D ∧ MemLpLoc p U D μ := by
  simp only [memWkpLoc_succ_iff, memWkpLoc_zero_iff, hf.memLpLoc, true_and]

/-- On an open domain, a continuous function lies in `W^{1,p}_loc(Ω; F)` if and only if it has a
weak derivative on `Ω` belonging to `MemLpLoc p Ω`. -/
theorem _root_.ContinuousOn.memWkpLoc_one_iff_of_isOpen [OpensMeasurableSpace E]
    [IsFiniteMeasureOnCompacts μ] (hf : ContinuousOn f Ω) :
    MemWkpLoc p Ω 1 f μ ↔
      ∃ D : E → E →L[ℝ] F, HasWeakFDerivOn μ Ω f D ∧ MemLpLoc p Ω D μ := by
  simp only [memWkpLoc_succ_iff_of_isOpen, memWkpLoc_zero_iff, hf.memLpLoc, true_and]

/-- Every local Sobolev function is locally `Lᵖ`. -/
theorem MemWkpLoc.memLpLoc (hf : MemWkpLoc p U k f μ) : MemLpLoc p U f μ := by
  cases k with
  | zero => exact hf
  | succ k => exact hf.1

/-- A positive-order local Sobolev function has a weak derivative of the preceding order. -/
theorem MemWkpLoc.exists_weakFDeriv (hf : MemWkpLoc p U (k + 1) f μ) :
    ∃ D : E → E →L[ℝ] F, HasWeakFDerivOn μ (Opens.interior U) f D ∧
      MemWkpLoc p U k D μ := (memWkpLoc_succ_iff.1 hf).2

/-- On an open domain, positive-order membership gives a weak derivative on that domain. -/
theorem MemWkpLoc.exists_weakFDeriv_of_isOpen (hf : MemWkpLoc p Ω (k + 1) f μ) :
    ∃ D : E → E →L[ℝ] F, HasWeakFDerivOn μ Ω f D ∧ MemWkpLoc p Ω k D μ :=
  (memWkpLoc_succ_iff_of_isOpen.mp hf).2

/-- Positive-order membership retains the completeness required by weak derivatives. -/
theorem MemWkpLoc.completeSpace (hf : MemWkpLoc p U (k + 1) f μ) : CompleteSpace F := by
  obtain ⟨D, hD, _⟩ := hf.exists_weakFDeriv
  exact hD.completeSpace

private theorem memWkpLoc_mono_max {F : Type max u v} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (hf : MemWkpLoc p U k f μ) (hVU : V ⊆ U) : MemWkpLoc p V k f μ := by
  induction k generalizing F with
  | zero => exact (memWkpLoc_zero_iff.1 hf).mono_set hVU
  | succ k ih =>
    obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
    exact memWkpLoc_succ_iff.2 ⟨hp.mono_set hVU, D, hD.mono (interior_mono hVU), ih hk⟩

/-- Restriction preserves the interior weak derivatives and the bounds on compact subsets. -/
theorem MemWkpLoc.mono (hf : MemWkpLoc p U k f μ) (hVU : V ⊆ U) :
    MemWkpLoc p V k f μ := by
  cases k with
  | zero => exact (memWkpLoc_zero_iff.1 hf).mono_set hVU
  | succ k =>
    obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
    exact memWkpLoc_succ_iff.2
      ⟨hp.mono_set hVU, D, hD.mono (interior_mono hVU), memWkpLoc_mono_max hk hVU⟩

/-- Almost-everywhere changes of the function preserve its local Sobolev class. -/
theorem MemWkpLoc.congr_ae (hf : MemWkpLoc p U k f μ)
    (hfg : f =ᵐ[μ.restrict U] g) : MemWkpLoc p U k g μ := by
  cases k with
  | zero => exact (memWkpLoc_zero_iff.1 hf).congr_ae hfg
  | succ k =>
    obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
    exact memWkpLoc_succ_iff.2 ⟨hp.congr_ae hfg, D,
      hD.congr_ae (ae_mono (Measure.restrict_mono_set μ interior_subset) hfg), hk⟩

/-- Restricting to a subset preserves the local Sobolev class of any function agreeing with the
original one on that subset. -/
theorem MemWkpLoc.congr_mono [OpensMeasurableSpace E] (hf : MemWkpLoc p U k f μ)
    (hgf : Set.EqOn g f V) (hVU : V ⊆ U) : MemWkpLoc p V k g μ := by
  cases k with
  | zero => exact MemLpLoc.congr_mono (memWkpLoc_zero_iff.1 hf) hgf hVU
  | succ k =>
    obtain ⟨-, D, hD, hk⟩ := memWkpLoc_succ_iff.1 (hf.mono hVU)
    exact memWkpLoc_succ_iff.2 ⟨hf.memLpLoc.congr_mono hgf hVU, D, hD.congr_ae <| by
      filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with z hz using
        (hgf (interior_subset hz)).symm, hk⟩

/-- The local Sobolev class only depends on the values on the set. -/
theorem MemWkpLoc.congr [OpensMeasurableSpace E] (hf : MemWkpLoc p U k f μ)
    (hgf : Set.EqOn g f U) : MemWkpLoc p U k g μ :=
  hf.congr_mono hgf subset_rfl

/-- Every weak derivative of a member of `MemWkpLoc p Ω (k + 1)` is in `MemWkpLoc p Ω k`, not only
the one supplied by the definition: weak derivatives are unique almost everywhere. -/
theorem MemWkpLoc.memWkpLoc_of_hasWeakFDerivOn [FiniteDimensional ℝ E] [BorelSpace E]
    (hf : MemWkpLoc p Ω (k + 1) f μ) {D : E → E →L[ℝ] F} (hD : HasWeakFDerivOn μ Ω f D) :
    MemWkpLoc p Ω k D μ := by
  obtain ⟨D', hD', hD'k⟩ := hf.exists_weakFDeriv_of_isOpen
  exact hD'k.congr_ae (hD'.ae_eq hD)

/-- Every weak derivative of a member of `MemWkpLoc p Ω 1` is locally `Lᵖ` on `Ω`, not only the
one supplied by the definition: weak derivatives are unique almost everywhere. -/
theorem MemWkpLoc.memLpLoc_of_hasWeakFDerivOn [FiniteDimensional ℝ E] [BorelSpace E]
    (hf : MemWkpLoc p Ω 1 f μ) {D : E → E →L[ℝ] F} (hD : HasWeakFDerivOn μ Ω f D) :
    MemLpLoc p Ω D μ :=
  memWkpLoc_zero_iff.1 (hf.memWkpLoc_of_hasWeakFDerivOn hD)

private theorem memWkpLoc_mono_exponent_max [IsFiniteMeasureOnCompacts μ] {F : Type max u v}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (hf : MemWkpLoc p U k f μ)
    (hqp : q ≤ p) : MemWkpLoc q U k f μ := by
  induction k generalizing F with
  | zero => exact (memWkpLoc_zero_iff.1 hf).mono_exponent hqp
  | succ k ih =>
    obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
    exact memWkpLoc_succ_iff.2 ⟨hp.mono_exponent hqp, D, hD, ih hk⟩

/-- Decreasing the integrability exponent preserves each local derivative order. -/
theorem MemWkpLoc.mono_exponent [IsFiniteMeasureOnCompacts μ] (hf : MemWkpLoc p U k f μ)
    (hqp : q ≤ p) : MemWkpLoc q U k f μ := by
  cases k with
  | zero => exact (memWkpLoc_zero_iff.1 hf).mono_exponent hqp
  | succ k =>
    obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
    exact memWkpLoc_succ_iff.2 ⟨hp.mono_exponent hqp, D, hD, memWkpLoc_mono_exponent_max hk hqp⟩

private theorem memWkpLoc_of_succ_max {F : Type max u v} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (hf : MemWkpLoc p U (k + 1) f μ) : MemWkpLoc p U k f μ := by
  induction k generalizing F with
  | zero => exact hf.memLpLoc
  | succ k ih =>
    obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
    exact memWkpLoc_succ_iff.2 ⟨hp, D, hD, ih hk⟩

/-- Dropping the top derivative preserves local Sobolev membership. -/
theorem MemWkpLoc.of_succ (hf : MemWkpLoc p U (k + 1) f μ) : MemWkpLoc p U k f μ := by
  cases k with
  | zero => exact hf.memLpLoc
  | succ k =>
    obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
    exact memWkpLoc_succ_iff.2 ⟨hp, D, hD, memWkpLoc_of_succ_max hk⟩

/-- Membership at any smaller derivative order follows from membership at a larger one. -/
theorem MemWkpLoc.of_le (hf : MemWkpLoc p U k f μ) (hlk : l ≤ k) : MemWkpLoc p U l f μ := by
  induction hlk with
  | refl => exact hf
  | step _ ih => exact ih hf.of_succ

private theorem memWkpLoc_zero_fun_max {F : Type max u v} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] : MemWkpLoc p U k (0 : E → F) μ := by
  induction k generalizing F with
  | zero => exact memLpLoc_zero
  | succ k ih => exact memWkpLoc_succ_iff.2 ⟨memLpLoc_zero, 0, hasWeakFDerivOn_zero, ih⟩

/-- The zero function lies in every local Sobolev class with complete codomain. -/
@[simp]
theorem memWkpLoc_zero_fun [CompleteSpace F] : MemWkpLoc p U k (0 : E → F) μ := by
  cases k with
  | zero => exact memLpLoc_zero
  | succ k =>
    exact memWkpLoc_succ_iff.2 ⟨memLpLoc_zero, 0, hasWeakFDerivOn_zero, memWkpLoc_zero_fun_max⟩

private theorem memWkpLoc_add_max [OpensMeasurableSpace E] {F : Type max u v}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f g : E → F} (hf : MemWkpLoc p U k f μ)
    (hg : MemWkpLoc p U k g μ) : MemWkpLoc p U k (f + g) μ := by
  induction k generalizing F with
  | zero => exact (memWkpLoc_zero_iff.1 hf).add (memWkpLoc_zero_iff.1 hg)
  | succ k ih =>
    obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
    obtain ⟨hq, D', hD', hk'⟩ := memWkpLoc_succ_iff.1 hg
    exact memWkpLoc_succ_iff.2 ⟨hp.add hq, D + D', hD.add hD', ih hk hk'⟩

/-- Local Sobolev membership is closed under addition. -/
theorem MemWkpLoc.add [OpensMeasurableSpace E] (hf : MemWkpLoc p U k f μ)
    (hg : MemWkpLoc p U k g μ) : MemWkpLoc p U k (f + g) μ := by
  cases k with
  | zero => exact (memWkpLoc_zero_iff.1 hf).add (memWkpLoc_zero_iff.1 hg)
  | succ k =>
    obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
    obtain ⟨hq, D', hD', hk'⟩ := memWkpLoc_succ_iff.1 hg
    exact memWkpLoc_succ_iff.2 ⟨hp.add hq, D + D', hD.add hD', memWkpLoc_add_max hk hk'⟩

private theorem memWkpLoc_neg_max {F : Type max u v} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (hf : MemWkpLoc p U k f μ) : MemWkpLoc p U k (-f) μ := by
  induction k generalizing F with
  | zero => exact (memWkpLoc_zero_iff.1 hf).neg
  | succ k ih =>
    obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
    exact memWkpLoc_succ_iff.2 ⟨hp.neg, -D, hD.neg, ih hk⟩

/-- Local Sobolev membership is closed under negation. -/
theorem MemWkpLoc.neg (hf : MemWkpLoc p U k f μ) : MemWkpLoc p U k (-f) μ := by
  cases k with
  | zero => exact (memWkpLoc_zero_iff.1 hf).neg
  | succ k =>
    obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
    exact memWkpLoc_succ_iff.2 ⟨hp.neg, -D, hD.neg, memWkpLoc_neg_max hk⟩

/-- Local Sobolev membership is closed under subtraction. -/
theorem MemWkpLoc.sub [OpensMeasurableSpace E] (hf : MemWkpLoc p U k f μ)
    (hg : MemWkpLoc p U k g μ) : MemWkpLoc p U k (f - g) μ := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

private theorem memWkpLoc_const_smul_max {F : Type max u v} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E → F} (hf : MemWkpLoc p U k f μ) (c : ℝ) :
    MemWkpLoc p U k (c • f) μ := by
  induction k generalizing F with
  | zero => exact (memWkpLoc_zero_iff.1 hf).const_smul c
  | succ k ih =>
    obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
    exact memWkpLoc_succ_iff.2 ⟨hp.const_smul c, c • D, hD.const_smul c, ih hk⟩

/-- Real scalar multiplication preserves local Sobolev membership. -/
theorem MemWkpLoc.const_smul (hf : MemWkpLoc p U k f μ) (c : ℝ) :
    MemWkpLoc p U k (c • f) μ := by
  cases k with
  | zero => exact (memWkpLoc_zero_iff.1 hf).const_smul c
  | succ k =>
    obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
    exact memWkpLoc_succ_iff.2 ⟨hp.const_smul c, c • D, hD.const_smul c,
      memWkpLoc_const_smul_max hk c⟩

private theorem memWkpLoc_clm_comp_max [OpensMeasurableSpace E] {F : Type max u v}
    {G : Type max u w} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [CompleteSpace G] {f : E → F} (hf : MemWkpLoc p U k f μ) (A : F →L[ℝ] G) :
    MemWkpLoc p U k (fun z => A (f z)) μ := by
  induction k generalizing F G with
  | zero => exact (memWkpLoc_zero_iff.1 hf).clm_comp A
  | succ k ih =>
    obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
    exact memWkpLoc_succ_iff.2 ⟨hp.clm_comp A, fun z => A.comp (D z), hD.clm_comp A,
      ih hk ((ContinuousLinearMap.compL ℝ E F G) A)⟩

/-- Continuous linear maps of the codomain preserve all local weak derivative orders. -/
theorem MemWkpLoc.clm_comp [OpensMeasurableSpace E] [CompleteSpace G] (hf : MemWkpLoc p U k f μ)
    (A : F →L[ℝ] G) : MemWkpLoc p U k (fun z => A (f z)) μ := by
  cases k with
  | zero => exact (memWkpLoc_zero_iff.1 hf).clm_comp A
  | succ k =>
    obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
    exact memWkpLoc_succ_iff.2 ⟨hp.clm_comp A, fun z => A.comp (D z), hD.clm_comp A,
      memWkpLoc_clm_comp_max hk ((ContinuousLinearMap.compL ℝ E F G) A)⟩

/-- Multiplying a fixed vector in a Banach space by a scalar local Sobolev function preserves
every local Sobolev class, with no basis of the codomain required. -/
theorem MemWkpLoc.smul_const [OpensMeasurableSpace E] [CompleteSpace F] {a : E → ℝ}
    (ha : MemWkpLoc p U k a μ) (v : F) :
    MemWkpLoc p U k (fun z => a z • v) μ :=
  ha.clm_comp ((ContinuousLinearMap.id ℝ ℝ).smulRight v)

/-- **Pairs of local Sobolev maps.** Two maps in the local Sobolev class of order `k` pair to a map
in the same class, with values in the product. -/
theorem MemWkpLoc.prodMk [OpensMeasurableSpace E] [CompleteSpace F] [CompleteSpace G] {g : E → G}
    (hf : MemWkpLoc p U k f μ) (hg : MemWkpLoc p U k g μ) :
    MemWkpLoc p U k (fun z => (f z, g z)) μ := by
  have h := (hf.clm_comp (ContinuousLinearMap.inl ℝ F G)).add
    (hg.clm_comp (ContinuousLinearMap.inr ℝ F G))
  convert h using 1
  ext z <;> simp

/-- **Products of operator fields.** If two fields of continuous linear maps are in the local
Sobolev class of order `k`, so is their pointwise product map `(A z).prodMap (B z)`. -/
theorem MemWkpLoc.prodMap [OpensMeasurableSpace E] {E₁ E₂ E₃ E₄ : Type*} [NormedAddCommGroup E₁]
    [NormedSpace ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [CompleteSpace E₂]
    [NormedAddCommGroup E₃] [NormedSpace ℝ E₃] [NormedAddCommGroup E₄] [NormedSpace ℝ E₄]
    [CompleteSpace E₄] {A : E → E₁ →L[ℝ] E₂} {B : E → E₃ →L[ℝ] E₄} (hA : MemWkpLoc p U k A μ)
    (hB : MemWkpLoc p U k B μ) : MemWkpLoc p U k (fun z => (A z).prodMap (B z)) μ := by
  simpa using (hA.prodMk hB).clm_comp (ContinuousLinearMap.prodMapL ℝ E₁ E₂ E₃ E₄)

/-- A continuous linear change of codomain preserves and reflects every local weak
Sobolev order. -/
@[simp]
theorem _root_.ContinuousLinearEquiv.comp_memWkpLoc_iff [OpensMeasurableSpace E] (e : F ≃L[ℝ] G) :
    MemWkpLoc p U k (fun z => e (f z)) μ ↔ MemWkpLoc p U k f μ := by
  cases k with
  | zero =>
    simpa only [memWkpLoc_zero_iff] using
      (e.comp_memLpLoc_iff (p := p) (U := U) (f := f) (μ := μ))
  | succ k =>
    constructor
    · intro h
      have : CompleteSpace G := h.completeSpace
      have : CompleteSpace F :=
        (e.isUniformEmbedding.isUniformInducing.completeSpace_congr e.surjective).mpr inferInstance
      simpa only [ContinuousLinearEquiv.coe_coe, e.symm_apply_apply] using
        h.clm_comp e.symm.toContinuousLinearMap
    · intro h
      have : CompleteSpace F := h.completeSpace
      have : CompleteSpace G :=
        (e.isUniformEmbedding.isUniformInducing.completeSpace_congr e.surjective).mp inferInstance
      exact h.clm_comp e.toContinuousLinearMap

/-- Constant functions belong to every local Sobolev class, for any additive Haar measure on a
finite-dimensional domain. -/
@[simp]
theorem memWkpLoc_const [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure]
    [CompleteSpace F] (c : F) : MemWkpLoc p U k (fun _ => c) μ := by
  cases k with
  | zero => exact memLpLoc_const c
  | succ k =>
    refine memWkpLoc_succ_iff.2 ⟨memLpLoc_const c, 0, ?_, memWkpLoc_zero_fun⟩
    apply hasWeakFDerivOn_iff.mpr
    exact fun v => hasWeakLineDerivOn_const (μ := μ) (Ω := Opens.interior U) (v := v) c

/-- Finite sums of local Sobolev functions remain in the same class. -/
theorem MemWkpLoc.sum [OpensMeasurableSpace E] {ι : Type*} [CompleteSpace F] (s : Finset ι)
    {f : ι → E → F} (hf : ∀ i ∈ s, MemWkpLoc p U k (f i) μ) :
    MemWkpLoc p U k (fun z => ∑ i ∈ s, f i z) μ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty, Pi.zero_def] using
      (memWkpLoc_zero_fun (p := p) (U := U) (k := k) (F := F) (μ := μ))
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi, Pi.add_def] using
      (hf i (Finset.mem_insert_self i s)).add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- A function differentiable at every point of an open set `Ω` with locally `Lᵖ` Fréchet
derivative lies in `W^{1,p}_loc(Ω; F)` whenever `1 ≤ p`. -/
theorem memWkpLoc_one_of_differentiableOn [FiniteDimensional ℝ E] [BorelSpace E]
    [μ.IsAddHaarMeasure] [CompleteSpace F] (hp : 1 ≤ p)
    (hdiff : ∀ x ∈ (Ω : Set E), DifferentiableAt ℝ f x)
    (hD : MemLpLoc p Ω (fderiv ℝ f) μ) : MemWkpLoc p Ω 1 f μ := by
  have hc : ContinuousOn f Ω := fun x hx => (hdiff x hx).continuousAt.continuousWithinAt
  exact hc.memWkpLoc_one_iff_of_isOpen.2
    ⟨fderiv ℝ f, hasWeakFDerivOn_of_differentiableOn
      (hD.locallyIntegrableOn hp Ω.isOpen.isLocallyClosed) hdiff, hD⟩

/-- A function differentiable at every point of an open set `Ω` with continuous Fréchet derivative
on `Ω` lies in `W^{1,p}_loc(Ω; F)` for every exponent `p`, including `p < 1` and `p = ∞`, with weak
derivative `fderiv ℝ f`. -/
theorem memWkpLoc_one_of_continuousOn_fderiv [FiniteDimensional ℝ E] [BorelSpace E]
    [μ.IsAddHaarMeasure] [CompleteSpace F]
    (hdiff : ∀ x ∈ (Ω : Set E), DifferentiableAt ℝ f x)
    (hDc : ContinuousOn (fderiv ℝ f) Ω) : MemWkpLoc p Ω 1 f μ := by
  have hc : ContinuousOn f Ω := fun x hx => (hdiff x hx).continuousAt.continuousWithinAt
  exact hc.memWkpLoc_one_iff_of_isOpen.2
    ⟨fderiv ℝ f, hasWeakFDerivOn_of_differentiableOn
      (hDc.locallyIntegrableOn Ω.isOpen.measurableSet) hdiff, hDc.memLpLoc⟩

private theorem contDiffOn_memWkpLoc_max [FiniteDimensional ℝ E] [BorelSpace E]
    [μ.IsAddHaarMeasure] {F : Type max u v} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {f : E → F} (hf : ContDiffOn ℝ k f (Ω : Set E)) (hU : U ⊆ Ω) :
    MemWkpLoc p U k f μ := by
  induction k generalizing F with
  | zero => exact (hf.continuousOn.mono hU).memLpLoc
  | succ k ih =>
    have hD : ContDiffOn ℝ k (fderiv ℝ f) (Ω : Set E) :=
      hf.fderiv_of_isOpen Ω.isOpen (by simp)
    refine memWkpLoc_succ_iff.2 ⟨(hf.continuousOn.mono hU).memLpLoc, fderiv ℝ f, ?_, ih hD⟩
    exact (hf.of_le (by simp)).hasWeakFDerivOn_fderiv.mono (interior_subset.trans hU)

/-- A map that is `Cᵏ` on an open neighbourhood of `U` has locally `Lᵖ` weak derivatives
through order `k` on `U`, with bounds reaching its boundary, for every exponent. -/
theorem _root_.ContDiffOn.memWkpLoc [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure]
    [CompleteSpace F] (hf : ContDiffOn ℝ k f (Ω : Set E)) (hU : U ⊆ Ω) :
    MemWkpLoc p U k f μ := by
  cases k with
  | zero => exact (hf.continuousOn.mono hU).memLpLoc
  | succ k =>
    have hD : ContDiffOn ℝ k (fderiv ℝ f) (Ω : Set E) :=
      hf.fderiv_of_isOpen Ω.isOpen (by simp)
    refine memWkpLoc_succ_iff.2
      ⟨(hf.continuousOn.mono hU).memLpLoc, fderiv ℝ f, ?_, contDiffOn_memWkpLoc_max hD hU⟩
    exact (hf.of_le (by simp)).hasWeakFDerivOn_fderiv.mono (interior_subset.trans hU)

/-- A `Cᵏ` map on the whole space is in the local class `W^{k,p}` on every set, for every
exponent. -/
theorem _root_.ContDiff.memWkpLoc [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure]
    [CompleteSpace F] (hf : ContDiff ℝ k f) : MemWkpLoc p U k f μ :=
  hf.contDiffOn.memWkpLoc (Ω := ⊤) ((Set.subset_univ U).trans_eq Opens.coe_top.symm)

end MemWkpLoc

/-! ### Bounds for chains of weak derivatives -/

section WeakDerivChainLe

universe u v

/-- Auxiliary recursion for `TauCeti.WeakDerivChainLe` whose codomain lies in `Type max u v`, so
iterated operator spaces `E →L[ℝ] F` stay in the same universe. -/
private def weakDerivChainLeAux {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] (μ : Measure E) (p : ℝ≥0∞) (S T : Set E) (C : ℝ≥0∞) :
    (m : ℕ) → {F : Type max u v} → [NormedAddCommGroup F] → [NormedSpace ℝ F] →
      (E → F) → (E → F) → Prop
  | 0, _, _, _, f, g => eLpNorm f p (μ.restrict S) ≤ C * eLpNorm g p (μ.restrict T)
  | m + 1, F, _, _, f, g =>
      eLpNorm f p (μ.restrict S) ≤ C * eLpNorm g p (μ.restrict T) ∧
        ∀ Df Dg : E → E →L[ℝ] F, HasWeakFDerivOn μ (Opens.interior S) f Df →
          HasWeakFDerivOn μ (Opens.interior T) g Dg →
            weakDerivChainLeAux μ p S T C m Df Dg

private theorem weakDerivChainLeAux_univ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] {μ : Measure E} {p C : ℝ≥0∞} {S T : Set E} {m : ℕ}
    {F : Type max u v} [NormedAddCommGroup F] [NormedSpace ℝ F] {f g : E → F} :
    weakDerivChainLeAux.{u, v} μ p S T C m f g ↔
      weakDerivChainLeAux.{u, max u v} μ p S T C m f g := by
  induction m generalizing F with
  | zero => exact Iff.rfl
  | succ m ih =>
    exact and_congr_right fun _ => forall_congr' fun Df => forall_congr' fun Dg =>
      imp_congr_right fun _ => imp_congr_right fun _ => ih (F := E →L[ℝ] F) (f := Df) (g := Dg)

variable {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure E} {p C : ℝ≥0∞} {S T : Set E} {m : ℕ} {f g : E → F}

/-- `WeakDerivChainLe p S T C m f g μ` bounds the iterated weak derivatives of `f` through order
`m` by those of `g`: the `Lᵖ(S)` norm of `f` is at most `C` times the `Lᵖ(T)` norm of `g`, and for
every weak derivative `Df` of `f` on the interior of `S` and every weak derivative `Dg` of `g` on
the interior of `T`, the pair `Df`, `Dg` satisfies the same through order `m - 1`. Since the
quantification is over all weak derivatives, the bound holds for every choice of the iterated
derivatives `D^i f` and `D^i g`, `i ≤ m`. -/
def WeakDerivChainLe (p : ℝ≥0∞) (S T : Set E) (C : ℝ≥0∞) (m : ℕ) (f g : E → F)
    (μ : Measure E := by volume_tac) : Prop :=
  match m with
  | 0 => eLpNorm f p (μ.restrict S) ≤ C * eLpNorm g p (μ.restrict T)
  | m + 1 =>
      eLpNorm f p (μ.restrict S) ≤ C * eLpNorm g p (μ.restrict T) ∧
        ∀ Df Dg : E → E →L[ℝ] F, HasWeakFDerivOn μ (Opens.interior S) f Df →
          HasWeakFDerivOn μ (Opens.interior T) g Dg →
            weakDerivChainLeAux.{u, v} μ p S T C m Df Dg

private theorem weakDerivChainLe_iff_aux {F : Type max u v} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f g : E → F} :
    WeakDerivChainLe.{u, max u v} p S T C m f g μ ↔
      weakDerivChainLeAux.{u, v} μ p S T C m f g := by
  cases m with
  | zero => exact Iff.rfl
  | succ m =>
    exact and_congr_right fun _ => forall_congr' fun _ => forall_congr' fun _ =>
      imp_congr_right fun _ => imp_congr_right fun _ =>
        (weakDerivChainLeAux_univ.{u, v}).symm

/-- At order zero the chain bound is the `Lᵖ` bound. -/
@[simp]
theorem weakDerivChainLe_zero_iff :
    WeakDerivChainLe p S T C 0 f g μ ↔
      eLpNorm f p (μ.restrict S) ≤ C * eLpNorm g p (μ.restrict T) :=
  Iff.rfl

/-- At a successor order the chain bound is the `Lᵖ` bound together with the chain bound for
every pair of weak derivatives. -/
theorem weakDerivChainLe_succ_iff :
    WeakDerivChainLe p S T C (m + 1) f g μ ↔
      eLpNorm f p (μ.restrict S) ≤ C * eLpNorm g p (μ.restrict T) ∧
        ∀ Df Dg : E → E →L[ℝ] F, HasWeakFDerivOn μ (Opens.interior S) f Df →
          HasWeakFDerivOn μ (Opens.interior T) g Dg → WeakDerivChainLe p S T C m Df Dg μ :=
  and_congr_right fun _ => forall_congr' fun _ => forall_congr' fun _ =>
    imp_congr_right fun _ => imp_congr_right fun _ =>
      (weakDerivChainLe_iff_aux.{u, v}).symm

/-- A chain bound gives the `Lᵖ` bound at order zero. -/
theorem WeakDerivChainLe.eLpNorm_le (h : WeakDerivChainLe p S T C m f g μ) :
    eLpNorm f p (μ.restrict S) ≤ C * eLpNorm g p (μ.restrict T) := by
  cases m with
  | zero => exact h
  | succ m => exact h.1

/-- A chain bound passes to every pair of weak derivatives, one order lower. -/
theorem WeakDerivChainLe.weakFDeriv (h : WeakDerivChainLe p S T C (m + 1) f g μ)
    {Df Dg : E → E →L[ℝ] F} (hf : HasWeakFDerivOn μ (Opens.interior S) f Df)
    (hg : HasWeakFDerivOn μ (Opens.interior T) g Dg) :
    WeakDerivChainLe p S T C m Df Dg μ :=
  (weakDerivChainLe_succ_iff.1 h).2 Df Dg hf hg

end WeakDerivChainLe

/-! ### Classical derivatives of `Cᵏ` representatives -/

section ClassicalRepresentatives

universe u v

variable {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {p : ℝ≥0∞} {U : Set E} {k m : ℕ} {u g : E → F}

/-- **The derivative of a `C¹` representative is a weak derivative.** Let `U` agree almost
everywhere with its interior, as an open set does and as a half-disc `Ω ∩ {0 ≤ im}` does
(`TauCeti.inter_setOf_im_nonneg_ae_eq_interior`). If `g` is `C¹` on the interior of `U` and
agrees almost everywhere on `U` with `u ∈ MemWkpLoc p U (k + 1)`, then `fderiv ℝ g` is a weak
derivative of `u` on the interior of `U` and lies in `MemWkpLoc p U k`. By uniqueness of weak
derivatives (`TauCeti.HasWeakFDerivOn.ae_eq`), every weak derivative of `u` on the interior of `U`
agrees with `fderiv ℝ g` almost everywhere on `U`. -/
theorem MemWkpLoc.hasWeakFDerivOn_fderiv_of_contDiffOn (hu : MemWkpLoc p U (k + 1) u μ)
    (hU : U =ᵐ[μ] (Opens.interior U : Set E)) (hg : ContDiffOn ℝ 1 g (Opens.interior U))
    (hug : u =ᵐ[μ.restrict U] g) :
    HasWeakFDerivOn μ (Opens.interior U) u (fderiv ℝ g) ∧ MemWkpLoc p U k (fderiv ℝ g) μ := by
  have := hu.completeSpace
  rw [Measure.restrict_congr_set hU] at hug
  have hg' : HasWeakFDerivOn μ (Opens.interior U) g (fderiv ℝ g) := hg.hasWeakFDerivOn_fderiv
  obtain ⟨D, hD, hDk⟩ := hu.exists_weakFDeriv
  refine ⟨hg'.congr_ae hug.symm, hDk.congr_ae ?_⟩
  rw [Measure.restrict_congr_set hU]
  exact (hD.congr_ae hug).ae_eq hg'

private theorem iteratedFDeriv_of_contDiffOn_max {F : Type max u v}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {u g : E → F}
    (hu : MemWkpLoc p U (k + m) u μ) (hU : U =ᵐ[μ] (Opens.interior U : Set E))
    (hg : ContDiffOn ℝ k g (Opens.interior U)) (hug : u =ᵐ[μ.restrict U] g) :
    MemWkpLoc p U m (iteratedFDeriv ℝ k g) μ := by
  induction k generalizing F with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp]
    exact ((continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.comp_memWkpLoc_iff
      (E := E) (μ := μ)).2 ((Nat.zero_add m ▸ hu).congr_ae hug)
  | succ k ih =>
    rw [Nat.add_right_comm] at hu
    have : CompleteSpace F := hu.completeSpace
    obtain ⟨-, hDk⟩ := hu.hasWeakFDerivOn_fderiv_of_contDiffOn hU
      (hg.of_le (by exact_mod_cast Nat.le_add_left 1 k)) hug
    have hgk : ContDiffOn ℝ k (fderiv ℝ g) (Opens.interior U) :=
      hg.fderiv_of_isOpen isOpen_interior (by push_cast; rfl)
    have h := ih hDk hgk (Filter.EventuallyEq.refl _ _)
    let L :=
      (continuousMultilinearCurryRightEquiv' ℝ k E F).symm.toLinearIsometry.toContinuousLinearMap
    have heq : iteratedFDeriv ℝ (k + 1) g = fun z => L (iteratedFDeriv ℝ k (fderiv ℝ g) z) := by
      ext1 z
      exact iteratedFDeriv_succ_eq_comp_right
    rw [heq]
    exact h.clm_comp L

/-- **Iterated derivatives of a `Cᵏ` representative.** Let `U` agree almost everywhere with its
interior, as an open set does and as a half-disc `Ω ∩ {0 ≤ im}` does
(`TauCeti.inter_setOf_im_nonneg_ae_eq_interior`). If `g` is `Cᵏ` on the interior of `U` and agrees
almost everywhere on `U` with `u ∈ MemWkpLoc p U (k + m)`, then `iteratedFDeriv ℝ k g` lies in
`MemWkpLoc p U m`. No restriction on `p` is needed. -/
theorem MemWkpLoc.iteratedFDeriv_of_contDiffOn (hu : MemWkpLoc p U (k + m) u μ)
    (hU : U =ᵐ[μ] (Opens.interior U : Set E)) (hg : ContDiffOn ℝ k g (Opens.interior U))
    (hug : u =ᵐ[μ.restrict U] g) :
    MemWkpLoc p U m (iteratedFDeriv ℝ k g) μ := by
  cases k with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp]
    exact ((continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.comp_memWkpLoc_iff
      (E := E) (μ := μ)).2 ((Nat.zero_add m ▸ hu).congr_ae hug)
  | succ k =>
    rw [Nat.add_right_comm] at hu
    have : CompleteSpace F := hu.completeSpace
    obtain ⟨-, hDk⟩ := hu.hasWeakFDerivOn_fderiv_of_contDiffOn hU
      (hg.of_le (by exact_mod_cast Nat.le_add_left 1 k)) hug
    have hgk : ContDiffOn ℝ k (fderiv ℝ g) (Opens.interior U) :=
      hg.fderiv_of_isOpen isOpen_interior (by push_cast; rfl)
    have h := iteratedFDeriv_of_contDiffOn_max hDk hU hgk (Filter.EventuallyEq.refl _ _)
    let L :=
      (continuousMultilinearCurryRightEquiv' ℝ k E F).symm.toLinearIsometry.toContinuousLinearMap
    have heq : iteratedFDeriv ℝ (k + 1) g = fun z => L (iteratedFDeriv ℝ k (fderiv ℝ g) z) := by
      ext1 z
      exact iteratedFDeriv_succ_eq_comp_right
    rw [heq]
    exact h.clm_comp L

end ClassicalRepresentatives

end TauCeti
