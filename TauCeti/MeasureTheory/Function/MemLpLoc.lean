/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Prod
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import TauCeti.MeasureTheory.Function.PreciseRepresentative
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Function.LpSeminorm.ContinuousOn

/-!
# Local `Lᵖ` classes

`TauCeti.MemLpLoc p U f μ` says that `f` lies in `Lᵖ(μ)` on every compact subset of `U`. It is the
order-zero local class underlying local Sobolev classes: no integrability at infinity or near the
boundary of `U` is asserted, only on compact sets inside `U`. When `U` is not open, those compact
sets may reach its boundary, as for half-discs in the plane. The measure is an auto-parameter
defaulting to `volume`, as for `MeasureTheory.MemLp`. Strong measurability is part of membership,
since `MeasureTheory.MemLp` includes it, so for a Banach-valued `f` the class is the Bochner one.

This file supplies the basic API for every source with a measure: restriction to smaller sets,
almost-everywhere changes, linearity, continuous-linear composition, multiplication by continuous
factors (with extension by zero for factors supported in `U`, and global `Lᵖ` membership for
compactly supported ones), composition of local `Lᵖ` operator families with continuous ones,
Hölder's inequality on compact sets (`TauCeti.MemLpLoc.clm_apply`), decreasing the integrability
exponent, and comparison with local integrability. A locally `Lᵖ` function vanishing off a compact
subset of `U` is globally `Lᵖ`. Continuous functions, and more generally a.e.-strongly measurable
functions bounded near every point of `U`, are locally `Lᵖ` for every exponent, as is the extension
by zero of a function bounded near every point of `U` on a measurable subset
(`TauCeti.memLpLoc_indicator_of_forall_eventually_norm_le`). On an open set,
membership is detected on the open subsets with compact closure inside it, and on a ball of a proper
metric space on the smaller concentric balls (`TauCeti.memLpLoc_ball_iff`); with `1 ≤ p` a locally
`Lᵖ` function agrees almost everywhere with its precise representative.

Membership for `μ` passes to every measure bounded by a finite multiple of `μ`
(`TauCeti.MemLpLoc.of_measure_le_smul`). Two additive Haar measures on a locally compact group
are proportional on every compact set, so the class does not depend on the choice of Haar
measure (`TauCeti.memLpLoc_iff_of_isAddHaarMeasure`). Compact sets correspond under a
homeomorphism, which carries the class for `μ` to the class for the image measure
(`Homeomorph.memLpLoc_comp_iff`). Since the image of an additive Haar measure under a continuous
linear equivalence is an additive Haar measure, a continuous linear equivalence `E ≃L[ℝ] E₁` onto
a finite-dimensional space carries the class of `E₁` to that of `E` for any choice of Haar
measures (`ContinuousLinearEquiv.memLpLoc_comp_right_iff`). Thus the class on a finite-dimensional
space needs no inner product or preferred basis.
-/

public noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal

namespace TauCeti

section Basic

variable {X F G : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [NormedAddCommGroup F] [NormedAddCommGroup G]
  {μ ν : Measure X} {p q : ℝ≥0∞} {U V : Set X} {f g : X → F}

/-- A function is locally `Lᵖ` on `U` when it belongs to `Lᵖ` on every compact subset of `U`.
When `U` is not open, those compact subsets may reach its boundary. -/
def MemLpLoc (p : ℝ≥0∞) (U : Set X) (f : X → F) (μ : Measure X := by volume_tac) : Prop :=
  ∀ K : Set X, K ⊆ U → IsCompact K → MemLp f p (μ.restrict K)

/-- Local `Lᵖ` membership is characterized by `Lᵖ` membership on every compact subset. -/
theorem memLpLoc_iff : MemLpLoc p U f μ ↔
    ∀ K : Set X, K ⊆ U → IsCompact K → MemLp f p (μ.restrict K) := Iff.rfl

/-- Local `Lᵖ` membership restricts to any smaller set. -/
theorem MemLpLoc.mono_set (hf : MemLpLoc p U f μ) (hVU : V ⊆ U) : MemLpLoc p V f μ :=
  fun K hK hc => hf K (hK.trans hVU) hc

/-- Local `Lᵖ` membership on `U` gives `Lᵖ` membership on every set whose closure is compact and
contained in `U`. -/
theorem MemLpLoc.memLp_restrict_of_isCompact_closure (hf : MemLpLoc p U f μ) {W : Set X}
    (hWc : IsCompact (closure W)) (hWU : closure W ⊆ U) : MemLp f p (μ.restrict W) :=
  (hf _ hWU hWc).mono_measure (Measure.restrict_mono subset_closure le_rfl)

/-- A function that is `Lᵖ` on `U` is locally `Lᵖ` there. -/
theorem _root_.MeasureTheory.MemLp.memLpLoc (hf : MemLp f p (μ.restrict U)) :
    MemLpLoc p U f μ :=
  fun _ hK _ => hf.mono_measure (Measure.restrict_mono hK le_rfl)

/-- A function that is `Lᵖ` on a set `W` is locally `Lᵖ` on every set `U` contained in `W` up to a
null set, including on compact subsets of `U` that leave `W`. -/
theorem _root_.MeasureTheory.MemLp.memLpLoc_of_ae_le {W : Set X}
    (hf : MemLp f p (μ.restrict W)) (hUW : U ≤ᵐ[μ] W) : MemLpLoc p U f μ :=
  memLpLoc_iff.2 fun _ hK _ => hf.mono_measure
    (Measure.restrict_mono_ae ((Filter.EventuallySubset.of_subset hK).trans hUW))

/-- Domination almost everywhere on `U` by a locally `Lᵖ` function preserves local `Lᵖ`
membership, for a function almost everywhere strongly measurable on `U`. -/
theorem MemLpLoc.of_le (hg : MemLpLoc p U g μ) {h : X → G}
    (hh : AEStronglyMeasurable h (μ.restrict U)) (hhg : ∀ᵐ x ∂μ.restrict U, ‖h x‖ ≤ ‖g x‖) :
    MemLpLoc p U h μ := fun K hK hc =>
  (hg K hK hc).of_le (hh.mono_measure (Measure.restrict_mono hK le_rfl))
    (ae_mono (Measure.restrict_mono hK le_rfl) hhg)

/-- Almost-everywhere equality on `U` preserves local `Lᵖ` membership. -/
theorem MemLpLoc.congr_ae (hf : MemLpLoc p U f μ)
    (hfg : f =ᵐ[μ.restrict U] g) : MemLpLoc p U g μ := by
  intro K hK hc
  exact (hf K hK hc).ae_eq (ae_mono (Measure.restrict_mono_set μ hK) hfg)

/-- Local `Lᵖ` membership for `μ` gives it for every measure `ν ≤ c • μ` with `c` finite. -/
theorem MemLpLoc.of_measure_le_smul {c : ℝ≥0∞} (hc : c ≠ ∞) (hνμ : ν ≤ c • μ)
    (hf : MemLpLoc p U f μ) : MemLpLoc p U f ν := fun K hK hKc =>
  (hf K hK hKc).of_measure_le_smul hc <| by
    simpa only [Measure.restrict_smul] using Measure.restrict_mono subset_rfl hνμ

/-- Local `Lᵖ` membership passes to a smaller measure. -/
theorem MemLpLoc.mono_measure (hνμ : ν ≤ μ) (hf : MemLpLoc p U f μ) : MemLpLoc p U f ν :=
  hf.of_measure_le_smul ENNReal.one_ne_top (by rwa [one_smul])

/-- The zero function belongs to every local `Lᵖ` class. -/
@[simp]
theorem memLpLoc_zero : MemLpLoc p U (0 : X → F) μ := fun _ _ _ => MemLp.zero

/-- Local `Lᵖ` membership is closed under addition. -/
theorem MemLpLoc.add (hf : MemLpLoc p U f μ) (hg : MemLpLoc p U g μ) :
    MemLpLoc p U (f + g) μ := fun K hK hc => (hf K hK hc).add (hg K hK hc)

/-- Local `Lᵖ` membership is closed under negation. -/
theorem MemLpLoc.neg (hf : MemLpLoc p U f μ) : MemLpLoc p U (-f) μ :=
  fun K hK hc => (hf K hK hc).neg

/-- Local `Lᵖ` membership is closed under subtraction. -/
theorem MemLpLoc.sub (hf : MemLpLoc p U f μ) (hg : MemLpLoc p U g μ) :
    MemLpLoc p U (f - g) μ := fun K hK hc => (hf K hK hc).sub (hg K hK hc)

/-- A finite sum of locally `Lᵖ` functions is locally `Lᵖ`, without a completeness assumption. -/
theorem MemLpLoc.sum {ι : Type*} (s : Finset ι) {f : ι → X → F}
    (hf : ∀ i ∈ s, MemLpLoc p U (f i) μ) : MemLpLoc p U (fun z => ∑ i ∈ s, f i z) μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty, Pi.zero_def] using (memLpLoc_zero (p := p) (U := U))
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi, Pi.add_def] using
      (hf i (Finset.mem_insert_self i s)).add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- Compact subsets have finite measure, so decreasing the exponent preserves local membership.
In particular this passes from the infinity endpoint to every finite exponent. -/
theorem MemLpLoc.mono_exponent [IsFiniteMeasureOnCompacts μ] (hf : MemLpLoc p U f μ)
    (hqp : q ≤ p) : MemLpLoc q U f μ := by
  intro K hK hc
  have : IsFiniteMeasure (μ.restrict K) := ⟨by simpa using hc.measure_lt_top⟩
  exact (hf K hK hc).mono_exponent hqp

/-- On a locally compact regular space, local `Lᵖ` membership on an open set `Ω` is detected on
the open subsets `W` whose closure is compact and contained in `Ω`: an `Lᵖ` function on `W`
agreeing with `f` there suffices. -/
theorem memLpLoc_of_forall_opens [LocallyCompactSpace X] [RegularSpace X] {Ω : Opens X}
    (h : ∀ W : Opens X, IsCompact (closure (W : Set X)) → closure (W : Set X) ⊆ Ω →
      ∃ g : X → F, MemLp g p (μ.restrict (W : Set X)) ∧ g =ᵐ[μ.restrict W] f) :
    MemLpLoc p Ω f μ := by
  refine fun K hKΩ hK => ?_
  obtain ⟨W, hWo, hKW, hWΩ, hWc⟩ := exists_open_between_and_isCompact_closure hK Ω.isOpen hKΩ
  obtain ⟨g, hg, hgf⟩ := h ⟨W, hWo⟩ hWc hWΩ
  exact (hg.ae_eq hgf).mono_measure (Measure.restrict_mono hKW le_rfl)

section Measurable

variable [OpensMeasurableSpace X] [T2Space X]

/-- Restricting to a subset preserves local `Lᵖ` membership of any function agreeing with the
original one on that subset. -/
theorem MemLpLoc.congr_mono (hf : MemLpLoc p U f μ) (hgf : Set.EqOn g f V) (hVU : V ⊆ U) :
    MemLpLoc p V g μ := fun K hK hc => (hf K (hK.trans hVU) hc).ae_eq <| by
  filter_upwards [ae_restrict_mem hc.measurableSet] with z hz using (hgf (hK hz)).symm

/-- A locally `Lᵖ` function on `U` that vanishes off a compact set `T ⊆ U` is `Lᵖ` on the whole
space. -/
theorem MemLpLoc.memLp_of_forall_notMem_eq_zero (hf : MemLpLoc p U f μ) {T : Set X}
    (hT : IsCompact T) (hTU : T ⊆ U) (h0 : ∀ z ∉ T, f z = 0) : MemLp f p μ := by
  have : T.indicator f = f :=
    Set.indicator_eq_self.2 fun z hz => by_contra fun h' => hz (h0 z h')
  rw [← this, memLp_indicator_iff_restrict hT.measurableSet.nullMeasurableSet]
  exact hf T hTU hT

/-- A function continuous on `U` is locally `Lᵖ` there, with no global bound required. -/
theorem _root_.ContinuousOn.memLpLoc [IsFiniteMeasureOnCompacts μ] (hf : ContinuousOn f U) :
    MemLpLoc p U f μ :=
  fun _K hK hc => (hf.mono hK).memLp_restrict_of_subset_isCompact
    hc hc.measurableSet subset_rfl p

/-- Every constant function is locally `Lᵖ` for all exponents, including infinity. -/
@[simp]
theorem memLpLoc_const [IsFiniteMeasureOnCompacts μ] (c : F) :
    MemLpLoc p U (fun _ => c) μ :=
  continuousOn_const.memLpLoc

open scoped Topology in
/-- An a.e.-strongly measurable function on `U` that is bounded near every point of `U` is locally
`Lᵖ` on `U` for every exponent, including infinity: it is bounded on each compact subset. -/
theorem memLpLoc_of_forall_eventually_norm_le [IsFiniteMeasureOnCompacts μ]
    (hf : AEStronglyMeasurable f (μ.restrict U)) (hb : ∀ z ∈ U, ∃ M, ∀ᶠ w in 𝓝 z, ‖f w‖ ≤ M) :
    MemLpLoc p U f μ := by
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

open scoped Topology in
/-- A function a.e.-strongly measurable on a measurable subset `V` of `U`, and bounded on `V` near
every point of `U`, is locally `Lᵖ` on `U` for every exponent once extended by zero off `V`. -/
theorem memLpLoc_indicator_of_forall_eventually_norm_le [IsFiniteMeasureOnCompacts μ]
    (hV : MeasurableSet V) (hVU : V ⊆ U) (hf : AEStronglyMeasurable f (μ.restrict V))
    (hb : ∀ z ∈ U, ∃ M, ∀ᶠ w in 𝓝[U] z, w ∈ V → ‖f w‖ ≤ M) :
    MemLpLoc p U (V.indicator f) μ := by
  refine memLpLoc_of_forall_eventually_norm_le
    (((aestronglyMeasurable_indicator_iff hV).2 hf).mono_measure Measure.restrict_le_self)
    fun z hz ↦ ?_
  obtain ⟨M, hM⟩ := hb z hz
  refine ⟨max M 0, (eventually_nhdsWithin_iff.1 hM).mono fun w hw ↦ ?_⟩
  by_cases hwV : w ∈ V
  · rw [Set.indicator_of_mem hwV]
    exact (hw (hVU hwV) hwV).trans (le_max_left _ _)
  · simp [Set.indicator_of_notMem hwV]

end Measurable

/-- A locally `Lᵖ` function on a locally closed set is locally integrable when `1 ≤ p`.
This supplies the local integrability hypothesis used by the weak-derivative API. -/
theorem MemLpLoc.locallyIntegrableOn [LocallyCompactSpace X] [IsFiniteMeasureOnCompacts μ]
    (hf : MemLpLoc p U f μ) (hp : 1 ≤ p) (hU : IsLocallyClosed U) :
    LocallyIntegrableOn f U μ :=
  (locallyIntegrableOn_iff hU).2 fun K hK hc =>
    memLp_one_iff_integrable.1 ((hf.mono_exponent hp) K hK hc)

/-- On a locally closed set, local `L¹` membership is exactly local integrability. -/
theorem memLpLoc_one_iff_locallyIntegrableOn [LocallyCompactSpace X]
    [IsFiniteMeasureOnCompacts μ] (hU : IsLocallyClosed U) :
    MemLpLoc 1 U f μ ↔ LocallyIntegrableOn f U μ :=
  ⟨fun hf => hf.locallyIntegrableOn le_rfl hU,
    fun hf _K hK hc => memLp_one_iff_integrable.2 (hf.integrableOn_compact_subset hK hc)⟩

variable [NormedSpace ℝ F] [NormedSpace ℝ G]

/-- Real scalar multiplication preserves local `Lᵖ` membership. -/
theorem MemLpLoc.const_smul (hf : MemLpLoc p U f μ) (c : ℝ) : MemLpLoc p U (c • f) μ :=
  fun K hK hc => (hf K hK hc).const_smul c

/-- A continuous linear map on the codomain preserves local `Lᵖ` membership. -/
theorem MemLpLoc.clm_comp (hf : MemLpLoc p U f μ) (A : F →L[ℝ] G) :
    MemLpLoc p U (fun z => A (f z)) μ :=
  fun K hK hc => A.comp_memLp' (hf K hK hc)

/-- A continuous linear change of codomain preserves and reflects local `Lᵖ` membership. -/
@[simp]
theorem _root_.ContinuousLinearEquiv.comp_memLpLoc_iff (e : F ≃L[ℝ] G) :
    MemLpLoc p U (fun z => e (f z)) μ ↔ MemLpLoc p U f μ := by
  constructor
  · intro h
    simpa only [ContinuousLinearEquiv.coe_coe, e.symm_apply_apply] using
      h.clm_comp e.symm.toContinuousLinearMap
  · exact fun h => h.clm_comp e.toContinuousLinearMap

/-- Pairing two locally `Lᵖ` fields of continuous linear maps into their product map preserves
local `Lᵖ` membership. -/
theorem MemLpLoc.clm_prod {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : X → E →L[ℝ] F} {B : X → E →L[ℝ] G} (hA : MemLpLoc p U A μ) (hB : MemLpLoc p U B μ) :
    MemLpLoc p U (fun z => (A z).prod (B z)) μ := by
  convert (hA.clm_comp (ContinuousLinearMap.compL ℝ E F (F × G)
    (ContinuousLinearMap.inl ℝ F G))).add
      (hB.clm_comp (ContinuousLinearMap.compL ℝ E G (F × G) (ContinuousLinearMap.inr ℝ F G)))
    using 1
  funext z
  ext v <;> simp

/-- **Hölder's inequality on compact subsets**, for a Hölder triple `1/r = 1/p + 1/q`: a locally
`Lᵖ` field of continuous linear maps applied to a locally `L^q` field is locally `Lʳ`. With `p = ∞`
this covers locally bounded coefficient fields. -/
theorem MemLpLoc.clm_apply {A : X → F →L[ℝ] G} {w : X → F} {r : ℝ≥0∞}
    [ENNReal.HolderTriple p q r] (hA : MemLpLoc p U A μ) (hw : MemLpLoc q U w μ) :
    MemLpLoc r U (fun z => A z (w z)) μ :=
  fun K hK hc => (ContinuousLinearMap.id ℝ (F →L[ℝ] G)).memLp_of_bilin r (hA K hK hc) (hw K hK hc)

/-- **Hölder's inequality on compact subsets** with exponent one: a locally `Lᵖ` field of
continuous linear maps applied to a locally `L^q` field is locally `L¹` when `1/p + 1/q ≤ 1`. -/
theorem MemLpLoc.memLpLoc_one_clm_apply [IsFiniteMeasureOnCompacts μ] {A : X → F →L[ℝ] G}
    {w : X → F} (hA : MemLpLoc p U A μ) (hw : MemLpLoc q U w μ) (hpq : p⁻¹ + q⁻¹ ≤ 1) :
    MemLpLoc 1 U (fun z => A z (w z)) μ := by
  have : ENNReal.HolderTriple p q (p⁻¹ + q⁻¹)⁻¹ := ⟨(inv_inv _).symm⟩
  exact (hA.clm_apply hw).mono_exponent (ENNReal.one_le_inv.2 hpq)

/-- **Hölder's inequality on compact subsets**: a locally `Lᵖ` field of continuous linear maps
applied to a locally `L^q` field is locally integrable on a locally closed set when
`1/p + 1/q ≤ 1`. -/
theorem MemLpLoc.locallyIntegrableOn_clm_apply [LocallyCompactSpace X]
    [IsFiniteMeasureOnCompacts μ] {A : X → F →L[ℝ] G} {w : X → F}
    (hA : MemLpLoc p U A μ) (hw : MemLpLoc q U w μ) (hpq : p⁻¹ + q⁻¹ ≤ 1)
    (hU : IsLocallyClosed U) : LocallyIntegrableOn (fun z => A z (w z)) U μ :=
  (hA.memLpLoc_one_clm_apply hw hpq).locallyIntegrableOn le_rfl hU

section Continuous

variable [OpensMeasurableSpace X] [T2Space X]

/-- Composing a locally `Lᵖ` operator family on the left with one continuous on `U` preserves
local `Lᵖ` membership, since the continuous factor is bounded on every compact subset of `U`. -/
theorem MemLpLoc.continuousOn_clm_comp {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : X → G →L[ℝ] H} {B : X → F →L[ℝ] G} (hB : MemLpLoc p U B μ) (hA : ContinuousOn A U) :
    MemLpLoc p U (fun z => A z ∘L B z) μ :=
  memLpLoc_iff.2 fun K hKU hK => (memLpLoc_iff.1 hB K hKU hK).clm_comp_of_continuousOn
    (hA.mono hKU) hK hK.measurableSet subset_rfl

/-- Composing a locally `Lᵖ` operator family on the right with one continuous on `U` preserves
local `Lᵖ` membership, since the continuous factor is bounded on every compact subset of `U`. -/
theorem MemLpLoc.clm_comp_continuousOn {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {B : X → G →L[ℝ] H} {E : X → F →L[ℝ] G} (hB : MemLpLoc p U B μ) (hE : ContinuousOn E U) :
    MemLpLoc p U (fun z => B z ∘L E z) μ :=
  memLpLoc_iff.2 fun K hKU hK => (ContinuousLinearMap.compL ℝ F G H).memLp_of_bilin p
    (memLpLoc_iff.1 hB K hKU hK)
    ((hE.mono hKU).memLp_top_restrict_of_subset_isCompact hK hK.measurableSet subset_rfl)

/-- A continuous compactly supported factor whose support meets the closed set `T` inside `S`
makes a function in `MemLpLoc 1 S` integrable on `T`, even though `T` may be unbounded or leave
`S`. -/
theorem MemLpLoc.integrableOn_smul {S T : Set X} {h : X → F} (hh : MemLpLoc 1 S h μ)
    {χ : X → ℝ} (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hT : IsClosed T)
    (hχS : tsupport χ ∩ T ⊆ S) : IntegrableOn (fun z => χ z • h z) T μ := by
  have hK : IsCompact (tsupport χ ∩ T) := hχc.isCompact.inter_right hT
  have hhK : IntegrableOn h (tsupport χ ∩ T) μ :=
    memLp_one_iff_integrable.1 (hh _ hχS hK)
  refine (hhK.continuousOn_smul hχ.continuousOn hK).of_forall_sdiff_eq_zero hT.measurableSet
    fun z hz => ?_
  simp [image_eq_zero_of_notMem_tsupport fun h => hz.2 ⟨h, hz.1⟩]

variable [IsFiniteMeasureOnCompacts μ]

/-- A factor continuous on `U` preserves local `Lᵖ` membership on `U`, since it is bounded on
every compact subset of `U`. -/
theorem MemLpLoc.continuousOn_smul {χ : X → ℝ} (hf : MemLpLoc p U f μ)
    (hχ : ContinuousOn χ U) : MemLpLoc p U (fun z => χ z • f z) μ :=
  memLpLoc_iff.2 fun K hK hc =>
    (memLpLoc_iff.1 (hχ.memLpLoc (p := ⊤) (μ := μ)) K hK hc).smul (memLpLoc_iff.1 hf K hK hc)

/-- A locally `Lᵖ` field of continuous linear maps applied to a map continuous on `U` is locally
`Lᵖ` on `U`, since the map is bounded on every compact subset of `U`. -/
theorem MemLpLoc.clm_apply_continuousOn {A : X → F →L[ℝ] G} (hA : MemLpLoc p U A μ)
    (hf : ContinuousOn f U) : MemLpLoc p U (fun z => A z (f z)) μ :=
  memLpLoc_iff.2 fun K hK hc =>
    (memLpLoc_iff.1 hA K hK hc).of_bilin (fun B x => B x) 1
      (memLpLoc_iff.1 (hf.memLpLoc (p := ⊤) (μ := μ)) K hK hc)
      isBoundedBilinearMap_apply.continuous
      (.of_forall fun z => by simpa using (A z).le_opNNNorm (f z))

/-- A continuous factor supported in `U` extends a local `Lᵖ` function on `U` by zero to a local
`Lᵖ` function on the whole space: on a compact set `K` the product only sees
`K ∩ tsupport χ`, a compact subset of `U`. -/
theorem MemLpLoc.continuous_smul_of_tsupport_subset {χ : X → ℝ} (hf : MemLpLoc p U f μ)
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
theorem MemLpLoc.memLp_smul_of_hasCompactSupport {χ : X → ℝ} (hf : MemLpLoc p U f μ)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hsupp : tsupport χ ⊆ U) :
    MemLp (fun z => χ z • f z) p μ := by
  have hcl : IsClosed (tsupport χ) := isClosed_tsupport χ
  have heq : (fun z => χ z • f z) = (tsupport χ).indicator (fun z => χ z • f z) := by
    refine (Set.indicator_eq_self.2 ?_).symm
    exact (Function.support_smul_subset_left χ f).trans (subset_tsupport χ)
  rw [heq, memLp_indicator_iff_restrict hcl.measurableSet.nullMeasurableSet]
  exact memLpLoc_iff.1 (hf.continuousOn_smul hχ.continuousOn) _ hsupp hχc

end Continuous

end Basic

section PreciseRepresentative

open TauCeti.MeasureTheory

variable {X F : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [LocallyCompactSpace X]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {μ : Measure X} [IsUnifLocDoublingMeasure μ] [IsLocallyFiniteMeasure μ]
  {p : ℝ≥0∞} {f : X → F}

/-- A locally `Lᵖ` function on an open set `Ω`, with `1 ≤ p`, agrees almost everywhere on `Ω` with
its precise representative. -/
theorem MemLpLoc.ae_eq_preciseRepresentative {Ω : Opens X} (hp : 1 ≤ p)
    (hu : MemLpLoc p Ω f μ) : f =ᵐ[μ.restrict Ω] preciseRepresentative μ f :=
  ae_eq_restrict_preciseRepresentative Ω.isOpen
    (hu.locallyIntegrableOn hp Ω.isOpen.isLocallyClosed)

end PreciseRepresentative

section Ball

variable {X F : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X]
  [NormedAddCommGroup F] {μ : Measure X} {p : ℝ≥0∞} {f : X → F}

/-- On a proper metric space, local `Lᵖ` membership on a ball `ball c r` is `Lᵖ` membership on
every smaller concentric ball `ball c R`, `R < r`. -/
theorem memLpLoc_ball_iff {c : X} {r : ℝ} :
    MemLpLoc p (Metric.ball c r) f μ ↔ ∀ R < r, MemLp f p (μ.restrict (Metric.ball c R)) := by
  refine ⟨fun hf R hR => hf.memLp_restrict_of_isCompact_closure Metric.isCompact_closure_ball
    (Metric.closure_ball_subset_closedBall.trans (Metric.closedBall_subset_ball hR)),
    fun hf K hK hKc => ?_⟩
  obtain ⟨R, hR, hKR⟩ := exists_lt_subset_ball hKc.isClosed hK
  exact (hf R hR).mono_measure (Measure.restrict_mono hKR le_rfl)

end Ball

section Haar

variable {G F : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup F] {p : ℝ≥0∞} {U : Set G} {f : G → F}

/-- **Independence of the Haar measure.** Two additive Haar measures on a locally compact group
are proportional on every compact set, so they define the same local `Lᵖ` classes. -/
theorem memLpLoc_iff_of_isAddHaarMeasure (μ ν : Measure G) [μ.IsAddHaarMeasure]
    [ν.IsAddHaarMeasure] : MemLpLoc p U f μ ↔ MemLpLoc p U f ν := by
  have key : ∀ (μ ν : Measure G) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure],
      MemLpLoc p U f μ → MemLpLoc p U f ν := fun μ ν _ _ h K hKU hK =>
    (h K hKU hK).of_measure_le_smul ENNReal.coe_ne_top <| le_of_eq <| Measure.ext fun s hs => by
      rw [smul_apply, Measure.restrict_apply hs, Measure.restrict_apply hs]
      exact Measure.measure_isAddInvariant_eq_smul_of_isCompact_closure ν μ
        (hK.closure_of_subset Set.inter_subset_right)
  exact ⟨key μ ν, key ν μ⟩

end Haar

end TauCeti

section Transport

open TauCeti

variable {X Y F : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [NormedAddCommGroup F]
  {μ : Measure X} {p : ℝ≥0∞} {U : Set Y} {f : Y → F}

/-- **Transport by a homeomorphism.** Precomposing with a homeomorphism `e` carries the local
`Lᵖ` class of the image measure `μ.map e` on `U` to the local `Lᵖ` class of `μ` on `e ⁻¹' U`:
compact sets correspond under `e`, and `Lᵖ` membership transfers along the measurable
equivalence `e`. -/
theorem Homeomorph.memLpLoc_comp_iff (e : X ≃ₜ Y) :
    MemLpLoc p (e ⁻¹' U) (f ∘ e) μ ↔ MemLpLoc p U f (μ.map e) := by
  have hmem (K : Set Y) :
      MemLp f p ((μ.map e).restrict K) ↔ MemLp (f ∘ e) p (μ.restrict (e ⁻¹' K)) := by
    rw [← e.toMeasurableEquiv_coe, MeasurableEquiv.restrict_map,
      MeasurableEquiv.memLp_map_measure_iff]
  constructor
  · intro h K hKU hK
    exact (hmem K).2 (h _ (Set.preimage_mono hKU) (e.isCompact_preimage.2 hK))
  · intro h K hKU hK
    have hKe : e ⁻¹' (e '' K) = K := e.preimage_image K
    simpa only [hKe] using (hmem (e '' K)).1
      (h _ (Set.image_subset_iff.2 hKU) (hK.image e.continuous))

variable {E E₁ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [MeasurableSpace E₁] [BorelSpace E₁] {U : Set E₁} {f : E₁ → F}

/-- **Linear changes of variables.** A continuous linear equivalence `e : E ≃L[ℝ] E₁` onto a
finite-dimensional real normed space carries the local `Lᵖ` class of `U` in `E₁` to that of
`e ⁻¹' U` in `E`, for any additive Haar measures on the two spaces. -/
theorem ContinuousLinearEquiv.memLpLoc_comp_right_iff (e : E ≃L[ℝ] E₁) (μ : Measure E)
    [μ.IsAddHaarMeasure] (ν : Measure E₁) [ν.IsAddHaarMeasure] :
    MemLpLoc p (e ⁻¹' U) (f ∘ e) μ ↔ MemLpLoc p U f ν := by
  rw [← memLpLoc_iff_of_isAddHaarMeasure (μ.map e) ν]
  exact e.toHomeomorph.memLpLoc_comp_iff

end Transport
