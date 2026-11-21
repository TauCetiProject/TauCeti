/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Prod
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import TauCeti.MeasureTheory.Function.LocallyIntegrable
public import TauCeti.Topology.Sets.Opens
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas
import TauCeti.MeasureTheory.Function.LpSeminorm.ContinuousOn

/-!
# Local vector-valued `Lᵖ` classes

`TauCeti.MemLpLoc p U f` requires `Lᵖ` membership on every compact subset of `U` for a function
`f : E → F` on a topological measure space `E`. On subsets reaching part of their boundary, the
compact subsets include the boundary points in `U`.

These predicates concern actual functions; almost-everywhere changes do not affect membership. They
impose no global integrability condition on the possibly unbounded domain. Global `Lᵖ` membership on
a set implies local membership there (`MeasureTheory.MemLp.memLpLoc`). On every σ-compact set (in
particular every open subset of a locally compact second-countable space), local `Lᵖ` membership is
equivalent to a.e. strong measurability together with local `Lᵖ` membership of the pointwise norm
(`TauCeti.memLpLoc_iff_aestronglyMeasurable_and_norm`).

This file supplies restriction to arbitrary subsets (also combined with a change of the function
off the subset), linearity, continuous-linear composition, pairing of fields of continuous linear
maps into product maps, multiplication of local `Lᵖ` functions by continuous factors (with
extension by zero for factors supported in the domain, and global `Lᵖ` membership for compactly
supported ones), Hölder's inequality for local `Lᵖ` fields of continuous linear maps
(`TauCeti.MemLpLoc.clm_apply`), composition of local `Lᵖ` operator families with continuous ones,
decreasing the integrability exponent, and testing on open sets or concentric balls
(`TauCeti.memLpLoc_ball_iff`). On locally closed subsets of a locally compact space, local `L¹`
membership is identified with local integrability. The indicator of an open half-space
`{x | 0 < ℓ x}` is locally `Lᵖ` on every set (`TauCeti.memLpLoc_indicator_pos`).

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (local `Lᵖ` and Sobolev spaces).
* W. Arendt and M. Kreuter, *Mapping theorems for Sobolev spaces of vector-valued functions*,
  Studia Math. 240 (2018), §2.
-/

public noncomputable section

open MeasureTheory TopologicalSpace

namespace TauCeti

section MemLpLoc

variable {E F G : Type*} [TopologicalSpace E] [MeasureSpace E]
  [NormedAddCommGroup F] [NormedAddCommGroup G]
  {p q : ENNReal} {U V : Set E} {f g : E → F}

/-- A function is locally `Lᵖ` on `U` when it belongs to `Lᵖ` on every compact subset of `U`.
On a set reaching part of its boundary, those compact subsets include the boundary points in `U`. -/
def MemLpLoc (p : ENNReal) (U : Set E) (f : E → F) : Prop :=
  ∀ K : Set E, K ⊆ U → IsCompact K → MemLp f p (volume.restrict K)

/-- Local `Lᵖ` membership is characterized by `Lᵖ` membership on every compact subset. -/
theorem memLpLoc_iff : MemLpLoc p U f ↔
    ∀ K : Set E, K ⊆ U → IsCompact K → MemLp f p (volume.restrict K) := Iff.rfl

/-- Local `Lᵖ` membership restricts to any smaller set. -/
theorem MemLpLoc.mono_set (hf : MemLpLoc p U f) (hVU : V ⊆ U) : MemLpLoc p V f :=
  fun K hK hc => hf K (hK.trans hVU) hc

/-- Local `Lᵖ` membership on `U` gives `Lᵖ` membership on every set whose closure is compact and
contained in `U`. -/
theorem MemLpLoc.memLp_of_closure_subset (hf : MemLpLoc p U f) (hV : IsCompact (closure V))
    (hVU : closure V ⊆ U) : MemLp f p (volume.restrict V) :=
  (hf _ hVU hV).mono_measure (Measure.restrict_mono subset_closure le_rfl)

/-- A locally `Lᵖ` function on `U` that vanishes off a compact set `T ⊆ U` is `Lᵖ` on the whole
space. -/
theorem MemLpLoc.memLp_of_forall_notMem_eq_zero [T2Space E] [OpensMeasurableSpace E]
    (hf : MemLpLoc p U f) {T : Set E}
    (hT : IsCompact T) (hTU : T ⊆ U) (h0 : ∀ z ∉ T, f z = 0) : MemLp f p volume := by
  have : T.indicator f = f :=
    Set.indicator_eq_self.2 fun z hz => by_contra fun h' => hz (h0 z h')
  rw [← this, memLp_indicator_iff_restrict hT.measurableSet.nullMeasurableSet]
  exact hf T hTU hT

/-- A function that is `Lᵖ` on `U` is locally `Lᵖ` there. -/
theorem _root_.MeasureTheory.MemLp.memLpLoc (hf : MemLp f p (volume.restrict U)) :
    MemLpLoc p U f :=
  fun _ hK _ => hf.mono_measure (Measure.restrict_mono hK le_rfl)

/-- Almost-everywhere equality on `U` preserves local `Lᵖ` membership. -/
theorem MemLpLoc.congr_ae (hf : MemLpLoc p U f)
    (hfg : f =ᵐ[volume.restrict U] g) : MemLpLoc p U g := by
  intro K hK hc
  exact (hf K hK hc).ae_eq (ae_mono (Measure.restrict_mono_set volume hK) hfg)

/-- Restricting to a subset preserves local `Lᵖ` membership of any function agreeing with the
original one on that subset. -/
theorem MemLpLoc.congr_mono [T2Space E] [OpensMeasurableSpace E] (hf : MemLpLoc p U f)
    (hgf : Set.EqOn g f V) (hVU : V ⊆ U) :
    MemLpLoc p V g := fun K hK hc => (hf K (hK.trans hVU) hc).ae_eq <| by
  filter_upwards [ae_restrict_mem hc.measurableSet] with z hz using (hgf (hK hz)).symm

/-- The zero function belongs to every local `Lᵖ` class. -/
@[simp]
theorem memLpLoc_zero : MemLpLoc p U (0 : E → F) := fun _ _ _ => MemLp.zero

/-- Local `Lᵖ` membership is closed under addition. -/
theorem MemLpLoc.add (hf : MemLpLoc p U f) (hg : MemLpLoc p U g) :
    MemLpLoc p U (f + g) := fun K hK hc => (hf K hK hc).add (hg K hK hc)

/-- Local `Lᵖ` membership is closed under negation. -/
theorem MemLpLoc.neg (hf : MemLpLoc p U f) : MemLpLoc p U (-f) :=
  fun K hK hc => (hf K hK hc).neg

/-- Local `Lᵖ` membership is closed under subtraction. -/
theorem MemLpLoc.sub (hf : MemLpLoc p U f) (hg : MemLpLoc p U g) :
    MemLpLoc p U (f - g) := fun K hK hc => (hf K hK hc).sub (hg K hK hc)

/-- Local `Lᵖ` membership passes to the pointwise norm. -/
theorem MemLpLoc.norm (hf : MemLpLoc p U f) : MemLpLoc p U (fun x => ‖f x‖) :=
  fun K hK hc => (hf K hK hc).norm

/-- A locally `Lᵖ` function on a σ-compact set is a.e. strongly measurable there, for every
exponent `p`. -/
theorem MemLpLoc.aestronglyMeasurable (hf : MemLpLoc p U f) (hU : IsSigmaCompact U) :
    AEStronglyMeasurable f (volume.restrict U) := by
  obtain ⟨K, hKc, rfl⟩ := hU
  exact aestronglyMeasurable_iUnion_iff.2 fun n =>
    (hf (K n) (Set.subset_iUnion K n) (hKc n)).aestronglyMeasurable

/-- A locally `Lᵖ` function on an open subset of a locally compact second-countable space is a.e.
strongly measurable there, for every exponent `p`. -/
theorem MemLpLoc.aestronglyMeasurable_of_isOpen [LocallyCompactSpace E] [SecondCountableTopology E]
    {Ω : Opens E} (hf : MemLpLoc p Ω f) : AEStronglyMeasurable f (volume.restrict Ω) := by
  have : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  exact hf.aestronglyMeasurable (isSigmaCompact_iff_sigmaCompactSpace.2 inferInstance)

/-- **Strong measurability and norm integrability characterize local `Lᵖ`.** On a σ-compact set,
a function lies in `MemLpLoc p U` exactly when it is a.e. strongly measurable on `U` and its
pointwise norm lies in `MemLpLoc p U`. In a non-separable Banach codomain, strong measurability
cannot be omitted. -/
theorem memLpLoc_iff_aestronglyMeasurable_and_norm (hU : IsSigmaCompact U) :
    MemLpLoc p U f ↔
      AEStronglyMeasurable f (volume.restrict U) ∧ MemLpLoc p U (fun x => ‖f x‖) := by
  refine ⟨fun hf => ⟨hf.aestronglyMeasurable hU, hf.norm⟩, fun ⟨hm, hn⟩ K hK hc => ?_⟩
  exact (memLp_norm_iff (hm.mono_measure (Measure.restrict_mono hK le_rfl))).1 (hn K hK hc)

/-- On an open subset of a locally compact second-countable space, local `Lᵖ` membership is
equivalent to a.e. strong measurability together with local `Lᵖ` membership of the norm. -/
theorem memLpLoc_iff_aestronglyMeasurable_and_norm_of_isOpen [LocallyCompactSpace E]
    [SecondCountableTopology E] {Ω : Opens E} :
    MemLpLoc p Ω f ↔
      AEStronglyMeasurable f (volume.restrict Ω) ∧ MemLpLoc p Ω (fun x => ‖f x‖) := by
  have : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  exact memLpLoc_iff_aestronglyMeasurable_and_norm
    (isSigmaCompact_iff_sigmaCompactSpace.2 inferInstance)

/-- Compact subsets have finite volume, so decreasing the exponent preserves local membership.
In particular this passes from the infinity endpoint to every finite exponent. -/
theorem MemLpLoc.mono_exponent [IsFiniteMeasureOnCompacts (volume : Measure E)]
    (hf : MemLpLoc p U f) (hqp : q ≤ p) : MemLpLoc q U f := by
  intro K hK hc
  have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hc.measure_lt_top⟩
  exact (hf K hK hc).mono_exponent hqp

/-- A function continuous on `U` is locally `Lᵖ` there, with no global bound required. -/
theorem _root_.ContinuousOn.memLpLoc [T2Space E] [OpensMeasurableSpace E]
    [IsFiniteMeasureOnCompacts (volume : Measure E)] (hf : ContinuousOn f U) :
    MemLpLoc p U f :=
  fun _K hK hc => (hf.mono hK).memLp_restrict_of_subset_isCompact
    hc hc.measurableSet subset_rfl p

open scoped Topology in
/-- An a.e.-strongly measurable function on `U` that is bounded near every point of `U` is locally
`Lᵖ` on `U` for every exponent, including infinity: it is bounded on each compact subset. -/
theorem memLpLoc_of_forall_eventually_norm_le [T2Space E] [OpensMeasurableSpace E]
    [IsFiniteMeasureOnCompacts (volume : Measure E)]
    (hf : AEStronglyMeasurable f (volume.restrict U))
    (hb : ∀ z ∈ U, ∃ M, ∀ᶠ w in 𝓝 z, ‖f w‖ ≤ M) : MemLpLoc p U f := by
  intro K hKU hK
  have : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
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
theorem memLpLoc_const [IsFiniteMeasureOnCompacts (volume : Measure E)] (c : F) :
    MemLpLoc p U (fun _ => c) := fun K _ hc => by
  have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hc.measure_lt_top⟩
  exact memLp_const c

/-- A locally `Lᵖ` function on a locally closed set is locally integrable when `1 ≤ p`.
This supplies the local integrability hypothesis used by the weak-derivative API. -/
theorem MemLpLoc.locallyIntegrableOn [LocallyCompactSpace E]
    [IsFiniteMeasureOnCompacts (volume : Measure E)] (hf : MemLpLoc p U f) (hp : 1 ≤ p)
    (hU : IsLocallyClosed U) : LocallyIntegrableOn f U volume :=
  (locallyIntegrableOn_iff hU).2 fun K hK hc =>
    memLp_one_iff_integrable.1 ((hf.mono_exponent hp) K hK hc)

/-- On a locally closed set, local `L¹` membership is exactly local integrability. -/
theorem memLpLoc_one_iff_locallyIntegrableOn [LocallyCompactSpace E] (hU : IsLocallyClosed U) :
    MemLpLoc 1 U f ↔ LocallyIntegrableOn f U volume :=
  ⟨fun hf => (locallyIntegrableOn_iff hU).2 fun K hK hc =>
      memLp_one_iff_integrable.1 (hf K hK hc),
    fun hf _K hK hc => memLp_one_iff_integrable.2 (hf.integrableOn_compact_subset hK hc)⟩

/-- A finite sum of locally `Lᵖ` functions is locally `Lᵖ`, without a completeness assumption. -/
theorem MemLpLoc.sum {ι : Type*} (s : Finset ι) {f : ι → E → F}
    (hf : ∀ i ∈ s, MemLpLoc p U (f i)) : MemLpLoc p U (fun z => ∑ i ∈ s, f i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty, Pi.zero_def] using (memLpLoc_zero (p := p) (U := U))
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi, Pi.add_def] using
      (hf i (Finset.mem_insert_self i s)).add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- On an open set `Ω`, a function that agrees almost everywhere with an `Lᵖ` function on every
open `W` whose closure is compact and contained in `Ω` is locally `Lᵖ` on `Ω`. -/
theorem memLpLoc_of_forall_opens [LocallyCompactSpace E] [RegularSpace E] {Ω : Opens E}
    (h : ∀ W : Opens E, IsCompact (closure (W : Set E)) → closure (W : Set E) ⊆ Ω →
      ∃ g : E → F, MemLp g p (volume.restrict (W : Set E)) ∧ g =ᵐ[volume.restrict W] f) :
    MemLpLoc p Ω f := by
  refine fun K hKΩ hK => ?_
  obtain ⟨W, hWo, hKW, hWΩ, hWc⟩ := exists_open_between_and_isCompact_closure hK Ω.isOpen hKΩ
  obtain ⟨g, hg, hgf⟩ := h ⟨W, hWo⟩ hWc hWΩ
  exact (hg.ae_eq hgf).mono_measure (Measure.restrict_mono hKW le_rfl)

/-- A function that is `Lᵖ` on a set `W` is locally `Lᵖ` on every set `U` contained in `W` up to a
null set, including on compact subsets of `U` that leave `W`. -/
theorem _root_.MeasureTheory.MemLp.memLpLoc_of_ae_le {W : Set E}
    (hf : MemLp f p (volume.restrict W)) (hUW : U ≤ᵐ[volume] W) : MemLpLoc p U f :=
  memLpLoc_iff.2 fun _ hK _ => hf.mono_measure
    (Measure.restrict_mono_ae ((Filter.EventuallySubset.of_subset hK).trans hUW))

variable [NormedSpace ℝ F] [NormedSpace ℝ G]

/-- Real scalar multiplication preserves local `Lᵖ` membership. -/
theorem MemLpLoc.const_smul (hf : MemLpLoc p U f) (c : ℝ) : MemLpLoc p U (c • f) :=
  fun K hK hc => (hf K hK hc).const_smul c

/-- A continuous linear map on the codomain preserves local `Lᵖ` membership. -/
theorem MemLpLoc.clm_comp (hf : MemLpLoc p U f) (A : F →L[ℝ] G) :
    MemLpLoc p U (fun z => A (f z)) :=
  fun K hK hc => A.comp_memLp' (hf K hK hc)

/-- Multiplying a scalar locally `Lᵖ` function by a fixed vector preserves local `Lᵖ`
membership. -/
theorem MemLpLoc.smul_const {a : E → ℝ} (ha : MemLpLoc p U a) (v : F) :
    MemLpLoc p U (fun x => a x • v) := by
  simpa using ha.clm_comp ((ContinuousLinearMap.id ℝ ℝ).smulRight v)

/-- Pairing two locally `Lᵖ` fields of continuous linear maps into their product map preserves
local `Lᵖ` membership. -/
theorem MemLpLoc.clm_prod {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {A : E → E' →L[ℝ] F} {B : E → E' →L[ℝ] G} (hA : MemLpLoc p U A)
    (hB : MemLpLoc p U B) :
    MemLpLoc p U (fun z => (A z).prod (B z)) := by
  convert (hA.clm_comp (ContinuousLinearMap.compL ℝ E' F (F × G)
    (ContinuousLinearMap.inl ℝ F G))).add
      (hB.clm_comp (ContinuousLinearMap.compL ℝ E' G (F × G) (ContinuousLinearMap.inr ℝ F G)))
    using 1
  funext z
  ext v <;> simp

/-- Composing a locally `Lᵖ` operator family on the left with one continuous on `U` preserves
local `Lᵖ` membership, since the continuous factor is bounded on every compact subset of `U`. -/
theorem MemLpLoc.continuousOn_clm_comp [T2Space E] [OpensMeasurableSpace E]
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : E → G →L[ℝ] H} {B : E → F →L[ℝ] G} (hB : MemLpLoc p U B)
    (hA : ContinuousOn A U) :
    MemLpLoc p U (fun z => A z ∘L B z) :=
  memLpLoc_iff.2 fun K hKU hK => (memLpLoc_iff.1 hB K hKU hK).clm_comp_of_continuousOn
    (hA.mono hKU) hK hK.measurableSet subset_rfl

/-- Composing a locally `Lᵖ` operator family on the right with one continuous on `U` preserves
local `Lᵖ` membership, since the continuous factor is bounded on every compact subset of `U`. -/
theorem MemLpLoc.clm_comp_continuousOn [T2Space E] [OpensMeasurableSpace E]
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {B : E → G →L[ℝ] H} {A : E → F →L[ℝ] G} (hB : MemLpLoc p U B)
    (hA : ContinuousOn A U) :
    MemLpLoc p U (fun z => B z ∘L A z) := by
  exact memLpLoc_iff.2 fun K hKU hK => (ContinuousLinearMap.compL ℝ F G H).memLp_of_bilin p
    (memLpLoc_iff.1 hB K hKU hK)
    ((hA.mono hKU).memLp_top_restrict_of_subset_isCompact hK hK.measurableSet subset_rfl)

/-- **Hölder's inequality on compact subsets**, for a Hölder triple `1/r = 1/p + 1/q`: a locally
`Lᵖ` field of continuous linear maps applied to a locally `L^q` field is locally `Lʳ`. With `p = ∞`
this covers locally bounded coefficient fields. -/
theorem MemLpLoc.clm_apply {A : E → F →L[ℝ] G} {w : E → F} {r : ENNReal}
    [ENNReal.HolderTriple p q r] (hA : MemLpLoc p U A) (hw : MemLpLoc q U w) :
    MemLpLoc r U (fun z => A z (w z)) := by
  exact fun K hK hc =>
    (ContinuousLinearMap.id ℝ (F →L[ℝ] G)).memLp_of_bilin r (hA K hK hc) (hw K hK hc)

/-- **Hölder's inequality on compact subsets** with exponent one: a locally `Lᵖ` field of
continuous linear maps applied to a locally `L^q` field is locally `L¹` when `1/p + 1/q ≤ 1`. -/
theorem MemLpLoc.memLpLoc_one_clm_apply [IsFiniteMeasureOnCompacts (volume : Measure E)]
    {A : E → F →L[ℝ] G} {w : E → F} (hA : MemLpLoc p U A)
    (hw : MemLpLoc q U w) (hpq : p⁻¹ + q⁻¹ ≤ 1) : MemLpLoc 1 U (fun z => A z (w z)) := by
  have : ENNReal.HolderTriple p q (p⁻¹ + q⁻¹)⁻¹ := ⟨(inv_inv _).symm⟩
  exact (hA.clm_apply hw).mono_exponent (ENNReal.one_le_inv.2 hpq)

/-- **Hölder's inequality on compact subsets**: a locally `Lᵖ` field of continuous linear maps
applied to a locally `L^q` field is locally integrable on a locally closed set when
`1/p + 1/q ≤ 1`. -/
theorem MemLpLoc.locallyIntegrableOn_clm_apply [LocallyCompactSpace E]
    [IsFiniteMeasureOnCompacts (volume : Measure E)] {A : E → F →L[ℝ] G} {w : E → F}
    (hA : MemLpLoc p U A) (hw : MemLpLoc q U w) (hpq : p⁻¹ + q⁻¹ ≤ 1)
    (hU : IsLocallyClosed U) : LocallyIntegrableOn (fun z => A z (w z)) U volume :=
  (hA.memLpLoc_one_clm_apply hw hpq).locallyIntegrableOn le_rfl hU

/-- A continuous linear change of codomain preserves and reflects local `Lᵖ` membership. -/
@[simp]
theorem _root_.ContinuousLinearEquiv.comp_memLpLoc_iff (e : F ≃L[ℝ] G) :
    MemLpLoc p U (fun z => e (f z)) ↔ MemLpLoc p U f := by
  constructor
  · intro h
    simpa only [ContinuousLinearEquiv.coe_coe, e.symm_apply_apply] using
      h.clm_comp e.symm.toContinuousLinearMap
  · exact fun h => h.clm_comp e.toContinuousLinearMap

/-- A factor continuous on `U` preserves local `Lᵖ` membership on `U`, since it is bounded on
every compact subset of `U`. -/
theorem MemLpLoc.continuousOn_smul [T2Space E] [OpensMeasurableSpace E]
    {χ : E → ℝ} (hf : MemLpLoc p U f) (hχ : ContinuousOn χ U) :
    MemLpLoc p U (fun z => χ z • f z) :=
  memLpLoc_iff.2 fun K hK hc =>
    ((hχ.mono hK).memLp_top_restrict_of_subset_isCompact hc hc.measurableSet subset_rfl).smul
      (memLpLoc_iff.1 hf K hK hc)

/-- A locally `Lᵖ` field of continuous linear maps applied to a map continuous on `U` is locally
`Lᵖ` on `U`, since the map is bounded on every compact subset of `U`. -/
theorem MemLpLoc.clm_apply_continuousOn [T2Space E] [OpensMeasurableSpace E]
    {A : E → F →L[ℝ] G} (hA : MemLpLoc p U A) (hf : ContinuousOn f U) :
    MemLpLoc p U (fun z => A z (f z)) :=
  memLpLoc_iff.2 fun K hK hc =>
    (memLpLoc_iff.1 hA K hK hc).of_bilin (fun B x => B x) 1
      ((hf.mono hK).memLp_top_restrict_of_subset_isCompact hc hc.measurableSet subset_rfl)
      isBoundedBilinearMap_apply.continuous
      (.of_forall fun z => by simpa using (A z).le_opNNNorm (f z))

/-- A continuous factor supported in `U` extends a local `Lᵖ` function on `U` by zero to a local
`Lᵖ` function on the whole space: on a compact set `K` the product only sees
`K ∩ tsupport χ`, a compact subset of `U`. -/
theorem MemLpLoc.continuous_smul_of_tsupport_subset [T2Space E] [OpensMeasurableSpace E]
    {χ : E → ℝ} (hf : MemLpLoc p U f) (hχ : Continuous χ) (hsupp : tsupport χ ⊆ U) :
    MemLpLoc p Set.univ (fun z => χ z • f z) := by
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
theorem MemLpLoc.memLp_smul_of_hasCompactSupport [T2Space E] [OpensMeasurableSpace E]
    {χ : E → ℝ} (hf : MemLpLoc p U f) (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hsupp : tsupport χ ⊆ U) :
    MemLp (fun z => χ z • f z) p volume := by
  have hcl : IsClosed (tsupport χ) := isClosed_tsupport χ
  have heq : (fun z => χ z • f z) = (tsupport χ).indicator (fun z => χ z • f z) := by
    refine (Set.indicator_eq_self.2 ?_).symm
    exact (Function.support_smul_subset_left χ f).trans (subset_tsupport χ)
  rw [heq, memLp_indicator_iff_restrict hcl.measurableSet.nullMeasurableSet]
  exact memLpLoc_iff.1 (hf.continuousOn_smul hχ.continuousOn) _ hsupp hχc

/-- A continuous compactly supported factor whose support meets the closed set `T` inside `S`
makes a function in `MemLpLoc 1 S` integrable on `T`, even though `T` may be unbounded or leave
`S`. -/
theorem MemLpLoc.integrableOn_smul [T2Space E] [OpensMeasurableSpace E] {S T : Set E}
    {h : E → F} (hh : MemLpLoc 1 S h) {φ : E → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (hT : IsClosed T) (hφS : tsupport φ ∩ T ⊆ S) :
    IntegrableOn (fun z => φ z • h z) T := by
  have hK : IsCompact (tsupport φ ∩ T) := hφc.isCompact.inter_right hT
  have hhK : IntegrableOn h (tsupport φ ∩ T) :=
    memLp_one_iff_integrable.1 (hh _ hφS hK)
  refine (hhK.continuousOn_smul hφ.continuousOn hK).of_forall_sdiff_eq_zero hT.measurableSet
    fun z hz => ?_
  simp [image_eq_zero_of_notMem_tsupport fun h => hz.2 ⟨h, hz.1⟩]

end MemLpLoc

section HalfSpace

/-- The indicator of any open half-space `{x | 0 < ℓ x}` is locally `Lᵖ` on every set, for every
exponent. -/
theorem memLpLoc_indicator_pos {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [OpensMeasurableSpace E] [IsFiniteMeasureOnCompacts (volume : Measure E)]
    {p : ENNReal} {U : Set E} (ℓ : E →L[ℝ] ℝ) :
    MemLpLoc p U ({x : E | 0 < ℓ x}.indicator fun _ => (1 : ℝ)) := by
  refine memLpLoc_iff.2 fun K _ hK => ?_
  have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
  exact memLp_indicator_const p
    (measurableSet_lt measurable_const ℓ.continuous.measurable).nullMeasurableSet 1
    (Or.inr (measure_ne_top _ _))

end HalfSpace

section MemLpLocBall

variable {E F : Type*} [MetricSpace E] [ProperSpace E] [MeasureSpace E]
  [NormedAddCommGroup F] {p : ENNReal} {f : E → F}

/-- Local `Lᵖ` membership on a ball `ball c r` in a proper metric space is `Lᵖ` membership on
every smaller concentric ball `ball c R`, `R < r`. -/
theorem memLpLoc_ball_iff {c : E} {r : ℝ} :
    MemLpLoc p (Metric.ball c r) f ↔ ∀ R < r, MemLp f p (volume.restrict (Metric.ball c R)) := by
  refine ⟨fun hf R hR => hf.memLp_of_closure_subset Metric.isCompact_closure_ball
    (Metric.closure_ball_subset_closedBall.trans (Metric.closedBall_subset_ball hR)),
    fun hf K hK hKc => ?_⟩
  obtain ⟨R, hR, hKR⟩ := exists_lt_subset_ball hKc.isClosed hK
  exact (hf R hR).mono_measure (Measure.restrict_mono hKR le_rfl)

end MemLpLocBall

end TauCeti
