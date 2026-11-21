/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Prod
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import TauCeti.Analysis.Complex.ReImTopology
public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
public import TauCeti.MeasureTheory.Function.PreciseRepresentative
public import TauCeti.MeasureTheory.Function.LocallyIntegrable
public import TauCeti.Topology.Sets.Opens
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas
import TauCeti.MeasureTheory.Function.LpSeminorm.ContinuousOn
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Local vector-valued Sobolev classes

`TauCeti.MemLpLoc p U f` requires `Lᵖ` membership on every compact subset of `U` for a function
`f : E → F` on a topological measure space `E`.
`TauCeti.MemWkpLoc p U k f` requires iterated weak derivatives through order `k` on
`interior U`, with `Lᵖ` bounds on every compact subset of `U` itself, for a real normed measure
space `E`. On subsets reaching a boundary (such as half-discs in `ℂ`), the `Lᵖ` bounds reach the
boundary while test functions stay in the interior. On open sets this is the usual local Sobolev
class `W^{k,p}_loc(Ω; F)`. Derivatives take values in iterated continuous linear maps rather than
scalar jets.

These predicates concern actual functions; almost-everywhere changes do not affect membership.
They impose no global integrability condition on the possibly unbounded domain. Global `Lᵖ`
membership on a set implies local membership there (`MeasureTheory.MemLp.memLpLoc`). On every
σ-compact set (in particular every open subset of a locally compact second-countable space),
local `Lᵖ` membership is equivalent to a.e. strong measurability together with local `Lᵖ`
membership of the pointwise norm (`TauCeti.memLpLoc_iff_aestronglyMeasurable_and_norm`).

This file supplies restriction to arbitrary subsets (also combined with a change of the function
off the subset), linearity, continuous-linear composition, pairing of fields of continuous linear
maps into product maps, multiplication of local `Lᵖ` functions by continuous factors (with
extension by zero for factors supported in the domain, and global `Lᵖ` membership for compactly
supported ones), Hölder's inequality for local `Lᵖ` fields of continuous linear maps
(`TauCeti.MemLpLoc.clm_apply`), composition of local `Lᵖ` operator families with continuous ones,
pairing, pointwise product maps of operator fields, decreasing the integrability exponent, and
decreasing the derivative order. On an open set, local `Lᵖ` membership is detected on the open
subsets with compact closure inside it, and on a ball in a proper metric space on the smaller
concentric balls (`TauCeti.memLpLoc_ball_iff`).
Differentiability on an open set with a locally `Lᵖ` (in particular continuous) derivative gives
first-order local Sobolev membership (`DifferentiableOn.memWkpLoc_one`), smoothness on an open
neighbourhood gives membership at every order, and smooth or continuous linear maps on the whole
space are in every class on every set.
Conversely, let `U` agree almost everywhere with its interior, as open sets and half-discs do.
If `g` is `Cᵏ` on the interior of `U` and agrees almost everywhere on `U` with
`u ∈ MemWkpLoc p U (k + m)`, then `fderiv ℝ g` is a weak derivative of `u`
(`TauCeti.MemWkpLoc.hasWeakFDerivOn_fderiv_of_contDiffOn`, for `k ≥ 1`) and
`iteratedFDeriv ℝ k g ∈ MemWkpLoc p U m` (`TauCeti.MemWkpLoc.iteratedFDeriv_of_contDiffOn`).
On a relatively open subset `Ω ∩ {0 ≤ im}` of the closed upper half-plane in `ℂ`, the
interior is `Ω ∩ {0 < im}` (`TauCeti.interior_inter_setOf_im_nonneg`), and since the real axis is
null, local
`Lᵖ` membership there is detected on the upper halves `W ∩ {0 < im}`
(`TopologicalSpace.Opens.upperHalf`) of the open `W` with compact closure inside `Ω`
(`TauCeti.memLpLoc_inter_setOf_im_nonneg_iff`). No boundary trace is asserted here;
extension across the real axis is in `TauCeti.Analysis.Sobolev.Local.Reflection`. On locally closed
subsets of a locally compact space, local `L¹` membership is identified with local integrability,
supplying the native weak-derivative hypotheses.
On open domains with a locally finite uniformly locally doubling measure, a locally `Lᵖ` function
with `1 ≤ p` agrees almost everywhere with its precise representative. In finite dimension with a
Borel measure, every weak derivative of a member of `MemWkpLoc p Ω (k + 1)` is in
`MemWkpLoc p Ω k`; at order one, it is locally `Lᵖ`.
`TauCeti.WeakDerivChainLe` compares the `Lᵖ` norms of two maps and, recursively, of every pair of
their weak derivatives through a given order.
In positive order, completeness is inherited from the native weak-derivative predicate; the
definitions admit every real normed codomain without an additional typeclass assumption.
The continuous-linear composition result requires a complete target, as does the native
weak-derivative result it uses.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (local Sobolev spaces and their elementary operations).
* W. Arendt and M. Kreuter, *Mapping theorems for Sobolev spaces of vector-valued functions*,
  Studia Math. 240 (2018), §2 (Bochner-valued first-order Sobolev spaces).
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

/-- Local `Lᵖ` membership on `U` gives `Lᵖ` membership on every set whose closure is compact and
contained in `U`. -/
theorem MemLpLoc.memLp_restrict_of_isCompact_closure (hf : MemLpLoc p U f) {W : Set E}
    (hWc : IsCompact (closure W)) (hWU : closure W ⊆ U) : MemLp f p (volume.restrict W) :=
  (hf _ hWU hWc).mono_measure (Measure.restrict_mono subset_closure le_rfl)

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

/-- **Local `Lᵖ` on a half-disc through upper halves.** A function is locally `Lᵖ` on
`Ω ∩ {0 ≤ im}`, up to the real axis, exactly when it is `Lᵖ` on the upper half `W ∩ {0 < im}` of
every open `W` whose closure is compact and contained in `Ω`. The real axis is null, so the
compact sets reaching it see no more than these upper halves. -/
theorem memLpLoc_inter_setOf_im_nonneg_iff {Ω : Opens ℂ} {f : ℂ → F} :
    MemLpLoc p ((Ω : Set ℂ) ∩ {z : ℂ | 0 ≤ z.im}) f ↔
      ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
        MemLp f p (volume.restrict (W.upperHalf : Set ℂ)) := by
  refine ⟨fun hf W hWc hWΩ => ?_, fun h => memLpLoc_iff.2 fun K hKU hK => ?_⟩
  · have hK : IsCompact (closure (W : Set ℂ) ∩ {z : ℂ | 0 ≤ z.im}) :=
      hWc.inter_right (isClosed_le continuous_const Complex.continuous_im)
    refine (memLpLoc_iff.1 hf _ (Set.inter_subset_inter_left _ hWΩ) hK).mono_measure
      (Measure.restrict_mono ?_ le_rfl)
    intro z hz
    obtain ⟨hzW, hz0⟩ := Opens.mem_upperHalf.1 hz
    exact ⟨subset_closure hzW, hz0.le⟩
  · obtain ⟨W, hWo, hKW, hWΩ, hWc⟩ := exists_open_between_and_isCompact_closure hK Ω.isOpen
      (hKU.trans Set.inter_subset_left)
    refine (h ⟨W, hWo⟩ hWc hWΩ).mono_measure (Measure.restrict_mono_ae ?_)
    filter_upwards [(Complex.setOf_le_im_ae_eq 0).subset] with z hz hzK
    exact Opens.mem_upperHalf.2 ⟨hKW hzK, hz (hKU hzK).2⟩

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
    MemLpLoc p U (fun z => B z ∘L A z) :=
  memLpLoc_iff.2 fun K hKU hK => (ContinuousLinearMap.compL ℝ F G H).memLp_of_bilin p
    (memLpLoc_iff.1 hB K hKU hK)
    ((hA.mono hKU).memLp_top_restrict_of_subset_isCompact hK hK.measurableSet subset_rfl)

/-- **Hölder's inequality on compact subsets**, for a Hölder triple `1/r = 1/p + 1/q`: a locally
`Lᵖ` field of continuous linear maps applied to a locally `L^q` field is locally `Lʳ`. With `p = ∞`
this covers locally bounded coefficient fields. -/
theorem MemLpLoc.clm_apply {A : E → F →L[ℝ] G} {w : E → F} {r : ENNReal}
    [ENNReal.HolderTriple p q r] (hA : MemLpLoc p U A) (hw : MemLpLoc q U w) :
    MemLpLoc r U (fun z => A z (w z)) :=
  fun K hK hc => (ContinuousLinearMap.id ℝ (F →L[ℝ] G)).memLp_of_bilin r (hA K hK hc) (hw K hK hc)

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

section PreciseRepresentative

open TauCeti.MeasureTheory in
/-- A locally `Lᵖ` function on an open set `Ω`, with `1 ≤ p`, agrees almost everywhere on `Ω`
with its precise representative. -/
theorem MemLpLoc.ae_eq_preciseRepresentative {E F : Type*} [PseudoMetricSpace E]
    [SecondCountableTopology E] [LocallyCompactSpace E] [MeasureSpace E] [BorelSpace E]
    [IsUnifLocDoublingMeasure (volume : Measure E)] [IsLocallyFiniteMeasure (volume : Measure E)]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {p : ENNReal} {Ω : Opens E} {f : E → F} (hp : 1 ≤ p) (hu : MemLpLoc p Ω f) :
    f =ᵐ[volume.restrict Ω] preciseRepresentative volume f :=
  ae_eq_restrict_preciseRepresentative Ω.isOpen
    (hu.locallyIntegrableOn hp Ω.isOpen.isLocallyClosed)

end PreciseRepresentative

section MemWkpLoc

universe u v w

variable {E : Type u} {F : Type v} {G : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasureSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
  [NormedSpace ℝ G] {p q : ENNReal} {U V : Set E} {Ω : Opens E} {k l m : ℕ} {f g u : E → F}

private def MemWkpLocAux (p : ENNReal) (U : Set E) :
    (k : ℕ) → {F : Type (max u v)} → [NormedAddCommGroup F] → [NormedSpace ℝ F] →
      (E → F) → Prop
  | 0, _, _, _, f => MemLpLoc p U f
  | k + 1, F, _, _, f => MemLpLoc p U f ∧
      ∃ D : E → E →L[ℝ] F, HasWeakFDerivOn volume (Opens.interior U) f D ∧
        MemWkpLocAux p U k D

/-- The iterated weak derivatives through order `k` exist on `interior U` and are `Lᵖ` on
every compact subset of `U`, including compact sets reaching its boundary.
The first derivative takes values in `E →L[ℝ] F`; higher derivatives iterate this construction.
No integrability at infinity or boundary trace is required. -/
def MemWkpLoc (p : ENNReal) (U : Set E) :
    (k : ℕ) → {F : Type v} → [NormedAddCommGroup F] → [NormedSpace ℝ F] →
      (E → F) → Prop
  | 0, _, _, _, f => MemLpLoc p U f
  | k + 1, F, _, _, f => MemLpLoc p U f ∧
      ∃ D : E → E →L[ℝ] F, HasWeakFDerivOn volume (Opens.interior U) f D ∧
        MemWkpLocAux.{u, v} p U k D

private theorem memWkpLocAux_max {F : Type (max u v)} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} : MemWkpLocAux.{u, v} p U k f ↔ MemWkpLocAux.{u, max u v} p U k f := by
  induction k generalizing F with
  | zero => exact Iff.rfl
  | succ k ih =>
    unfold MemWkpLocAux
    exact and_congr_right fun _ => exists_congr fun _ => and_congr_right fun _ => ih

private theorem memWkpLocAux_iff_memWkpLoc {F : Type (max u v)} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E → F} :
    MemWkpLocAux.{u, v} p U k f ↔ MemWkpLoc.{u, max u v} p U k f := by
  cases k with
  | zero => exact Iff.rfl
  | succ k =>
    unfold MemWkpLocAux MemWkpLoc
    exact and_congr_right fun _ => exists_congr fun _ => and_congr_right fun _ => memWkpLocAux_max

/-- At order zero the local Sobolev class is exactly the local `Lᵖ` class. -/
@[simp]
theorem memWkpLoc_zero_iff : MemWkpLoc p U 0 f ↔ MemLpLoc p U f := Iff.rfl

/-- The successor-order characterization supplies a weak derivative in the preceding class. -/
theorem memWkpLoc_succ_iff : MemWkpLoc p U (k + 1) f ↔ MemLpLoc p U f ∧
    ∃ D : E → E →L[ℝ] F, HasWeakFDerivOn volume (Opens.interior U) f D ∧
      MemWkpLoc p U k D :=
  and_congr_right fun _ => exists_congr fun _ => and_congr_right fun _ =>
    memWkpLocAux_iff_memWkpLoc

/-- On an open domain, the successor-order weak derivative is tested on the domain itself. -/
theorem memWkpLoc_succ_iff_of_isOpen : MemWkpLoc p Ω (k + 1) f ↔ MemLpLoc p Ω f ∧
    ∃ D : E → E →L[ℝ] F, HasWeakFDerivOn volume Ω f D ∧ MemWkpLoc p Ω k D := by
  simp only [memWkpLoc_succ_iff, Opens.interior_coe]

/-- At order one, local Sobolev membership means `f` is locally `Lᵖ` and has a locally `Lᵖ` weak
derivative on `interior U`. -/
theorem memWkpLoc_one_iff : MemWkpLoc p U 1 f ↔ MemLpLoc p U f ∧
    ∃ D : E → E →L[ℝ] F, HasWeakFDerivOn volume (Opens.interior U) f D ∧
      MemLpLoc p U D := Iff.rfl

/-- On an open domain, order-one local Sobolev membership means `f` is locally `Lᵖ` and has a
locally `Lᵖ` weak derivative on `Ω`. -/
theorem memWkpLoc_one_iff_of_isOpen : MemWkpLoc p Ω 1 f ↔ MemLpLoc p Ω f ∧
    ∃ D : E → E →L[ℝ] F, HasWeakFDerivOn volume Ω f D ∧ MemLpLoc p Ω D := by
  simp only [memWkpLoc_one_iff, Opens.interior_coe]

/-- Every local Sobolev function is locally `Lᵖ`. -/
theorem MemWkpLoc.memLpLoc (hf : MemWkpLoc p U k f) : MemLpLoc p U f := by
  cases k with
  | zero => exact hf
  | succ k => exact hf.1

/-- A positive-order local Sobolev function has a weak derivative of the preceding order. -/
theorem MemWkpLoc.exists_weakFDeriv (hf : MemWkpLoc p U (k + 1) f) :
    ∃ D : E → E →L[ℝ] F, HasWeakFDerivOn volume (Opens.interior U) f D ∧
      MemWkpLoc p U k D :=
  (memWkpLoc_succ_iff.mp hf).2

/-- On an open domain, positive-order membership gives a weak derivative on that domain. -/
theorem MemWkpLoc.exists_weakFDeriv_of_isOpen (hf : MemWkpLoc p Ω (k + 1) f) :
    ∃ D : E → E →L[ℝ] F, HasWeakFDerivOn volume Ω f D ∧ MemWkpLoc p Ω k D :=
  (memWkpLoc_succ_iff_of_isOpen.mp hf).2

/-- Positive-order membership retains the completeness required by weak derivatives. -/
theorem MemWkpLoc.completeSpace (hf : MemWkpLoc p U (k + 1) f) : CompleteSpace F := by
  obtain ⟨D, hD, _⟩ := hf.exists_weakFDeriv
  exact hD.completeSpace

/-- For a continuous function on `U`, local `Lᵖ` membership is automatic, so successor-order
local Sobolev membership is equivalent to having a weak derivative of the preceding order. -/
theorem _root_.ContinuousOn.memWkpLoc_succ_iff [OpensMeasurableSpace E]
    [IsFiniteMeasureOnCompacts (volume : Measure E)] (hf : ContinuousOn f U) :
    MemWkpLoc p U (k + 1) f ↔
      ∃ D : E → E →L[ℝ] F, HasWeakFDerivOn volume (Opens.interior U) f D ∧
        MemWkpLoc p U k D :=
  TauCeti.memWkpLoc_succ_iff.trans (and_iff_right hf.memLpLoc)

/-- For a continuous function on an open set `Ω`, order-one local Sobolev membership is equivalent
to having a locally `Lᵖ` weak derivative on `Ω`. -/
theorem _root_.ContinuousOn.memWkpLoc_one_iff [OpensMeasurableSpace E]
    [IsFiniteMeasureOnCompacts (volume : Measure E)] (hf : ContinuousOn f Ω) :
    MemWkpLoc p Ω 1 f ↔
      ∃ D : E → E →L[ℝ] F, HasWeakFDerivOn volume Ω f D ∧ MemLpLoc p Ω D := by
  simpa only [Opens.interior_coe, memWkpLoc_zero_iff] using hf.memWkpLoc_succ_iff (p := p) (k := 0)

/-- Restriction preserves the interior weak derivatives and the bounds on compact subsets. -/
theorem MemWkpLoc.mono (hf : MemWkpLoc p U k f) (hVU : V ⊆ U) :
    MemWkpLoc p V k f := by
  have aux : ∀ (k : ℕ) {F : Type (max u v)} [NormedAddCommGroup F] [NormedSpace ℝ F]
      {f : E → F}, MemWkpLoc p U k f → MemWkpLoc p V k f := by
    intro k
    induction k with
    | zero => intro _ _ _ _ hf; exact hf.mono_set hVU
    | succ k ih =>
      intro _ _ _ _ hf
      obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
      exact memWkpLoc_succ_iff.2 ⟨hp.mono_set hVU, D, hD.mono (interior_mono hVU), ih hk⟩
  cases k with
  | zero => exact hf.mono_set hVU
  | succ k =>
    obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
    exact memWkpLoc_succ_iff.2 ⟨hp.mono_set hVU, D, hD.mono (interior_mono hVU), aux k hk⟩

/-- Almost-everywhere changes of the function preserve its local Sobolev class. -/
theorem MemWkpLoc.congr_ae (hf : MemWkpLoc p U k f)
    (hfg : f =ᵐ[volume.restrict U] g) : MemWkpLoc p U k g := by
  cases k with
  | zero => exact MemLpLoc.congr_ae hf hfg
  | succ k =>
    obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
    exact memWkpLoc_succ_iff.2 ⟨hp.congr_ae hfg, D,
      hD.congr_ae (ae_mono (Measure.restrict_mono_set volume interior_subset) hfg), hk⟩

/-- Restricting to a subset preserves the local Sobolev class of any function agreeing with the
original one on that subset. -/
theorem MemWkpLoc.congr_mono [OpensMeasurableSpace E] (hf : MemWkpLoc p U k f)
    (hgf : Set.EqOn g f V) (hVU : V ⊆ U) :
    MemWkpLoc p V k g := by
  cases k with
  | zero => exact MemLpLoc.congr_mono hf hgf hVU
  | succ k =>
    obtain ⟨-, D, hD, hk⟩ := memWkpLoc_succ_iff.1 (hf.mono hVU)
    exact memWkpLoc_succ_iff.2 ⟨hf.memLpLoc.congr_mono hgf hVU, D, hD.congr_ae <| by
      filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with z hz using
        (hgf (interior_subset hz)).symm, hk⟩

/-- The local Sobolev class only depends on the values on the set. -/
theorem MemWkpLoc.congr [OpensMeasurableSpace E] (hf : MemWkpLoc p U k f)
    (hgf : Set.EqOn g f U) : MemWkpLoc p U k g :=
  hf.congr_mono hgf subset_rfl

/-- Every weak derivative of a member of `MemWkpLoc p Ω (k + 1)` is in `MemWkpLoc p Ω k`, not only
the one supplied by the definition: weak derivatives are unique almost everywhere. -/
theorem MemWkpLoc.memWkpLoc_of_hasWeakFDerivOn [FiniteDimensional ℝ E] [BorelSpace E]
    (hf : MemWkpLoc p Ω (k + 1) f) {D : E → E →L[ℝ] F} (hD : HasWeakFDerivOn volume Ω f D) :
    MemWkpLoc p Ω k D := by
  obtain ⟨D', hD', hD'k⟩ := hf.exists_weakFDeriv_of_isOpen
  exact hD'k.congr_ae (hD'.ae_eq hD)

/-- Every weak derivative of a member of `MemWkpLoc p Ω 1` is locally `Lᵖ` on `Ω`, not only the
one supplied by the definition: weak derivatives are unique almost everywhere. -/
theorem MemWkpLoc.memLpLoc_of_hasWeakFDerivOn [FiniteDimensional ℝ E] [BorelSpace E]
    (hf : MemWkpLoc p Ω 1 f) {D : E → E →L[ℝ] F} (hD : HasWeakFDerivOn volume Ω f D) :
    MemLpLoc p Ω D :=
  memWkpLoc_zero_iff.1 (hf.memWkpLoc_of_hasWeakFDerivOn hD)

/-- Decreasing the integrability exponent preserves each local derivative order. -/
theorem MemWkpLoc.mono_exponent [IsFiniteMeasureOnCompacts (volume : Measure E)]
    (hf : MemWkpLoc p U k f) (hqp : q ≤ p) :
    MemWkpLoc q U k f := by
  have aux : ∀ (k : ℕ) {F : Type (max u v)} [NormedAddCommGroup F] [NormedSpace ℝ F]
      {f : E → F}, MemWkpLoc p U k f → MemWkpLoc q U k f := by
    intro k
    induction k with
    | zero => intro _ _ _ _ hf; exact MemLpLoc.mono_exponent hf hqp
    | succ k ih =>
      intro _ _ _ _ hf
      obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
      exact memWkpLoc_succ_iff.2 ⟨hp.mono_exponent hqp, D, hD, ih hk⟩
  cases k with
  | zero => exact MemLpLoc.mono_exponent hf hqp
  | succ k =>
    obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
    exact memWkpLoc_succ_iff.2 ⟨hp.mono_exponent hqp, D, hD, aux k hk⟩

/-- Dropping the top derivative preserves local Sobolev membership. -/
theorem MemWkpLoc.of_succ (hf : MemWkpLoc p U (k + 1) f) : MemWkpLoc p U k f := by
  have aux : ∀ (k : ℕ) {F : Type (max u v)} [NormedAddCommGroup F] [NormedSpace ℝ F]
      {f : E → F}, MemWkpLoc p U (k + 1) f → MemWkpLoc p U k f := by
    intro k
    induction k with
    | zero => intro _ _ _ _ hf; exact hf.1
    | succ k ih =>
      intro _ _ _ _ hf
      obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
      exact memWkpLoc_succ_iff.2 ⟨hp, D, hD, ih hk⟩
  cases k with
  | zero => exact hf.1
  | succ k =>
    obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
    exact memWkpLoc_succ_iff.2 ⟨hp, D, hD, aux k hk⟩

/-- Membership at any smaller derivative order follows from membership at a larger one. -/
theorem MemWkpLoc.of_le (hf : MemWkpLoc p U k f) (hlk : l ≤ k) : MemWkpLoc p U l f := by
  induction hlk with
  | refl => exact hf
  | step _ ih => exact ih hf.of_succ

/-- The zero function lies in every local Sobolev class with complete codomain. -/
@[simp]
theorem memWkpLoc_zero_fun [CompleteSpace F] : MemWkpLoc p U k (0 : E → F) := by
  have aux : ∀ (k : ℕ) {F : Type (max u v)} [NormedAddCommGroup F] [NormedSpace ℝ F]
      [CompleteSpace F], MemWkpLoc p U k (0 : E → F) := by
    intro k
    induction k with
    | zero => intro _ _ _ _; exact memLpLoc_zero
    | succ k ih =>
      intro _ _ _ _
      exact memWkpLoc_succ_iff.2 ⟨memLpLoc_zero, 0, hasWeakFDerivOn_zero, ih⟩
  cases k with
  | zero => exact memLpLoc_zero
  | succ k => exact memWkpLoc_succ_iff.2 ⟨memLpLoc_zero, 0, hasWeakFDerivOn_zero, aux k⟩

/-- Local Sobolev membership is closed under addition. -/
theorem MemWkpLoc.add [OpensMeasurableSpace E] (hf : MemWkpLoc p U k f) (hg : MemWkpLoc p U k g) :
    MemWkpLoc p U k (f + g) := by
  have aux : ∀ (k : ℕ) {F : Type (max u v)} [NormedAddCommGroup F] [NormedSpace ℝ F]
      {f g : E → F}, MemWkpLoc p U k f → MemWkpLoc p U k g → MemWkpLoc p U k (f + g) := by
    intro k
    induction k with
    | zero => intro _ _ _ _ _ hf hg; exact MemLpLoc.add hf hg
    | succ k ih =>
      intro _ _ _ _ _ hf hg
      obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
      obtain ⟨hq, D', hD', hk'⟩ := memWkpLoc_succ_iff.1 hg
      exact memWkpLoc_succ_iff.2 ⟨hp.add hq, D + D', hD.add hD', ih hk hk'⟩
  cases k with
  | zero => exact MemLpLoc.add hf hg
  | succ k =>
    obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
    obtain ⟨hq, D', hD', hk'⟩ := memWkpLoc_succ_iff.1 hg
    exact memWkpLoc_succ_iff.2 ⟨hp.add hq, D + D', hD.add hD', aux k hk hk'⟩

/-- Local Sobolev membership is closed under negation. -/
theorem MemWkpLoc.neg (hf : MemWkpLoc p U k f) : MemWkpLoc p U k (-f) := by
  have aux : ∀ (k : ℕ) {F : Type (max u v)} [NormedAddCommGroup F] [NormedSpace ℝ F]
      {f : E → F}, MemWkpLoc p U k f → MemWkpLoc p U k (-f) := by
    intro k
    induction k with
    | zero => intro _ _ _ _ hf; exact MemLpLoc.neg hf
    | succ k ih =>
      intro _ _ _ _ hf
      obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
      exact memWkpLoc_succ_iff.2 ⟨hp.neg, -D, hD.neg, ih hk⟩
  cases k with
  | zero => exact MemLpLoc.neg hf
  | succ k =>
    obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
    exact memWkpLoc_succ_iff.2 ⟨hp.neg, -D, hD.neg, aux k hk⟩

/-- Local Sobolev membership is closed under subtraction. -/
theorem MemWkpLoc.sub [OpensMeasurableSpace E] (hf : MemWkpLoc p U k f) (hg : MemWkpLoc p U k g) :
    MemWkpLoc p U k (f - g) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- Real scalar multiplication preserves local Sobolev membership. -/
theorem MemWkpLoc.const_smul (hf : MemWkpLoc p U k f) (c : ℝ) :
    MemWkpLoc p U k (c • f) := by
  have aux : ∀ (k : ℕ) {F : Type (max u v)} [NormedAddCommGroup F] [NormedSpace ℝ F]
      {f : E → F}, MemWkpLoc p U k f → MemWkpLoc p U k (c • f) := by
    intro k
    induction k with
    | zero => intro _ _ _ _ hf; exact MemLpLoc.const_smul hf c
    | succ k ih =>
      intro _ _ _ _ hf
      obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
      exact memWkpLoc_succ_iff.2 ⟨hp.const_smul c, c • D, hD.const_smul c, ih hk⟩
  cases k with
  | zero => exact MemLpLoc.const_smul hf c
  | succ k =>
    obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
    exact memWkpLoc_succ_iff.2 ⟨hp.const_smul c, c • D, hD.const_smul c, aux k hk⟩

/-- Continuous linear maps of the codomain preserve all local weak derivative orders. -/
theorem MemWkpLoc.clm_comp [OpensMeasurableSpace E] [CompleteSpace G] (hf : MemWkpLoc p U k f)
    (A : F →L[ℝ] G) : MemWkpLoc p U k (fun z => A (f z)) := by
  have aux : ∀ (k : ℕ) {F : Type (max u v)} {G : Type (max u w)}
      [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
      [CompleteSpace G] {f : E → F},
      MemWkpLoc p U k f → (A : F →L[ℝ] G) → MemWkpLoc p U k (fun z => A (f z)) := by
    intro k
    induction k with
    | zero => intro _ _ _ _ _ _ _ _ hf A; exact MemLpLoc.clm_comp hf A
    | succ k ih =>
      intro _ _ _ _ _ _ _ _ hf A
      obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
      exact memWkpLoc_succ_iff.2 ⟨hp.clm_comp A, fun z => A.comp (D z), hD.clm_comp A,
        ih hk ((ContinuousLinearMap.compL ℝ E _ _) A)⟩
  cases k with
  | zero => exact MemLpLoc.clm_comp hf A
  | succ k =>
    obtain ⟨hp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hf
    exact memWkpLoc_succ_iff.2 ⟨hp.clm_comp A, fun z => A.comp (D z), hD.clm_comp A,
      aux k hk ((ContinuousLinearMap.compL ℝ E F G) A)⟩

/-- Multiplying a scalar local Sobolev function by a fixed vector in a complete real normed space
preserves local Sobolev membership at every order. -/
theorem MemWkpLoc.smul_const [OpensMeasurableSpace E] [CompleteSpace F] {a : E → ℝ}
    (ha : MemWkpLoc p U k a) (v : F) : MemWkpLoc p U k (fun x => a x • v) := by
  simpa using ha.clm_comp ((ContinuousLinearMap.id ℝ ℝ).smulRight v)

/-- **Pairs of local Sobolev maps.** Two maps in the local Sobolev class of order `k` pair to a map
in the same class, with values in the product. -/
theorem MemWkpLoc.prodMk [OpensMeasurableSpace E] [CompleteSpace F] [CompleteSpace G] {g : E → G}
    (hf : MemWkpLoc p U k f) (hg : MemWkpLoc p U k g) :
    MemWkpLoc p U k (fun z => (f z, g z)) := by
  have h := (hf.clm_comp (ContinuousLinearMap.inl ℝ F G)).add
    (hg.clm_comp (ContinuousLinearMap.inr ℝ F G))
  convert h using 1
  ext z <;> simp

/-- **Products of operator fields.** If two fields of continuous linear maps are in the local
Sobolev class of order `k`, so is their pointwise product map `(A z).prodMap (B z)`. -/
theorem MemWkpLoc.prodMap [OpensMeasurableSpace E] {E₁ E₂ E₃ E₄ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [CompleteSpace E₂] [NormedAddCommGroup E₃]
    [NormedSpace ℝ E₃] [NormedAddCommGroup E₄] [NormedSpace ℝ E₄] [CompleteSpace E₄]
    {A : E → E₁ →L[ℝ] E₂} {B : E → E₃ →L[ℝ] E₄} (hA : MemWkpLoc p U k A)
    (hB : MemWkpLoc p U k B) : MemWkpLoc p U k (fun z => (A z).prodMap (B z)) := by
  simpa using (hA.prodMk hB).clm_comp (ContinuousLinearMap.prodMapL ℝ E₁ E₂ E₃ E₄)

/-- A continuous linear change of codomain preserves and reflects every local weak
Sobolev order. -/
@[simp]
theorem _root_.ContinuousLinearEquiv.comp_memWkpLoc_iff [OpensMeasurableSpace E]
    (e : F ≃L[ℝ] G) :
    MemWkpLoc p U k (fun z => e (f z)) ↔ MemWkpLoc p U k f := by
  cases k with
  | zero =>
    simpa only [memWkpLoc_zero_iff] using
      (e.comp_memLpLoc_iff (p := p) (U := U) (f := f))
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

/-- Constant functions belong to every local Sobolev class. -/
@[simp]
theorem memWkpLoc_const [FiniteDimensional ℝ E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure] [CompleteSpace F] (c : F) :
    MemWkpLoc p U k (fun _ => c) := by
  cases k with
  | zero => exact memLpLoc_const c
  | succ k =>
    refine memWkpLoc_succ_iff.2 ⟨memLpLoc_const c, 0, ?_, memWkpLoc_zero_fun⟩
    apply hasWeakFDerivOn_iff.mpr
    exact fun v => hasWeakLineDerivOn_const (μ := volume) (Ω := Opens.interior U) (v := v) c

/-- Finite sums of local Sobolev functions remain in the same class. -/
theorem MemWkpLoc.sum [OpensMeasurableSpace E] {ι : Type*} [CompleteSpace F] (s : Finset ι)
    {f : ι → E → F} (hf : ∀ i ∈ s, MemWkpLoc p U k (f i)) :
    MemWkpLoc p U k (fun z => ∑ i ∈ s, f i z) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty, Pi.zero_def] using
      (memWkpLoc_zero_fun (p := p) (U := U) (k := k) (F := F))
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi, Pi.add_def] using
      (hf i (Finset.mem_insert_self i s)).add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- A map differentiable on an open set `Ω` whose derivative is locally `Lᵖ` on `Ω` (with
`1 ≤ p`) belongs to `W^{1,p}_loc(Ω; F)`, with weak derivative `fderiv ℝ f`. -/
theorem _root_.DifferentiableOn.memWkpLoc_one_of_memLpLoc [FiniteDimensional ℝ E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure] [CompleteSpace F] (hf : DifferentiableOn ℝ f Ω)
    (hp : 1 ≤ p) (hD : MemLpLoc p Ω (fderiv ℝ f)) : MemWkpLoc p Ω 1 f :=
  hf.continuousOn.memWkpLoc_one_iff.2 ⟨fderiv ℝ f,
    hasWeakFDerivOn_of_differentiableOn
      (hD.locallyIntegrableOn hp Ω.isOpen.isLocallyClosed)
      (fun _ hx => hf.differentiableAt (Ω.isOpen.mem_nhds hx)),
    hD⟩

/-- A map differentiable on an open set `Ω` with continuous derivative belongs to
`W^{1,p}_loc(Ω; F)` for every exponent `p`, with weak derivative `fderiv ℝ f`. -/
theorem _root_.DifferentiableOn.memWkpLoc_one [FiniteDimensional ℝ E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure] [CompleteSpace F] (hf : DifferentiableOn ℝ f Ω)
    (hD : ContinuousOn (fderiv ℝ f) Ω) : MemWkpLoc p Ω 1 f :=
  hf.continuousOn.memWkpLoc_one_iff.2 ⟨fderiv ℝ f,
    hasWeakFDerivOn_of_differentiableOn
      (hD.locallyIntegrableOn Ω.isOpen.measurableSet)
      (fun _ hx => hf.differentiableAt (Ω.isOpen.mem_nhds hx)),
    hD.memLpLoc⟩

/-- A map that is `Cᵏ` on an open neighbourhood of `U` has locally `Lᵖ` weak derivatives
through order `k` on `U`, with bounds reaching its boundary, for every exponent. -/
theorem _root_.ContDiffOn.memWkpLoc [FiniteDimensional ℝ E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure] [CompleteSpace F]
    (hf : ContDiffOn ℝ k f (Ω : Set E)) (hU : U ⊆ Ω) : MemWkpLoc p U k f := by
  have aux : ∀ (k : ℕ) {F : Type (max u v)} [NormedAddCommGroup F] [NormedSpace ℝ F]
      [CompleteSpace F] {f : E → F}, ContDiffOn ℝ k f (Ω : Set E) → MemWkpLoc p U k f := by
    intro k
    induction k with
    | zero => intro _ _ _ _ _ hf; exact (hf.continuousOn.mono hU).memLpLoc
    | succ k ih =>
      intro _ _ _ _ f hf
      have hD : ContDiffOn ℝ k (fderiv ℝ f) (Ω : Set E) :=
        hf.fderiv_of_isOpen Ω.isOpen (by simp)
      refine memWkpLoc_succ_iff.2 ⟨(hf.continuousOn.mono hU).memLpLoc, fderiv ℝ f, ?_, ih hD⟩
      exact (hf.of_le (by simp)).hasWeakFDerivOn_fderiv.mono (interior_subset.trans hU)
  cases k with
  | zero => exact (hf.continuousOn.mono hU).memLpLoc
  | succ k =>
    have hD : ContDiffOn ℝ k (fderiv ℝ f) (Ω : Set E) :=
      hf.fderiv_of_isOpen Ω.isOpen (by simp)
    refine memWkpLoc_succ_iff.2 ⟨(hf.continuousOn.mono hU).memLpLoc, fderiv ℝ f, ?_, aux k hD⟩
    exact (hf.of_le (by simp)).hasWeakFDerivOn_fderiv.mono (interior_subset.trans hU)

/-- A `Cᵏ` map on the whole space is in the local class `W^{k,p}` on every set, for every
exponent. -/
theorem _root_.ContDiff.memWkpLoc [FiniteDimensional ℝ E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure] [CompleteSpace F] (hf : ContDiff ℝ k f) :
    MemWkpLoc p U k f :=
  hf.contDiffOn.memWkpLoc (Ω := ⊤) ((Set.subset_univ U).trans_eq Opens.coe_top.symm)

/-- Every continuous linear map belongs to every local Sobolev class on every set. -/
theorem _root_.ContinuousLinearMap.memWkpLoc [FiniteDimensional ℝ E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure] [CompleteSpace F] (A : E →L[ℝ] F) :
    MemWkpLoc p U k A :=
  A.contDiff.memWkpLoc

/-! ### Bounds for chains of weak derivatives -/

section WeakDerivChainLe

private def WeakDerivChainLeAux (p : ENNReal) (S T : Set E) (C : ENNReal) :
    (m : ℕ) → {F : Type (max u v)} → [NormedAddCommGroup F] → [NormedSpace ℝ F] →
      (E → F) → (E → F) → Prop
  | 0, _, _, _, f, g => eLpNorm f p (volume.restrict S) ≤ C * eLpNorm g p (volume.restrict T)
  | m + 1, F, _, _, f, g =>
      eLpNorm f p (volume.restrict S) ≤ C * eLpNorm g p (volume.restrict T) ∧
        ∀ Df Dg : E → E →L[ℝ] F, HasWeakFDerivOn volume (Opens.interior S) f Df →
          HasWeakFDerivOn volume (Opens.interior T) g Dg → WeakDerivChainLeAux p S T C m Df Dg

/-- `WeakDerivChainLe p S T C m f g` bounds the iterated weak derivatives of `f` through order `m`
by those of `g`: the `Lᵖ(S)` norm of `f` is at most `C` times the `Lᵖ(T)` norm of `g`, and for
every weak derivative `Df` of `f` on the interior of `S` and every weak derivative `Dg` of `g` on
the interior of `T`, the pair `Df`, `Dg` satisfies the same through order `m - 1`. Since the
quantification is over all weak derivatives, the bound holds for every choice of the iterated
derivatives `D^i f` and `D^i g`, `i ≤ m`. -/
def WeakDerivChainLe (p : ENNReal) (S T : Set E) (C : ENNReal) :
    (m : ℕ) → {F : Type v} → [NormedAddCommGroup F] → [NormedSpace ℝ F] →
      (E → F) → (E → F) → Prop
  | 0, _, _, _, f, g => eLpNorm f p (volume.restrict S) ≤ C * eLpNorm g p (volume.restrict T)
  | m + 1, F, _, _, f, g =>
      eLpNorm f p (volume.restrict S) ≤ C * eLpNorm g p (volume.restrict T) ∧
        ∀ Df Dg : E → E →L[ℝ] F, HasWeakFDerivOn volume (Opens.interior S) f Df →
          HasWeakFDerivOn volume (Opens.interior T) g Dg →
            WeakDerivChainLeAux.{u, v} p S T C m Df Dg

variable {C : ENNReal} {S T : Set E}

private theorem weakDerivChainLeAux_max {F : Type (max u v)} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f g : E → F} :
    WeakDerivChainLeAux.{u, v} p S T C m f g ↔
      WeakDerivChainLeAux.{u, max u v} p S T C m f g := by
  induction m generalizing F with
  | zero => exact Iff.rfl
  | succ m ih =>
    unfold WeakDerivChainLeAux
    exact and_congr_right fun _ => forall_congr' fun _ => forall_congr' fun _ =>
      forall_congr' fun _ => forall_congr' fun _ => ih

private theorem weakDerivChainLeAux_iff {F : Type (max u v)} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f g : E → F} :
    WeakDerivChainLeAux.{u, v} p S T C m f g ↔
      WeakDerivChainLe.{u, max u v} p S T C m f g := by
  cases m with
  | zero => exact Iff.rfl
  | succ m =>
    unfold WeakDerivChainLeAux WeakDerivChainLe
    exact and_congr_right fun _ => forall_congr' fun _ => forall_congr' fun _ =>
      forall_congr' fun _ => forall_congr' fun _ => weakDerivChainLeAux_max

/-- At order zero the chain bound is the `Lᵖ` bound. -/
@[simp]
theorem weakDerivChainLe_zero_iff :
    WeakDerivChainLe p S T C 0 f g ↔
      eLpNorm f p (volume.restrict S) ≤ C * eLpNorm g p (volume.restrict T) :=
  Iff.rfl

/-- At a successor order the chain bound is the `Lᵖ` bound together with the chain bound for
every pair of weak derivatives. -/
theorem weakDerivChainLe_succ_iff :
    WeakDerivChainLe p S T C (m + 1) f g ↔
      eLpNorm f p (volume.restrict S) ≤ C * eLpNorm g p (volume.restrict T) ∧
        ∀ Df Dg : E → E →L[ℝ] F, HasWeakFDerivOn volume (Opens.interior S) f Df →
          HasWeakFDerivOn volume (Opens.interior T) g Dg → WeakDerivChainLe p S T C m Df Dg :=
  and_congr_right fun _ => forall_congr' fun _ => forall_congr' fun _ =>
    forall_congr' fun _ => forall_congr' fun _ => weakDerivChainLeAux_iff

/-- A chain bound gives the `Lᵖ` bound at order zero. -/
theorem WeakDerivChainLe.eLpNorm_le (h : WeakDerivChainLe p S T C m f g) :
    eLpNorm f p (volume.restrict S) ≤ C * eLpNorm g p (volume.restrict T) := by
  cases m with
  | zero => exact h
  | succ m => exact h.1

/-- A chain bound passes to every pair of weak derivatives, one order lower. -/
theorem WeakDerivChainLe.weakFDeriv (h : WeakDerivChainLe p S T C (m + 1) f g)
    {Df Dg : E → E →L[ℝ] F} (hf : HasWeakFDerivOn volume (Opens.interior S) f Df)
    (hg : HasWeakFDerivOn volume (Opens.interior T) g Dg) : WeakDerivChainLe p S T C m Df Dg :=
  (weakDerivChainLe_succ_iff.1 h).2 Df Dg hf hg

end WeakDerivChainLe

/-! ### Classical derivatives of `Cᵏ` representatives -/

section ContDiffRepresentatives

variable [FiniteDimensional ℝ E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]

/-- **The derivative of a `C¹` representative is a weak derivative.** Let `U` agree almost
everywhere with its interior, as an open set does and as a half-disc `Ω ∩ {0 ≤ im}` does
(`TauCeti.inter_setOf_im_nonneg_ae_eq_interior`). If `g` is `C¹` on the interior of `U` and
agrees almost everywhere on `U` with `u ∈ MemWkpLoc p U (k + 1)`, then `fderiv ℝ g` is a weak
derivative of `u` on the interior of `U` and lies in `MemWkpLoc p U k`. By uniqueness of weak
derivatives (`TauCeti.HasWeakFDerivOn.ae_eq`), every weak derivative of `u` on the interior of `U`
agrees with `fderiv ℝ g` almost everywhere on `U`. -/
theorem MemWkpLoc.hasWeakFDerivOn_fderiv_of_contDiffOn (hu : MemWkpLoc p U (k + 1) u)
    (hU : U =ᵐ[volume] (Opens.interior U : Set E)) (hg : ContDiffOn ℝ 1 g (Opens.interior U))
    (hug : u =ᵐ[volume.restrict U] g) :
    HasWeakFDerivOn volume (Opens.interior U) u (fderiv ℝ g) ∧ MemWkpLoc p U k (fderiv ℝ g) := by
  have := hu.completeSpace
  rw [Measure.restrict_congr_set hU] at hug
  have hg' : HasWeakFDerivOn volume (Opens.interior U) g (fderiv ℝ g) := hg.hasWeakFDerivOn_fderiv
  obtain ⟨D, hD, hDk⟩ := hu.exists_weakFDeriv
  refine ⟨hg'.congr_ae hug.symm, hDk.congr_ae ?_⟩
  rw [Measure.restrict_congr_set hU]
  exact (hD.congr_ae hug).ae_eq hg'

/-- **Iterated derivatives of a `Cᵏ` representative.** Let `U` agree almost everywhere with its
interior, as an open set does and as a half-disc `Ω ∩ {0 ≤ im}` does
(`TauCeti.inter_setOf_im_nonneg_ae_eq_interior`). If `g` is `Cᵏ` on the interior of `U` and agrees
almost everywhere on `U` with `u ∈ MemWkpLoc p U (k + m)`, then `iteratedFDeriv ℝ k g` lies in
`MemWkpLoc p U m`. No restriction on `p` is needed. -/
theorem MemWkpLoc.iteratedFDeriv_of_contDiffOn (hu : MemWkpLoc p U (k + m) u)
    (hU : U =ᵐ[volume] (Opens.interior U : Set E)) (hg : ContDiffOn ℝ k g (Opens.interior U))
    (hug : u =ᵐ[volume.restrict U] g) :
    MemWkpLoc p U m (iteratedFDeriv ℝ k g) := by
  have aux : ∀ (k : ℕ) {F : Type (max u v)} [NormedAddCommGroup F] [NormedSpace ℝ F]
      {u g : E → F}, MemWkpLoc p U (k + m) u → ContDiffOn ℝ k g (Opens.interior U) →
      u =ᵐ[volume.restrict U] g → MemWkpLoc p U m (iteratedFDeriv ℝ k g) := by
    intro k
    induction k with
    | zero =>
      intro F _ _ u g hu _ hug
      rw [iteratedFDeriv_zero_eq_comp]
      exact (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv
        |>.comp_memWkpLoc_iff.2 ((Nat.zero_add m ▸ hu).congr_ae hug)
    | succ k ih =>
      intro F _ _ u g hu hg hug
      rw [Nat.add_right_comm] at hu
      obtain ⟨-, hDk⟩ := hu.hasWeakFDerivOn_fderiv_of_contDiffOn hU
        (hg.of_le (by exact_mod_cast Nat.le_add_left 1 k)) hug
      have hgk : ContDiffOn ℝ k (fderiv ℝ g) (Opens.interior U) :=
        hg.fderiv_of_isOpen isOpen_interior (by push_cast; rfl)
      have h := ih hDk hgk (Filter.EventuallyEq.refl _ _)
      have heq : iteratedFDeriv ℝ (k + 1) g =
          fun z => (continuousMultilinearCurryRightEquiv' ℝ k E F).symm
            (iteratedFDeriv ℝ k (fderiv ℝ g) z) := by
        ext1 z
        exact iteratedFDeriv_succ_eq_comp_right
      rw [heq]
      exact (continuousMultilinearCurryRightEquiv' ℝ k E F).symm.toContinuousLinearEquiv
        |>.comp_memWkpLoc_iff.2 h
  cases k with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp]
    exact (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv
      |>.comp_memWkpLoc_iff.2 ((Nat.zero_add m ▸ hu).congr_ae hug)
  | succ k =>
    rw [Nat.add_right_comm] at hu
    obtain ⟨-, hDk⟩ := hu.hasWeakFDerivOn_fderiv_of_contDiffOn hU
      (hg.of_le (by exact_mod_cast Nat.le_add_left 1 k)) hug
    have hgk : ContDiffOn ℝ k (fderiv ℝ g) (Opens.interior U) :=
      hg.fderiv_of_isOpen isOpen_interior (by push_cast; rfl)
    have h := aux k hDk hgk (Filter.EventuallyEq.refl _ _)
    have heq : iteratedFDeriv ℝ (k + 1) g =
        fun z => (continuousMultilinearCurryRightEquiv' ℝ k E F).symm
          (iteratedFDeriv ℝ k (fderiv ℝ g) z) := by
      ext1 z
      exact iteratedFDeriv_succ_eq_comp_right
    rw [heq]
    exact (continuousMultilinearCurryRightEquiv' ℝ k E F).symm.toContinuousLinearEquiv
      |>.comp_memWkpLoc_iff.2 h

end ContDiffRepresentatives

end MemWkpLoc

end TauCeti
