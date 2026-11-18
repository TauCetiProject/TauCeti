/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Prod
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Topology.Sets.Opens
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.MeasureTheory.Function.LpSeminorm.ContinuousOn

/-!
# Local Lebesgue classes on measured topological spaces

A map `f : X → F` belongs to `TauCeti.MemLpLoc p U f` on a subset `U` of a measured topological
space `X` when it belongs to `Lᵖ` on every compact subset of `U`. No global integrability condition
is imposed, and `U` need not be open: on a set reaching its boundary, the compact subsets include
those touching the boundary. Membership depends only on almost-everywhere values on `U`, and
global `Lᵖ` membership implies local membership (`MeasureTheory.MemLp.memLpLoc`).

## Main declarations

* `TauCeti.MemLpLoc`, `TauCeti.memLpLoc_iff`: the local `Lᵖ` predicate and its unfolding.
* `TauCeti.MemLpLoc.mono_set`, `.congr_ae`, `.congr_mono`, `.congr`: restriction and congruence.
* `TauCeti.MemLpLoc.aestronglyMeasurable_of_isCompact`, `.aestronglyMeasurable_restrict`:
  almost-everywhere strong measurability on compact subsets, and on any locally closed subset of a
  locally compact second-countable space, for every exponent `p : ENNReal`.
* `TauCeti.MemLpLoc.memLp_of_closure_subset`, `TauCeti.memLpLoc_of_forall_opens`: detection on
  relatively compact open subsets.
* `TauCeti.MemLpLoc.mono_exponent`, `ContinuousOn.memLpLoc`, `Continuous.memLpLoc`,
  `TauCeti.memLpLoc_const`: exponent monotonicity and continuous functions.
* `TauCeti.MemLpLoc.locallyIntegrableOn`, `TauCeti.memLpLoc_one_iff_locallyIntegrableOn`:
  identification of `MemLpLoc 1` with `LocallyIntegrableOn` on locally closed sets.
* `TauCeti.MemLpLoc.add`, `.neg`, `.sub`, `.sum`, `.const_smul`, `.clm_comp`, `.clm_prod`,
  `ContinuousLinearEquiv.comp_memLpLoc_iff`: algebraic and linear closure properties.
* `TauCeti.MemLpLoc.continuousOn_smul`, `.continuousOn_clm_comp`, `.clm_comp_continuousOn`,
  `.clm_apply_continuousOn`, `.continuous_smul_of_tsupport_subset`, `.integrableOn_smul`,
  `.locallyIntegrableOn_clm_apply`: multiplication, operator composition, compact-support cutoffs,
  and Hölder's inequality on compact subsets.
* `TauCeti.memLpLoc_iff_locally`, `TauCeti.memLpLoc_iff_forall_inter`,
  `TauCeti.memLpLoc_iSup_iff`: locality and the sheaf property on regular spaces.
* `Module.Basis.memLpLoc_iff`: finite codomain-basis characterization.
* `TauCeti.memLpLoc_smul_volume_iff`, `TauCeti.memLpLoc_iff_of_isAddHaarMeasure`: invariance under
  positive rescaling of `volume` and independence of the choice of Borel additive Haar measure.
* `TauCeti.MemLpLoc.comp_continuousLinearEquiv`, `ContinuousLinearEquiv.memLpLoc_comp_iff`:
  transport under continuous linear equivalences between finite-dimensional spaces carrying Borel
  additive Haar measures.
* `TauCeti.memLpLoc_indicator_pos`: local `Lᵖ` membership of open half-space indicators.

The almost-everywhere equality with the precise representative is in
`TauCeti.MeasureTheory.Function.MemLpLoc.PreciseRepresentative`, and the inverse-norm sharpness
characterization `x ↦ ‖x‖⁻¹` is in `TauCeti.MeasureTheory.Function.MemLpLoc.NormInv`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (local Lebesgue and Sobolev spaces).
* W. P. Ziemer, *Weakly Differentiable Functions*, Graduate Texts in Mathematics 120, Springer,
  1989, §1.1.
-/

public noncomputable section

open MeasureTheory Set TopologicalSpace Filter
open scoped ENNReal NNReal Topology

namespace TauCeti

section MemLpLoc

variable {X F G : Type*} [TopologicalSpace X] [MeasureSpace X]
  [NormedAddCommGroup F] [NormedAddCommGroup G]
  {p q : ENNReal} {U V : Set X} {f g : X → F}

/-- A function is locally `Lᵖ` on `U` when it belongs to `Lᵖ` on every compact subset of `U`.
On a set reaching its boundary, those compact subsets include the boundary. -/
def MemLpLoc (p : ENNReal) (U : Set X) (f : X → F) : Prop :=
  ∀ K : Set X, K ⊆ U → IsCompact K → MemLp f p (volume.restrict K)

/-- Local `Lᵖ` membership is characterized by `Lᵖ` membership on every compact subset. -/
theorem memLpLoc_iff : MemLpLoc p U f ↔
    ∀ K : Set X, K ⊆ U → IsCompact K → MemLp f p (volume.restrict K) := Iff.rfl

/-- Local `Lᵖ` membership restricts to any smaller set. -/
theorem MemLpLoc.mono_set (hf : MemLpLoc p U f) (hVU : V ⊆ U) : MemLpLoc p V f :=
  fun K hK hc => hf K (hK.trans hVU) hc

/-- Local `Lᵖ` membership on `U` gives almost-everywhere strong measurability on every compact
subset of `U`, for every exponent `p : ENNReal`. -/
theorem MemLpLoc.aestronglyMeasurable_of_isCompact (hf : MemLpLoc p U f) {K : Set X}
    (hKU : K ⊆ U) (hK : IsCompact K) : AEStronglyMeasurable f (volume.restrict K) :=
  (hf K hKU hK).aestronglyMeasurable

/-- On a locally closed subset of a locally compact second-countable space (in particular on every
open or closed subset), local `Lᵖ` membership implies almost-everywhere strong measurability on the
subset, for every exponent `p : ENNReal`. -/
theorem MemLpLoc.aestronglyMeasurable_restrict [LocallyCompactSpace X] [SecondCountableTopology X]
    (hf : MemLpLoc p U f) (hU : IsLocallyClosed U) :
    AEStronglyMeasurable f (volume.restrict U) := by
  rcases hU with ⟨O, Z, hO, hZ, rfl⟩
  have hK : ∀ x : ↥(O ∩ Z), ∃ K : Set X, IsCompact K ∧ x.1 ∈ interior K ∧ K ⊆ O :=
    fun x => exists_compact_subset hO x.2.1
  choose K hKc hxK hKO using hK
  obtain ⟨T, hTc, hT⟩ := isOpen_iUnion_countable (fun x => interior (K x)) fun x => isOpen_interior
  have hcov : O ∩ Z = ⋃ x : T, interior (K x.1) ∩ (O ∩ Z) := by
    refine Subset.antisymm (fun y hy => ?_) (iUnion_subset fun _ => inter_subset_right)
    have hyU : y ∈ ⋃ x, interior (K x) := mem_iUnion.2 ⟨⟨y, hy⟩, hxK ⟨y, hy⟩⟩
    obtain ⟨x, hxT, hyx⟩ := mem_iUnion₂.1 (hT ▸ hyU)
    exact mem_iUnion.2 ⟨⟨x, hxT⟩, hyx, hy⟩
  have : Countable T := hTc
  rw [hcov]
  refine AEStronglyMeasurable.iUnion fun ⟨x, _⟩ => ?_
  have hsub : interior (K x) ∩ (O ∩ Z) ⊆ K x ∩ Z := fun _ hy => ⟨interior_subset hy.1, hy.2.2⟩
  exact (hf (K x ∩ Z) (inter_subset_inter_left Z (hKO x))
    ((hKc x).inter_right hZ)).aestronglyMeasurable.mono_measure (Measure.restrict_mono hsub le_rfl)

/-- Local `Lᵖ` membership on `U` gives `Lᵖ` membership on every set whose closure is compact and
contained in `U`. -/
theorem MemLpLoc.memLp_of_closure_subset (hf : MemLpLoc p U f) (hV : IsCompact (closure V))
    (hVU : closure V ⊆ U) : MemLp f p (volume.restrict V) :=
  (hf _ hVU hV).mono_measure (Measure.restrict_mono subset_closure le_rfl)

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
theorem MemLpLoc.congr_mono [OpensMeasurableSpace X] [T2Space X] (hf : MemLpLoc p U f)
    (hgf : EqOn g f V) (hVU : V ⊆ U) :
    MemLpLoc p V g := fun K hK hc => (hf K (hK.trans hVU) hc).ae_eq <| by
  filter_upwards [ae_restrict_mem hc.measurableSet] with z hz using (hgf (hK hz)).symm

/-- Local `Lᵖ` membership on `U` only depends on the values of the function on `U`. -/
theorem MemLpLoc.congr [OpensMeasurableSpace X] [T2Space X] (hf : MemLpLoc p U f)
    (hgf : EqOn g f U) : MemLpLoc p U g :=
  hf.congr_mono hgf subset_rfl

/-- The zero function belongs to every local `Lᵖ` class. -/
@[simp]
theorem memLpLoc_zero : MemLpLoc p U (0 : X → F) := fun _ _ _ => MemLp.zero

/-- Local `Lᵖ` membership is closed under addition. -/
theorem MemLpLoc.add (hf : MemLpLoc p U f) (hg : MemLpLoc p U g) :
    MemLpLoc p U (f + g) := fun K hK hc => (hf K hK hc).add (hg K hK hc)

/-- Local `Lᵖ` membership is closed under negation. -/
theorem MemLpLoc.neg (hf : MemLpLoc p U f) : MemLpLoc p U (-f) :=
  fun K hK hc => (hf K hK hc).neg

/-- Local `Lᵖ` membership is closed under subtraction. -/
theorem MemLpLoc.sub (hf : MemLpLoc p U f) (hg : MemLpLoc p U g) :
    MemLpLoc p U (f - g) := fun K hK hc => (hf K hK hc).sub (hg K hK hc)

/-- Compact subsets have finite volume, so decreasing the exponent preserves local membership.
In particular this passes from the infinity endpoint to every finite exponent. -/
theorem MemLpLoc.mono_exponent [IsFiniteMeasureOnCompacts (volume : Measure X)]
    (hf : MemLpLoc p U f) (hqp : q ≤ p) : MemLpLoc q U f := by
  intro K hK hc
  have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hc.measure_lt_top⟩
  exact (hf K hK hc).mono_exponent hqp

/-- A function continuous on `U` is locally `Lᵖ` there, with no global bound required. -/
theorem _root_.ContinuousOn.memLpLoc [OpensMeasurableSpace X] [T2Space X]
    [IsFiniteMeasureOnCompacts (volume : Measure X)] (hf : ContinuousOn f U) : MemLpLoc p U f :=
  (memLpLoc_iff.2 fun _K hK hc =>
    (hf.mono hK).memLp_top_restrict_of_subset_isCompact hc hc.measurableSet subset_rfl
    ).mono_exponent le_top

/-- A continuous function is locally `Lᵖ` on every subset, with no global bound required. -/
theorem _root_.Continuous.memLpLoc [OpensMeasurableSpace X] [T2Space X]
    [IsFiniteMeasureOnCompacts (volume : Measure X)] (hf : Continuous f) : MemLpLoc p U f :=
  hf.continuousOn.memLpLoc

/-- Every constant function is locally `Lᵖ` for all exponents, including infinity. -/
@[simp]
theorem memLpLoc_const [IsFiniteMeasureOnCompacts (volume : Measure X)] (c : F) :
    MemLpLoc p U (fun _ => c) := by
  intro K _ hc
  have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hc.measure_lt_top⟩
  exact memLp_const c

/-- A locally `Lᵖ` function on a locally closed set is locally integrable when `1 ≤ p`. -/
theorem MemLpLoc.locallyIntegrableOn [LocallyCompactSpace X]
    [IsFiniteMeasureOnCompacts (volume : Measure X)] (hf : MemLpLoc p U f) (hp : 1 ≤ p)
    (hU : IsLocallyClosed U) : LocallyIntegrableOn f U volume :=
  (locallyIntegrableOn_iff hU).2 fun K hK hc =>
    memLp_one_iff_integrable.1 ((hf.mono_exponent hp) K hK hc)

/-- On a locally closed set, local `L¹` membership is exactly local integrability. -/
theorem memLpLoc_one_iff_locallyIntegrableOn [LocallyCompactSpace X] (hU : IsLocallyClosed U) :
    MemLpLoc 1 U f ↔ LocallyIntegrableOn f U volume :=
  ⟨fun hf => (locallyIntegrableOn_iff hU).2 fun K hK hc => memLp_one_iff_integrable.1 (hf K hK hc),
    fun hf _K hK hc => memLp_one_iff_integrable.2 (hf.integrableOn_compact_subset hK hc)⟩

/-- A finite sum of locally `Lᵖ` functions is locally `Lᵖ`, without a completeness assumption. -/
theorem MemLpLoc.sum {ι : Type*} (s : Finset ι) {f : ι → X → F}
    (hf : ∀ i ∈ s, MemLpLoc p U (f i)) : MemLpLoc p U (fun z => ∑ i ∈ s, f i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty, Pi.zero_def] using (memLpLoc_zero (p := p) (U := U))
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi, Pi.add_def] using
      (hf i (Finset.mem_insert_self i s)).add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- On an open set `Ω`, a function that agrees almost everywhere with an `Lᵖ` function on every
open `W` whose closure is compact and contained in `Ω` is locally `Lᵖ` on `Ω`. -/
theorem memLpLoc_of_forall_opens [LocallyCompactSpace X] [RegularSpace X] {Ω : Opens X}
    (h : ∀ W : Opens X, IsCompact (closure (W : Set X)) → closure (W : Set X) ⊆ Ω →
      ∃ g : X → F, MemLp g p (volume.restrict (W : Set X)) ∧ g =ᵐ[volume.restrict W] f) :
    MemLpLoc p Ω f := by
  refine fun K hKΩ hK => ?_
  obtain ⟨W, hWo, hKW, hWΩ, hWc⟩ := exists_open_between_and_isCompact_closure hK Ω.isOpen hKΩ
  obtain ⟨g, hg, hgf⟩ := h ⟨W, hWo⟩ hWc hWΩ
  exact (hg.ae_eq hgf).mono_measure (Measure.restrict_mono hKW le_rfl)

/-- A function that is `Lᵖ` on a set `W` is locally `Lᵖ` on every set `U` contained in `W` up to a
null set, including on compact subsets of `U` that leave `W`. -/
theorem _root_.MeasureTheory.MemLp.memLpLoc_of_ae_le {W : Set X}
    (hf : MemLp f p (volume.restrict W)) (hUW : U ≤ᵐ[volume] W) : MemLpLoc p U f :=
  memLpLoc_iff.2 fun _ hK _ => hf.mono_measure
    (Measure.restrict_mono_ae ((EventuallySubset.of_subset hK).trans hUW))

variable [NormedSpace ℝ F] [NormedSpace ℝ G]

/-- Real scalar multiplication preserves local `Lᵖ` membership. -/
theorem MemLpLoc.const_smul (hf : MemLpLoc p U f) (c : ℝ) : MemLpLoc p U (c • f) :=
  fun K hK hc => (hf K hK hc).const_smul c

/-- A continuous linear map on the codomain preserves local `Lᵖ` membership. -/
theorem MemLpLoc.clm_comp (hf : MemLpLoc p U f) (A : F →L[ℝ] G) :
    MemLpLoc p U (fun z => A (f z)) :=
  fun K hK hc => A.comp_memLp' (hf K hK hc)

/-- Pairing two locally `Lᵖ` fields of continuous linear maps into their product map preserves
local `Lᵖ` membership. -/
theorem MemLpLoc.clm_prod {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : X → E →L[ℝ] F} {B : X → E →L[ℝ] G} (hA : MemLpLoc p U A) (hB : MemLpLoc p U B) :
    MemLpLoc p U (fun z => (A z).prod (B z)) := by
  convert (hA.clm_comp (ContinuousLinearMap.compL ℝ E F (F × G)
    (ContinuousLinearMap.inl ℝ F G))).add
      (hB.clm_comp (ContinuousLinearMap.compL ℝ E G (F × G) (ContinuousLinearMap.inr ℝ F G)))
    using 1
  funext z
  ext v <;> simp

/-- Composing a locally `Lᵖ` operator family on the left with one continuous on `U` preserves
local `Lᵖ` membership, since the continuous factor is bounded on every compact subset of `U`. -/
theorem MemLpLoc.continuousOn_clm_comp [OpensMeasurableSpace X] [T2Space X]
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : X → G →L[ℝ] H} {B : X → F →L[ℝ] G} (hB : MemLpLoc p U B) (hA : ContinuousOn A U) :
    MemLpLoc p U (fun z => A z ∘L B z) :=
  memLpLoc_iff.2 fun K hKU hK => (memLpLoc_iff.1 hB K hKU hK).clm_comp_of_continuousOn
    (hA.mono hKU) hK hK.measurableSet subset_rfl

/-- Composing a locally `Lᵖ` operator family on the right with one continuous on `U` preserves
local `Lᵖ` membership, since the continuous factor is bounded on every compact subset of `U`. -/
theorem MemLpLoc.clm_comp_continuousOn [OpensMeasurableSpace X] [T2Space X]
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {B : X → G →L[ℝ] H} {E : X → F →L[ℝ] G} (hB : MemLpLoc p U B) (hE : ContinuousOn E U) :
    MemLpLoc p U (fun z => B z ∘L E z) :=
  memLpLoc_iff.2 fun K hKU hK => (ContinuousLinearMap.compL ℝ F G H).memLp_of_bilin p
    (memLpLoc_iff.1 hB K hKU hK)
    ((hE.mono hKU).memLp_top_restrict_of_subset_isCompact hK hK.measurableSet subset_rfl)

/-- **Hölder's inequality on compact subsets**: a locally `Lᵖ` field of continuous linear maps
applied to a locally `L^q` field is locally integrable on a locally closed set when
`1/p + 1/q ≤ 1`. -/
theorem MemLpLoc.locallyIntegrableOn_clm_apply [LocallyCompactSpace X]
    [IsFiniteMeasureOnCompacts (volume : Measure X)] {A : X → F →L[ℝ] G} {w : X → F}
    (hA : MemLpLoc p U A) (hw : MemLpLoc q U w) (hpq : p⁻¹ + q⁻¹ ≤ 1)
    (hU : IsLocallyClosed U) : LocallyIntegrableOn (fun z => A z (w z)) U volume := by
  have : ENNReal.HolderTriple p q (p⁻¹ + q⁻¹)⁻¹ := ⟨(inv_inv _).symm⟩
  exact MemLpLoc.locallyIntegrableOn
    (fun K hK hc => (ContinuousLinearMap.id ℝ (F →L[ℝ] G)).memLp_of_bilin _ (hA K hK hc)
      (hw K hK hc))
    (ENNReal.one_le_inv.2 hpq) hU

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
theorem MemLpLoc.continuousOn_smul [OpensMeasurableSpace X] [T2Space X] {χ : X → ℝ}
    (hf : MemLpLoc p U f) (hχ : ContinuousOn χ U) :
    MemLpLoc p U (fun z => χ z • f z) :=
  memLpLoc_iff.2 fun K hK hc =>
    ((hχ.mono hK).memLp_top_restrict_of_subset_isCompact hc hc.measurableSet subset_rfl).smul
      (memLpLoc_iff.1 hf K hK hc)

/-- A locally `Lᵖ` field of continuous linear maps applied to a map continuous on `U` is locally
`Lᵖ` on `U`, since the map is bounded on every compact subset of `U`. -/
theorem MemLpLoc.clm_apply_continuousOn [OpensMeasurableSpace X] [T2Space X]
    {A : X → F →L[ℝ] G} (hA : MemLpLoc p U A) (hf : ContinuousOn f U) :
    MemLpLoc p U (fun z => A z (f z)) :=
  memLpLoc_iff.2 fun K hK hc =>
    (memLpLoc_iff.1 hA K hK hc).of_bilin (fun B x => B x) 1
      ((hf.mono hK).memLp_top_restrict_of_subset_isCompact hc hc.measurableSet subset_rfl)
      isBoundedBilinearMap_apply.continuous
      (.of_forall fun z => by simpa using (A z).le_opNNNorm (f z))

/-- A continuous factor supported in `U` extends a local `Lᵖ` function on `U` by zero to a local
`Lᵖ` function on the whole space: on a compact set `K` the product only sees
`K ∩ tsupport χ`, a compact subset of `U`. -/
theorem MemLpLoc.continuous_smul_of_tsupport_subset [OpensMeasurableSpace X] [T2Space X]
    {χ : X → ℝ} (hf : MemLpLoc p U f) (hχ : Continuous χ) (hsupp : tsupport χ ⊆ U) :
    MemLpLoc p univ (fun z => χ z • f z) := by
  have hT := hf.continuousOn_smul hχ.continuousOn
  have hcl : IsClosed (tsupport χ) := isClosed_tsupport χ
  refine memLpLoc_iff.2 fun K _ hK => ?_
  have heq : (fun z => χ z • f z) = (tsupport χ).indicator (fun z => χ z • f z) := by
    refine (indicator_eq_self.2 ?_).symm
    exact (Function.support_smul_subset_left χ f).trans (subset_tsupport χ)
  rw [heq, memLp_indicator_iff_restrict hcl.measurableSet.nullMeasurableSet,
    Measure.restrict_restrict hcl.measurableSet]
  exact memLpLoc_iff.1 hT _ (inter_subset_left.trans hsupp) (hK.inter_left hcl)

/-- A continuous compactly supported factor whose support meets the closed set `T` inside `S`
makes a function in `MemLpLoc 1 S` integrable on `T`, even though `T` may be unbounded or leave
`S`. -/
theorem MemLpLoc.integrableOn_smul [OpensMeasurableSpace X] [T2Space X] {S T : Set X}
    {h : X → F} (hh : MemLpLoc 1 S h) {f : X → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hT : IsClosed T) (hfS : tsupport f ∩ T ⊆ S) : IntegrableOn (fun z => f z • h z) T := by
  have hK : IsCompact (tsupport f ∩ T) := hfc.isCompact.inter_right hT
  have hhK : IntegrableOn h (tsupport f ∩ T) :=
    memLp_one_iff_integrable.1 (hh _ hfS hK)
  refine (hhK.continuousOn_smul hf.continuousOn hK).of_forall_sdiff_eq_zero hT.measurableSet
    fun z hz => ?_
  simp [image_eq_zero_of_notMem_tsupport fun h => hz.2 ⟨h, hz.1⟩]

end MemLpLoc

/-! ### Locality and the sheaf property -/

section Locality

variable {X F : Type*} [TopologicalSpace X] [RegularSpace X] [MeasureSpace X]
  [NormedAddCommGroup F] {p : ENNReal} {U : Set X} {f : X → F}

/-- Local `Lᵖ` membership is a local property: it holds on `U` exactly when every point of `U`
has a neighbourhood within `U` on which it holds. -/
theorem memLpLoc_iff_locally :
    MemLpLoc p U f ↔ ∀ x ∈ U, ∃ V ∈ 𝓝[U] x, MemLpLoc p V f := by
  refine ⟨fun hf _ _ => ⟨U, self_mem_nhdsWithin, hf⟩,
    fun h => memLpLoc_iff.2 fun K hKU hK => ?_⟩
  refine hK.induction_on (p := fun s => MemLp f p (volume.restrict s)) (by simp)
    (fun s t hst ht => ht.mono_measure (Measure.restrict_mono hst le_rfl))
    (fun s t hs ht => (hs.add_measure ht).mono_measure (Measure.restrict_union_le s t))
    fun x hx => ?_
  obtain ⟨V, hV, hfV⟩ := h x (hKU hx)
  obtain ⟨O, hO, hOV⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hV
  obtain ⟨C, hC, hCc, hCO⟩ := exists_mem_nhds_isClosed_subset hO
  exact ⟨K ∩ C, inter_mem_nhdsWithin K hC,
    memLpLoc_iff.1 hfV _ (fun z hz => hOV ⟨hCO hz.2, hKU hz.1⟩)
      (hK.inter_right hCc)⟩

/-- Local `Lᵖ` membership on `U` can be checked on the traces `U ∩ O i` of an open cover. -/
theorem memLpLoc_iff_forall_inter {ι : Type*} (O : ι → Opens X) (hU : U ⊆ ⋃ i, (O i : Set X)) :
    MemLpLoc p U f ↔ ∀ i, MemLpLoc p (U ∩ O i) f := by
  refine ⟨fun hf i => hf.mono_set inter_subset_left, fun h => memLpLoc_iff_locally.2 ?_⟩
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.1 (hU hx)
  exact ⟨U ∩ O i, inter_mem_nhdsWithin U ((O i).isOpen.mem_nhds hi), h i⟩

/-- Local `Lᵖ` membership on the union of open sets is membership on each of them. -/
theorem memLpLoc_iSup_iff {ι : Type*} (V : ι → Opens X) :
    MemLpLoc p (⨆ i, V i : Opens X) f ↔ ∀ i, MemLpLoc p (V i) f := by
  rw [memLpLoc_iff_forall_inter V (by simp)]
  simp only [Opens.coe_iSup, inter_eq_right.2 (subset_iUnion (fun i => (V i : Set X)) _)]

end Locality

/-! ### Finite codomain-basis characterization -/

/-- Local `Lᵖ` membership on any measured topological space can be tested in any finite basis of
the codomain. No completeness of the codomain is needed. -/
theorem _root_.Module.Basis.memLpLoc_iff {X F ι : Type*} [TopologicalSpace X] [MeasureSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [Finite ι] {p : ENNReal} {U : Set X} {f : X → F}
    (b : Module.Basis ι ℝ F) :
    MemLpLoc p U f ↔ ∀ i, MemLpLoc p U (fun x => b.repr (f x) i) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : FiniteDimensional ℝ F := b.finiteDimensional_of_finite
  constructor
  · intro h i
    exact h.clm_comp ((ContinuousLinearMap.proj i).comp b.equivFunL.toContinuousLinearMap)
  · intro h
    have hs : MemLpLoc p U (fun x => ∑ i, b.repr (f x) i • b i) := by
      apply MemLpLoc.sum
      intro i _
      exact (h i).clm_comp ((ContinuousLinearMap.id ℝ ℝ).smulRight (b i))
    simpa only [b.sum_repr] using hs

/-! ### Measure scaling, Haar invariance, linear transport, and half-space indicators -/

section MeasureAndLinear

/-- Rescaling `volume` by any positive factor `c : ℝ≥0` (`c ≠ 0`) leaves `MemLpLoc` unchanged. -/
theorem memLpLoc_smul_volume_iff {X F : Type*} [TopologicalSpace X] [MeasureSpace X]
    [NormedAddCommGroup F] {c : ℝ≥0} (hc : c ≠ 0) {p : ℝ≥0∞} {U : Set X} {f : X → F} :
    @MemLpLoc X F _ (MeasureSpace.mk ((c : ℝ≥0∞) • (volume : Measure X))) _ p U f ↔
      MemLpLoc p U f := by
  rw [@memLpLoc_iff X F _ (MeasureSpace.mk ((c : ℝ≥0∞) • (volume : Measure X))), memLpLoc_iff]
  dsimp only [volume]
  constructor
  · intro h K hKU hK
    have h1 : MemLp f p (((c : ℝ≥0∞) • (volume : Measure X)).restrict K) := h K hKU hK
    rw [Measure.restrict_smul] at h1
    have h2 := h1.smul_measure (c := (c⁻¹ : ℝ≥0)) ENNReal.coe_ne_top
    rwa [smul_smul, ← ENNReal.coe_mul, inv_mul_cancel₀ hc, ENNReal.coe_one, one_smul] at h2
  · intro h K hKU hK
    rw [Measure.restrict_smul]
    exact (h K hKU hK).smul_measure ENNReal.coe_ne_top

/-- **Haar-measure independence of `MemLpLoc`.** On a locally compact second-countable topological
additive group, `MemLpLoc` does not depend on the choice of Borel additive Haar measure. -/
theorem memLpLoc_iff_of_isAddHaarMeasure {G F : Type*} [AddGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] [NormedAddCommGroup F]
    (μ ν : Measure G) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    {p : ℝ≥0∞} {U : Set G} {f : G → F} :
    @MemLpLoc G F _ (MeasureSpace.mk μ) _ p U f ↔
      @MemLpLoc G F _ (MeasureSpace.mk ν) _ p U f := by
  have aux : ∀ (μ₁ μ₂ : Measure G) [μ₁.IsAddHaarMeasure] [μ₂.IsAddHaarMeasure],
      @MemLpLoc G F _ (MeasureSpace.mk μ₁) _ p U f →
        @MemLpLoc G F _ (MeasureSpace.mk μ₂) _ p U f := by
    intro μ₁ μ₂ _ _ h
    rw [@memLpLoc_iff G F _ (MeasureSpace.mk μ₁)] at h
    rw [@memLpLoc_iff G F _ (MeasureSpace.mk μ₂)]
    dsimp only [volume] at h ⊢
    intro K hKU hK
    rw [Measure.isAddLeftInvariant_eq_smul μ₂ μ₁, Measure.restrict_smul]
    exact (h K hKU hK).smul_measure ENNReal.coe_ne_top
  exact ⟨aux μ ν, aux ν μ⟩

/-- Precomposition with a continuous linear equivalence into a finite-dimensional space carrying a
Borel additive Haar measure preserves `MemLpLoc`. -/
theorem MemLpLoc.comp_continuousLinearEquiv {E₁ E F : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [MeasureSpace E₁] [BorelSpace E₁] [(volume : Measure E₁).IsAddHaarMeasure]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
    [NormedAddCommGroup F]
    {p : ℝ≥0∞} {U : Set E₁} {V : Set E} {u : E → F}
    (hu : MemLpLoc p V u) (e : E₁ ≃L[ℝ] E) (hUV : MapsTo e U V) :
    MemLpLoc p U (u ∘ e) := by
  have : ((volume : Measure E₁).map e).IsAddHaarMeasure := e.isAddHaarMeasure_map volume
  have hu_map : @MemLpLoc E F _ (MeasureSpace.mk ((volume : Measure E₁).map e)) _ p V u :=
    (memLpLoc_iff_of_isAddHaarMeasure volume ((volume : Measure E₁).map e)).1 hu
  rw [@memLpLoc_iff E F _ (MeasureSpace.mk ((volume : Measure E₁).map e))] at hu_map
  dsimp only [volume] at hu_map
  refine memLpLoc_iff.2 fun K hKU hK => ?_
  have hKe : IsCompact (e '' K) := hK.image e.continuous
  have h1 : MemLp u p (((volume : Measure E₁).map e).restrict (e '' K)) :=
    hu_map (e '' K) ((image_mono hKU).trans hUV.image_subset) hKe
  have hemp : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have hres : ((volume : Measure E₁).map e).restrict (e '' K) =
      ((volume : Measure E₁).restrict K).map e := by
    rw [hemp.restrict_map, preimage_image_eq _ e.injective]
  rw [hres, hemp.memLp_map_measure_iff] at h1
  exact h1

/-- Precomposition with a continuous linear equivalence preserves and reflects `MemLpLoc`. -/
@[simp]
theorem _root_.ContinuousLinearEquiv.memLpLoc_comp_iff {E₁ E F : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [MeasureSpace E₁] [BorelSpace E₁] [(volume : Measure E₁).IsAddHaarMeasure]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
    [NormedAddCommGroup F]
    {p : ℝ≥0∞} {V : Set E} {u : E → F} (e : E₁ ≃L[ℝ] E) :
    MemLpLoc p (e ⁻¹' V) (u ∘ e) ↔ MemLpLoc p V u := by
  refine ⟨fun h => ?_, fun h => h.comp_continuousLinearEquiv e (mapsTo_preimage e V)⟩
  have hVU : MapsTo e.symm V (e ⁻¹' V) := fun y hy => by simpa using hy
  simpa [Function.comp_def] using h.comp_continuousLinearEquiv e.symm hVU

/-- The indicator of an open half-space `{x : E | 0 < ℓ x}` belongs to `MemLpLoc p U` on every
subset `U` and for every exponent `p : ℝ≥0∞`. -/
theorem memLpLoc_indicator_pos {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [OpensMeasurableSpace E] [IsFiniteMeasureOnCompacts (volume : Measure E)]
    (ℓ : StrongDual ℝ E) (p : ℝ≥0∞) (U : Set E) :
    MemLpLoc p U ({x : E | 0 < ℓ x}.indicator fun _ => (1 : ℝ)) := by
  refine memLpLoc_iff.2 fun K _ hK => ?_
  have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
  exact memLp_indicator_const p
    (isOpen_lt continuous_const ℓ.continuous).measurableSet.nullMeasurableSet 1
    (Or.inr (measure_ne_top _ _))

end MeasureAndLinear

end TauCeti
