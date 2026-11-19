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
# Local Lebesgue classes

A map `f : X → F` on a measured topological space `X` belongs to `TauCeti.MemLpLoc p U f` on a
subset `U` when it belongs to `Lᵖ` on every compact subset of `U`. No global integrability is
imposed, and `U` need not be open: on a set reaching its boundary, the compact subsets include
those touching the boundary. The codomain `F` is any normed group, for instance a real Banach
space with no separability assumption: membership includes almost-everywhere strong
measurability on each compact subset (`TauCeti.MemLpLoc.aestronglyMeasurable_of_isCompact`), so
it is not determined by the scalar compositions `ℓ ∘ f` alone.

The main case is a finite-dimensional real normed space `E` with an additive Haar measure
`volume`, where the class does not depend on the choice of Haar measure
(`TauCeti.memLpLoc_iff_of_isAddHaarMeasure`) and is carried along continuous linear equivalences
(`ContinuousLinearEquiv.memLpLoc_comp_iff`). The planar class of `ℂ` is the case `E = ℂ`.

## Main declarations

* `TauCeti.MemLpLoc`: the local `Lᵖ` predicate.
* `TauCeti.MemLpLoc.mono_set`, `.congr_ae`, `.congr_mono`, `.congr`: restriction and congruence.
* `TauCeti.MemLpLoc.mono_exponent`, `ContinuousOn.memLpLoc`, `TauCeti.memLpLoc_const`:
  exponent monotonicity and continuous functions.
* `TauCeti.MemLpLoc.locallyIntegrableOn`, `TauCeti.memLpLoc_one_iff_locallyIntegrableOn`:
  local integrability for `1 ≤ p`.
* `TauCeti.MemLpLoc.add`, `.sub`, `.sum`, `.const_smul`, `.clm_comp`,
  `ContinuousLinearEquiv.comp_memLpLoc_iff`: linear closure properties.
* `TauCeti.memLpLoc_iff_locally`, `TauCeti.memLpLoc_iSup_iff`: the sheaf property.
* `Module.Basis.memLpLoc_iff`: coordinates in a finite basis of the codomain.
* `TauCeti.memLpLoc_iff_of_isAddHaarMeasure`: independence of the Haar measure.
* `ContinuousLinearEquiv.memLpLoc_comp_iff`: transport along continuous linear equivalences.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (local Lebesgue and Sobolev spaces).
* W. Arendt and M. Kreuter, *Mapping theorems for Sobolev spaces of vector-valued functions*,
  Studia Math. 240 (2018), §2.
-/

public noncomputable section

open MeasureTheory Set TopologicalSpace Filter
open scoped ENNReal NNReal Topology

namespace TauCeti

section MemLpLoc

variable {X F G : Type*} [TopologicalSpace X] [MeasureSpace X]
  [NormedAddCommGroup F] [NormedAddCommGroup G]
  {p q : ℝ≥0∞} {U V : Set X} {f g : X → F}

/-- A function is locally `Lᵖ` on `U` when it belongs to `Lᵖ` on every compact subset of `U`.
On a set reaching its boundary, those compact subsets include the boundary. -/
def MemLpLoc (p : ℝ≥0∞) (U : Set X) (f : X → F) : Prop :=
  ∀ K : Set X, K ⊆ U → IsCompact K → MemLp f p (volume.restrict K)

/-- Local `Lᵖ` membership is characterized by `Lᵖ` membership on every compact subset. -/
theorem memLpLoc_iff : MemLpLoc p U f ↔
    ∀ K : Set X, K ⊆ U → IsCompact K → MemLp f p (volume.restrict K) := Iff.rfl

/-- Local `Lᵖ` membership restricts to any smaller set. -/
theorem MemLpLoc.mono_set (hf : MemLpLoc p U f) (hVU : V ⊆ U) : MemLpLoc p V f :=
  fun K hK hc => hf K (hK.trans hVU) hc

/-- Local `Lᵖ` membership on `U` gives almost-everywhere strong measurability on every compact
subset of `U`, for every exponent. -/
theorem MemLpLoc.aestronglyMeasurable_of_isCompact (hf : MemLpLoc p U f) {K : Set X}
    (hKU : K ⊆ U) (hK : IsCompact K) : AEStronglyMeasurable f (volume.restrict K) :=
  (hf K hKU hK).aestronglyMeasurable

/-- Local `Lᵖ` membership on `U` gives `Lᵖ` membership on every set whose closure is compact and
contained in `U`. -/
theorem MemLpLoc.memLp_of_closure_subset (hf : MemLpLoc p U f) (hV : IsCompact (closure V))
    (hVU : closure V ⊆ U) : MemLp f p (volume.restrict V) :=
  (hf _ hVU hV).mono_measure (Measure.restrict_mono subset_closure le_rfl)

/-- Local `Lᵖ` membership on `U` gives `Lᵖ` membership on every set whose closure is compact and
contained in `U`. -/
theorem MemLpLoc.memLp_restrict_of_isCompact_closure (hf : MemLpLoc p U f) {W : Set X}
    (hWc : IsCompact (closure W)) (hWU : closure W ⊆ U) : MemLp f p (volume.restrict W) :=
  hf.memLp_of_closure_subset hWc hWU

/-- A function that is `Lᵖ` on `U` is locally `Lᵖ` there. -/
theorem _root_.MeasureTheory.MemLp.memLpLoc (hf : MemLp f p (volume.restrict U)) :
    MemLpLoc p U f :=
  fun _ hK _ => hf.mono_measure (Measure.restrict_mono hK le_rfl)

/-- A function that is `Lᵖ` on a set `W` is locally `Lᵖ` on every set `U` contained in `W` up to a
null set, including on compact subsets of `U` that leave `W`. -/
theorem _root_.MeasureTheory.MemLp.memLpLoc_of_ae_le {W : Set X}
    (hf : MemLp f p (volume.restrict W)) (hUW : U ≤ᵐ[volume] W) : MemLpLoc p U f :=
  fun _ hK _ => hf.mono_measure
    (Measure.restrict_mono_ae ((EventuallySubset.of_subset hK).trans hUW))

/-- Almost-everywhere equality on `U` preserves local `Lᵖ` membership. -/
theorem MemLpLoc.congr_ae (hf : MemLpLoc p U f)
    (hfg : f =ᵐ[volume.restrict U] g) : MemLpLoc p U g := fun K hK hc =>
  (hf K hK hc).ae_eq (ae_mono (Measure.restrict_mono_set volume hK) hfg)

/-- Restricting to a subset preserves local `Lᵖ` membership of any function agreeing with the
original one on that subset. -/
theorem MemLpLoc.congr_mono [OpensMeasurableSpace X] [T2Space X] (hf : MemLpLoc p U f)
    (hgf : EqOn g f V) (hVU : V ⊆ U) : MemLpLoc p V g := fun K hK hc =>
  (hf K (hK.trans hVU) hc).ae_eq <| by
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

/-- A finite sum of locally `Lᵖ` functions is locally `Lᵖ`, without a completeness assumption. -/
theorem MemLpLoc.sum {ι : Type*} (s : Finset ι) {f : ι → X → F}
    (hf : ∀ i ∈ s, MemLpLoc p U (f i)) : MemLpLoc p U (fun z => ∑ i ∈ s, f i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty, Pi.zero_def] using (memLpLoc_zero (p := p) (U := U))
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi, Pi.add_def] using
      (hf i (Finset.mem_insert_self i s)).add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- Compact subsets have finite volume, so decreasing the exponent preserves local membership.
In particular this passes from the infinity endpoint to every finite exponent. -/
theorem MemLpLoc.mono_exponent [IsFiniteMeasureOnCompacts (volume : Measure X)]
    (hf : MemLpLoc p U f) (hqp : q ≤ p) : MemLpLoc q U f := fun K hK hc =>
  have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hc.measure_lt_top⟩
  (hf K hK hc).mono_exponent hqp

/-- A function continuous on `U` is locally `Lᵖ` there, with no global bound required. -/
theorem _root_.ContinuousOn.memLpLoc [OpensMeasurableSpace X] [T2Space X]
    [IsFiniteMeasureOnCompacts (volume : Measure X)] (hf : ContinuousOn f U) :
    MemLpLoc p U f :=
  MemLpLoc.mono_exponent (p := ∞) (fun _K hK hc =>
    (hf.mono hK).memLp_top_restrict_of_subset_isCompact hc hc.measurableSet subset_rfl) le_top

/-- A continuous function is locally `Lᵖ` on every set. -/
theorem _root_.Continuous.memLpLoc [OpensMeasurableSpace X] [T2Space X]
    [IsFiniteMeasureOnCompacts (volume : Measure X)] (hf : Continuous f) : MemLpLoc p U f :=
  hf.continuousOn.memLpLoc

/-- Every constant function is locally `Lᵖ` for all exponents, including infinity. -/
@[simp]
theorem memLpLoc_const [IsFiniteMeasureOnCompacts (volume : Measure X)] (c : F) :
    MemLpLoc p U (fun _ => c) := fun K _ hc =>
  have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hc.measure_lt_top⟩
  memLp_const c

/-- A locally `Lᵖ` function on a locally closed set is locally integrable when `1 ≤ p`.
This supplies the local integrability hypothesis used by the weak-derivative API. -/
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

variable [NormedSpace ℝ F] [NormedSpace ℝ G]

/-- Real scalar multiplication preserves local `Lᵖ` membership. -/
theorem MemLpLoc.const_smul (hf : MemLpLoc p U f) (c : ℝ) : MemLpLoc p U (c • f) :=
  fun K hK hc => (hf K hK hc).const_smul c

/-- A continuous linear map on the codomain preserves local `Lᵖ` membership. -/
theorem MemLpLoc.clm_comp (hf : MemLpLoc p U f) (A : F →L[ℝ] G) :
    MemLpLoc p U (fun z => A (f z)) :=
  fun K hK hc => A.comp_memLp' (hf K hK hc)

/-- A continuous linear change of codomain preserves and reflects local `Lᵖ` membership. -/
@[simp]
theorem _root_.ContinuousLinearEquiv.comp_memLpLoc_iff (e : F ≃L[ℝ] G) :
    MemLpLoc p U (fun z => e (f z)) ↔ MemLpLoc p U f := by
  refine ⟨fun h => ?_, fun h => h.clm_comp e.toContinuousLinearMap⟩
  simpa only [ContinuousLinearEquiv.coe_coe, e.symm_apply_apply] using
    h.clm_comp e.symm.toContinuousLinearMap

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
    MemLpLoc p U (fun z => A z ∘L B z) := fun K hKU hK =>
  (hB K hKU hK).clm_comp_of_continuousOn (hA.mono hKU) hK hK.measurableSet subset_rfl

/-- Composing a locally `Lᵖ` operator family on the right with one continuous on `U` preserves
local `Lᵖ` membership, since the continuous factor is bounded on every compact subset of `U`. -/
theorem MemLpLoc.clm_comp_continuousOn [OpensMeasurableSpace X] [T2Space X]
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {B : X → G →L[ℝ] H} {E : X → F →L[ℝ] G} (hB : MemLpLoc p U B) (hE : ContinuousOn E U) :
    MemLpLoc p U (fun z => B z ∘L E z) := fun K hKU hK =>
  (ContinuousLinearMap.compL ℝ F G H).memLp_of_bilin p (hB K hKU hK)
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

/-- A factor continuous on `U` preserves local `Lᵖ` membership on `U`, since it is bounded on
every compact subset of `U`. -/
theorem MemLpLoc.continuousOn_smul [OpensMeasurableSpace X] [T2Space X] {χ : X → ℝ}
    (hf : MemLpLoc p U f) (hχ : ContinuousOn χ U) :
    MemLpLoc p U (fun z => χ z • f z) := fun K hK hc =>
  ((hχ.mono hK).memLp_top_restrict_of_subset_isCompact hc hc.measurableSet subset_rfl).smul
    (hf K hK hc)

/-- A locally `Lᵖ` field of continuous linear maps applied to a map continuous on `U` is locally
`Lᵖ` on `U`, since the map is bounded on every compact subset of `U`. -/
theorem MemLpLoc.clm_apply_continuousOn [OpensMeasurableSpace X] [T2Space X]
    {A : X → F →L[ℝ] G} (hA : MemLpLoc p U A) (hf : ContinuousOn f U) :
    MemLpLoc p U (fun z => A z (f z)) := fun K hK hc =>
  (hA K hK hc).of_bilin (fun B x => B x) 1
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
  refine fun K _ hK => ?_
  have heq : (fun z => χ z • f z) = (tsupport χ).indicator (fun z => χ z • f z) :=
    (indicator_eq_self.2 <|
      (Function.support_smul_subset_left χ f).trans (subset_tsupport χ)).symm
  rw [heq, memLp_indicator_iff_restrict hcl.measurableSet.nullMeasurableSet,
    Measure.restrict_restrict hcl.measurableSet]
  exact hT _ (inter_subset_left.trans hsupp) (hK.inter_left hcl)

/-- A continuous compactly supported factor whose support meets the closed set `T` inside `S`
makes a function in `MemLpLoc 1 S` integrable on `T`, even though `T` may be unbounded or leave
`S`. -/
theorem MemLpLoc.integrableOn_smul [OpensMeasurableSpace X] [T2Space X] {S T : Set X}
    {h : X → F} (hh : MemLpLoc 1 S h) {f : X → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hT : IsClosed T) (hfS : tsupport f ∩ T ⊆ S) : IntegrableOn (fun z => f z • h z) T := by
  have hK : IsCompact (tsupport f ∩ T) := hfc.isCompact.inter_right hT
  have hhK : IntegrableOn h (tsupport f ∩ T) := memLp_one_iff_integrable.1 (hh _ hfS hK)
  refine (hhK.continuousOn_smul hf.continuousOn hK).of_forall_sdiff_eq_zero hT.measurableSet
    fun z hz => ?_
  simp [image_eq_zero_of_notMem_tsupport fun h => hz.2 ⟨h, hz.1⟩]

end MemLpLoc

/-! ### Locality and the sheaf property -/

section Locality

variable {X F : Type*} [TopologicalSpace X] [RegularSpace X] [MeasureSpace X]
  [NormedAddCommGroup F] {p : ℝ≥0∞} {U : Set X} {f : X → F}

/-- Local `Lᵖ` membership is a local property: it holds on `U` exactly when every point of `U`
has a neighbourhood within `U` on which it holds. -/
theorem memLpLoc_iff_locally :
    MemLpLoc p U f ↔ ∀ x ∈ U, ∃ V ∈ 𝓝[U] x, MemLpLoc p V f := by
  refine ⟨fun hf _ _ => ⟨U, self_mem_nhdsWithin, hf⟩, fun h K hKU hK => ?_⟩
  refine hK.induction_on (p := fun s => MemLp f p (volume.restrict s)) (by simp)
    (fun s t hst ht => ht.mono_measure (Measure.restrict_mono hst le_rfl))
    (fun s t hs ht => (hs.add_measure ht).mono_measure (Measure.restrict_union_le s t))
    fun x hx => ?_
  obtain ⟨V, hV, hfV⟩ := h x (hKU hx)
  obtain ⟨O, hO, hOV⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hV
  obtain ⟨C, hC, hCc, hCO⟩ := exists_mem_nhds_isClosed_subset hO
  exact ⟨K ∩ C, inter_mem_nhdsWithin K hC,
    hfV _ (fun z hz => hOV ⟨hCO hz.2, hKU hz.1⟩) (hK.inter_right hCc)⟩

/-- Local `Lᵖ` membership on `U` can be checked on the traces `U ∩ O i` of an open cover. -/
theorem memLpLoc_iff_forall_inter {ι : Type*} (O : ι → Opens X) (hU : U ⊆ ⋃ i, (O i : Set X)) :
    MemLpLoc p U f ↔ ∀ i, MemLpLoc p (U ∩ O i) f := by
  refine ⟨fun hf i => hf.mono_set inter_subset_left, fun h => memLpLoc_iff_locally.2 ?_⟩
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.1 (hU hx)
  exact ⟨U ∩ O i, inter_mem_nhdsWithin U ((O i).isOpen.mem_nhds hi), h i⟩

/-- **The sheaf property.** Local `Lᵖ` membership on the union of open sets is membership on each
of them. -/
theorem memLpLoc_iSup_iff {ι : Type*} (V : ι → Opens X) :
    MemLpLoc p (⨆ i, V i : Opens X) f ↔ ∀ i, MemLpLoc p (V i) f := by
  rw [memLpLoc_iff_forall_inter V (by simp)]
  simp only [Opens.coe_iSup, inter_eq_right.2 (subset_iUnion (fun i => (V i : Set X)) _)]

end Locality

/-- Local `Lᵖ` membership can be tested in the coordinates of any finite basis of the codomain.
No completeness of the codomain is needed. -/
theorem _root_.Module.Basis.memLpLoc_iff {X F ι : Type*} [TopologicalSpace X] [MeasureSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [Finite ι] {p : ℝ≥0∞} {U : Set X} {f : X → F}
    (b : Module.Basis ι ℝ F) :
    MemLpLoc p U f ↔ ∀ i, MemLpLoc p U (fun x => b.repr (f x) i) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : FiniteDimensional ℝ F := b.finiteDimensional_of_finite
  refine ⟨fun h i => h.clm_comp
    ((ContinuousLinearMap.proj i).comp b.equivFunL.toContinuousLinearMap), fun h => ?_⟩
  have hs : MemLpLoc p U (fun x => ∑ i, b.repr (f x) i • b i) :=
    MemLpLoc.sum Finset.univ fun i _ =>
      (h i).clm_comp ((ContinuousLinearMap.id ℝ ℝ).smulRight (b i))
  simpa only [b.sum_repr] using hs

/-! ### Independence of the Haar measure and linear changes of variables -/

section Haar

variable {E F : Type*} [NormedAddCommGroup F] {p : ℝ≥0∞}

/-- **Independence of the Haar measure.** On a locally compact second-countable topological
additive group whose `volume` is an additive Haar measure, local `Lᵖ` membership can be tested
with any other additive Haar measure `μ`. -/
theorem memLpLoc_iff_of_isAddHaarMeasure [AddGroup E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [LocallyCompactSpace E] [SecondCountableTopology E]
    [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
    (μ : Measure E) [μ.IsAddHaarMeasure] {U : Set E} {f : E → F} :
    MemLpLoc p U f ↔ ∀ K : Set E, K ⊆ U → IsCompact K → MemLp f p (μ.restrict K) := by
  refine ⟨fun h K hKU hK => ?_, fun h K hKU hK => ?_⟩
  · rw [Measure.isAddLeftInvariant_eq_smul μ volume, Measure.restrict_smul]
    exact (h K hKU hK).smul_measure ENNReal.coe_ne_top
  · rw [Measure.isAddLeftInvariant_eq_smul volume μ, Measure.restrict_smul]
    exact (h K hKU hK).smul_measure ENNReal.coe_ne_top

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]

/-- Precomposition with a continuous linear equivalence `e : E₁ ≃L[ℝ] E` of finite-dimensional
spaces with additive Haar measures carries local `Lᵖ` membership on `V` to local `Lᵖ`
membership on every `U` that `e` maps into `V`. -/
theorem MemLpLoc.comp_continuousLinearEquiv {E₁ : Type*} [NormedAddCommGroup E₁]
    [NormedSpace ℝ E₁] [MeasureSpace E₁] [BorelSpace E₁] [(volume : Measure E₁).IsAddHaarMeasure]
    {U : Set E₁} {V : Set E} {u : E → F} (hu : MemLpLoc p V u) (e : E₁ ≃L[ℝ] E)
    (hUV : MapsTo e U V) : MemLpLoc p U (u ∘ e) := by
  have : FiniteDimensional ℝ E₁ := e.symm.toLinearEquiv.finiteDimensional
  have : ((volume : Measure E₁).map e).IsAddHaarMeasure := e.isAddHaarMeasure_map volume
  have hemb : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  intro K hKU hK
  have h := (memLpLoc_iff_of_isAddHaarMeasure ((volume : Measure E₁).map e)).1 hu (e '' K)
    ((image_mono hKU).trans hUV.image_subset) (hK.image e.continuous)
  rwa [hemb.restrict_map, preimage_image_eq _ e.injective, hemb.memLp_map_measure_iff] at h

/-- **Linear changes of variables.** Precomposition with a continuous linear equivalence of
finite-dimensional spaces with additive Haar measures preserves and reflects local `Lᵖ`
membership. -/
@[simp]
theorem _root_.ContinuousLinearEquiv.memLpLoc_comp_iff {E₁ : Type*} [NormedAddCommGroup E₁]
    [NormedSpace ℝ E₁] [MeasureSpace E₁] [BorelSpace E₁] [(volume : Measure E₁).IsAddHaarMeasure]
    {V : Set E} {u : E → F} (e : E₁ ≃L[ℝ] E) :
    MemLpLoc p (e ⁻¹' V) (u ∘ e) ↔ MemLpLoc p V u := by
  have : FiniteDimensional ℝ E₁ := e.symm.toLinearEquiv.finiteDimensional
  refine ⟨fun h => ?_, fun h => h.comp_continuousLinearEquiv e (mapsTo_preimage e V)⟩
  simpa [Function.comp_def] using
    h.comp_continuousLinearEquiv e.symm fun y hy => by simpa using hy

end Haar

end TauCeti
