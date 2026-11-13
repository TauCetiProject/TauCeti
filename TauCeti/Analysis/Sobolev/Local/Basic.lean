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
import TauCeti.MeasureTheory.Function.LpSeminorm.ContinuousOn
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Local vector-valued Sobolev classes on planar domains

`TauCeti.MemLpLoc p U f` requires `Lᵖ` membership on every compact subset of `U`.
`TauCeti.MemWkpLoc p U k f` requires iterated weak derivatives through order `k` on
`interior U`, with `Lᵖ` bounds on every compact subset of `U` itself. For half-discs these
bounds reach the real axis, while test functions stay in the interior. On open sets this is
the usual local Sobolev class. Derivatives take values in iterated continuous linear maps,
rather than scalar jets.
These predicates concern actual functions; almost-everywhere changes do not affect membership.
They impose no global integrability condition on the possibly unbounded domain.
Global `Lᵖ` membership on a set implies local membership there (`MeasureTheory.MemLp.memLpLoc`).

This file supplies restriction to arbitrary subsets, linearity, continuous-linear composition,
pairing of fields of continuous linear maps into product maps,
multiplication of local `Lᵖ` functions by continuous factors (with extension by zero for factors
supported in the domain), composition of local `Lᵖ` operator families with continuous ones,
application of local `Lᵖ` or continuous operator families to local `L^q` fields by Hölder's
inequality (`TauCeti.MemLpLoc.clm_apply`, `TauCeti.MemLpLoc.continuousOn_clm_apply`),
pairing, pointwise product maps of operator fields, decreasing the integrability exponent, and
decreasing the derivative order. On an open set, local `Lᵖ` membership is detected on the open
subsets with compact closure inside it.
Smoothness on an open neighbourhood gives membership, without requiring a global smooth extension,
and smooth maps on the whole plane are in every class on every set.
Conversely, if `g` is `Cᵏ` on an open set `Ω` and agrees almost everywhere there with
`u ∈ MemWkpLoc p Ω (k + m)`, then `fderiv ℝ g` is a weak derivative of `u`
(`TauCeti.MemWkpLoc.hasWeakFDerivOn_fderiv_of_contDiffOn`, for `k ≥ 1`) and
`iteratedFDeriv ℝ k g ∈ MemWkpLoc p Ω m` (`TauCeti.MemWkpLoc.iteratedFDeriv_of_contDiffOn`).
On a relatively open subset `Ω ∩ {0 ≤ im}` of the closed upper half-plane the interior is
`Ω ∩ {0 < im}` (`TauCeti.interior_inter_setOf_im_nonneg`), and since the real axis is null, local
`Lᵖ` membership there is detected on the upper halves `W ∩ {0 < im}`
(`TopologicalSpace.Opens.upperHalf`) of the open `W` with compact closure inside `Ω`
(`TauCeti.memLpLoc_inter_setOf_im_nonneg_iff`). No boundary trace is asserted here;
extension across the real axis is in `TauCeti.Analysis.Sobolev.Local.Reflection`. On open
domains, local `L¹` membership is identified with local integrability, supplying the native
weak-derivative hypotheses.
There, with `1 ≤ p`, a locally `Lᵖ` function agrees almost everywhere with its precise
representative, and every weak derivative of a member of `MemWkpLoc p Ω (k + 1)` is in
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
-/

public noncomputable section

open MeasureTheory TopologicalSpace

namespace TauCeti

variable {F G : Type*} [NormedAddCommGroup F] [NormedAddCommGroup G]
  {p q : ENNReal} {U V : Set ℂ} {f g : ℂ → F}

/-- A function is locally `Lᵖ` on `U` when it belongs to `Lᵖ` on every compact subset of `U`.
On a set reaching the real axis, those compact subsets include the boundary. -/
def MemLpLoc (p : ENNReal) (U : Set ℂ) (f : ℂ → F) : Prop :=
  ∀ K : Set ℂ, K ⊆ U → IsCompact K → MemLp f p (volume.restrict K)

/-- Local `Lᵖ` membership is characterized by `Lᵖ` membership on every compact subset. -/
theorem memLpLoc_iff : MemLpLoc p U f ↔
    ∀ K : Set ℂ, K ⊆ U → IsCompact K → MemLp f p (volume.restrict K) := Iff.rfl

/-- Local integrability restricts to any smaller set. -/
theorem MemLpLoc.mono_set (hf : MemLpLoc p U f) (hVU : V ⊆ U) : MemLpLoc p V f :=
  fun K hK hc => hf K (hK.trans hVU) hc

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

/-- The zero function belongs to every local `Lᵖ` class. -/
@[simp]
theorem memLpLoc_zero : MemLpLoc p U (0 : ℂ → F) := fun _ _ _ => MemLp.zero

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
theorem MemLpLoc.mono_exponent (hf : MemLpLoc p U f) (hqp : q ≤ p) : MemLpLoc q U f := by
  intro K hK hc
  have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hc.measure_lt_top⟩
  exact (hf K hK hc).mono_exponent hqp

/-- A function continuous on `U` is locally `Lᵖ` there, with no global bound required. -/
theorem _root_.ContinuousOn.memLpLoc (hf : ContinuousOn f U) : MemLpLoc p U f :=
  fun _K hK hc => (hf.mono hK).memLp_restrict_of_subset_isCompact
    hc hc.measurableSet subset_rfl p

/-- Every constant function is locally `Lᵖ` for all exponents, including infinity. -/
@[simp]
theorem memLpLoc_const (c : F) : MemLpLoc p U (fun _ => c) :=
  continuousOn_const.memLpLoc

/-- A locally `Lᵖ` function on a locally closed set is locally integrable when `1 ≤ p`.
This supplies the local integrability hypothesis used by the weak-derivative API. -/
theorem MemLpLoc.locallyIntegrableOn (hf : MemLpLoc p U f) (hp : 1 ≤ p) (hU : IsLocallyClosed U) :
    LocallyIntegrableOn f U volume :=
  (locallyIntegrableOn_iff hU).2 fun K hK hc =>
    memLp_one_iff_integrable.1 ((hf.mono_exponent hp) K hK hc)

/-- On a locally closed set, local `L¹` membership is exactly local integrability. -/
theorem memLpLoc_one_iff_locallyIntegrableOn (hU : IsLocallyClosed U) :
    MemLpLoc 1 U f ↔ LocallyIntegrableOn f U volume :=
  ⟨fun hf => hf.locallyIntegrableOn le_rfl hU,
    fun hf _K hK hc => memLp_one_iff_integrable.2 (hf.integrableOn_compact_subset hK hc)⟩

/-- A finite sum of locally `Lᵖ` functions is locally `Lᵖ`, without a completeness assumption. -/
theorem MemLpLoc.sum {ι : Type*} (s : Finset ι) {f : ι → ℂ → F}
    (hf : ∀ i ∈ s, MemLpLoc p U (f i)) : MemLpLoc p U (fun z => ∑ i ∈ s, f i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty, Pi.zero_def] using (memLpLoc_zero (p := p) (U := U))
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi, Pi.add_def] using
      (hf i (Finset.mem_insert_self i s)).add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- Local `Lᵖ` membership on `U` gives `Lᵖ` membership on every set whose closure is compact and
contained in `U`. -/
theorem MemLpLoc.memLp_restrict_of_isCompact_closure (hf : MemLpLoc p U f) {W : Set ℂ}
    (hWc : IsCompact (closure W)) (hWU : closure W ⊆ U) : MemLp f p (volume.restrict W) :=
  (hf _ hWU hWc).mono_measure (Measure.restrict_mono subset_closure le_rfl)

/-- On an open set `Ω`, a function that agrees almost everywhere with an `Lᵖ` function on every
open `W` whose closure is compact and contained in `Ω` is locally `Lᵖ` on `Ω`. -/
theorem memLpLoc_of_forall_opens {Ω : Opens ℂ}
    (h : ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
      ∃ g : ℂ → F, MemLp g p (volume.restrict (W : Set ℂ)) ∧ g =ᵐ[volume.restrict W] f) :
    MemLpLoc p Ω f := by
  refine fun K hKΩ hK => ?_
  obtain ⟨W, hWo, hKW, hWΩ, hWc⟩ := exists_open_between_and_isCompact_closure hK Ω.isOpen hKΩ
  obtain ⟨g, hg, hgf⟩ := h ⟨W, hWo⟩ hWc hWΩ
  exact (hg.ae_eq hgf).mono_measure (Measure.restrict_mono hKW le_rfl)

/-- A function that is `Lᵖ` on a set `W` is locally `Lᵖ` on every set `U` contained in `W` up to a
null set, including on compact subsets of `U` that leave `W`. -/
theorem _root_.MeasureTheory.MemLp.memLpLoc_of_ae_le {W : Set ℂ}
    (hf : MemLp f p (volume.restrict W)) (hUW : U ≤ᵐ[volume] W) : MemLpLoc p U f :=
  memLpLoc_iff.2 fun _ hK _ => hf.mono_measure
    (Measure.restrict_mono_ae ((Filter.EventuallySubset.of_subset hK).trans hUW))

/-- **Local `Lᵖ` on a half-disc through upper halves.** A function is locally `Lᵖ` on
`Ω ∩ {0 ≤ im}`, up to the real axis, exactly when it is `Lᵖ` on the upper half `W ∩ {0 < im}` of
every open `W` whose closure is compact and contained in `Ω`. The real axis is null, so the
compact sets reaching it see no more than these upper halves. -/
theorem memLpLoc_inter_setOf_im_nonneg_iff {Ω : Opens ℂ} :
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

/-- Pairing two locally `Lᵖ` fields of continuous linear maps into their product map preserves
local `Lᵖ` membership. -/
theorem MemLpLoc.clm_prod {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : ℂ → E →L[ℝ] F} {B : ℂ → E →L[ℝ] G} (hA : MemLpLoc p U A) (hB : MemLpLoc p U B) :
    MemLpLoc p U (fun z => (A z).prod (B z)) := by
  convert (hA.clm_comp (ContinuousLinearMap.compL ℝ E F (F × G)
    (ContinuousLinearMap.inl ℝ F G))).add
      (hB.clm_comp (ContinuousLinearMap.compL ℝ E G (F × G) (ContinuousLinearMap.inr ℝ F G)))
    using 1
  funext z
  ext v <;> simp

/-- Composing a locally `Lᵖ` operator family on the left with one continuous on `U` preserves
local `Lᵖ` membership, since the continuous factor is bounded on every compact subset of `U`. -/
theorem MemLpLoc.continuousOn_clm_comp {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {A : ℂ → G →L[ℝ] H} {B : ℂ → F →L[ℝ] G} (hB : MemLpLoc p U B) (hA : ContinuousOn A U) :
    MemLpLoc p U (fun z => A z ∘L B z) :=
  memLpLoc_iff.2 fun K hKU hK => (memLpLoc_iff.1 hB K hKU hK).clm_comp_of_continuousOn
    (hA.mono hKU) hK hK.measurableSet subset_rfl

/-- Composing a locally `Lᵖ` operator family on the right with one continuous on `U` preserves
local `Lᵖ` membership, since the continuous factor is bounded on every compact subset of `U`. -/
theorem MemLpLoc.clm_comp_continuousOn {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {B : ℂ → G →L[ℝ] H} {E : ℂ → F →L[ℝ] G} (hB : MemLpLoc p U B) (hE : ContinuousOn E U) :
    MemLpLoc p U (fun z => B z ∘L E z) :=
  memLpLoc_iff.2 fun K hKU hK => (ContinuousLinearMap.compL ℝ F G H).memLp_of_bilin p
    (memLpLoc_iff.1 hB K hKU hK)
    ((hE.mono hKU).memLp_top_restrict_of_subset_isCompact hK hK.measurableSet subset_rfl)

/-- **Hölder's inequality on compact subsets**: a locally `Lᵖ` field of continuous linear maps
applied to a locally `L^q` field is locally `Lʳ` when `1/p + 1/q ≤ 1/r`. -/
theorem MemLpLoc.clm_apply {r : ENNReal} {A : ℂ → F →L[ℝ] G} {w : ℂ → F} (hA : MemLpLoc p U A)
    (hw : MemLpLoc q U w) (hpqr : p⁻¹ + q⁻¹ ≤ r⁻¹) : MemLpLoc r U (fun z => A z (w z)) := by
  have : ENNReal.HolderTriple p q (p⁻¹ + q⁻¹)⁻¹ := ⟨(inv_inv _).symm⟩
  exact MemLpLoc.mono_exponent (p := (p⁻¹ + q⁻¹)⁻¹)
    (fun K hK hc => (ContinuousLinearMap.id ℝ (F →L[ℝ] G)).memLp_of_bilin _ (hA K hK hc)
      (hw K hK hc))
    (ENNReal.inv_le_inv.1 (by rwa [inv_inv]))

/-- **Hölder's inequality on compact subsets**: a locally `Lᵖ` field of continuous linear maps
applied to a locally `L^q` field is locally integrable on a locally closed set when
`1/p + 1/q ≤ 1`. -/
theorem MemLpLoc.locallyIntegrableOn_clm_apply {A : ℂ → F →L[ℝ] G} {w : ℂ → F}
    (hA : MemLpLoc p U A) (hw : MemLpLoc q U w) (hpq : p⁻¹ + q⁻¹ ≤ 1)
    (hU : IsLocallyClosed U) : LocallyIntegrableOn (fun z => A z (w z)) U volume :=
  (hA.clm_apply hw (r := 1) (by rwa [inv_one])).locallyIntegrableOn le_rfl hU

/-- A field of continuous linear maps continuous on `U`, applied to a locally `Lᵖ` field, is
locally `Lᵖ`, since the continuous factor is bounded on every compact subset of `U`. -/
theorem MemLpLoc.continuousOn_clm_apply {A : ℂ → F →L[ℝ] G} {w : ℂ → F} (hw : MemLpLoc p U w)
    (hA : ContinuousOn A U) : MemLpLoc p U (fun z => A z (w z)) :=
  (hA.memLpLoc (p := ⊤)).clm_apply hw (by simp)

open TauCeti.MeasureTheory in
/-- A locally `Lᵖ` function on an open set `Ω`, with `1 ≤ p`, agrees almost everywhere on `Ω` with
its precise representative. -/
theorem MemLpLoc.ae_eq_preciseRepresentative [CompleteSpace F] {Ω : Opens ℂ} (hp : 1 ≤ p)
    (hu : MemLpLoc p Ω f) : f =ᵐ[volume.restrict Ω] preciseRepresentative volume f :=
  ae_eq_restrict_preciseRepresentative Ω.isOpen
    (hu.locallyIntegrableOn hp Ω.isOpen.isLocallyClosed)

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
theorem MemLpLoc.continuousOn_smul {χ : ℂ → ℝ} (hf : MemLpLoc p U f) (hχ : ContinuousOn χ U) :
    MemLpLoc p U (fun z => χ z • f z) :=
  memLpLoc_iff.2 fun K hK hc =>
    (memLpLoc_iff.1 (hχ.memLpLoc (p := ⊤)) K hK hc).smul (memLpLoc_iff.1 hf K hK hc)

/-- A locally `Lᵖ` field of continuous linear maps applied to a map continuous on `U` is locally
`Lᵖ` on `U`, since the map is bounded on every compact subset of `U`. -/
theorem MemLpLoc.clm_apply_continuousOn {A : ℂ → F →L[ℝ] G} (hA : MemLpLoc p U A)
    (hf : ContinuousOn f U) : MemLpLoc p U (fun z => A z (f z)) :=
  hA.clm_apply (hf.memLpLoc (p := ⊤)) (by simp)

/-- A continuous factor supported in `U` extends a local `Lᵖ` function on `U` by zero to a local
`Lᵖ` function on the whole plane: on a compact set `K` the product only sees
`K ∩ tsupport χ`, a compact subset of `U`. -/
theorem MemLpLoc.continuous_smul_of_tsupport_subset {χ : ℂ → ℝ} (hf : MemLpLoc p U f)
    (hχ : Continuous χ) (hsupp : tsupport χ ⊆ U) : MemLpLoc p Set.univ (fun z => χ z • f z) := by
  have hT := hf.continuousOn_smul hχ.continuousOn
  have hcl : IsClosed (tsupport χ) := isClosed_tsupport χ
  refine memLpLoc_iff.2 fun K _ hK => ?_
  have heq : (fun z => χ z • f z) = (tsupport χ).indicator (fun z => χ z • f z) := by
    refine (Set.indicator_eq_self.2 ?_).symm
    exact (Function.support_smul_subset_left χ f).trans (subset_tsupport χ)
  rw [heq, memLp_indicator_iff_restrict hcl.measurableSet.nullMeasurableSet,
    Measure.restrict_restrict hcl.measurableSet]
  exact memLpLoc_iff.1 hT _ (Set.inter_subset_left.trans hsupp) (hK.inter_left hcl)

/-- The iterated weak derivatives through order `k` exist on `interior U` and are `Lᵖ` on
every compact subset of `U`, including compact sets reaching its boundary.
The first derivative takes values in `ℂ →L[ℝ] F`; higher derivatives iterate this construction.
No integrability at infinity or boundary trace is required. -/
def MemWkpLoc (p : ENNReal) (U : Set ℂ) :
    (k : ℕ) → {F : Type*} → [NormedAddCommGroup F] → [NormedSpace ℝ F] → (ℂ → F) → Prop
  | 0, _, _, _, f => MemLpLoc p U f
  | k + 1, F, _, _, f => MemLpLoc p U f ∧
      ∃ D : ℂ → ℂ →L[ℝ] F, HasWeakFDerivOn volume (Opens.interior U) f D ∧ MemWkpLoc p U k D

/-- A continuous compactly supported factor whose support meets the closed set `T` inside `S`
makes a function in `MemLpLoc 1 S` integrable on `T`, even though `T` may be unbounded or leave
`S`. -/
theorem MemLpLoc.integrableOn_smul {S T : Set ℂ} {h : ℂ → F} (hh : MemLpLoc 1 S h)
    {f : ℂ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) (hT : IsClosed T)
    (hfS : tsupport f ∩ T ⊆ S) : IntegrableOn (fun z => f z • h z) T := by
  have hK : IsCompact (tsupport f ∩ T) := hfc.isCompact.inter_right hT
  have hhK : IntegrableOn h (tsupport f ∩ T) :=
    memLp_one_iff_integrable.1 (hh _ hfS hK)
  refine (hhK.continuousOn_smul hf.continuousOn hK).of_forall_sdiff_eq_zero hT.measurableSet
    fun z hz => ?_
  simp [image_eq_zero_of_notMem_tsupport fun h => hz.2 ⟨h, hz.1⟩]

variable {Ω : Opens ℂ} {k l : ℕ}

/-- At order zero the local Sobolev class is exactly the local `Lᵖ` class. -/
@[simp]
theorem memWkpLoc_zero_iff : MemWkpLoc p U 0 f ↔ MemLpLoc p U f := Iff.rfl

/-- The successor-order characterization supplies a weak derivative in the preceding class. -/
theorem memWkpLoc_succ_iff : MemWkpLoc p U (k + 1) f ↔ MemLpLoc p U f ∧
    ∃ D : ℂ → ℂ →L[ℝ] F, HasWeakFDerivOn volume (Opens.interior U) f D ∧
      MemWkpLoc p U k D := Iff.rfl

/-- On an open domain, the successor-order weak derivative is tested on the domain itself. -/
theorem memWkpLoc_succ_iff_of_isOpen : MemWkpLoc p Ω (k + 1) f ↔ MemLpLoc p Ω f ∧
    ∃ D : ℂ → ℂ →L[ℝ] F, HasWeakFDerivOn volume Ω f D ∧ MemWkpLoc p Ω k D := by
  simp only [memWkpLoc_succ_iff, Opens.interior_coe]

/-- Every local Sobolev function is locally `Lᵖ`. -/
theorem MemWkpLoc.memLpLoc (hf : MemWkpLoc p U k f) : MemLpLoc p U f := by
  cases k with
  | zero => exact hf
  | succ k => exact hf.1

/-- A positive-order local Sobolev function has a weak derivative of the preceding order. -/
theorem MemWkpLoc.exists_weakFDeriv (hf : MemWkpLoc p U (k + 1) f) :
    ∃ D : ℂ → ℂ →L[ℝ] F, HasWeakFDerivOn volume (Opens.interior U) f D ∧
      MemWkpLoc p U k D := hf.2

/-- On an open domain, positive-order membership gives a weak derivative on that domain. -/
theorem MemWkpLoc.exists_weakFDeriv_of_isOpen (hf : MemWkpLoc p Ω (k + 1) f) :
    ∃ D : ℂ → ℂ →L[ℝ] F, HasWeakFDerivOn volume Ω f D ∧ MemWkpLoc p Ω k D :=
  (memWkpLoc_succ_iff_of_isOpen.mp hf).2

/-- Positive-order membership retains the completeness required by weak derivatives. -/
theorem MemWkpLoc.completeSpace (hf : MemWkpLoc p U (k + 1) f) : CompleteSpace F := by
  obtain ⟨D, hD, _⟩ := hf.exists_weakFDeriv
  exact hD.completeSpace

/-- Restriction preserves the interior weak derivatives and the bounds on compact subsets. -/
theorem MemWkpLoc.mono (hf : MemWkpLoc p U k f) (hVU : V ⊆ U) :
    MemWkpLoc p V k f := by
  induction k generalizing F with
  | zero => exact hf.mono_set hVU
  | succ k ih =>
    obtain ⟨hp, D, hD, hk⟩ := hf
    exact ⟨hp.mono_set hVU, D, hD.mono (interior_mono hVU), ih hk⟩

/-- Almost-everywhere changes of the function preserve its local Sobolev class. -/
theorem MemWkpLoc.congr_ae (hf : MemWkpLoc p U k f)
    (hfg : f =ᵐ[volume.restrict U] g) : MemWkpLoc p U k g := by
  cases k with
  | zero => exact hf.congr_ae hfg
  | succ k =>
    obtain ⟨hp, D, hD, hk⟩ := hf
    exact ⟨hp.congr_ae hfg, D,
      hD.congr_ae (ae_mono (Measure.restrict_mono_set volume interior_subset) hfg), hk⟩

/-- On a measurable set, the local Sobolev class only depends on the values on that set. -/
theorem MemWkpLoc.congr_fun (hf : MemWkpLoc p U k f) (hfg : Set.EqOn f g U)
    (hU : MeasurableSet U) : MemWkpLoc p U k g :=
  hf.congr_ae ((ae_restrict_mem hU).mono hfg)

/-- Every weak derivative of a member of `MemWkpLoc p Ω (k + 1)` is in `MemWkpLoc p Ω k`, not only
the one supplied by the definition: weak derivatives are unique almost everywhere. -/
theorem MemWkpLoc.memWkpLoc_of_hasWeakFDerivOn (hf : MemWkpLoc p Ω (k + 1) f)
    {D : ℂ → ℂ →L[ℝ] F} (hD : HasWeakFDerivOn volume Ω f D) : MemWkpLoc p Ω k D := by
  obtain ⟨D', hD', hD'k⟩ := hf.exists_weakFDeriv_of_isOpen
  exact hD'k.congr_ae (hD'.ae_eq hD)

/-- Every weak derivative of a member of `MemWkpLoc p Ω 1` is locally `Lᵖ` on `Ω`, not only the
one supplied by the definition: weak derivatives are unique almost everywhere. -/
theorem MemWkpLoc.memLpLoc_of_hasWeakFDerivOn (hf : MemWkpLoc p Ω 1 f)
    {D : ℂ → ℂ →L[ℝ] F} (hD : HasWeakFDerivOn volume Ω f D) : MemLpLoc p Ω D :=
  memWkpLoc_zero_iff.1 (hf.memWkpLoc_of_hasWeakFDerivOn hD)

/-- Decreasing the integrability exponent preserves each local derivative order. -/
theorem MemWkpLoc.mono_exponent (hf : MemWkpLoc p U k f) (hqp : q ≤ p) :
    MemWkpLoc q U k f := by
  induction k generalizing F with
  | zero => exact hf.mono_exponent hqp
  | succ k ih =>
    obtain ⟨hp, D, hD, hk⟩ := hf
    exact ⟨hp.mono_exponent hqp, D, hD, ih hk⟩

/-- Dropping the top derivative preserves local Sobolev membership. -/
theorem MemWkpLoc.of_succ (hf : MemWkpLoc p U (k + 1) f) : MemWkpLoc p U k f := by
  induction k generalizing F with
  | zero => exact hf.1
  | succ k ih =>
    obtain ⟨hp, D, hD, hk⟩ := hf
    exact ⟨hp, D, hD, ih hk⟩

/-- Membership at any smaller derivative order follows from membership at a larger one. -/
theorem MemWkpLoc.of_le (hf : MemWkpLoc p U k f) (hlk : l ≤ k) : MemWkpLoc p U l f := by
  induction hlk with
  | refl => exact hf
  | step _ ih => exact ih hf.of_succ

/-- The zero function lies in every local Sobolev class with complete codomain. -/
@[simp]
theorem memWkpLoc_zero_fun [CompleteSpace F] : MemWkpLoc p U k (0 : ℂ → F) := by
  induction k generalizing F with
  | zero => exact memLpLoc_zero
  | succ k ih => exact ⟨memLpLoc_zero, 0, hasWeakFDerivOn_zero, ih⟩

/-- Local Sobolev membership is closed under addition. -/
theorem MemWkpLoc.add (hf : MemWkpLoc p U k f) (hg : MemWkpLoc p U k g) :
    MemWkpLoc p U k (f + g) := by
  induction k generalizing F with
  | zero => exact hf.add hg
  | succ k ih =>
    obtain ⟨hp, D, hD, hk⟩ := hf
    obtain ⟨hq, D', hD', hk'⟩ := hg
    exact ⟨hp.add hq, D + D', hD.add hD', ih hk hk'⟩

/-- Local Sobolev membership is closed under negation. -/
theorem MemWkpLoc.neg (hf : MemWkpLoc p U k f) : MemWkpLoc p U k (-f) := by
  induction k generalizing F with
  | zero => exact hf.neg
  | succ k ih =>
    obtain ⟨hp, D, hD, hk⟩ := hf
    exact ⟨hp.neg, -D, hD.neg, ih hk⟩

/-- Local Sobolev membership is closed under subtraction. -/
theorem MemWkpLoc.sub (hf : MemWkpLoc p U k f) (hg : MemWkpLoc p U k g) :
    MemWkpLoc p U k (f - g) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- Real scalar multiplication preserves local Sobolev membership. -/
theorem MemWkpLoc.const_smul (hf : MemWkpLoc p U k f) (c : ℝ) :
    MemWkpLoc p U k (c • f) := by
  induction k generalizing F with
  | zero => exact hf.const_smul c
  | succ k ih =>
    obtain ⟨hp, D, hD, hk⟩ := hf
    exact ⟨hp.const_smul c, c • D, hD.const_smul c, ih hk⟩

/-- Continuous linear maps of the codomain preserve all local weak derivative orders. -/
theorem MemWkpLoc.clm_comp [CompleteSpace G] (hf : MemWkpLoc p U k f)
    (A : F →L[ℝ] G) : MemWkpLoc p U k (fun z => A (f z)) := by
  induction k generalizing F G with
  | zero => exact hf.clm_comp A
  | succ k ih =>
    obtain ⟨hp, D, hD, hk⟩ := hf
    exact ⟨hp.clm_comp A, fun z => A.comp (D z), hD.clm_comp A,
      ih hk ((ContinuousLinearMap.compL ℝ ℂ F G) A)⟩

/-- **Pairs of local Sobolev maps.** Two maps in the local Sobolev class of order `k` pair to a map
in the same class, with values in the product. -/
theorem MemWkpLoc.prodMk [CompleteSpace F] [CompleteSpace G] {g : ℂ → G}
    (hf : MemWkpLoc p U k f) (hg : MemWkpLoc p U k g) :
    MemWkpLoc p U k (fun z => (f z, g z)) := by
  have h := (hf.clm_comp (ContinuousLinearMap.inl ℝ F G)).add
    (hg.clm_comp (ContinuousLinearMap.inr ℝ F G))
  convert h using 1
  ext z <;> simp

/-- **Products of operator fields.** If two fields of continuous linear maps are in the local
Sobolev class of order `k`, so is their pointwise product map `(A z).prodMap (B z)`. -/
theorem MemWkpLoc.prodMap {E₁ E₂ E₃ E₄ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [CompleteSpace E₂] [NormedAddCommGroup E₃]
    [NormedSpace ℝ E₃] [NormedAddCommGroup E₄] [NormedSpace ℝ E₄] [CompleteSpace E₄]
    {A : ℂ → E₁ →L[ℝ] E₂} {B : ℂ → E₃ →L[ℝ] E₄} (hA : MemWkpLoc p U k A)
    (hB : MemWkpLoc p U k B) : MemWkpLoc p U k (fun z => (A z).prodMap (B z)) := by
  simpa using (hA.prodMk hB).clm_comp (ContinuousLinearMap.prodMapL ℝ E₁ E₂ E₃ E₄)

/-- A continuous linear change of codomain preserves and reflects every local weak
Sobolev order. -/
@[simp]
theorem _root_.ContinuousLinearEquiv.comp_memWkpLoc_iff (e : F ≃L[ℝ] G) :
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
theorem memWkpLoc_const [CompleteSpace F] (c : F) : MemWkpLoc p U k (fun _ => c) := by
  cases k with
  | zero => exact memLpLoc_const c
  | succ k =>
    refine ⟨memLpLoc_const c, 0, ?_, memWkpLoc_zero_fun⟩
    apply hasWeakFDerivOn_iff.mpr
    exact fun v => hasWeakLineDerivOn_const (μ := volume) (Ω := Opens.interior U) (v := v) c

/-- Finite sums of local Sobolev functions remain in the same class. -/
theorem MemWkpLoc.sum {ι : Type*} [CompleteSpace F] (s : Finset ι)
    {f : ι → ℂ → F} (hf : ∀ i ∈ s, MemWkpLoc p U k (f i)) :
    MemWkpLoc p U k (fun z => ∑ i ∈ s, f i z) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty, Pi.zero_def] using
      (memWkpLoc_zero_fun (p := p) (U := U) (k := k) (F := F))
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi, Pi.add_def] using
      (hf i (Finset.mem_insert_self i s)).add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- A map that is `Cᵏ` on an open neighbourhood of `U` has locally `Lᵖ` weak derivatives
through order `k` on `U`, with bounds reaching its boundary, for every exponent. -/
theorem _root_.ContDiffOn.memWkpLoc [CompleteSpace F]
    (hf : ContDiffOn ℝ k f (Ω : Set ℂ)) (hU : U ⊆ Ω) : MemWkpLoc p U k f := by
  induction k generalizing F with
  | zero => exact (hf.continuousOn.mono hU).memLpLoc
  | succ k ih =>
    have hD : ContDiffOn ℝ k (fderiv ℝ f) (Ω : Set ℂ) :=
      hf.fderiv_of_isOpen Ω.isOpen (by simp)
    refine ⟨(hf.continuousOn.mono hU).memLpLoc, fderiv ℝ f, ?_, ih hD⟩
    exact (hf.of_le (by simp)).hasWeakFDerivOn_fderiv.mono (interior_subset.trans hU)

/-- A `Cᵏ` map on the whole plane is in the local class `W^{k,p}` on every set, for every
exponent. -/
theorem _root_.ContDiff.memWkpLoc [CompleteSpace F] (hf : ContDiff ℝ k f) :
    MemWkpLoc p U k f :=
  hf.contDiffOn.memWkpLoc (Ω := ⊤) ((Set.subset_univ U).trans_eq Opens.coe_top.symm)

/-! ### Bounds for chains of weak derivatives -/

section WeakDerivChainLe

/-- `WeakDerivChainLe p S T C m f g` bounds the iterated weak derivatives of `f` through order `m`
by those of `g`: the `Lᵖ(S)` norm of `f` is at most `C` times the `Lᵖ(T)` norm of `g`, and for
every weak derivative `Df` of `f` on the interior of `S` and every weak derivative `Dg` of `g` on
the interior of `T`, the pair `Df`, `Dg` satisfies the same through order `m - 1`. Since the
quantification is over all weak derivatives, the bound holds for every choice of the iterated
derivatives `D^i f` and `D^i g`, `i ≤ m`. -/
def WeakDerivChainLe (p : ENNReal) (S T : Set ℂ) (C : ENNReal) :
    (m : ℕ) → {F : Type*} → [NormedAddCommGroup F] → [NormedSpace ℝ F] → (ℂ → F) → (ℂ → F) →
      Prop
  | 0, _, _, _, f, g => eLpNorm f p (volume.restrict S) ≤ C * eLpNorm g p (volume.restrict T)
  | m + 1, F, _, _, f, g =>
      eLpNorm f p (volume.restrict S) ≤ C * eLpNorm g p (volume.restrict T) ∧
        ∀ Df Dg : ℂ → ℂ →L[ℝ] F, HasWeakFDerivOn volume (Opens.interior S) f Df →
          HasWeakFDerivOn volume (Opens.interior T) g Dg → WeakDerivChainLe p S T C m Df Dg

variable {C : ENNReal} {S T : Set ℂ} {m : ℕ}

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
        ∀ Df Dg : ℂ → ℂ →L[ℝ] F, HasWeakFDerivOn volume (Opens.interior S) f Df →
          HasWeakFDerivOn volume (Opens.interior T) g Dg → WeakDerivChainLe p S T C m Df Dg :=
  Iff.rfl

/-- A chain bound gives the `Lᵖ` bound at order zero. -/
theorem WeakDerivChainLe.eLpNorm_le (h : WeakDerivChainLe p S T C m f g) :
    eLpNorm f p (volume.restrict S) ≤ C * eLpNorm g p (volume.restrict T) := by
  cases m with
  | zero => exact h
  | succ m => exact h.1

/-- A chain bound passes to every pair of weak derivatives, one order lower. -/
theorem WeakDerivChainLe.weakFDeriv (h : WeakDerivChainLe p S T C (m + 1) f g)
    {Df Dg : ℂ → ℂ →L[ℝ] F} (hf : HasWeakFDerivOn volume (Opens.interior S) f Df)
    (hg : HasWeakFDerivOn volume (Opens.interior T) g Dg) : WeakDerivChainLe p S T C m Df Dg :=
  h.2 Df Dg hf hg

end WeakDerivChainLe

/-! ### Classical derivatives of `Cᵏ` representatives -/

variable {m : ℕ} {u : ℂ → F}

/-- **The derivative of a `C¹` representative is a weak derivative.** If `g` is `C¹` on `Ω` and
agrees almost everywhere on `Ω` with `u ∈ MemWkpLoc p Ω (k + 1)`, then `fderiv ℝ g` is a weak
derivative of `u` on `Ω` and lies in `MemWkpLoc p Ω k`. By uniqueness of weak derivatives
(`TauCeti.HasWeakFDerivOn.ae_eq`), every weak derivative of `u` on `Ω` agrees with `fderiv ℝ g`
almost everywhere on `Ω`. -/
theorem MemWkpLoc.hasWeakFDerivOn_fderiv_of_contDiffOn (hu : MemWkpLoc p Ω (k + 1) u)
    (hg : ContDiffOn ℝ 1 g Ω) (hug : u =ᵐ[volume.restrict Ω] g) :
    HasWeakFDerivOn volume Ω u (fderiv ℝ g) ∧ MemWkpLoc p Ω k (fderiv ℝ g) := by
  have := hu.completeSpace
  have hg' : HasWeakFDerivOn volume Ω g (fderiv ℝ g) := hg.hasWeakFDerivOn_fderiv
  obtain ⟨D, hD, hDk⟩ := hu.exists_weakFDeriv_of_isOpen
  exact ⟨hg'.congr_ae hug.symm, hDk.congr_ae ((hD.congr_ae hug).ae_eq hg')⟩

/-- **Iterated derivatives of a `Cᵏ` representative.** If `g` is `Cᵏ` on `Ω` and agrees almost
everywhere on `Ω` with `u ∈ MemWkpLoc p Ω (k + m)`, then `iteratedFDeriv ℝ k g` lies in
`MemWkpLoc p Ω m`. No restriction on `p` is needed. -/
theorem MemWkpLoc.iteratedFDeriv_of_contDiffOn (hu : MemWkpLoc p Ω (k + m) u)
    (hg : ContDiffOn ℝ k g Ω) (hug : u =ᵐ[volume.restrict Ω] g) :
    MemWkpLoc p Ω m (iteratedFDeriv ℝ k g) := by
  induction k generalizing F with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp]
    exact (continuousMultilinearCurryFin0 ℝ ℂ F).symm.toContinuousLinearEquiv.comp_memWkpLoc_iff.2
      ((Nat.zero_add m ▸ hu).congr_ae hug)
  | succ k ih =>
    rw [Nat.add_right_comm] at hu
    obtain ⟨-, hDk⟩ := hu.hasWeakFDerivOn_fderiv_of_contDiffOn
      (hg.of_le (by exact_mod_cast Nat.le_add_left 1 k)) hug
    have hgk : ContDiffOn ℝ k (fderiv ℝ g) Ω := hg.fderiv_of_isOpen Ω.isOpen (by push_cast; rfl)
    have h := ih hDk hgk (Filter.EventuallyEq.refl _ _)
    have heq : iteratedFDeriv ℝ (k + 1) g =
        fun z => (continuousMultilinearCurryRightEquiv' ℝ k ℂ F).symm
          (iteratedFDeriv ℝ k (fderiv ℝ g) z) := by
      ext1 z
      exact iteratedFDeriv_succ_eq_comp_right
    rw [heq]
    exact (continuousMultilinearCurryRightEquiv' ℝ k ℂ F).symm.toContinuousLinearEquiv
      |>.comp_memWkpLoc_iff.2 h

end TauCeti
