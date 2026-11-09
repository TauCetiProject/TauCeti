/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import TauCeti.MeasureTheory.Function.StronglyMeasurable.Caratheodory
public import TauCeti.Topology.VectorBundle.OrthonormalFrame.Basic
public import TauCeti.Topology.VectorBundle.Section
public import TauCeti.Topology.FiberBundle.Countable

/-!
# Almost everywhere strongly measurable sections of vector bundles

Let `E → B` be a topological vector bundle over `𝕜` with model fibre `F`, over a base carrying a
measure `μ` on its Borel sets. A section `s : ∀ x, E x` is *a.e.-strongly measurable*
(`TauCeti.AEStronglyMeasurableSection 𝕜 F μ s`) when its coordinates `x ↦ (e ⟨x, s x⟩).2` in every
trivialization `e` of the bundle atlas are a.e.-strongly measurable for `μ` restricted to the base
set of `e`. This is the measurability notion underlying the spaces `Lᵖ(E, μ)` of sections.

Over a second-countable base, measurability can be tested on any countable family of atlas charts
whose domains cover the base, and more generally on any countable measurable partition subordinate
to atlas charts (`TauCeti.aestronglyMeasurableSection_restrict_iUnion_iff`): coordinates in two
charts differ by the continuous coordinate change. Consequently the fibre norm `x ↦ ‖s x‖` of a
measurable section is a.e.-strongly measurable when the fibre norm is continuous
(`TauCeti.AEStronglyMeasurableSection.aestronglyMeasurable_norm`), and so is the fibre inner
product of two measurable sections of a bundle with fibre inner products, by polarization.

A *measurable isometric frame* `Φ x : V ≃ₗᵢ[𝕜] E x` (`TauCeti.IsMeasurableIsometricFrame`) is a
family of linear isometries from a fixed normed space `V` onto the fibres for which a section is
a.e.-strongly measurable exactly when its coordinates `x ↦ (Φ x).symm (s x)` are. For a
finite-rank bundle whose fibres carry inner products with continuous norm (a continuous Riemannian
or Hermitian metric), Gram–Schmidt frames of the atlas charts, glued along a countable Borel
partition of the base, form a global measurable isometric frame modelled on an inner product space
(`TauCeti.exists_isMeasurableIsometricFrame`). Such a frame identifies measurable sections of `E`
with measurable `V`-valued functions, isometrically in each fibre; it is how the spaces of
`Lᵖ` sections are compared with Mathlib's `MeasureTheory.Lp`.

The measurability of functions `x ↦ G x (f x)` with `G x` continuous and `G · c` measurable is
`MeasureTheory.AEStronglyMeasurable.apply_of_forall_of_continuousAt`; it is what lets coordinates be
changed without any metrizability or countability assumption on the model fibre.

## Main definitions

* `TauCeti.AEStronglyMeasurableSection 𝕜 F μ s`: the coordinates of `s` in every atlas chart are
  a.e.-strongly measurable on the chart domain.
* `TauCeti.IsMeasurableIsometricFrame F μ Φ`: the family of fibre isometries `Φ` detects
  a.e.-strong measurability of sections.

## Main results

* `TauCeti.aestronglyMeasurableSection_restrict_iUnion_iff`: measurability is tested on a
  countable measurable partition subordinate to atlas charts.
* `TauCeti.AEStronglyMeasurableSection.aestronglyMeasurable_norm`,
  `TauCeti.AEStronglyMeasurableSection.aestronglyMeasurable_inner`: fibre norms and fibre inner
  products of measurable sections are measurable.
* `TauCeti.isMeasurableIsometricFrame_restrict_iUnion`: Gram–Schmidt frames of atlas charts glued
  along a countable measurable partition form a measurable isometric frame.
* `TauCeti.exists_isMeasurableIsometricFrame`: a finite-rank bundle with continuous fibre metric
  over a second-countable base has a global measurable isometric frame.

## References

* L. I. Nicolaescu, *Lectures on the Geometry of Manifolds*, 3rd ed., §10.2.3
  (Definition 10.2.30 and Proposition 10.2.31).
-/

public section

noncomputable section

open Bundle MeasureTheory Set Filter Module
open scoped Topology InnerProductSpace

variable {𝕜 B F : Type*} [RCLike 𝕜] [TopologicalSpace B] [MeasurableSpace B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  {μ ν : Measure B}

namespace TauCeti

section Normed

variable [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)] [FiberBundle F E]
  [VectorBundle 𝕜 F E] {s t : ∀ x, E x}

variable (𝕜 F) in
/-- A section `s` of the `𝕜`-vector bundle `E` with model fibre `F` is *a.e.-strongly measurable*
for the measure `μ` on the base when, for every trivialization `e` in the bundle atlas, its
coordinates `x ↦ e.continuousLinearMapAt 𝕜 x (s x)` (extended by zero outside the base set of `e`)
are a.e.-strongly measurable for `μ` restricted to the base set of `e`. -/
def AEStronglyMeasurableSection (μ : Measure B) (s : ∀ x, E x) : Prop :=
  ∀ (e : Trivialization F (π F E)) [MemTrivializationAtlas e],
    AEStronglyMeasurable (fun x ↦ e.continuousLinearMapAt 𝕜 x (s x)) (μ.restrict e.baseSet)

/-- Introduction rule for `TauCeti.AEStronglyMeasurableSection`. -/
theorem AEStronglyMeasurableSection.mk
    (h : ∀ (e : Trivialization F (π F E)) [MemTrivializationAtlas e],
      AEStronglyMeasurable (fun x ↦ e.continuousLinearMapAt 𝕜 x (s x)) (μ.restrict e.baseSet)) :
    AEStronglyMeasurableSection 𝕜 F μ s :=
  h

/-- The coordinates of an a.e.-strongly measurable section in an atlas chart, extended by zero, are
a.e.-strongly measurable on the base set of the chart. -/
theorem AEStronglyMeasurableSection.aestronglyMeasurable_continuousLinearMapAt
    (hs : AEStronglyMeasurableSection 𝕜 F μ s) (e : Trivialization F (π F E))
    [MemTrivializationAtlas e] :
    AEStronglyMeasurable (fun x ↦ e.continuousLinearMapAt 𝕜 x (s x)) (μ.restrict e.baseSet) :=
  hs e

/-- A.e.-strong measurability of sections is inherited by smaller measures. -/
theorem AEStronglyMeasurableSection.mono_measure (hs : AEStronglyMeasurableSection 𝕜 F μ s)
    (h : ν ≤ μ) : AEStronglyMeasurableSection 𝕜 F ν s :=
  fun e _ ↦ (hs e).mono_measure (Measure.restrict_mono subset_rfl h)

/-- A.e.-strong measurability of a section is inherited by restrictions of the measure. -/
theorem AEStronglyMeasurableSection.restrict (hs : AEStronglyMeasurableSection 𝕜 F μ s)
    (A : Set B) : AEStronglyMeasurableSection 𝕜 F (μ.restrict A) s :=
  hs.mono_measure Measure.restrict_le_self

/-- A section almost everywhere equal to an a.e.-strongly measurable section is a.e.-strongly
measurable. -/
theorem AEStronglyMeasurableSection.congr (hs : AEStronglyMeasurableSection 𝕜 F μ s)
    (h : ∀ᵐ x ∂μ, s x = t x) : AEStronglyMeasurableSection 𝕜 F μ t :=
  fun e _ ↦ (hs e).congr (ae_restrict_of_ae (h.mono fun x hx ↦ by simp only [hx]))

theorem aestronglyMeasurableSection_congr (h : ∀ᵐ x ∂μ, s x = t x) :
    AEStronglyMeasurableSection 𝕜 F μ s ↔ AEStronglyMeasurableSection 𝕜 F μ t :=
  ⟨fun hs ↦ hs.congr h, fun ht ↦ ht.congr (h.mono fun _ hx ↦ hx.symm)⟩

/-- Over an empty base, every section is a.e.-strongly measurable. -/
theorem AEStronglyMeasurableSection.of_isEmpty [IsEmpty B] (s : ∀ x, E x) :
    AEStronglyMeasurableSection 𝕜 F μ s :=
  fun _ _ ↦ .of_subsingleton_dom

variable (𝕜 F E μ) in
/-- The zero section is a.e.-strongly measurable. -/
theorem AEStronglyMeasurableSection.zero : AEStronglyMeasurableSection 𝕜 F μ (0 : ∀ x, E x) :=
  fun e _ ↦ by simpa only [Pi.zero_apply, map_zero] using aestronglyMeasurable_const

theorem AEStronglyMeasurableSection.add (hs : AEStronglyMeasurableSection 𝕜 F μ s)
    (ht : AEStronglyMeasurableSection 𝕜 F μ t) :
    AEStronglyMeasurableSection 𝕜 F μ (fun x ↦ s x + t x) :=
  fun e _ ↦ ((hs e).add (ht e)).congr (.of_forall fun x ↦ by simp)

theorem AEStronglyMeasurableSection.const_smul (hs : AEStronglyMeasurableSection 𝕜 F μ s)
    (c : 𝕜) : AEStronglyMeasurableSection 𝕜 F μ (fun x ↦ c • s x) :=
  fun e _ ↦ ((hs e).const_smul c).congr (.of_forall fun x ↦ by simp)

theorem AEStronglyMeasurableSection.neg (hs : AEStronglyMeasurableSection 𝕜 F μ s) :
    AEStronglyMeasurableSection 𝕜 F μ (fun x ↦ -s x) :=
  fun e _ ↦ ((hs e).neg).congr (.of_forall fun x ↦ by simp)

theorem AEStronglyMeasurableSection.sub (hs : AEStronglyMeasurableSection 𝕜 F μ s)
    (ht : AEStronglyMeasurableSection 𝕜 F μ t) :
    AEStronglyMeasurableSection 𝕜 F μ (fun x ↦ s x - t x) :=
  fun e _ ↦ ((hs e).sub (ht e)).congr (.of_forall fun x ↦ by simp)

variable [OpensMeasurableSpace B]

/-- The coordinates of a measurable section in an atlas chart, read through the chart itself, are
a.e.-strongly measurable on its base set. -/
theorem AEStronglyMeasurableSection.aestronglyMeasurable_coord
    (hs : AEStronglyMeasurableSection 𝕜 F μ s) (e : Trivialization F (π F E))
    [MemTrivializationAtlas e] :
    AEStronglyMeasurable (fun x ↦ (e ⟨x, s x⟩).2) (μ.restrict e.baseSet) :=
  (hs e).congr <| (ae_restrict_mem e.open_baseSet.measurableSet).mono fun _ hx ↦
    e.continuousLinearMapAt_apply_of_mem (R := 𝕜) hx _

/-- A section is a.e.-strongly measurable once its coordinates `(e ⟨x, s x⟩).2` in every atlas
chart are a.e.-strongly measurable on the base set of the chart. -/
theorem AEStronglyMeasurableSection.of_coord
    (h : ∀ (e : Trivialization F (π F E)) [MemTrivializationAtlas e],
      AEStronglyMeasurable (fun x ↦ (e ⟨x, s x⟩).2) (μ.restrict e.baseSet)) :
    AEStronglyMeasurableSection 𝕜 F μ s :=
  fun e _ ↦ (h e).congr <| (ae_restrict_mem e.open_baseSet.measurableSet).mono fun _ hx ↦
    (e.continuousLinearMapAt_apply_of_mem (R := 𝕜) hx _).symm

variable [SecondCountableTopology B]

/-- **Independence of the atlas.** Let `A i` be countably many measurable sets, each contained in
the base set of an atlas chart `e i`. A section is a.e.-strongly measurable for `μ` restricted to
`⋃ i, A i` exactly when, for each `i`, its coordinates in `e i` are a.e.-strongly measurable for
`μ` restricted to `A i`. Coordinates in any other atlas chart are obtained by the continuous
coordinate change. -/
theorem aestronglyMeasurableSection_restrict_iUnion_iff {ι : Type*} [Countable ι]
    {A : ι → Set B} (hA : ∀ i, MeasurableSet (A i)) (e : ι → Trivialization F (π F E))
    [∀ i, MemTrivializationAtlas (e i)] (hAe : ∀ i, A i ⊆ (e i).baseSet) :
    AEStronglyMeasurableSection 𝕜 F (μ.restrict (⋃ i, A i)) s ↔
      ∀ i, AEStronglyMeasurable (fun x ↦ (e i ⟨x, s x⟩).2) (μ.restrict (A i)) := by
  refine ⟨fun hs i ↦ ?_, fun h ↦ .of_coord fun e' _ ↦ ?_⟩
  · refine (hs.aestronglyMeasurable_coord (e i)).mono_measure ?_
    rw [Measure.restrict_restrict (e i).open_baseSet.measurableSet]
    exact Measure.restrict_mono (subset_inter (hAe i) (subset_iUnion A i)) le_rfl
  rw [Measure.restrict_restrict e'.open_baseSet.measurableSet, inter_iUnion,
    aestronglyMeasurable_iUnion_iff]
  intro i
  have hm : MeasurableSet (e'.baseSet ∩ A i) := e'.open_baseSet.measurableSet.inter (hA i)
  have hsub : e'.baseSet ∩ A i ⊆ (e i).baseSet ∩ e'.baseSet :=
    fun x hx ↦ ⟨hAe i hx.2, hx.1⟩
  -- On `e'.baseSet ∩ A i`, the coordinates in `e'` are the coordinate change applied to the
  -- coordinates in `e i`; the coordinate change is continuous in the base point.
  refine ((h i).mono_measure (Measure.restrict_mono inter_subset_right le_rfl)
    |>.apply_of_forall_of_continuousAt (g := fun x ↦ (e i).coordChangeL 𝕜 e' x) (fun v ↦ ?_)
      (ae_of_all _ fun x ↦ ((e i).coordChangeL 𝕜 e' x).continuous.continuousAt)).congr ?_
  · exact (((continuousOn_coordChange 𝕜 (e i) e').clm_apply continuousOn_const).mono
      hsub).aestronglyMeasurable hm
  · filter_upwards [ae_restrict_mem hm] with x hx
    rw [Trivialization.coordChangeL_apply _ _ (hsub hx),
      (e i).symm_apply_apply_mk (hsub hx).1]

/-- On a measurable set inside the base set of an atlas chart `e`, a section is a.e.-strongly
measurable exactly when its coordinates in `e` are. -/
theorem aestronglyMeasurableSection_restrict_iff_of_subset_baseSet {U : Set B}
    (hU : MeasurableSet U) (e : Trivialization F (π F E)) [MemTrivializationAtlas e]
    (hUe : U ⊆ e.baseSet) :
    AEStronglyMeasurableSection 𝕜 F (μ.restrict U) s ↔
      AEStronglyMeasurable (fun x ↦ (e ⟨x, s x⟩).2) (μ.restrict U) := by
  simpa only [iUnion_const, forall_const] using
    aestronglyMeasurableSection_restrict_iUnion_iff (𝕜 := 𝕜) (μ := μ) (s := s) (ι := Unit)
      (fun _ ↦ hU) (fun _ ↦ e) fun _ ↦ hUe

/-- Inverse coordinates in an atlas chart `e` of an a.e.-strongly measurable function, on a
measurable subset `U` of the base set of `e`, form an a.e.-strongly measurable section for `μ`
restricted to `U`. -/
theorem aestronglyMeasurableSection_restrict_symm {U : Set B} (hU : MeasurableSet U)
    (e : Trivialization F (π F E)) [MemTrivializationAtlas e] (hUe : U ⊆ e.baseSet) {g : B → F}
    (hg : AEStronglyMeasurable g (μ.restrict U)) :
    AEStronglyMeasurableSection 𝕜 F (μ.restrict U) (fun x ↦ e.symm x (g x)) := by
  refine (aestronglyMeasurableSection_restrict_iff_of_subset_baseSet hU e hUe).2 (hg.congr ?_)
  filter_upwards [ae_restrict_mem hU] with x hx
  rw [e.apply_mk_symm (hUe hx)]

/-- Measurability of a section can be tested on a countable family of atlas charts whose base sets
cover the base. -/
theorem aestronglyMeasurableSection_iff_of_iUnion_baseSet_eq_univ {ι : Type*} [Countable ι]
    (e : ι → Trivialization F (π F E)) [∀ i, MemTrivializationAtlas (e i)]
    (he : ⋃ i, (e i).baseSet = univ) :
    AEStronglyMeasurableSection 𝕜 F μ s ↔
      ∀ i, AEStronglyMeasurable (fun x ↦ (e i ⟨x, s x⟩).2) (μ.restrict (e i).baseSet) := by
  rw [← aestronglyMeasurableSection_restrict_iUnion_iff (𝕜 := 𝕜)
    (fun i ↦ (e i).open_baseSet.measurableSet)
    e fun _ ↦ subset_rfl, he, Measure.restrict_univ]

/-- The fibre norm of an a.e.-strongly measurable section is a.e.-strongly measurable, when the
fibre norm is continuous on the total space. -/
theorem AEStronglyMeasurableSection.aestronglyMeasurable_norm [ContinuousFiberNorm F E]
    (hs : AEStronglyMeasurableSection 𝕜 F μ s) : AEStronglyMeasurable (fun x ↦ ‖s x‖) μ := by
  cases isEmpty_or_nonempty B
  · exact .of_subsingleton_dom
  obtain ⟨p, hp⟩ := FiberBundle.exists_iUnion_baseSet_trivializationAt_eq_univ F E (B := B)
  rw [← Measure.restrict_univ (μ := μ), ← hp, aestronglyMeasurable_iUnion_iff]
  intro n
  set e := trivializationAt F E (p n)
  have hm := e.open_baseSet.measurableSet
  -- On `e.baseSet`, the fibre norm is `‖e.symmL x v‖` at the coordinates `v` of `s`; this is
  -- continuous in `v` and, for fixed `v`, continuous in `x` since the fibre norm is.
  refine ((hs.aestronglyMeasurable_coord e).apply_of_forall_of_continuousAt
    (g := fun x v ↦ ‖e.symmL 𝕜 x v‖) (fun v ↦ ?_)
      (ae_of_all _ fun x ↦ (e.symmL 𝕜 x).continuous.norm.continuousAt)).congr ?_
  · exact (ContinuousOn.norm_bundle_of_continuousFiberNorm (b := id)
      (v := fun x ↦ e.symmL 𝕜 x v) (e.continuousOn_mk_symmL v)).aestronglyMeasurable hm
  · filter_upwards [ae_restrict_mem hm] with x hx
    rw [e.symmL_apply hx, e.symm_apply_apply_mk hx]


end Normed

section IsometricFrame

variable [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)] [FiberBundle F E]
  [VectorBundle 𝕜 F E] {s : ∀ x, E x} {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]

variable (F μ) in
/-- A family of linear isometries `Φ x : V ≃ₗᵢ[𝕜] E x` from a fixed normed space onto the fibres
is a *measurable isometric frame* for `μ` when a section is a.e.-strongly measurable for `μ`
exactly when its coordinates `x ↦ (Φ x).symm (s x)` in the frame are. -/
def IsMeasurableIsometricFrame (Φ : ∀ x, V ≃ₗᵢ[𝕜] E x) : Prop :=
  ∀ s : ∀ x, E x,
    AEStronglyMeasurableSection 𝕜 F μ s ↔ AEStronglyMeasurable (fun x ↦ (Φ x).symm (s x)) μ

theorem isMeasurableIsometricFrame_iff {Φ : ∀ x, V ≃ₗᵢ[𝕜] E x} :
    IsMeasurableIsometricFrame F μ Φ ↔ ∀ s : ∀ x, E x,
      AEStronglyMeasurableSection 𝕜 F μ s ↔ AEStronglyMeasurable (fun x ↦ (Φ x).symm (s x)) μ :=
  Iff.rfl

namespace IsMeasurableIsometricFrame

variable {Φ : ∀ x, V ≃ₗᵢ[𝕜] E x}

/-- The coordinates of a measurable section in a measurable isometric frame are measurable. -/
theorem aestronglyMeasurable_symm_apply (hΦ : IsMeasurableIsometricFrame F μ Φ)
    (hs : AEStronglyMeasurableSection 𝕜 F μ s) :
    AEStronglyMeasurable (fun x ↦ (Φ x).symm (s x)) μ :=
  (hΦ s).1 hs

/-- A measurable function with values in the model space `V` of a measurable isometric frame gives
a measurable section through the frame. -/
theorem aestronglyMeasurableSection_apply (hΦ : IsMeasurableIsometricFrame F μ Φ) {f : B → V}
    (hf : AEStronglyMeasurable f μ) : AEStronglyMeasurableSection 𝕜 F μ (fun x ↦ Φ x (f x)) :=
  (hΦ _).2 (by simpa only [LinearIsometryEquiv.symm_apply_apply] using hf)

end IsMeasurableIsometricFrame

end IsometricFrame

section Inner

variable [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace 𝕜 (E x)] [FiberBundle F E]
  [VectorBundle 𝕜 F E] [OpensMeasurableSpace B] [SecondCountableTopology B]
  [ContinuousFiberNorm F E] {s t : ∀ x, E x}

/-- The fibre inner product of two a.e.-strongly measurable sections is a.e.-strongly measurable,
when the fibre norm is continuous on the total space. -/
theorem AEStronglyMeasurableSection.aestronglyMeasurable_inner
    (hs : AEStronglyMeasurableSection 𝕜 F μ s) (ht : AEStronglyMeasurableSection 𝕜 F μ t) :
    AEStronglyMeasurable (fun x ↦ ⟪s x, t x⟫_𝕜) μ := by
  -- By polarization, the inner product is a combination of the norms of `s + c • t`.
  have hn (c : 𝕜) : AEStronglyMeasurable (fun x ↦ ((‖s x + c • t x‖ : ℝ) : 𝕜)) μ :=
    RCLike.continuous_ofReal.comp_aestronglyMeasurable
      (hs.add (ht.const_smul c)).aestronglyMeasurable_norm
  refine (((((hn 1).pow 2).sub ((hn (-1)).pow 2)).add
    ((((hn (-RCLike.I)).pow 2).sub ((hn RCLike.I).pow 2)).mul_const RCLike.I)).mul_const
      (4⁻¹ : 𝕜)).congr
    (.of_forall fun x ↦ ?_)
  simp only [Pi.add_apply, Pi.sub_apply, Pi.pow_apply, one_smul, neg_smul, ← sub_eq_add_neg,
    inner_eq_sum_norm_sq_div_four (s x) (t x), div_eq_mul_inv]

end Inner

section UnitaryFrame

variable [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace 𝕜 (E x)] [FiberBundle F E]
  [VectorBundle 𝕜 F E] {s : ∀ x, E x} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]


variable [OpensMeasurableSpace B] [SecondCountableTopology B] [ContinuousFiberNorm F E] {ι : Type*}
  [Fintype ι] [LinearOrder ι] [LocallyFiniteOrderBot ι] (c : Basis ι 𝕜 F)
  (b : OrthonormalBasis ι 𝕜 V)

/-- On a measurable set `A` inside the base set of a linear chart `e`, the coordinates of a section
in `e` are a.e.-strongly measurable exactly when its coordinates in the Gram–Schmidt orthonormal
frame of `e` are. The two are related by continuous families of linear maps. -/
private theorem aestronglyMeasurable_coord_iff_orthonormalFrame (e : Trivialization F (π F E))
    [e.IsLinear 𝕜] {A : Set B} (hA : MeasurableSet A) (hAe : A ⊆ e.baseSet)
    {Φ : ∀ x, V ≃ₗᵢ[𝕜] E x} (hΦ : ∀ x (hx : x ∈ A), Φ x = e.orthonormalFrame c b ⟨x, hAe hx⟩) :
    AEStronglyMeasurable (fun x ↦ (e ⟨x, s x⟩).2) (μ.restrict A) ↔
      AEStronglyMeasurable (fun x ↦ (Φ x).symm (s x)) (μ.restrict A) := by
  -- On `A`, the frame `Φ` is the chosen frame `e.orthonormalFrameAt c b`, whose coordinates are
  -- continuous over `e.baseSet`; the two coordinate maps are continuous families of linear maps.
  have hΦ' (x : B) (hx : x ∈ A) : Φ x = e.orthonormalFrameAt c b x := by
    rw [hΦ x hx, e.orthonormalFrameAt_of_mem c b (hAe hx)]
  constructor
  · intro h
    refine (h.apply_of_forall_of_continuousAt
      (g := fun x v ↦ (e.orthonormalFrameAt c b x).symm (e.symmL 𝕜 x v)) (fun v ↦ ?_)
      (ae_of_all _ fun x ↦ ((e.orthonormalFrameAt c b x).symm.continuous.comp
        (e.symmL 𝕜 x).continuous).continuousAt)).congr ?_
    · exact (((e.continuousOn_orthonormalFrameAt_symm c b).comp (e.continuousOn_mk_symmL v)
        fun _ hx ↦ hx).mono hAe).aestronglyMeasurable hA
    · filter_upwards [ae_restrict_mem hA] with x hx
      rw [hΦ' x hx, e.symmL_apply (hAe hx), e.symm_apply_apply_mk (hAe hx)]
  · intro h
    refine (h.apply_of_forall_of_continuousAt
      (g := fun x w ↦ e.continuousLinearMapAt 𝕜 x (e.orthonormalFrameAt c b x w)) (fun w ↦ ?_)
      (ae_of_all _ fun x ↦ ((e.continuousLinearMapAt 𝕜 x).continuous.comp
        (e.orthonormalFrameAt c b x).continuous).continuousAt)).congr ?_
    · refine (ContinuousOn.congr ?_ fun x hx ↦
        e.continuousLinearMapAt_apply_of_mem (R := 𝕜) hx _).mono hAe |>.aestronglyMeasurable hA
      exact continuous_snd.comp_continuousOn
        (e.continuousOn.comp (e.continuousOn_totalSpaceMk_orthonormalFrameAt c b w) fun x hx ↦
          e.mem_source.2 hx)
    · filter_upwards [ae_restrict_mem hA] with x hx
      rw [← hΦ' x hx, LinearIsometryEquiv.apply_symm_apply,
        e.continuousLinearMapAt_apply_of_mem (R := 𝕜) (hAe hx)]

/-- **Gluing Gram–Schmidt frames.** Let `A i` be countably many measurable sets, each contained in
the base set of an atlas chart `e i`, and let `Φ` agree on each `A i` with the Gram–Schmidt
orthonormal frame of `e i`. Then `Φ` is a measurable isometric frame for `μ` restricted to
`⋃ i, A i`. -/
theorem isMeasurableIsometricFrame_restrict_iUnion {κ : Type*} [Countable κ] {A : κ → Set B}
    (hA : ∀ i, MeasurableSet (A i)) (e : κ → Trivialization F (π F E))
    [∀ i, MemTrivializationAtlas (e i)] (hAe : ∀ i, A i ⊆ (e i).baseSet)
    {Φ : ∀ x, V ≃ₗᵢ[𝕜] E x}
    (hΦ : ∀ i x (hx : x ∈ A i), Φ x = (e i).orthonormalFrame c b ⟨x, hAe i hx⟩) :
    IsMeasurableIsometricFrame F (μ.restrict (⋃ i, A i)) Φ := fun s ↦ by
  rw [aestronglyMeasurableSection_restrict_iUnion_iff hA e hAe, aestronglyMeasurable_iUnion_iff]
  exact forall_congr' fun i ↦
    aestronglyMeasurable_coord_iff_orthonormalFrame c b (e i) (hA i) (hAe i) (hΦ i)

/-- The Gram–Schmidt orthonormal frame of an atlas chart `e`, extended arbitrarily outside its base
set, is a measurable isometric frame for `μ` restricted to the base set of `e`. -/
theorem isMeasurableIsometricFrame_restrict_baseSet (e : Trivialization F (π F E))
    [MemTrivializationAtlas e] {Φ : ∀ x, V ≃ₗᵢ[𝕜] E x}
    (hΦ : ∀ x (hx : x ∈ e.baseSet), Φ x = e.orthonormalFrame c b ⟨x, hx⟩) :
    IsMeasurableIsometricFrame F (μ.restrict e.baseSet) Φ := by
  simpa only [iUnion_const] using isMeasurableIsometricFrame_restrict_iUnion (κ := Unit) c b
    (fun _ ↦ e.open_baseSet.measurableSet) (fun _ ↦ e) (fun _ ↦ subset_rfl) fun _ ↦ hΦ

/-- The chosen orthonormal frame `e.orthonormalFrameAt c b` of an atlas chart `e` is a measurable
isometric frame for `μ` restricted to the base set of `e`. -/
theorem _root_.Bundle.Trivialization.isMeasurableIsometricFrame_orthonormalFrameAt
    (e : Trivialization F (π F E)) [MemTrivializationAtlas e] :
    IsMeasurableIsometricFrame F (μ.restrict e.baseSet) (e.orthonormalFrameAt c b) :=
  isMeasurableIsometricFrame_restrict_baseSet c b e fun _ ↦ e.orthonormalFrameAt_of_mem c b

omit c b in
variable (F E V) in
/-- **Existence of measurable isometric frames.** A finite-rank vector bundle with continuous fibre
metric over a second-countable base has a global measurable isometric frame, modelled on any
finite-dimensional inner product space `V` of the same dimension as the model fibre, for every
measure on the base. It is obtained by gluing Gram–Schmidt frames of countably many atlas charts
along the Borel partition of the base they induce. -/
theorem exists_isMeasurableIsometricFrame [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 V]
    (hV : finrank 𝕜 V = finrank 𝕜 F) :
    ∃ Φ : ∀ x, V ≃ₗᵢ[𝕜] E x, ∀ μ : Measure B, IsMeasurableIsometricFrame F μ Φ := by
  classical
  cases isEmpty_or_nonempty B
  · exact ⟨fun x ↦ isEmptyElim x, fun μ s ↦
      ⟨fun _ ↦ .of_subsingleton_dom, fun _ ↦ .of_isEmpty s⟩⟩
  let c := Module.finBasis 𝕜 F
  let b := (stdOrthonormalBasis 𝕜 V).reindex (finCongr hV)
  obtain ⟨p, hp⟩ := FiberBundle.exists_iUnion_baseSet_trivializationAt_eq_univ F E (B := B)
  let e (n : ℕ) := trivializationAt F E (p n)
  have hcover (x : B) : ∃ n, x ∈ (e n).baseSet := mem_iUnion.1 (hp.symm ▸ mem_univ x)
  -- Each point uses the chart of least index containing it.
  let A (n : ℕ) : Set B := {x | Nat.find (hcover x) = n}
  have hAe (n : ℕ) : A n ⊆ (e n).baseSet := fun x hx ↦ hx ▸ Nat.find_spec (hcover x)
  have hA (n : ℕ) : MeasurableSet (A n) :=
    measurable_find hcover (fun k ↦ (e k).open_baseSet.measurableSet)
      (measurableSet_singleton n)
  have hAU : ⋃ n, A n = univ := eq_univ_of_forall fun x ↦ mem_iUnion.2 ⟨_, rfl⟩
  have hframe (x : B) {n m : ℕ} (hn : x ∈ (e n).baseSet) (hm : x ∈ (e m).baseSet) (h : n = m) :
      (e n).orthonormalFrame c b ⟨x, hn⟩ = (e m).orthonormalFrame c b ⟨x, hm⟩ := by
    subst h
    rfl
  refine ⟨fun x ↦ (e (Nat.find (hcover x))).orthonormalFrame c b ⟨x, Nat.find_spec (hcover x)⟩,
    fun μ ↦ ?_⟩
  simpa only [hAU, Measure.restrict_univ] using
    isMeasurableIsometricFrame_restrict_iUnion (μ := μ) c b hA e hAe fun n x hx ↦ hframe x _ _ hx

end UnitaryFrame

end TauCeti
