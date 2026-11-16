/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.MeasureTheory.Measure.Support
public import TauCeti.MeasureTheory.Measure.Atom
public import TauCeti.MeasureTheory.Measure.Dirac

import TauCeti.MeasureTheory.Measure.AEMeasurable
import TauCeti.MeasureTheory.Measure.Prod

/-!
# Conditioning laws, source atoms and connected sources

Conditioning a map on the preimage of a measurable event conditions its law on that event.
This allows conditional distribution identities proved on a canonical law to be used for
arbitrary random variables with that law, including null conditioning events. Likewise,
almost everywhere measurability for a law pulls back along a random variable with that law.

A finite-mass measurable atom of a source measure is an obstruction to a prescribed law: every
almost-everywhere measurable map sends its whole mass to a single point of a standard Borel target.
For singleton atoms this needs no condition on the target measurable space, since their image is
already explicit. This file records both forms of the constraint and their consequences for
transporting Dirac measures and for laws that are null on singletons.

Connectedness of the source is a second obstruction, this time to continuous maps. A map that is
continuous on a set `s` carrying `μ`, with every point of `s` in the support of `μ`, sends all of
`s` into the support of its law. If `s` is moreover preconnected, the law cannot charge
both of two disjoint closed sets that together carry it. So no transport map from a law with
connected support onto a law split into two separated pieces is continuous on that support, which
is the topological reason why optimal transport maps onto disconnected targets are discontinuous.

Adjoining a coordinate with an s-finite measure to a random variable gives the pair the product
measure. Completing the source measure preserves every random variable's law.
Nonnegative random variables whose real coercions have a common law are identically distributed.

## Main results

* `ProbabilityTheory.HasLaw.cond` — conditioning transports a prescribed law;
* `ProbabilityTheory.HasLaw.aemeasurable_of_ae_eq_comp` — a map almost everywhere equal to an
  a.e. measurable map composed with a random variable of the right law is a.e. measurable;
* `ProbabilityTheory.HasLaw.measure_singleton_le` — the law of `T` gives `{T x}` at least the
  mass the source gives `{x}`, with `ProbabilityTheory.HasLaw.measure_singleton_eq_zero` and
  `TauCeti.Probability.not_hasLaw_of_measure_singleton_ne_zero` its reading for a law that is
  null on singletons;
* `ProbabilityTheory.HasLaw.prod_extension` — adjoining a coordinate with an s-finite measure to
  a random variable gives the pair the product measure;
* `ProbabilityTheory.IndepFun.hasLaw_apply_bind` — applying an indexed family to an independent
  selector and noise variable gives a measure bind;
* `ProbabilityTheory.HasLaw.eval_bind` — evaluating a countable family at an independent selector
  gives the bind of its component laws;
* `AEMeasurable.exists_map_restrict_eq_smul_dirac_of_atom` — the image of a finite positive
  measurable atom under an a.e.-measurable map to a standard Borel space is a point mass;
* `ProbabilityTheory.HasLaw.exists_measure_atom_le_measure_singleton` — a law receiving such an
  atom has a singleton of at least the atom's mass;
* `TauCeti.Probability.hasLaw_dirac_source_iff` — an a.e. measurable map has law `ν` under
  `Measure.dirac x` exactly when `ν` is the Dirac measure at its value at `x`;
* `TauCeti.Probability.not_hasLaw_dirac_source_of_forall_ne_dirac` — no map at all has a
  non-Dirac law under a Dirac measure;
* `ProbabilityTheory.HasLaw.mapsTo_support_of_continuousOn` — a map continuous on a carrier of
  `μ` inside its support sends that carrier into the support of its law;
* `ProbabilityTheory.HasLaw.measure_eq_zero_or_measure_eq_zero_of_continuousOn` — a map
  continuous on a preconnected such carrier has a law that does not charge both of two disjoint
  closed sets carrying it.

Mathlib's `ProbabilityTheory.hasLaw_dirac_iff` is the statement for a Dirac *target*; the results
here are about a Dirac *source*, which is what `dirac_source` records in their names.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace TauCeti

namespace Probability

variable {X : Type*} {Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {T : X → Y}
variable {μ : Measure X} {ν : Measure Y}

/-- Conditioning a random variable on the preimage of a measurable event gives its law
conditioned on that event. The statement includes events of zero or infinite mass, when both
conditional measures vanish. -/
theorem _root_.ProbabilityTheory.HasLaw.cond (hT : HasLaw T ν μ) {s : Set Y}
    (hs : MeasurableSet s) :
    HasLaw T (ProbabilityTheory.cond ν s) (ProbabilityTheory.cond μ (T ⁻¹' s)) := by
  refine ⟨hT.aemeasurable.mono_ac cond_absolutelyContinuous, ?_⟩
  rw [ProbabilityTheory.cond, Measure.map_smul _ hT.aemeasurable.restrict,
    ← Measure.restrict_map_of_aemeasurable hT.aemeasurable hs,
    ← Measure.map_apply_of_aemeasurable hT.aemeasurable hs, hT.map_eq,
    ProbabilityTheory.cond]

/-- Nonnegative random variables whose real coercions have the same law are identically
distributed, even when defined on different measure spaces. -/
theorem _root_.ProbabilityTheory.HasLaw.identDistrib_nnreal
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} {X : Ω → ℝ≥0} {Y : Ω' → ℝ≥0} {μ : Measure ℝ}
    (hX : HasLaw (fun ω ↦ (X ω : ℝ)) μ P)
    (hY : HasLaw (fun ω ↦ (Y ω : ℝ)) μ Q) : IdentDistrib X Y P Q := by
  simpa only [Function.comp_def, Real.toNNReal_coe] using
    (hX.identDistrib hY).comp measurable_real_toNNReal

/-- Completing the source measure does not change a random variable's law. -/
theorem _root_.ProbabilityTheory.HasLaw.completion (hT : HasLaw T ν μ) :
    HasLaw (fun x : NullMeasurableSpace X μ => T x) ν μ.completion := by
  have hmeas : AEMeasurable (fun x : NullMeasurableSpace X μ => T x) μ.completion :=
    ⟨hT.aemeasurable.mk T,
      hT.aemeasurable.measurable_mk.mono le_eventuallyMeasurableSpace le_rfl,
      hT.aemeasurable.ae_eq_mk⟩
  refine ⟨hmeas, Measure.ext fun A hA => ?_⟩
  rw [Measure.map_apply_of_aemeasurable hmeas hA]
  -- The type tag on the preimage only records the completed source sigma-algebra.
  exact (Measure.completion_apply μ (T ⁻¹' A)).trans
    ((Measure.map_apply_of_aemeasurable hT.aemeasurable hA).symm.trans
      (congrArg (fun ρ : Measure Y => ρ A) hT.map_eq))

section Atom

variable [StandardBorelSpace Y]

/-- **A source atom constrains the law.** If `A` is a positive finite-mass measurable atom of
`μ`, then every law of a map from `μ` to a standard Borel space has a singleton of mass at least
`μ A`. -/
theorem _root_.ProbabilityTheory.HasLaw.exists_measure_atom_le_measure_singleton
    (h : HasLaw T ν μ) {A : Set X} (hAfin : μ A ≠ ⊤) (hAatom : μ.IsAtom A) :
    ∃ y : Y, μ A ≤ ν {y} := by
  obtain ⟨y, hy⟩ :=
    h.aemeasurable.restrict.exists_map_restrict_eq_smul_dirac_of_atom hAfin hAatom
  refine ⟨y, ?_⟩
  calc
    μ A = Measure.map T (μ.restrict A) {y} := by simp [hy]
    _ ≤ Measure.map T μ {y} :=
      Measure.map_mono_of_aemeasurable Measure.restrict_le_self h.aemeasurable {y}
    _ = ν {y} := by rw [h.map_eq]

/-- A measure with a positive finite-mass measurable atom has no map onto a standard Borel law
that is null on singletons. -/
theorem not_hasLaw_of_measure_atom [NullSingletonClass ν] {A : Set X} (hAfin : μ A ≠ ⊤)
    (hAatom : μ.IsAtom A) (T : X → Y) : ¬HasLaw T ν μ := by
  intro hT
  obtain ⟨y, hy⟩ := hT.exists_measure_atom_le_measure_singleton hAfin hAatom
  exact not_le_of_gt hAatom.pos (hy.trans_eq (measure_singleton y))

end Atom

/-- **A source point mass constrains the law.** A map moves all the mass of `{x}` to the single
point `T x`, so its law weighs `{T x}` at least as much as the source weighs `{x}`. No
measurability of the singletons is needed: the bound comes from
`MeasureTheory.Measure.le_map_apply_image`, which only uses a.e. measurability of the map. -/
theorem _root_.ProbabilityTheory.HasLaw.measure_singleton_le (h : HasLaw T ν μ) (x : X) :
    μ {x} ≤ ν {T x} := by
  simpa only [Set.image_singleton, h.map_eq] using Measure.le_map_apply_image h.aemeasurable {x}

/-- A map whose law is null on singletons has a source that is null on singletons. -/
theorem _root_.ProbabilityTheory.HasLaw.measure_singleton_eq_zero [NullSingletonClass ν]
    (h : HasLaw T ν μ) (x : X) : μ {x} = 0 :=
  nonpos_iff_eq_zero.1 ((h.measure_singleton_le x).trans_eq (measure_singleton _))

/-- Adjoining a coordinate with an s-finite measure `ν` to a random variable with law `μ` gives
the pair the product measure. -/
theorem _root_.ProbabilityTheory.HasLaw.prod_extension {Ω α E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace E] {X : Ω → α}
    {μ : Measure α} {P : Measure Ω} {ν : Measure E} [SFinite ν]
    (hX : HasLaw X μ P) :
    HasLaw (fun z : Ω × E => (X z.1, z.2)) (μ.prod ν) (P.prod ν) := by
  refine ⟨hX.aemeasurable.prodMap measurable_id.aemeasurable, ?_⟩
  -- The product-map measure identity is stated for `Prod.map`.
  have hpair : (fun z : Ω × E => (X z.1, z.2)) = Prod.map X id := by
    funext z
    rfl
  rw [hpair, ← Measure.map_prod_map_of_aemeasurable P ν hX.aemeasurable
    measurable_id.aemeasurable]
  rw [hX.map_eq, Measure.map_id]

/-- Applying an indexed family to an independent selector and noise variable gives the bind of the
component pushforwards. -/
theorem _root_.ProbabilityTheory.IndepFun.hasLaw_apply_bind_map
    {Ω I A B : Type*} [MeasurableSpace Ω] [MeasurableSpace I] [MeasurableSpace A]
    [MeasurableSpace B] {P : Measure Ω} {Z : Ω → I} {U : Ω → A} {μ : Measure I}
    {ρ : Measure A} {f : I → A → B} [IsFiniteMeasure μ] (hZU : IndepFun Z U P)
    (hZ : HasLaw Z μ P) (hU : HasLaw U ρ P)
    (hf : AEMeasurable (Function.uncurry f) (μ.prod ρ)) :
    HasLaw (fun ω ↦ f (Z ω) (U ω)) (μ.bind fun i ↦ ρ.map (f i)) P := by
  let _ : IsFiniteMeasure P := hZ.isFiniteMeasure
  let _ : IsFiniteMeasure ρ := hU.isFiniteMeasure_iff.mp inferInstance
  exact (HasLaw.mk hf (Measure.map_uncurry_prod_eq_bind_map μ ρ hf)).fun_comp
    (hZU.hasLaw_prod hZ hU)

/-- Applying an indexed family to an independent selector and noise variable gives the bind of any
component kernel that agrees almost everywhere with the component pushforwards. -/
theorem _root_.ProbabilityTheory.IndepFun.hasLaw_apply_bind
    {Ω I A B : Type*} [MeasurableSpace Ω] [MeasurableSpace I] [MeasurableSpace A]
    [MeasurableSpace B] {P : Measure Ω} {Z : Ω → I} {U : Ω → A} {μ : Measure I}
    {ρ : Measure A} {K : I → Measure B} {f : I → A → B} [IsFiniteMeasure μ]
    (hZU : IndepFun Z U P) (hZ : HasLaw Z μ P) (hU : HasLaw U ρ P)
    (hf : AEMeasurable (Function.uncurry f) (μ.prod ρ))
    (hK : (fun i ↦ ρ.map (f i)) =ᵐ[μ] K) :
    HasLaw (fun ω ↦ f (Z ω) (U ω)) (μ.bind K) P := by
  have h := hZU.hasLaw_apply_bind_map hZ hU hf
  rw [Measure.bind_congr_right hK] at h
  exact h

/-- Evaluating a countable family of potential random variables at a selector gives the bind of
their laws when the selector is independent of almost every component. Dependence between the
potential variables themselves is allowed. -/
theorem _root_.ProbabilityTheory.HasLaw.eval_bind
    {Ω I B : Type*} [MeasurableSpace Ω] [Countable I] [MeasurableSpace I]
    [MeasurableSingletonClass I] [MeasurableSpace B] {P : Measure Ω} {Z : Ω → I}
    {μ : Measure I} {K : I → Measure B} {Y : I → Ω → B} (hZ : HasLaw Z μ P)
    (hZY : ∀ᵐ i ∂μ, IndepFun Z (Y i) P) (hY : ∀ᵐ i ∂μ, HasLaw (Y i) (K i) P) :
    HasLaw (fun ω ↦ Y (Z ω) ω) (μ.bind K) P := by
  have hZi (i : I) : P (Z ⁻¹' {i}) = μ {i} := hZ.measure_eq (measurableSet_singleton i)
  have hZY' := ae_iff_of_countable.1 hZY
  have hY' := ae_iff_of_countable.1 hY
  have hsel : AEMeasurable (fun ω ↦ Y (Z ω) ω) P :=
    hZ.aemeasurable.eval_selector_of_countable fun i hi ↦
      (hY' i (hZi i ▸ hi)).aemeasurable
  refine ⟨hsel, ?_⟩
  have hK : Measurable K := Measurable.of_discrete
  have hbind : μ.bind K = Measure.sum (fun i ↦ μ {i} • K i) := by
    calc
      μ.bind K = (Measure.sum fun i ↦ μ {i} • Measure.dirac i).bind K := by
        rw [Measure.sum_smul_dirac]
      _ = Measure.sum (fun i ↦ (μ {i} • Measure.dirac i).bind K) :=
        Measure.bind_sum _ _ hK.aemeasurable
      _ = Measure.sum (fun i ↦ μ {i} • K i) := by
        congr 1
        funext i
        rw [Measure.bind_smul _ _ hK.aemeasurable, Measure.dirac_bind hK]
  ext s hs
  rw [Measure.map_apply_of_aemeasurable hsel hs, hbind, Measure.sum_apply _ hs]
  have hpre : (fun ω ↦ Y (Z ω) ω) ⁻¹' s = ⋃ i, Z ⁻¹' {i} ∩ Y i ⁻¹' s := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_singleton_iff]
    exact ⟨fun h ↦ ⟨Z ω, rfl, h⟩, fun ⟨_i, hi, h⟩ ↦ hi ▸ h⟩
  rw [hpre, measure_iUnion₀]
  · simp only [smul_apply, smul_eq_mul]
    apply tsum_congr
    intro i
    by_cases hi : μ {i} = 0
    · rw [measure_mono_null Set.inter_subset_left (hZi i |>.trans hi), hi, zero_mul]
    · have hYi : P (Y i ⁻¹' s) = K i s := (hY' i hi).measure_eq hs
      rw [(hZY' i hi).measure_inter_preimage_eq_mul {i} s (measurableSet_singleton i) hs,
        hZi i, hYi]
  · intro i j hij
    exact Disjoint.aedisjoint
      (Disjoint.mono Set.inter_subset_left Set.inter_subset_left
        ((Set.disjoint_singleton.2 hij).preimage Z))
  · intro i
    by_cases hi : μ {i} = 0
    · exact NullMeasurableSet.of_null
        (measure_mono_null Set.inter_subset_left (hZi i |>.trans hi))
    · exact (hZ.aemeasurable.nullMeasurableSet_preimage (measurableSet_singleton i)).inter
        ((hY' i hi).aemeasurable.nullMeasurableSet_preimage hs)

/-- **A nonzero source singleton has no transport onto a law that is null on singletons.** This
is the basic infeasibility of the Monge problem: no map can push such a source measure onto such
a target measure. -/
theorem not_hasLaw_of_measure_singleton_ne_zero [NullSingletonClass ν] {x : X}
    (hx : μ {x} ≠ 0) (T : X → Y) : ¬HasLaw T ν μ :=
  fun h ↦ hx (h.measure_singleton_eq_zero x)

/-- A map almost everywhere equal to `T ∘ s`, where `s` has law `μ` and `T` is `μ`-almost
everywhere measurable, is almost everywhere measurable. -/
theorem _root_.ProbabilityTheory.HasLaw.aemeasurable_of_ae_eq_comp {Ω : Type*}
    [MeasurableSpace Ω] {m : Measure Ω} {s : Ω → X} {U : Ω → Y} (hs : HasLaw s μ m)
    (hT : AEMeasurable T μ) (h : U =ᵐ[m] T ∘ s) : AEMeasurable U m :=
  ((hasLaw_map hT).comp hs).aemeasurable.congr h.symm

/-- An a.e. measurable map transports a Dirac measure exactly onto the Dirac measure at its
value. The a.e. measurability is exactly what `ProbabilityTheory.HasLaw` already asks for. -/
theorem hasLaw_dirac_source_iff {x : X} (hT : AEMeasurable T (Measure.dirac x)) :
    HasLaw T ν (Measure.dirac x) ↔ ν = Measure.dirac (T x) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨hT, ?_⟩⟩
  · rw [← h.map_eq, Measure.map_dirac_of_aemeasurable hT]
  · rw [Measure.map_dirac_of_aemeasurable hT, h]

/-- **A Dirac source admits no non-Dirac law.** No map at all pushes a Dirac measure onto a
measure that is not itself a Dirac measure: a map carries its own a.e. measurability along with
the law it is claimed to have. -/
theorem not_hasLaw_dirac_source_of_forall_ne_dirac (hν : ∀ y : Y, ν ≠ Measure.dirac y) (x : X) :
    ¬HasLaw T ν (Measure.dirac x) :=
  fun h ↦ hν (T x) ((hasLaw_dirac_source_iff h.aemeasurable).1 h)

section Topology

variable [TopologicalSpace X] [TopologicalSpace Y] {s : Set X}

/-- **A continuous transport map sends its domain into the support of its law.** Let `T` be
continuous on a set `s` carrying `μ` and contained in the support of `μ`. Then `T` maps all of
`s`, not merely almost all of it, into the support of the law `ν` of `T`. -/
theorem _root_.ProbabilityTheory.HasLaw.mapsTo_support_of_continuousOn (h : HasLaw T ν μ)
    (hμs : ∀ᵐ x ∂μ, x ∈ s) (hsμ : s ⊆ μ.support) (hT : ContinuousOn T s) :
    Set.MapsTo T s ν.support := by
  intro x hx
  rw [Measure.support_eq_forall_isOpen]
  intro U hxU hU
  obtain ⟨V, hV, hVs⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 (hT x hx (hU.mem_nhds hxU))
  calc 0 < μ V := (Measure.mem_support_iff_forall x).1 (hsμ hx) V hV
    _ = μ (V ∩ s) := (measure_inter_conull (ae_iff.1 hμs)).symm
    _ ≤ μ (T ⁻¹' U) := measure_mono hVs
    _ ≤ ν U := h.map_eq ▸ Measure.le_map_apply h.aemeasurable U

variable [OpensMeasurableSpace Y]

/-- **A continuous map from a connected source cannot split its law.** Let `T` be continuous on
a preconnected set `s` carrying `μ` and contained in the support of `μ`. If the law `ν` of `T` is
carried by the union of two disjoint closed sets, then it does not charge one of them. -/
theorem _root_.ProbabilityTheory.HasLaw.measure_eq_zero_or_measure_eq_zero_of_continuousOn
    (h : HasLaw T ν μ) (hs : IsPreconnected s) (hμs : ∀ᵐ x ∂μ, x ∈ s) (hsμ : s ⊆ μ.support)
    (hT : ContinuousOn T s) {A B : Set Y} (hA : IsClosed A) (hB : IsClosed B)
    (hAB : Disjoint A B) (hνAB : ν (A ∪ B)ᶜ = 0) : ν A = 0 ∨ ν B = 0 := by
  -- If `T` maps `s` into one closed set, the other one has a null preimage, contained in `sᶜ`.
  have hnull : ∀ {C D : Set Y}, IsClosed D → Set.MapsTo T s C → Disjoint C D → ν D = 0 :=
    fun {C D} hD hTC hCD => by
      rw [← h.map_eq, Measure.map_apply_of_aemeasurable h.aemeasurable hD.measurableSet]
      refine measure_mono_null ?_ (ae_iff.1 hμs)
      exact fun x hx hxs => hCD.notMem_of_mem_left (hTC hxs) hx
  have hsub := isPreconnected_iff_subset_of_disjoint_closed.1 (hs.image T hT) A B hA hB
    ((h.mapsTo_support_of_continuousOn hμs hsμ hT).mono_right
      (Measure.support_subset_of_isClosed (hA.union hB) (mem_ae_iff.2 hνAB))).image_subset
    (by rw [hAB.inter_eq, Set.inter_empty])
  rcases hsub with hsA | hsB
  · exact Or.inr (hnull hB (Set.mapsTo_iff_image_subset.2 hsA) hAB)
  · exact Or.inl (hnull hA (Set.mapsTo_iff_image_subset.2 hsB) hAB.symm)

end Topology

end Probability

end TauCeti
